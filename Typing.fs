(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast

type subst = (tyvar * ty) list

// debug function
let rec printSubst (s : subst) = 
    match s with
    | [] -> ()
    | (tyvar, ty) :: tl -> 
        printfn "%d -> %A" tyvar ty
        printSubst tl

let print_sub (s : subst) =
    printf "\n SUBSTITUTIONs \n"
    printSubst s
    printf "\n END \n"

//
// Utility
//

let type_error fmt = throw_formatted TypeError fmt

let mutable tyVarCounter = 0

let freshTyVar = 
    tyVarCounter <- tyVarCounter + 1
    TyVar tyVarCounter

// TODO implement this (DONE)
let rec apply_subst (s : subst) (t : ty) : ty =
    match t with
    | TyName _ -> t

    | TyArrow (t1, t2) -> TyArrow (apply_subst s t1, apply_subst s t2)

    | TyVar tv -> 
        try
            let _, t1 = List.find (fun (tv1, _) -> tv1 = tv) s
            in
                t1
        with KeyNotFoundException -> t // maybe try this
        //TODO: avoid circularity

    | TyTuple ts -> TyTuple (List.map (apply_subst s) ts)

// given a list l, for every element of a list 
let mapEq (l: (tyvar * ty) List) ((tv: tyvar), (t: ty)) =
    let p = List.tryFind (fun (tvl,_) -> tv = tvl) l

    match p with
    | None -> tv, t // no element found
    | Some (tv2, t2) -> 
        if t2 <> t then type_error "Cannot compose substs with <> mappings for the same TyVar (s2 has [%d -> %O] while s1 has [%d -> %O])" tv t tv2 t2
        else tv2, apply_subst [(tv, t)] t2

// TODO implement this
let compose_subst (s1 : subst) (s2 : subst) : subst =
    (List.map (mapEq s1) s2) @ s1 
    

// TODO implement this (DONE)
let rec unify (t1 : ty) (t2 : ty) : subst = 
    match (t1, t2) with
    | TyName s1, TyName s2 when s1 = s2 -> [] 

    | TyVar tv, t
    | t, TyVar tv -> [tv, t]

    | TyArrow (t1, t2), TyArrow (t3, t4) -> compose_subst (unify t1 t3) (unify t2 t4)

    | TyTuple ts1, TyTuple ts2 when List.length ts1 = List.length ts2 ->
        List.fold (fun s (t1, t2) -> compose_subst s (unify t1 t2)) [] (List.zip ts1 ts2)

    | _ -> type_error "cannot unify types %O and %O" t1 t2

let rec freevars_ty t =
    match t with
    | TyName s -> Set.empty
    | TyArrow (t1, t2) -> (freevars_ty t1) + (freevars_ty t2)
    | TyVar tv -> Set.singleton tv
    | TyTuple ts -> List.fold (fun r t -> r + freevars_ty t) Set.empty ts

let freevars_scheme (Forall (tvs, t)) = freevars_ty t - tvs

let freevars_scheme_env (env: scheme env) =
    List.fold (fun r (_, sch) -> r + freevars_scheme sch) Set.empty env

// generalize a ty to scheme
let generalize_scheme_env (t: ty) (env: scheme env) : scheme  = 
        let tvs = freevars_ty t - freevars_scheme_env env
        let sch = Forall (tvs, t) 
        sch

// utility fun for inst_ty
let rec re (tvs: Set<tyvar>) (t: ty) : ty =
    match t with
    | TyName x -> TyName x

    | TyVar x -> 
        if(Set.contains x tvs) // controlla se 'a è in 'a negato  
            then freshTyVar 
            else TyVar x
    
    | TyArrow(t1, t2) -> TyArrow(re tvs t1, re tvs t2)
    
    | TyTuple(ts) -> TyTuple(List.map (fun (t) -> re tvs t) ts)


// instantiate a ty from a scheme
let inst_ty (Forall (tvs, t)) : ty = 
    re tvs t


// basic environment:
// TODO: add builtin operators at will

let gamma0 = [
    ("+", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("-", TyArrow (TyInt, TyArrow (TyInt, TyInt)))

]

// basic enviroment for type inference
// create a list as env of (string * type scheme)
let init_scheme_env = List.map (fun (s, t) -> (s, Forall (Set.empty, t))) gamma0


// TODO continue implementing this
let rec typeinfer_expr (env : scheme env) (e : expr) : ty * subst =
    match e with
    | Lit (LInt _) -> TyInt, [] 
    | Lit (LBool _) -> TyBool, []
    | Lit (LFloat _) -> TyFloat, [] 
    | Lit (LString _) -> TyString, []
    | Lit (LChar _) -> TyChar, [] 
    | Lit LUnit -> TyUnit, []

    | Var x -> 
        try
            let _, sch = List.find (fun (y, _) -> x = y) env // prendo schema di x
            let t = inst_ty sch // instanzializzo lo schema per ricavare t
            t, [] 
        with KeyNotFoundException -> type_error "%s in not in the domain" x

    | Lambda (x, tyo, e) ->  // tyo = type optional (annotated lambda)
        let tv = freshTyVar
        let sch = Forall(Set.empty, tv) // dummy ty scheme
        let t2, s1 = typeinfer_expr ((x, sch) :: env) e
        let t1 = apply_subst s1 tv

        // annotated lambdas
        let s2 = 
            match tyo with
            | None -> []
            | Some t -> unify t1 t 

        TyArrow(t1, t2), compose_subst s1 s2

    | Let (x, tyo, e1, e2) ->
        let t1, s1 = typeinfer_expr env e1
        //let tvs = freevars_ty t1 - freevars_scheme_env env
        //let sch = Forall (tvs, t1)
        let sch = generalize_scheme_env t1 env
        let t2, s2 = typeinfer_expr ((x, sch) :: env) e2 //TODO: manca applicazione sostituzione s1 a env (guarda regola)
        t2, compose_subst s2 s1

    | _ -> failwithf "not implemented"


// type checker
//
    
let rec typecheck_expr (env : ty env) (e : expr) : ty =
    match e with
    | Lit (LInt _) -> TyInt
    | Lit (LFloat _) -> TyFloat
    | Lit (LString _) -> TyString
    | Lit (LChar _) -> TyChar
    | Lit (LBool _) -> TyBool
    | Lit LUnit -> TyUnit

    | Var x ->
        let _, t = List.find (fun (y, _) -> x = y) env
        t

    | Lambda (x, None, e) -> unexpected_error "typecheck_expr: unannotated lambda is not supported"
    
    | Lambda (x, Some t1, e) ->
        let t2 = typecheck_expr ((x, t1) :: env) e
        TyArrow (t1, t2)

    | App (e1, e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1 with
        | TyArrow (l, r) ->
            if l = t2 then r 
            else type_error "wrong application: argument type %s does not match function domain %s" (pretty_ty t2) (pretty_ty l)
        | _ -> type_error "expecting a function on left side of application, but got %s" (pretty_ty t1)

    | Let (x, tyo, e1, e2) ->
        let t1 = typecheck_expr env e1
        match tyo with
        | None -> ()
        | Some t -> if t <> t1 then type_error "type annotation in let binding of %s is wrong: exptected %s, but got %s" x (pretty_ty t) (pretty_ty t1)
        typecheck_expr ((x, t1) :: env) e2

    | IfThenElse (e1, e2, e3o) ->
        let t1 = typecheck_expr env e1
        if t1 <> TyBool then type_error "if condition must be a bool, but got a %s" (pretty_ty t1)
        let t2 = typecheck_expr env e2
        match e3o with
        | None ->
            if t2 <> TyUnit then type_error "if-then without else requires unit type on then branch, but got %s" (pretty_ty t2)
            TyUnit
        | Some e3 ->
            let t3 = typecheck_expr env e3
            if t2 <> t3 then type_error "type mismatch in if-then-else: then branch has type %s and is different from else branch type %s" (pretty_ty t2) (pretty_ty t3)
            t2

    | Tuple es ->
        TyTuple (List.map (typecheck_expr env) es)

    | LetRec (f, None, e1, e2) ->
        unexpected_error "typecheck_expr: unannotated let rec is not supported"
        
    | LetRec (f, Some tf, e1, e2) ->
        let env0 = (f, tf) :: env
        let t1 = typecheck_expr env0 e1
        match t1 with
        | TyArrow _ -> ()
        | _ -> type_error "let rec is restricted to functions, but got type %s" (pretty_ty t1)
        if t1 <> tf then type_error "let rec type mismatch: expected %s, but got %s" (pretty_ty tf) (pretty_ty t1)
        typecheck_expr env0 e2

    | BinOp (e1, ("+" | "-" | "/" | "%" | "*" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyInt, TyInt -> TyInt
        | TyFloat, TyFloat -> TyFloat
        | TyInt, TyFloat
        | TyFloat, TyInt -> TyFloat
        | _ -> type_error "binary operator expects two int operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        
    | BinOp (e1, ("<" | "<=" | ">" | ">=" | "=" | "<>" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyInt, TyInt -> ()
        | _ -> type_error "binary operator expects two numeric operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        TyBool

    | BinOp (e1, ("and" | "or" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyBool, TyBool -> ()
        | _ -> type_error "binary operator expects two bools operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        TyBool

    | BinOp (_, op, _) -> unexpected_error "typecheck_expr: unsupported binary operator (%s)" op

    | UnOp ("not", e) ->
        let t = typecheck_expr env e
        if t <> TyBool then type_error "unary not expects a bool operand, but got %s" (pretty_ty t)
        TyBool
            
    | UnOp ("-", e) ->
        let t = typecheck_expr env e
        match t with
        | TyInt -> TyInt
        | TyFloat -> TyFloat
        | _ -> type_error "unary negation expects a numeric operand, but got %s" (pretty_ty t)

    | UnOp (op, _) -> unexpected_error "typecheck_expr: unsupported unary operator (%s)" op

    | _ -> unexpected_error "typecheck_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e
