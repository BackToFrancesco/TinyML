(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast

type subst = (tyvar * ty) list

//
// Utility
//

let type_error fmt = throw_formatted TypeError fmt

let mutable tyVarCounter = 0

let freshTyVar (): ty = 
    tyVarCounter <- tyVarCounter + 1
    TyVar tyVarCounter

let rec freevars_ty t =
    match t with
    | TyName s -> Set.empty
    | TyArrow (t1, t2) -> (freevars_ty t1) + (freevars_ty t2)
    | TyVar tv -> Set.singleton tv
    | TyTuple ts -> List.fold (fun r t -> r + freevars_ty t) Set.empty ts

let freevars_scheme (Forall (tvs, t)) = freevars_ty t - tvs

let freevars_scheme_env (env: scheme env) =
    List.fold (fun r (_, sch) -> r + freevars_scheme sch) Set.empty env

// TODO implement this (DONE)
let rec apply_subst (s : subst) (t : ty) : ty =
    match t with
    | TyName _ -> t

    | TyArrow (t1, t2) -> TyArrow (apply_subst s t1, apply_subst s t2)

    | TyVar tv -> 
            let p = List.tryFind (fun (tv1, _) -> tv1 = tv) s
            match p with
            | None -> t 
            | Some (_, t) -> 
            // avoid circularity e.g. 1 -> (1 -> int)
            let tvs = freevars_ty t 

            if Set.contains tv tvs then type_error "Cannot apply substitution [%O -> %O], circularity not allowed" tv t
            else t

    | TyTuple ts -> TyTuple (List.map (apply_subst s) ts)

// Apply a substitution to a scheme
let apply_subst_scheme  (Forall (tvs, t)) (s: subst): scheme = 
    let s1 = List.filter (fun (tv, _) -> not (Set.contains tv tvs)) s
    Forall(tvs, apply_subst s1 t)

// Apply a substitution to the env
let apply_subst_scheme_env (env: scheme env) (s: subst) : scheme env =
    List.map (fun (id , sch) -> id, apply_subst_scheme sch s) env

(* 
given a subst list l checks if there is an element in l (tvl, tl) and tvl = tv
  - if yes -> 
              1. controls tl <> t (type variable not mapped to different types)
              2. if tl = t return (tv, l(t))
  - if no -> return (tv, t)
*)
let mapEq (l: subst) ((tv: tyvar), (t: ty)) =
    let p = List.tryFind (fun (tvl,_) -> tv = tvl) l

    match p with
    | None -> tv, t
    | Some (_ , tl) -> 
        // disjoint 
        if tl <> t 
        then type_error "Cannot compose substs with <> mappings for the same TyVar (s2 has [%d -> %O] while s1 has [%d -> %O])" tv t tv tl
        else tv, apply_subst l t

// TODO implement this (DONE)
let compose_subst (s1 : subst) (s2 : subst) : subst = (List.map (mapEq s1) s2) @ s1   

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

// generalize a ty to scheme
let generalize_scheme_env (t: ty) (env: scheme env) : scheme  = 
        let tvs = freevars_ty t - freevars_scheme_env env
        Forall (tvs, t)

// instantiate a ty from a scheme
let inst_ty (Forall (tvs, t)) : ty =
    let s = Set.fold (fun acc tv -> (tv, freshTyVar ()) :: acc) List.Empty tvs
    apply_subst s t

//
//          Pretty print with greek letters
//

// utility function for pretty_ty_gl for print type in the correct format
let rec pretty_ty_tvs mappings t =
    match t with
    | TyName s -> s
    | TyArrow (TyArrow _ as t1, t3) -> sprintf "(%s) -> %s" (pretty_ty_tvs mappings t1) (pretty_ty_tvs mappings t3)
    | TyArrow (t1, t2) -> sprintf "%s -> %s" (pretty_ty_tvs mappings t1) (pretty_ty_tvs mappings t2)
    | TyVar n -> 
        let _, pretty_tv = List.find (fun (ftv, _) -> ftv = n) mappings
        sprintf "'%c" pretty_tv
    | TyTuple ts -> sprintf "(%s)" (Ast.pretty_tupled (pretty_ty_tvs mappings) ts)

// pretty_ty_gl is for printing greek letters instead numbers in types
let pretty_ty_gl t =
    let ftvs = freevars_ty t

    if Set.count ftvs > 0 
        then
            let alphabet = List.truncate (Set.count ftvs) ['a' .. 'z']
            pretty_ty_tvs (List.zip (Set.toList ftvs) alphabet) t
        else Ast.pretty_ty t

//
//           Basic environment:
//

let gamma0 = [
    // binary int operators
    ("+", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("-", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("*", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("/", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("%", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("<", TyArrow (TyInt, TyArrow(TyInt, TyBool)))
    ("<=", TyArrow (TyInt, TyArrow(TyInt, TyBool)))
    (">", TyArrow (TyInt, TyArrow(TyInt, TyBool)))
    (">=", TyArrow (TyInt, TyArrow(TyInt, TyBool)))
    ("=", TyArrow (TyInt, TyArrow(TyInt, TyBool)))
    ("<>", TyArrow (TyInt, TyArrow(TyInt, TyBool)))

    // binary float operators
    ("+.", TyArrow (TyFloat, TyArrow (TyFloat, TyFloat)))
    ("-.", TyArrow (TyFloat, TyArrow (TyFloat, TyFloat)))
    ("*.", TyArrow (TyFloat, TyArrow (TyFloat, TyFloat)))
    ("/.", TyArrow (TyFloat, TyArrow (TyFloat, TyFloat)))
    ("<.", TyArrow (TyFloat, TyArrow(TyFloat, TyBool)))
    ("<=.", TyArrow (TyFloat, TyArrow(TyFloat, TyBool)))
    (">.", TyArrow (TyFloat, TyArrow(TyFloat, TyBool)))
    (">=.", TyArrow (TyFloat, TyArrow(TyFloat, TyBool)))
    ("=.", TyArrow (TyFloat, TyArrow(TyFloat, TyBool)))
    ("<>.", TyArrow (TyFloat, TyArrow(TyFloat, TyBool)))

    // binary bool operators
    ("and", TyArrow (TyBool, TyArrow(TyBool, TyBool)))
    ("or", TyArrow (TyBool, TyArrow(TyBool, TyBool)))

    // unary operators
    ("not", TyArrow (TyBool, TyBool))
    ("neg", TyArrow (TyInt, TyInt))
    ("neg.", TyArrow (TyFloat, TyFloat))
]

// basic enviroment for type inference
let init_scheme_env = List.map (fun (s, t) -> (s, Forall (Set.empty, t))) gamma0


// TODO continue implementing this (DONE)
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
            let _, sch = List.find (fun (y, _) -> x = y) env
            let t = inst_ty sch
            t, [] 
        with KeyNotFoundException -> type_error "%s in not in the domain" x

    | Lambda (x, tyo, e) ->  // tyo = type optional (annotated lambda)
        let tv = freshTyVar ()
        let sch = Forall(Set.empty, tv) // dummy ty scheme
        let t2, s1 = typeinfer_expr ((x, sch) :: env) e
        let t1 = apply_subst s1 tv

        let s2 = 
            match tyo with
            | None -> []
            | Some t -> unify t1 t 

        TyArrow(apply_subst s2 t1, t2), compose_subst s1 s2

    | App(e1, e2) -> 
        let t1, s1 = typeinfer_expr env e1

        let t2, s2 = typeinfer_expr (apply_subst_scheme_env env s1) e2

        let fresh_ty = freshTyVar ()
        let s3 = compose_subst s1 s2

        let s4 = unify (TyArrow(apply_subst s3 t2, fresh_ty)) (apply_subst s3 t1)
        apply_subst s4 fresh_ty, compose_subst s3 s4

    | Let (x, tyo, e1, e2) ->
        let t1, s1 = typeinfer_expr env e1

        let s2 = 
            match tyo with
            | None -> list.Empty 
            | Some ty -> unify (apply_subst s1 t1) ty

        let s3 = compose_subst s1 s2

        let sch = generalize_scheme_env (apply_subst s3 t1) (apply_subst_scheme_env env s3)
        let t2, s4 = typeinfer_expr ((x, sch) :: (apply_subst_scheme_env env s3)) e2
        let s5 = compose_subst s3 s4
        apply_subst s5 t2, s5

    | IfThenElse (e1, e2, e3o) ->
        let t1, s1 = typeinfer_expr env e1
        let s2 = unify TyBool t1

        let s3 = compose_subst s1 s2
        let t2, s4 = typeinfer_expr (apply_subst_scheme_env env s3) e2
        let s5 = compose_subst s3 s4

        let t, s = 
            match e3o with
            | None -> 
                let so = unify t2 TyUnit
                apply_subst s5 t2, compose_subst s5 so
            // else branch
            | Some e3 ->
                let t3, s6 = typeinfer_expr (apply_subst_scheme_env env s5) e3
                let s7 = compose_subst s5 s6
                let s8 = unify (apply_subst s7 t2) (apply_subst s7 t3)
                apply_subst s8 t2, compose_subst s7 s8
        t, s  
        
    | Tuple es -> 
        let rec mapf (es: expr list) (s: subst) : ty list * subst =
            match es with
            | [] -> [], s
            | x::xs -> 
                let t1, s1 = typeinfer_expr (apply_subst_scheme_env env s) x
                let t2, s2 = mapf xs (compose_subst s s1)
                (apply_subst s1 t1)::t2, compose_subst s1 s2 
        
        let t, s = mapf es []

        TyTuple(t), s

    | LetRec (f, tfo, e1, e2) -> 
        let t1, s1 = typeinfer_expr ((f, Forall(Set.empty, freshTyVar ()))::env) e1

        let s2 = 
            match tfo with
            | None -> List.empty
            | Some t -> unify t t1 

        let s3 = compose_subst s1 s2

        let sch = generalize_scheme_env (apply_subst s3 t1) (apply_subst_scheme_env env s3)
        let t2, s4 = typeinfer_expr ((f, sch) :: (apply_subst_scheme_env env s3)) e2

        let s5 = compose_subst s3 s4
        apply_subst s5 t2, s5
        
    | BinOp (e1, op, e2) -> 
        if List.contains op (List.map (fun (s, _) -> s) init_scheme_env)
            then 
                typeinfer_expr env (App (App (Var op, e1), e2))
            else 
                unexpected_error "typeinfer_expr: unsupported binary operator (%s)" op

    | UnOp (op, e) ->
        if List.contains op (List.map (fun (s, _) -> s) init_scheme_env)
            then
                typeinfer_expr env (App (Var op, e))
            else 
                unexpected_error "typeinfer_expr: unsupported unary operator (%s)" op

    | _ -> failwithf "not implemented"

//
//          Type checker
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

