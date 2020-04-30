module FLispy.ParseExtension

let gensym =
    let prefix = sprintf "x@%d"
    let mutable n = -1
    fun () ->
        n <- n + 1
        prefix n

let private elementaryOperations =
    let ops = [
        "=", ["*dummy-type*"; "*dummy-type*"; "Bool"]
        "distinct", ["*dummy-type*"; "*dummy-type*"; "Bool"]
        ">", ["Int"; "Int"; "Bool"]
        "<", ["Int"; "Int"; "Bool"]
        "<=", ["Int"; "Int"; "Bool"]
        ">=", ["Int"; "Int"; "Bool"]
        "+", ["Int"; "Int"; "Int"]
        "-", ["Int"; "Int"; "Int"]
        "*", ["Int"; "Int"; "Int"]
        "mod", ["Int"; "Int"; "Int"]
        "div", ["Int"; "Int"; "Int"]
        "=>", ["Bool"; "Bool"; "Bool"]
    ]
    let ops = List.map (fun ((op, sign) as os) -> op, ElementaryOperation(os)) ops
    Map.ofList ops
let private hence = let f = Map.find "=>" elementaryOperations in fun t1 t2 -> Apply(f, [t1; t2])
let private equal = let f = Map.find "=" elementaryOperations in fun t1 t2 -> Apply(f, [t1; t2])

let typeOfOp = function
    | ElementaryOperation(_, s)
    | UserDefinedOperation(_, s) -> List.last s
let rec typeOf = function
    | Constant(Number _) -> "Int"
    | Forall _
    | Exists _
    | And _
    | Or _
    | Not _
    | Constant(Bool _) -> "Bool"
    | Ident(_, t) -> t
    | Apply(op, _) -> typeOfOp op
    | Match(_, ((_, t)::_))
    | Ite(_, t, _)
    | Let(_, t) -> typeOf t
    | Match(_, []) -> __unreachable__()

let private to_sorted_vars = List.map (function PList [PSymbol v; PSymbol s] -> v, s | _ -> __unreachable__())
let private to_var_binding = List.map (function PList [PSymbol v; t] -> v, t | _ -> __unreachable__())
let private obtain_sort vars retSort = List.map snd vars @ [retSort]
let private extend_env env vars = List.fold (fun typer (v, s) -> Map.add v s typer) env vars
let private create_env = extend_env Map.empty
let sort_of_operation = function
    | ElementaryOperation(_, s)
    | UserDefinedOperation(_, s) -> s
let addUserOperation typer name sorts = Map.add name (UserDefinedOperation(name, sorts)) typer
let addElementaryOperation typer name sorts = Map.add name (ElementaryOperation(name, sorts)) typer
let private tryTypeCheck f typer = Option.bind (sort_of_operation >> List.tryLast) (Map.tryFind f typer)
let private getOperation f typer =
    match Map.tryFind f typer with
    | Some r -> r
    | _ -> failwithf "Unknown type: %s" f
let private typeGet x (typer, env) =
    match Map.tryFind x env with
    | Some t -> t
    | None ->
        match tryTypeCheck x typer with
        | Some t -> t
        | None -> failwithf "Unknown type: %s" x

let rec private toExpr ((typer, env) as te) = function
    | PNumber n -> Constant (Number n)
    | PSymbol "true" -> Constant (Bool true)
    | PSymbol "false" -> Constant (Bool false)
    | PList [] -> __unreachable__()
    | PList [PSymbol "let"; PList bindings; body] ->
        let handle_binding env (v, e) =
            let e = toExpr (typer, env) e
            (v, e), Map.add v (typeOf e) env
        let bindings = to_var_binding bindings
        let bindings, env = List.mapFold handle_binding env bindings
        let body = toExpr (typer, env) body
        Let(bindings, body)
    | PList [PSymbol "forall"; PList vars; body] ->
        let vars = to_sorted_vars vars
        let env = extend_env env vars
        Forall(vars, toExpr (typer, env) body)
    | PList [PSymbol "exists"; PList vars; body] ->
        let vars = to_sorted_vars vars
        let env = extend_env env vars
        Exists(vars, toExpr (typer, env) body)
    | PList (op::args) ->
        let args = List.map (toExpr te) args
        match op, args with
        | PSymbol "ite", [i; t; e] -> Ite(i, t, e)
        | PSymbol "and", _ -> And args
        | PSymbol "or", _ -> Or args
        | PSymbol "not", [arg] -> Not arg
        | PSymbol f, args ->
            let op = getOperation f typer
            Apply(op, args)
        | e -> failwithf "%O" e
    | PSymbol x -> Ident(x, typeGet x te)
    | PMatch(t, cases) ->
        let t = toExpr te t
        let typ = typeOf t
        let extendEnvironment env = function
            | PSymbol v, typ ->
                let id = Ident(v, typ)
                match tryTypeCheck v typer with
                | Some _ -> id, env
                | None -> id, Map.add v typ env
            | _ -> __unreachable__()
        let handle_case (pat, body) =
            match pat with
            | PList (PSymbol constr::cargs) ->
                let op = getOperation constr typer
                let cargs, env = List.mapFold extendEnvironment env (List.zip cargs (butLast <| sort_of_operation op))
                Apply(op, cargs), toExpr (typer, env) body
            | _ ->
                let v, env = extendEnvironment env (pat, typ)
                v, toExpr (typer, env) body
        let cases = List.map handle_case cases
        Match(t, cases)

let parseToTerms command_mapper exprs =
    let toComm typer e =
        let define_fun name vars sort body constr =
            let vars = to_sorted_vars vars
            let typer = addUserOperation typer name (obtain_sort vars sort)
            let env = create_env vars
            let body = toExpr (typer, env) body
            constr(name, vars, sort, body), typer
        let parse_constructors typer adtname constrs =
            let handle_constr typer = function
                | PList (PSymbol fname::vars) ->
                    let vars = to_sorted_vars vars
                    let typer = List.fold (fun typer (pr, s) -> addElementaryOperation typer pr [adtname; s]) typer vars
                    let typer = addElementaryOperation typer fname (obtain_sort vars adtname)
                    (fname, vars), typer
                | _ -> __unreachable__()
            List.mapFold handle_constr typer constrs
        let comm, typer =
            match e with
            | PList [PSymbol "define-fun"; PSymbol name; PList vars; PSymbol sort; body] ->
                define_fun name vars sort body DefineFun
            | PList [PSymbol "define-fun-rec"; PSymbol name; PList vars; PSymbol sort; body] ->
                define_fun name vars sort body DefineFunRec
            | PList [PSymbol "define-funs-rec"; PList signs; PList bodies] ->
                let signs = signs |> List.map (function PList [PSymbol name; PList vars; PSymbol sort] -> name, to_sorted_vars vars, sort | _ -> __unreachable__())
                let typer = List.fold (fun typer (name, vars, sort) -> addUserOperation typer name (obtain_sort vars sort)) typer signs
                let fs = List.map2 (fun body (name, vars, sort) -> name, vars, sort, toExpr (typer, create_env vars) body) bodies signs
                DefineFunsRec fs, typer
            | PList [PSymbol "declare-datatype"; PSymbol adtname; PList constrs] ->
                let constrs, typer = parse_constructors typer adtname constrs
                DeclareDatatype(adtname, constrs), typer
            | PList [PSymbol "declare-datatypes"; PList signs; PList constr_groups] ->
                let names = signs |> List.map (function PList [PSymbol name; PNumber 0] -> name | _ -> __unreachable__())
                let dfs, typer = List.mapFold (fun typer (name, PList constrs) -> parse_constructors typer name constrs) typer (List.zip names constr_groups)
                DeclareDatatypes (List.zip names dfs), typer
            | PList [PSymbol "check-sat"] -> CheckSat, typer
            | PList [PSymbol "assert"; expr] ->
                Assert(toExpr (typer, Map.empty) expr), typer
            | PList [PSymbol "declare-sort"; PSymbol sort; PNumber 0] -> DeclareSort(sort), typer
            | PList [PSymbol "declare-const"; PSymbol name; PSymbol sort] ->
                DeclareConst(name, sort), addUserOperation typer name [sort]
            | PList [PSymbol "declare-fun"; PSymbol name; PList argTypes; PSymbol sort] ->
                let argTypes = argTypes |> List.map (function PSymbol t -> t | _ -> __unreachable__())
                DeclareFun(name, argTypes, sort), addUserOperation typer name (argTypes @ [sort])
            | e -> failwithf "%O" e
        command_mapper typer comm
    let comms, _ = List.mapFold toComm elementaryOperations exprs
    comms

//    member x.AssumptionsToBody(assumptions, retExpr) =
//        match retArg with
//        | Some (retArg, _) -> (equal retArg retExpr) :: assumptions
//        | None -> retExpr :: assumptions

let rec private expr_to_clauses typer env = function
    | Ite(i, t, e) ->
        let i = expr_to_clauses typer env i
        let t = expr_to_clauses typer env t
        let e = expr_to_clauses typer env e
        collector {
            let! ivars, iassumptions, iretExpr = i
            let! tvars, tassumptions, tretExpr = t
            let! evars, eassumptions, eretExpr = e
            return ivars @ tvars @ evars, iassumptions @ tassumptions @ eassumptions, Ite(iretExpr, tretExpr, eretExpr)
        }
    | Apply(op, args) ->
        let args = product typer env args
        let fallback_apply (v, a, rs) = v, a, Apply(op, rs)
        let app =
            match op with
            | ElementaryOperation _ -> fallback_apply
            | UserDefinedOperation(name, sign) ->
                let op' = getOperation name typer
                if op = op'
                then fallback_apply
                else
                    let retArg = gensym (), List.last sign
                    let retVar = Ident retArg
                    fun (vars, assumptions, args) ->
                    let expr = Apply(op', retVar::args)
                    (retArg::vars), (expr::assumptions), retVar
        List.map app args
    | Constant _
    | Ident _ as e -> [[], [], e]
    | Match(t, cases) ->
        let rec get_free_vars = function
            | Apply(_, ts) -> List.collect get_free_vars ts
            | Ident(name, _) when Map.containsKey name typer -> []
            | Ident(v, t) -> [v, t]
            | _ -> __unreachable__()
        let handle_case (pattern, body) =
            let pat_match = equal t pattern
            let vars = get_free_vars pattern
            let env = extend_env env vars
            expr_to_clauses typer env body
            |> List.map (fun (vars', assumptions, body) -> vars @ vars', pat_match::assumptions, body)
        List.collect handle_case cases
    | Or cases -> List.collect (expr_to_clauses typer env) cases
    | And exprs -> product typer env exprs |> List.map (fun (v, a, rs) -> v, a, And rs)
    | Let(bindings, body) ->
        let rec handle_bindings env = function
            | [] -> expr_to_clauses typer env body
            | (var, body)::bindings ->
                let typ = typeOf body
                let id = var, typ
                let varTerm = Ident id
                let body_clauses = expr_to_clauses typer env body
                let rest = handle_bindings (Map.add var typ env) bindings
                collector {
                    let! vb, ab, rb = body_clauses
                    let! vr, ar, rr = rest
                    return id :: vb @ vr, (equal varTerm rb) :: ab @ ar, rr
                }
        handle_bindings env bindings
    | e -> failwithf "not supported expr: %O" e
and product typer env args =
    let combine2 arg st =
        let arg = expr_to_clauses typer env arg
        collector {
            let! v, a, r = st
            let! v', a', r' = arg
            return v' @ v, a' @ a, r' :: r
        }
    List.foldBack combine2 args [[], [], []]

let functionToRelationInTyper typer (name, vars, sort, body) =
    match sort with
    | "Bool" -> typer
    | _ -> addUserOperation typer name (sort :: List.map snd vars @ ["Bool"])

let definition_to_clauses typer ((name, vars, sort, body) as df) =
    match sort with
    | "Bool" ->
        let sign = List.map snd vars
        let env = create_env vars
        let app = Apply(getOperation name typer, List.map Ident vars)
        let handle_clause (clvars, assumptions, retExpr) =
            Assert(Forall(vars @ clvars, hence (And (retExpr :: assumptions)) app))
        let bodies =
            expr_to_clauses typer env body
            |> List.map handle_clause
        DeclareFun(name, sign, "Bool")::bodies, typer
    | _ ->
        let sign = sort :: List.map snd vars
        let retArgName = gensym ()
        let retArg = (retArgName, sort)
        let vars = retArg :: vars
        let env = create_env vars
        let retArg = Ident retArg
        let app = Apply(getOperation name typer, List.map Ident vars)
        let handle_clause (clvars, assumptions, retExpr) =
            let body = equal retArg retExpr :: assumptions
            Assert(Forall(vars @ clvars, hence (And body) app))
        let bodies =
            expr_to_clauses typer env body
            |> List.map handle_clause
        DeclareFun(name, sign, "Bool")::bodies, typer

let comm_to_clauses typer = function
    | CheckSat
    | DeclareSort _
    | DeclareConst _
    | DeclareFun _
    | DeclareDatatypes _
    | DeclareDatatype _ as c -> [c], typer
    | DefineFun df
    | DefineFunRec df -> definition_to_clauses (functionToRelationInTyper typer df) df
    | DefineFunsRec dfs ->
        let typer = List.fold functionToRelationInTyper typer dfs
        List.foldBack (fun df (clauses, typer) -> let cls', typer = definition_to_clauses typer df in cls' @ clauses, typer) dfs ([], typer)
    | Assert(Not(Forall(vars, body))) ->
        let env = create_env vars
        match expr_to_clauses typer env body with
        | [vars', assumptions, body] -> [Assert(Not(Forall(vars @ vars', And (body :: assumptions))))], typer
        | clauses -> failwithf "Assertion generated too many clauses: %O" clauses
    | c -> failwithf "Can't obtain clauses from: %O" c

let private adt_df_to_sorted (typename, constructors) =
    let parse_constructor (name, args) = DeclareFun(name, List.map snd args, typename)
    let decsort = DeclareSort typename
    let decfuns = List.map parse_constructor constructors
    decsort, decfuns

let to_sorts = function
    | DeclareDatatypes dfs ->
        let dss, dfs = List.unzip <| List.map adt_df_to_sorted dfs
        dss @ List.concat dfs
    | DeclareDatatype(t, c) ->
        let decsort, decfuns = adt_df_to_sorted (t, c)
        decsort :: decfuns
    | e -> [e]

let to_cvc4 exprs =
    let clauses = exprs |> parseToTerms comm_to_clauses |> List.concat
    let sorted = clauses |> List.collect to_sorts
    let set_logic_all = SetLogic "ALL"
    set_logic_all::sorted