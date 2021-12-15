module RInGen.TTA
open System.Collections.Generic
open RInGen.Operations
open RInGen.IdentGenerator
open RInGen.Prelude

type private TTA ( ) =
    let predicate_constants = Dictionary()
    let rules = Dictionary()
    let transFuns = Dictionary()
    let orderedVars = List()
    // Sorts
    let tta_sort = gensymp "Tta" |> PrimitiveSort
    let state_sort = gensymp "State" |> PrimitiveSort
    let targetSort = gensymp "targetSort" |> PrimitiveSort

    // Function symbol
    let notState = gensymp "notState"
    let notFunc = Operation.makeElementaryOperationFromSorts notState [state_sort] state_sort 
    let andStates = gensymp "andStates"
    let andFunc = Operation.makeElementaryOperationFromSorts andStates [state_sort; state_sort] state_sort 
    let initState = gensymp "initState"
    let initFunc = Operation.makeElementaryOperationFromSorts initState [tta_sort] state_sort 
    
    let funcs = List.map Operation.declareOp [notFunc; andFunc; initFunc]
    
    // Predicates
    let trans_rel_name = gensymp "rho"
    let transRel = Operation.makeElementaryRelationFromSorts trans_rel_name [tta_sort; state_sort; dummySort; dummySort] 
    let isFinal_rel_name = gensymp "isFinal"
    let isFinalRel = Operation.makeElementaryRelationFromSorts isFinal_rel_name [state_sort]

    member private x.getPredicateConstant pred =
        match Dictionary.tryGetValue pred predicate_constants with
        | Some predConst -> predConst
        | None ->
            let constName = gensymp "PredTta"
            let cnst = Operation.makeConstantFromSort constName tta_sort 
            predicate_constants.Add(pred, cnst)
            
    member private x.generateTransitionRel (arity : int) =
        let relName = gensymp "TransRel"
        let argSorts = List.init arity (fun x -> targetSort)
        let rel = Operation.makeElementaryRelationFromSorts relName ([tta_sort; state_sort] @ argSorts)
        rel
        
    member private x.getTransitionFun (arity: int) =
        match Dictionary.tryGetValue arity transFuns with
        | Some transRel -> transRel
        | None ->
            let rel = x.generateTransitionRel arity
            transFuns.Add(arity, rel)
        
    // TODO: remove copypast from synchronization.fs
    member private x.CollectFreeVarsInTerm = function
        | TIdent(i, s) -> [i, s]
        | TConst _ -> []
        | TApply(_, ts) -> x.CollectFreeVarsInTerms ts
    
    member private x.CollectFreeVarsInTerms = List.collect x.CollectFreeVarsInTerm
    
    member private x.AddCombRule pred rule =
        match Dictionary.tryGetValue pred rules with
        | Some predRules ->
            rules.[pred] <- rule::predRules
        | None -> rules.Add(pred, [rule])

    member private x.CollectFreeVarsInAtom = function
        | AApply(_, ts) -> x.CollectFreeVarsInTerms ts
        | Equal _ | Distinct _ -> __unreachable__()
        | _ -> []    
    member private x.MakeClosedRule(body, head) : rule =
        // forall quantifiers around all vars
        let freeVars = head::body |> List.collect x.CollectFreeVarsInAtom |> Set.ofList |> Set.toList
        rule freeVars body head
    
    // ----------------
    
    member private x.generateV1 =
        let state_var = TIdent(gensym (), state_sort)
        let not_state_var = TApply(notFunc, [state_var])
        let head = AApply(isFinalRel, [state_var])
        let body = AApply(isFinalRel, [not_state_var])
        x.AddCombRule isFinalRel ([body], head)
        x.AddCombRule isFinalRel ([head], body)
        
    member private x.generateV2 =
        let state_var1 = TIdent(gensym (), state_sort)
        let state_var2 = TIdent(gensym (), state_sort)
        let andExpr = TApply(andFunc, [state_var1; state_var2])
        let body = [AApply(isFinalRel, [state_var1]); AApply(isFinalRel, [state_var2])]
        let head = AApply(isFinalRel, [andExpr])
        x.AddCombRule isFinalRel (body, head)
        
    member x.dumpAxioms () =
        x.generateV1
        x.generateV2
        let ops, rules = rules |> Dictionary.toList |> List.unzip
        let rules = rules |> List.map List.rev |> List.concat |> List.map x.MakeClosedRule
        let decls = List.map Operation.declareOp ops
        List.map OriginalCommand (decls @ funcs) @ List.map TransformedCommand rules
    
//    member x.dumpRules () =
//        

let synchronize commands =
    let tta = TTA()
    let newTypes = []
    let axioms = tta.dumpAxioms ()
    List.map OriginalCommand newTypes @ axioms
//    List.map OriginalCommand (adt_decl_commands @ commands) @ new_rules @ List.map TransformedCommand rules
