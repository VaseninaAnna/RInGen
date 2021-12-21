module RInGen.TTA
open System.Collections.Generic
open RInGen.Operations
open RInGen.IdentGenerator
open RInGen.Prelude

// Sorts
let tta_sort = gensymp "Tta" |> PrimitiveSort
let state_sort = gensymp "State" |> PrimitiveSort

// Function symbol
let notFunc = Operation.makeElementaryOperationFromSorts (gensymp "notState") [state_sort] state_sort 
let andFunc = Operation.makeElementaryOperationFromSorts (gensymp "andStates") [state_sort; state_sort] state_sort 
let initFunc = Operation.makeElementaryOperationFromSorts (gensymp "initState") [tta_sort] state_sort 

let funcs = List.map Operation.declareOp [notFunc; andFunc; initFunc]

// Predicates
let isFinalRel = Operation.makeElementaryRelationFromSorts (gensymp "isFinal") [state_sort]
let stateEq = equal_op state_sort

type private TTAaxioms ( ) =
    let rules = Dictionary()
    let ruleCloser = ruleCloser()
    
    member private x.AddCombRule pred rule =
        match Dictionary.tryGetValue pred rules with
        | Some predRules ->
            rules.[pred] <- rule::predRules
        | None -> rules.Add(pred, [rule])
    
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
        let rules = rules |> List.map List.rev |> List.concat |> List.map ruleCloser.MakeClosedRule
        let decls = List.map Operation.declareOp ops
        List.map OriginalCommand (decls @ funcs) @ List.map TransformedCommand rules

type private TTA (stateCnt) =
    let predicate_constants = Dictionary<operation,term>()
    let transFuns = Dictionary()
    let orderedVars = Dictionary()
    let posToSorts = Dictionary()
    let posQueue = List()
    let generatedRules = List<rule>()
    let ruleCloser = ruleCloser()
    let stateCnt = stateCnt

    member private x.generateStateVars =
        List.init stateCnt (fun _ -> TIdent(gensym (), state_sort))
    member private x.newPosition vList =
        let constName = gensymp "position"
        let posTta = Operation.makeConstantFromSort constName tta_sort
        let posTransFunc = x.getTransitionFunc vList
        let sortList = List.map (fun (t:term) -> t.toSort()) vList
        posToSorts.Add(posTta, sortList)
        posTta, posTransFunc
        
    member private x.getPredicateConstant pred =
        match Dictionary.tryGetValue pred predicate_constants with
        | Some predConst -> predConst
        | None ->
            let constName = gensymp "PredTta"
            let cnst = Operation.makeConstantFromSort constName tta_sort 
            predicate_constants.Add(pred, cnst)
            cnst
            
    member private x.generateTransitionFunc sortList =
        let relName = gensymp "TransRel"
        let stateSorts = List.init stateCnt (fun _ -> state_sort)
        let func = Operation.makeElementaryOperationFromSorts relName ([tta_sort] @ stateSorts @ sortList) state_sort
        func

    member private x.getTransitionFunc (tList: term list) =
        let sortList = List.map (fun (t:term) -> t.toSort()) tList
        match Dictionary.tryGetValue sortList transFuns with
        | Some transRel -> transRel
        | None ->
            let func = x.generateTransitionFunc sortList
            transFuns.Add(sortList, func)
            func
    member private x.addSortedVar sort vName =
        match Dictionary.tryGetValue sort orderedVars with
        | Some vars ->
            orderedVars.[sort] <- vName::vars
        | None -> orderedVars.Add(sort, [vName])
        
    member private x.ParseQuantifiers qList =
        for q in qList do
            match q with
            |ForallQuantifier(vList) ->
                for var in vList do
                    match var with
                    |(name, sort) ->
                        x.addSortedVar sort name
            |ExistsQuantifier(_) -> __unreachable__()

    member private x.ParseVariables = function
        | Rule(quantifiers, _, _) ->
            x.ParseQuantifiers quantifiers
        | Assertion(quantifiers, _) -> () // TODO: do we need to transform these too?

    member private x.AddShuffleRule predConst vList =
        let orderedVList = List.sort vList
        let posTta, posTransFunc =  x.newPosition orderedVList
        
        // generate rule
        let atomTransFunc = x.getTransitionFunc vList 
        let stateVars = x.generateStateVars
        let posTrans = TApply(posTransFunc, [posTta] @ stateVars @ orderedVList)
        let atomTrans = TApply(atomTransFunc, [predConst] @ stateVars @ vList)
        let posInit = TApply(initFunc, [posTta])
        let atomInit = TApply(initFunc, [predConst])
        let body = [AApply(stateEq, [posTrans; atomTrans]); AApply(stateEq, [posInit; atomInit])]
        let rule = ruleCloser.MakeClosedAssertion(body)
        generatedRules.Add(rule)
        posTta
    
    member private x.AddNegRule posTta =
        let posArgSorts =
            match Dictionary.tryGetValue posTta posToSorts with
            | Some transFunc -> transFunc
            | None -> __unreachable__()
        let posTransFunc =
            match Dictionary.tryGetValue posArgSorts transFuns with
            | Some transFunc -> transFunc
            | None -> __unreachable__()
        let negPosTta = Operation.makeConstantFromSort (gensymp "position") tta_sort
        posToSorts.Add(negPosTta, posArgSorts)
        
        // rule
        let stateVars = x.generateStateVars
        let notStateVars = List.map (fun x -> TApply(notFunc, [x])) stateVars
        let sortVars = List.map (fun s -> TIdent(gensym (), s)) posArgSorts
        let posTrans = TApply(notFunc, [TApply(posTransFunc, [posTta] @ stateVars @ sortVars)])
        let negTrans = TApply(posTransFunc, [negPosTta] @ notStateVars @ sortVars)
        let posInit = TApply(notFunc, [TApply(initFunc, [posTta])])
        let negInit = TApply(initFunc, [negPosTta])
        let body = [AApply(stateEq, [negInit; posInit]); AApply(stateEq, [negTrans; posTrans])]
        let rule = ruleCloser.MakeClosedAssertion(body)
        generatedRules.Add(rule)
        negPosTta
    
    member private x.addAndRule pos1 pos2 =
        // TODO: for this function we need position to orderedFreeVars mapping
        let stateVars1 = x.generateStateVars
        let stateVars2 = x.generateStateVars
        let andTta = Operation.makeConstantFromSort (gensymp "position") tta_sort
        let init1 = TApply(initFunc, [pos1])
        let init2 = TApply(initFunc, [pos2])
        let andInit = TApply(initFunc, [andTta])
        ()
        
    member private x.AddToPositionQueue rule =
        match rule with
        | Rule(_,body,head) ->
           for a in body do
               match a with
               | AApply(op, vList) ->
                   let pConst = x.getPredicateConstant op
                   let pos = x.AddShuffleRule pConst vList
                   posQueue.Add(pos)
               | Equal(term1, term2) ->
                   let tSort = term1.toSort()
                   let op = equal_op tSort
                   let pConst = x.getPredicateConstant op
                   let pos = x.AddShuffleRule pConst [term1; term2]
                   posQueue.Add(pos)
           match head with
           | AApply(op, vList) ->
                let pConst = x.getPredicateConstant op
                let pos = x.AddShuffleRule pConst vList
                let neg_pos = x.AddNegRule pos
                posQueue.Add(neg_pos)
           | _ -> ()

    
    member x.traverseRules rules =
        for r in rules do
            x.ParseVariables r
            x.AddToPositionQueue r
        // process AndQueue
        // process quantifiers
        // dump new rules
        // dump sorts
        rules
    
let synchronize commands =
    let commands1, rules = List.choose2 (function OriginalCommand o -> Choice1Of2 o | TransformedCommand t -> Choice2Of2 t) commands
    let rules, assertions = List.choose2 (function (Rule(_) as r) -> Choice1Of2 r | (Assertion(_) as a) -> Choice2Of2 a) rules
    let m = 1 // TODO : how do we determine m ? it must be the same for all transition relations
    let tta = TTA(m)
    // ttaAxioms should generate transition relation axioms for all transitions generated by tta
    let ttaAxioms = TTAaxioms()
    let newTypes = []
    let axioms = ttaAxioms.dumpAxioms ()
    let rules = tta.traverseRules rules
    commands
//    List.map OriginalCommand newTypes @ axioms
//    List.map OriginalCommand (adt_decl_commands @ commands) @ new_rules @ List.map TransformedCommand rules
