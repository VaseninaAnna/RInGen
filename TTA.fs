module RInGen.TTA
open System.Collections.Generic
open RInGen.Operations
open RInGen.IdentGenerator
open RInGen.Prelude

// Sorts
let tta_sort = gensymp "Tta" |> PrimitiveSort
let state_sort = gensymp "State" |> PrimitiveSort
let targetSort = gensymp "targetSort" |> PrimitiveSort

// Function symbol
let notFunc = Operation.makeElementaryOperationFromSorts (gensymp "notState") [state_sort] state_sort 
let andFunc = Operation.makeElementaryOperationFromSorts (gensymp "andStates") [state_sort; state_sort] state_sort 
let initFunc = Operation.makeElementaryOperationFromSorts (gensymp "initState") [tta_sort] state_sort 

let funcs = List.map Operation.declareOp [notFunc; andFunc; initFunc]

// Predicates
let transRel = Operation.makeElementaryRelationFromSorts (gensymp "rho") [tta_sort; state_sort; dummySort; dummySort] 
let isFinalRel = Operation.makeElementaryRelationFromSorts (gensymp "isFinal") [state_sort]
let transitionEq = equal_op state_sort


type private ruleCloser ( ) =
    // TODO: remove copypast from synchronization.fs
    member private x.CollectFreeVarsInTerm = function
        | TIdent(i, s) -> [i, s]
        | TConst _ -> []
        | TApply(_, ts) -> x.CollectFreeVarsInTerms ts

    member private x.CollectFreeVarsInTerms = List.collect x.CollectFreeVarsInTerm

    member private x.CollectFreeVarsInAtom = function
        | AApply(_, ts) -> x.CollectFreeVarsInTerms ts
        | Equal _ | Distinct _ -> __unreachable__()
        | _ -> []    
        
    member x.MakeClosedRule(body, head) : rule =
        // forall quantifiers around all vars
        let freeVars = head::body |> List.collect x.CollectFreeVarsInAtom |> Set.ofList |> Set.toList
        rule freeVars body head

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

type private TTA () =
    let predicate_constants = Dictionary<operation,term>()
    let transFuns = Dictionary()
    let orderedVars = Dictionary()
    let generatedRules = List<rule>()
    let ruleCloser = ruleCloser()

            
    member private x.getPredicateConstant pred =
        match Dictionary.tryGetValue pred predicate_constants with
        | Some predConst -> predConst
        | None ->
            let constName = gensymp "PredTta"
            let cnst = Operation.makeConstantFromSort constName tta_sort 
            predicate_constants.Add(pred, cnst)
            cnst
            
    member private x.generateTransitionFunc (arity : int) =
        let relName = gensymp "TransRel"
        let argSorts = List.init arity (fun x -> targetSort)
        let rel = Operation.makeElementaryRelationFromSorts relName ([tta_sort; state_sort] @ argSorts)
        rel
        
    member private x.getTransitionFunc (tList: term list) =
        let arity = List.length tList
        match Dictionary.tryGetValue arity transFuns with
        | Some transRel -> transRel
        | None ->
            let rel = x.generateTransitionFunc arity
            transFuns.Add(arity, rel)
            rel
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

    member private x.rearrangeVars (termList: term list) =
        let res = List()
        // perform ordering
        termList
 

    member private x.AddShuffleRule predConst vList =
        let orderedVList = x.rearrangeVars vList
        let constName = gensymp "position"
        let posTta = Operation.makeConstantFromSort constName tta_sort 
        
        // generate rule
//        let sortsList = List.map (fun x -> match x with |(_, y) -> y) orderedVList
        let transFunc = x.getTransitionFunc orderedVList
        
        let sortVars = [TIdent(gensym (), state_sort)] // TODO: get state sort
        let posTrans = TApply(transFunc, [posTta] @ sortVars @ orderedVList)
        let atomTrans = TApply(transFunc, [predConst] @ sortVars @ vList)
        let body = [AApply(transitionEq, [posTrans; atomTrans])]
        let head = Top
        let rule = ruleCloser.MakeClosedRule((body, head))
        generatedRules.Add(rule)
        // positionAndQueue.Add(posTta)
        
    member private x.AddToPositionQueue rule = function
        | Rule(_,body,head) ->
           for a in body do
               match a with
               | AApply(op, vList) ->
                   let pConst = x.getPredicateConstant op
                   let pos = x.AddShuffleRule pConst vList
                   ()
               | Equal(term1, term2) -> ()
    
                   //let pConst = x.getPredicateConstant op
                   //pConst
               // get predicate constant
               // add shuffle rule
               // add position to AndQueue
           // for head add shuffle rule, add not rule, add not position to queue
    
    member x.traverseRules rules =
        // First, we fix the order of variables 
        for r in rules do
            x.ParseVariables r
        // now generate rules with ordered shuffle
        for r in rules do
            x.AddToPositionQueue r
        // process AndQueue
        // process quantifiers
        // dump new rules
        // dump sorts
        // dump new
        rules
    
let synchronize commands =
    let commands, rules = List.choose2 (function OriginalCommand o -> Choice1Of2 o | TransformedCommand t -> Choice2Of2 t) commands
    let tta = TTA()
    // ttaAxioms should generate transition relation axioms for all transitions generated by tta
    let ttaAxioms = TTAaxioms()
    let newTypes = []
    let axioms = ttaAxioms.dumpAxioms ()
    let rules = tta.traverseRules rules 
    List.map OriginalCommand newTypes @ axioms
//    List.map OriginalCommand (adt_decl_commands @ commands) @ new_rules @ List.map TransformedCommand rules
