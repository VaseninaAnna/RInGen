module RInGen.TTA
open System.Collections.Generic
open RInGen.Operations
open RInGen.IdentGenerator
open RInGen.Prelude

// Sorts
let tta_sort = gensymp "Tta" |> PrimitiveSort
let state_sort = gensymp "State" |> PrimitiveSort
let emptyState = Operation.makeConstantFromSort (gensymp "EmptyState") state_sort

// Function symbol
let notFunc = Operation.makeElementaryOperationFromSorts (gensymp "notState") [state_sort] state_sort 
let andFunc = Operation.makeElementaryOperationFromSorts (gensymp "andStates") [state_sort; state_sort] state_sort 
let initFunc = Operation.makeElementaryOperationFromSorts (gensymp "initState") [tta_sort] state_sort

// Predicates
let isFinalRel = Operation.makeElementaryRelationFromSorts (gensymp "isFinal") [state_sort]
let isReachableRel = Operation.makeElementaryRelationFromSorts (gensymp "isReach") [state_sort; state_sort; tta_sort]
let addStateRel = Operation.makeElementaryRelationFromSorts (gensymp "addState") [state_sort; state_sort; state_sort]
let ttaStatesRel = Operation.makeElementaryRelationFromSorts (gensymp "ttaStates") [state_sort; tta_sort]
let stateInStates = Operation.makeElementaryRelationFromSorts (gensymp "StateIn") [state_sort; state_sort]
let stateEq = equal_op state_sort

type private TTAaxioms ( ) =
    let axioms = List()
    let ruleCloser = ruleCloser()

    member private x.generateV1 =
        let stateVar = TIdent(gensym (), state_sort)
        let notStateVar = TApply(notFunc, [stateVar])
        let l = AApply(isFinalRel, [notStateVar]) |> FOLAtom
        let r = AApply(isFinalRel, [stateVar]) |> FOLAtom
        let conj1 = FOLAnd([l; FOLNot(r)])
        let conj2 = FOLAnd([FOLNot(l); r])
        let axiomBody = FOLOr([conj1; conj2])
        let forallVars = [stateVar] |> List.map (function TIdent(n, s) -> (n, s) )
        let forallQuant = ForallQuantifier(forallVars)
        let axiom = FOLAssertion([forallQuant], axiomBody)
        axioms.Add(axiom)

    member private x.generateV2 =
        let stateVar1 = TIdent(gensym (), state_sort)
        let stateVar2 = TIdent(gensym (), state_sort)
        let andExpr = TApply(andFunc, [stateVar1; stateVar2])
        let l = AApply(isFinalRel, [andExpr]) |> FOLAtom
        let r = [AApply(isFinalRel, [stateVar1]); AApply(isFinalRel, [stateVar2])] |> List.map FOLAtom

        let conj1 = FOLAnd([l] @ r)
        let conj2 = FOLAnd([FOLNot(l); FOLNot(FOLAnd(r))])
        let axiomBody = FOLOr([conj1; conj2])

        let forallVars = [stateVar1; stateVar2] |> List.map (function TIdent(n, s) -> (n, s) )
        let forallQuant = ForallQuantifier(forallVars)
        let axiom = FOLAssertion([forallQuant], axiomBody)
        axioms.Add(axiom)

    member private x.generateV3 =
        let ttaVar = TIdent(gensym (), tta_sort)
        let stateVar1 = TIdent(gensym (), state_sort)
        let stateVar2 = TIdent(gensym (), state_sort)

        let isState = AApply(ttaStatesRel, [stateVar1; ttaVar])
        let sIsFinal = AApply(isFinalRel, [stateVar1])
        let sIsFinal2 = AApply(isFinalRel, [stateVar2])
        let sInS = AApply(stateInStates, [stateVar2; stateVar1])
        // TODO: todo
        ()

    member private x.generateA_empty =
        ()

    member private x.generateAdd =
        ()

    member x.dumpAxioms () =
        x.generateV1
        x.generateV2
        x.generateV3
        x.generateA_empty
        x.generateAdd
        let funcs = List.map Operation.declareOp [notFunc; andFunc; initFunc]
        let preds = List.map Operation.declareOp [isFinalRel; isReachableRel; addStateRel; ttaStatesRel; stateInStates]
//        List.map OriginalCommand (funcs @ preds) @ List.map TransformedCommand rules
        List.map OriginalCommand (funcs @ preds)

type private TTA (stateCnt) =
    let predicate_constants = Dictionary<operation,term>()
    let transFuns = Dictionary()
    let posToVars = Dictionary() // TODO: clean unneeded positions from this List
    let posQueue = List()
    let generatedRules = List<rule>()
    let transAxioms = List()
    let ruleCloser = ruleCloser()
    let stateCnt = stateCnt

    member private x.generateStateVars =
        List.init stateCnt (fun _ -> TIdent(gensym (), state_sort))

    member private x.newPosition vList =
        let constName = gensymp "position"
        let posTta = Operation.makeConstantFromSort constName tta_sort
        let posTransFunc = x.getTransitionFunc vList
        posToVars.Add(posTta, vList)
        posTta, posTransFunc

    member private x.getPosVars posTta =
        match Dictionary.tryGetValue posTta posToVars with
        | Some vars -> vars
        | None -> __unreachable__()

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
        // Add init axiom
        let ttaVarX = TIdent(gensym(), tta_sort)
        let initStates = List.init stateCnt (fun _ -> TApply(initFunc, [ttaVarX]))
        let bots = List.map (fun (s: sort) -> TConst(s.getBotSymbol(), s)) sortList
        let transitionFromBots = TApply(func, [ttaVarX] @ initStates @ bots)
        let initOfStateX = TApply(initFunc, [ttaVarX])
        let initAxiom = ruleCloser.MakeClosedAssertion([AApply(stateEq, [transitionFromBots; initOfStateX])])
        transAxioms.Add(initAxiom)
        func

    member private x.getTransitionFunc (tList: term list) =
        let sortList = List.map (fun (t:term) -> t.toSort()) tList
        match Dictionary.tryGetValue sortList transFuns with
        | Some transFun -> transFun
        | None ->
            let func = x.generateTransitionFunc sortList
            transFuns.Add(sortList, func)
            func

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
        let posArgVars = x.getPosVars posTta
        let posArgSorts = List.map (fun (t: term) -> t.toSort()) posArgVars
        let negPosTta, posTransFunc = x.newPosition posArgVars
        
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
        let stateVars1 = x.generateStateVars
        let stateVars2 = x.generateStateVars
        let andStateVars = List.map2 (fun x y -> TApply(andFunc, [x; y])) stateVars1 stateVars2

        let posVars1 = x.getPosVars pos1
        let posVars2 = x.getPosVars pos2
        let andPosVars = posVars1 @ posVars2 |> Set.ofList |> Set.toList |> List.sort
        
        let andTta, andTransFunc = x.newPosition andPosVars
        let andTrans = TApply(andTransFunc, [andTta] @ andStateVars @ andPosVars)
        
        let transFunc1 = x.getTransitionFunc posVars1
        let posTrans1 = TApply(transFunc1, [pos1] @ stateVars1 @ posVars1)
        let transFunc2 = x.getTransitionFunc posVars2
        let posTrans2 = TApply(transFunc2, [pos2] @ stateVars2 @ posVars2)
        let posTrans = TApply(andFunc, [posTrans1; posTrans2])
        
        let posInit1 = TApply(initFunc, [pos1])
        let posInit2 = TApply(initFunc, [pos2])
        let posInit = TApply(andFunc, [posInit1; posInit2])
        let andInit = TApply(initFunc, [andTta])
        
        let body = [AApply(stateEq, [andTrans; posTrans]) ; AApply(stateEq, [andInit; posInit])] 
        let rule = ruleCloser.MakeClosedAssertion(body)
        generatedRules.Add(rule)
        andTta
        
    member private x.AddToPositionQueue rules =
        for rule in rules do
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
                       // TODO: generate equality axiom (E)
                       let pos = x.AddShuffleRule pConst [term1; term2]
                       posQueue.Add(pos)
               match head with
               | AApply(op, vList) ->
                    let pConst = x.getPredicateConstant op
                    let pos = x.AddShuffleRule pConst vList
                    let neg_pos = x.AddNegRule pos
                    posQueue.Add(neg_pos)
               | _ -> ()
    
    member private x.processPosQueue queue =
        let mutable processingQueue = queue
        while not (List.length processingQueue = 1) do
            let pos1 = List.head processingQueue
            let tail = List.tail processingQueue
            let pos2 = List.head tail
            let andPos = x.addAndRule pos1 pos2
            processingQueue <- List.tail tail @ [andPos]
            
        processingQueue

    member private x.dumpPosQueue =
        seq {
            for p in posQueue do
                p
        }

    member private x.addRAxiom oldPos =
        let stateVar = TIdent(gensym(), state_sort)
        let stateVar' = TIdent(gensym(), state_sort)
        let isR = AApply(isReachableRel, [stateVar; stateVar'; oldPos])

        let sInState = AApply(stateInStates, [stateVar; stateVar'])
        let oldInit = TApply(initFunc, [oldPos])
        let sInInit = AApply(stateEq, [stateVar; oldInit])

        let oldPosVars = x.getPosVars oldPos
        let newVars, oldVar = List.splitAt (List.length oldPosVars - 1) oldPosVars

        let oldTransFunc = x.getTransitionFunc oldPosVars
        let oldStateVars = x.generateStateVars
        let bots = List.map (function TIdent(_, s) -> TConst(s.getBotSymbol(), s)) newVars

        let oldTrans = TApply(oldTransFunc, [oldPos] @ oldStateVars @ bots @ oldVar)
        let sIsOldTrans = AApply(stateEq, [stateVar; oldTrans])

        let stateVar'' = TIdent(gensym(), state_sort)
        let isReachList = List.map (fun x -> AApply(isReachableRel, [x; stateVar''; oldPos])) oldStateVars

        let addPred = AApply(addStateRel, [stateVar''; stateVar'; stateVar])

        // isR <=> (sInState /\ sInInit) \/ (sInState /\ sIsOldTrans /\ isReachList /\ addPred))
        let conj1 = [sInState; sInInit] |> List.map (fun (x: atom) -> FOLAtom(x)) |> FOLAnd
        let conj2 = [sInState; sIsOldTrans; addPred] @ isReachList |> List.map (fun (x: atom) -> FOLAtom(x)) |> FOLAnd
        let r = FOLOr([conj1; conj2])
        let l = FOLAtom(isR)
        let axiomBody = FOLOr([FOLAnd([l; r]); FOLAnd([FOLNot(l); FOLNot(r)])])

        let forallVars = [stateVar; stateVar'] |> List.map (function TIdent(n, s) -> (n, s) )
        let existsVars = [stateVar''] @ oldStateVars @ oldVar |> List.map (function TIdent(n, s) -> (n, s) )
        let forallQuant = ForallQuantifier(forallVars)
        let existsQuant = ExistsQuantifier(existsVars)
        let rAxiom = FOLAssertion([forallQuant; existsQuant], axiomBody)
        // TODO: dump axiom
        ()

    member private x.addSAxiom newPos oldPos =
        let oldStateSet = AApply(ttaStatesRel, [emptyState; oldPos])
        let stateVars = x.generateStateVars
        let newPosVars = x.getPosVars newPos
        let newTransRel = x.getTransitionFunc newPosVars

        let newTrans = TApply(newTransRel, [newPos] @ stateVars @ newPosVars)
        let newStateSet = AApply(ttaStatesRel, [newTrans; oldPos])
        let rule = ruleCloser.MakeClosedAssertion([oldStateSet; newStateSet])
        transAxioms.Add(rule)


    member private x.addAddAxiom oldPos =
        let sVar = TIdent(gensym(), state_sort)
        let sVar' = TIdent(gensym (), state_sort)
        let sVar'' = TIdent(gensym (), state_sort)

        let ttaStates1 = AApply(ttaStatesRel, [sVar; oldPos])

        let oldStateVars = x.generateStateVars
        let oldPosVars = x.getPosVars oldPos
        let oldTransFunc = x.getTransitionFunc oldPosVars
        let oldTrans = TApply(oldTransFunc, [oldPos] @ oldStateVars @ oldPosVars)

        let sEqTrans = AApply(stateEq, [sVar'; oldTrans])

        let ttaStates2 = AApply(ttaStatesRel, [sVar''; oldPos])
        let addPred = AApply(addStateRel, [sVar''; sVar; sVar'])

        let forallVars = [sVar; sVar'] |> List.map (function TIdent(n, s) -> (n, s) )
        let existsVars = oldStateVars @ oldPosVars @ [sVar''] |> List.map (function TIdent(n, s) -> (n, s) )
        let forallQuant = ForallQuantifier(forallVars)
        let existsQuant = ExistsQuantifier(existsVars)

        // ttaStates1 /\ sEqTrans => ttaStates2 /\ addPred
        let conj1 = [ttaStates1; sEqTrans] |> List.map (fun (x: atom) -> FOLAtom(x)) |> FOLAnd
        let conj2 = [ttaStates2; addPred] |> List.map (fun (x: atom) -> FOLAtom(x)) |> FOLAnd
        let axiomBody = FOLOr([FOLNot(conj1); conj2])
        let axiom = FOLAssertion([forallQuant; existsQuant], axiomBody)
        // TODO: dump axiom
        ()

    member private x.addExistentialAxioms newPos oldPos =
        x.addRAxiom oldPos
        x.addSAxiom newPos oldPos
        x.addAddAxiom oldPos

    member private x.processExistentialQuantor oldPos oldPosVars =
        let oldTransFun = x.getTransitionFunc oldPosVars
        let newPosVars, oldTransVar = List.splitAt (List.length oldPosVars - 1) oldPosVars
        let newPos, newTransFun = x.newPosition newPosVars

        // gamma1
        let stateVar = TIdent(gensym (), state_sort)
        let init = TApply(initFunc, [newPos])
        let sInInit = AApply(stateInStates, [stateVar; init])
        let isReach = AApply(isReachableRel, [stateVar; emptyState; oldPos])
        let rule = ruleCloser.MakeClosedRule([sInInit], isReach)
        generatedRules.Add(rule)
        let rule = ruleCloser.MakeClosedRule([isReach], sInInit)
        generatedRules.Add(rule)

        // gamma2
        let sVar = TIdent(gensym (), state_sort)
        let stateVars = List.init stateCnt (fun _ -> TIdent(gensym (), state_sort))
        let newStateVars = List.init stateCnt (fun _ -> TIdent(gensym (), state_sort))
        let newTrans = TApply(newTransFun, [newPos] @ stateVars @ newPosVars)
        let sInTrans = AApply(stateInStates, [sVar; newTrans])

        let newStateInOldState = List.map2 (fun x y -> AApply(stateInStates, [x; y])) newStateVars stateVars
        let oldTrans =  TApply(oldTransFun, [oldPos] @ newStateVars @ oldPosVars)
        let body = newStateInOldState @ [AApply(stateEq, [sVar; oldTrans])]

        let existsVars = newStateVars @ oldTransVar |> List.map (function TIdent(name, sort) -> (name, sort))
        let forallVars = [sVar] @ stateVars @ newPosVars  |> List.map (function TIdent(name, sort) -> (name, sort))
        let rule = aerule forallVars existsVars body sInTrans // <=
        generatedRules.Add(rule)
        // TODO: =>
        ()


    member x.traverseRules rules =
        x.AddToPositionQueue rules
        let positions = x.dumpPosQueue |> Seq.toList
        let preLastPos = List.exactlyOne (x.processPosQueue positions)
        let lastPos = x.AddNegRule preLastPos
        // TODO: process quantifiers
        let lastRule = ruleCloser.MakeClosedAssertion([AApply(isFinalRel, [TApply(initFunc, [lastPos])])])
        generatedRules.Add(lastRule)
        ()

    member x.dumpRules =
        seq {
            for r in generatedRules do
                r
        }
    member x.dumpDeclarations =
        let sorts = List.map DeclareSort [state_sort; tta_sort]
        let predDeclarations = seq {
            for KeyValue(_, term) in predicate_constants do
                match term with
                | TConst(name, sort) ->
                    DeclareFun(name, [emptySort], sort)
        }
        let predDeclarations = predDeclarations |> Seq.toList

        let posConstants = seq {
            for KeyValue(pos, vars) in posToVars do
                match pos with
                | TConst(name, _) ->
                    DeclareFun(name, [emptySort], tta_sort)
                | _ -> () 
        }
        let posConstants = posConstants |> Seq.toList

        let transFuncs = seq {
            for KeyValue(sorts, func) in transFuns do
                match func with
                | ElementaryOperation(name, inSorts, outSort)
                | UserDefinedOperation(name, inSorts, outSort) ->
                    DeclareFun(name, inSorts, outSort)
        }
        
        let transFuncs = transFuncs |> Seq.toList
        List.map OriginalCommand (sorts @ predDeclarations @ posConstants @ transFuncs)

    member x.dumpTransAxioms =
        seq {
            for axiom in transAxioms do
                axiom
        }

let defineBots commands =
    seq {
        for command in commands do
            match command with
            | DeclareSort s ->
                DeclareConst(s.getBotSymbol(), s)
            | _ -> ()
    }

let synchronize commands =
    let commands1, rules = List.choose2 (function OriginalCommand o -> Choice1Of2 o | TransformedCommand t -> Choice2Of2 t) commands
    let botConstants = defineBots commands1 |> Seq.toList
    let rules, assertions = List.choose2 (function (Rule(_) as r) -> Choice1Of2 r | (Assertion(_) as a) -> Choice2Of2 a) rules
    let m = 1 // TODO : how do we determine m ? it must be the same for all transition relations
    let tta = TTA(m)
    // ttaAxioms should generate transition relation axioms for all transitions generated by tta
    let ttaAxioms = TTAaxioms()
    let baseAxioms = ttaAxioms.dumpAxioms ()
    tta.traverseRules rules
    let transAxioms = tta.dumpTransAxioms |> Seq.toList
    let decls = tta.dumpDeclarations
    let rules = tta.dumpRules |> Seq.toList
    List.map OriginalCommand (commands1 @ botConstants) @ decls @ baseAxioms @ List.map TransformedCommand (transAxioms @ rules)
