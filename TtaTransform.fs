module RInGen.TtaTransform

open System.Collections.Generic
open System.Linq.Expressions
open RInGen

open RInGen.Prelude
open RInGen.IdentGenerator
open RInGen.Operations

let initStatePrefix = "init_"
let isFinalPrefix = "isFinal_"
let deltaPrefix = "delta_"

let stateSort = gensymp "State" |> PrimitiveSort

type pattern = Pattern of string * term list

type AutomataRecord =
    { initConst : term
      isFinal : operation
      delta : operation }

type Processer(adts) =
    // TODO: optimization
    let m = List.max (List.map (fun x -> List.length (snd x)) adts)
    let posDict = Dictionary()


    member x.generateAutomataDeclarations name sortList =
        let initStateName = initStatePrefix + name
        let isFinalName = isFinalPrefix + name
        let deltaName = deltaPrefix + name

        let initStateDecl = DeclareConst (initStateName, stateSort)
        let isFinalDecl = DeclareFun (isFinalName, [stateSort], boolSort)
        let deltaDecl = DeclareFun (deltaName, sortList @ [stateSort], stateSort)

        let initState = TConst(initStateName, stateSort)
        let isFinal = Operation.makeElementaryRelationFromSorts isFinalName [stateSort]
        let mStatesVec = List.init m (fun _ -> stateSort)
        let delta = Operation.makeElementaryOperationFromSorts deltaName (sortList @ mStatesVec) stateSort

        // 1st - declarations to be added to commands
        // 2nd - operations to be used in new rules
        let aRec = {initConst = initState; isFinal = isFinal; delta = delta}
        List.map OriginalCommand [initStateDecl; isFinalDecl; deltaDecl], aRec


    member x.processDeclarations oCommands =
        let f el = match el with
            | DeclareFun(fname, args, res) ->
                let decls, aRec = x.generateAutomataDeclarations fname args
                let p = Pattern(fname, [])
                posDict.Add(p, aRec)
                Some decls
            | _ -> None

        let xs = oCommands |> List.map f |> List.filter (fun x -> x.IsSome)

        seq {
            for el in xs do
                match el with
                | Some c -> yield! c
                | None -> ()
        }

    member x.parseDatatypes adts =
        let processDt(s, xs) =
            let ys = List.map (fun x -> DeclareConst (fst x, s)) xs
            let bot = DeclareConst(s.getBotSymbol(), s)

            // eq axioms
            let sortEq = equal_op s
            let eqRelName = "eq" + s.ToString()
            let decls, aRec = x.generateAutomataDeclarations eqRelName [s; s]
            let p = Pattern(eqRelName, [])
            posDict.Add(p, aRec)

            let iState, isFinal, delta = aRec.initConst, aRec.isFinal, aRec.delta
            let initAtom = AApply(isFinal, [iState])
            let initAxiom = TransformedCommand (rule [] [] initAtom)

            let q = TIdent(gensymp "q", stateSort)
            let f, g = TIdent(gensymp "f", s), TIdent(gensymp "g", s)
            let delta = TApply(delta, [f; g; q])
            let l = AApply(isFinal, [delta])
            let r = [AApply(sortEq, [f; g]); AApply(isFinal, [q])]
            let forallVars = [f; g; q] |> List.map (function TIdent(n, s) -> (n, s) )
            let forallQuant = ForallQuantifier(forallVars)
            let deltaAxiom = TransformedCommand (Equivalence([forallQuant], r, l))

            List.map OriginalCommand ([DeclareSort(s); bot] @ ys) @ decls  @ [initAxiom; deltaAxiom]

        seq {
            for c in adts do
                yield! (processDt c)
        }

    member private x.CollectFreeVarsInTerm = function
        | TIdent(i, s) -> [i]
        | TConst _ -> []
        | TApply(_, ts) -> x.CollectFreeVarsInTerms ts
    member private x.CollectFreeVarsInTerms = List.collect x.CollectFreeVarsInTerm


    member x.parsePattern p =
        let pName, pTerms =
            match p with
            | Pattern(name, ts) ->
                name, ts

        let f = function
            | TConst(name, s) -> TConst(name, s)
            | TApply(op, _) -> TConst(op.ToString(), op.getSort())
            | TIdent(_, _) -> __notImplemented__()

        let constructors = List.map f pTerms

        let sortList = List.map (fun (t: term) -> t.getSort()) pTerms
        let mStatesVec = List.init m (fun _ -> stateSort)
        let deltaName = deltaPrefix + pName
        let origDelta = Operation.makeElementaryOperationFromSorts deltaName (sortList @ mStatesVec) stateSort
        let stateVars = List.init m (fun _ -> TIdent(gensymp(), stateSort))
        let r = TApply(origDelta, constructors @ stateVars)
        let l =
        ()

    member x.addPattern (p: pattern) =

        let pName, pTerms =
            match p with
            | Pattern(name, ts) ->
                name, ts
        let vars = x.CollectFreeVarsInTerms pTerms
        let xs = List.mapi  (fun i _ -> "x_" + i.ToString()) vars
        let renameVar = Map.ofList <| List.zip vars xs
        let rec traverseTerm t =
            match t with
            | TIdent(i, s) ->
                let v = renameVar.[i]
                TIdent(v, s)
            | TConst _ -> t
            | TApply(op,ts) ->
                let ts' = List.map traverseTerm ts
                TApply(op, ts')
        let newPTerms = List.map traverseTerm pTerms
        let newPattern = Pattern(pName, newPTerms)

        match Dictionary.tryGetValue newPattern posDict with
        | Some _ -> []
        | None ->
            let sortList = List.map (fun (t: term) -> t.getSort()) newPTerms
            let decls, newRecord = x.generateAutomataDeclarations pName sortList
            posDict.Add(newPattern, newRecord)

            decls


    member x.fillPositions r =
        let atomToAutomata atom =
            match atom with
            | Equal(t1, t2) ->
                let sort = t1.getSort()
                let eqRelName = "eq" + sort.ToString()
                let p = Pattern(eqRelName, [t1;t2])
                x.addPattern(p)
                Some p
            | AApply(op, ts) ->
                let p = Pattern(op.ToString(), ts)
                x.addPattern(p)
                Some p
            | Distinct(t1, t2) ->
                let sort = t1.getSort()
                let eqRelName = "eq" + sort.ToString()
                let p = Pattern(eqRelName, [t1;t2])
                x.addPattern(p)
                Some p
            | _ -> None

        match r with
        | Rule(_, body, head) ->
            (body @ [head]) |> List.map atomToAutomata |> List.filter (fun x -> x.IsSome) |> List.map Option.get


    member x.dumpCommands() =
        let processeedDts = x.parseDatatypes adts
        processeedDts


let transform commands =
    let oCommands, tComands = List.choose2 (function OriginalCommand o -> Choice1Of2 o | TransformedCommand t -> Choice2Of2 t) commands
    let adt_decls, oCommands = oCommands |> List.choose2 (function DeclareDatatype(a, b) -> Choice1Of2 [(a, b)] | DeclareDatatypes dts -> Choice1Of2 dts | c -> Choice2Of2 c)
    let adt_decls = List.concat adt_decls
    let processer = Processer(adt_decls)
    let oCommands = processer.processDeclarations oCommands
    let tCommands = processer.dumpCommands()
    let commands = Seq.append tCommands oCommands |> Seq.toList
    //let newOCommands = parseOriginalCommands oCommands
    [OriginalCommand(DeclareSort(stateSort))] @ commands