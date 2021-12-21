module RInGen.Flattening
open System.Collections.Generic
open RInGen.Prelude
open RInGen.IdentGenerator

type private Flattener () =
    let axioms = Dictionary()
    let ruleCloser = ruleCloser()
    let funcToRel = Dictionary()
    
    member private x.addAxiom operation inSorts outSort =
        let inVarsSorted = List.map (fun s -> (gensym (), s)) inSorts
        let outVarSorted = (gensym (), outSort)
        let inTerms = List.map (fun x -> TIdent(x)) inVarsSorted
        let outTerm = TIdent(outVarSorted)
        let axiom_body = [AApply(operation, inTerms @ [outTerm])]
        let axiomQuantifiers = [ForallQuantifier inVarsSorted ; ExistsQuantifier [outVarSorted]]
        let axiom = Assertion(axiomQuantifiers, axiom_body)
        axioms.Add(operation, axiom)

    member x.parseDatatypes adts =
        let res = seq {
            for s, ops in adts do
                yield DeclareSort(s)
                for op in ops do
                    match op with
                    | ElementaryOperation(opName, inSorts, outSort)
                    | UserDefinedOperation(opName, inSorts, outSort) ->
                        let predSorts = inSorts @ [outSort]
                        let newOperation = ElementaryOperation(opName, predSorts, boolSort)
                        funcToRel.Add(opName, newOperation)
                        x.addAxiom newOperation inSorts outSort
                        yield DeclareFun(opName, predSorts, boolSort)
        }
        res
                
    member x.parseDeclarations fun_decls =
        let res = seq {
            for name, inSorts, outSort in fun_decls do
                if outSort = boolSort then
                    yield DeclareFun(name, inSorts, outSort)
                else    
                    let predSorts = inSorts @ [outSort]
                    let newOperation = ElementaryOperation(name, predSorts, boolSort)
                    funcToRel.Add(name, newOperation)
                    x.addAxiom newOperation inSorts outSort
                    yield DeclareFun(name, predSorts, boolSort)
        }
        res

    member private x.parseRule rule =
        let termToVar = Dictionary()
        
        let rec replaceTerm t =
            match t with
            | TConst(_,_) -> t
            | TIdent(_,_) -> t
            | TApply(op, ts) ->
                let vars = seq {
                    for t' in ts do
                        yield replaceTerm t'
                }
                let vars = Seq.toList vars
                let renamedTerm = TApply(op, vars)
                match Dictionary.tryGetValue renamedTerm termToVar with
                | Some var -> var
                | None -> 
                    let newVar = TIdent(gensym (), t.toSort())
                    termToVar.Add(t, newVar)
                    newVar

        let replaceAtom atom =
            match atom with
            | Equal(t1, t2) -> Equal(replaceTerm t1, replaceTerm t2)
            | AApply(op, ts) ->
                let newTerms = List.map replaceTerm ts
                AApply(op, newTerms)
            | _ -> atom
        
        match rule with
        |Rule(_, body, head) ->
            let renamedBody = List.map replaceAtom body
            let renamedHead = replaceAtom head
            let newAtoms =
                seq {
                    for KeyValue(term, var) in termToVar do
                        match term with
                        | TApply(op, ts) ->
                            let opName =
                                match op with
                                | ElementaryOperation(s, _, _)
                                | UserDefinedOperation(s, _, _) -> s

                            match Dictionary.tryGetValue opName funcToRel with
                            | Some op -> yield AApply(op, ts @ [var])
                            | None -> ()
                        | _ -> ()
                            
                }
            let newAtoms = Seq.toList newAtoms
            ruleCloser.MakeClosedRule(newAtoms @ renamedBody, renamedHead)
        | _ -> rule
        

    member x.parseClauses rules =
        let res = seq {
            for rule in rules do
                let new_rule = x.parseRule rule
                yield new_rule
        }
        res
    
    member x.dumpAxioms =
        let res = seq {
            for KeyValue(op, rule) in axioms do
                yield rule
        }
        res
        
let flatten commands =
    let commands, rules = List.choose2 (function OriginalCommand o -> Choice1Of2 o | TransformedCommand t -> Choice2Of2 t) commands
    let fun_decls, commands = commands |> List.choose2 (function DeclareFun(name, inSorts, outSort) -> Choice1Of2 (name, inSorts, outSort) | c -> Choice2Of2 c)
    let adt_decls, commands = commands |> List.choose2 (function DeclareDatatype(a, b) -> Choice1Of2 [a, b] | DeclareDatatypes dts -> Choice1Of2 dts | c -> Choice2Of2 c)
    let adt_decls = List.concat adt_decls
    let adt_decls = adt_decls |> List.map (fun (s, cs) -> s, List.map (fun (c, ss) -> Operation.makeElementaryOperationFromVars c ss s) cs)
    let flattener = Flattener()
    let pred_decls = (flattener.parseDatatypes adt_decls |> Seq.toList) @ (flattener.parseDeclarations fun_decls |> Seq.toList)
    let axioms = flattener.dumpAxioms |> Seq.toList
    let rules = flattener.parseClauses rules
    let rules = rules |> Seq.toList
    List.map OriginalCommand (commands @ pred_decls) @ List.map TransformedCommand (axioms @ rules)