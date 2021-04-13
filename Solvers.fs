module RInGen.Solvers
open System
open System.IO
open System.Diagnostics
open System.Text.RegularExpressions
open SolverResult

let private isBadBenchmark cmnds =
    let hasDefines = List.exists (function Definition _ -> true | _ -> false) cmnds
    let hasDeclareFuns = List.exists (function Command (DeclareFun _) -> true | _ -> false) cmnds
    hasDefines && hasDeclareFuns

let private containsExistentialClauses =
    let rec containsExistentialClauses = function
        | BaseRule _ -> false
        | ExistsRule _ -> true
        | ForallRule(_, r) -> containsExistentialClauses r
    let containsExistentialClauses = function
        | TransformedCommand r -> containsExistentialClauses r
        | _ -> false
    List.exists containsExistentialClauses

let private isNonLinearCHCSystem =
    let rec isNonLinearClause = function
        | BaseRule(atoms, _) ->
            atoms |> Seq.filter (function AApply _ -> true | _ -> false) |> Seq.length |> (<) 1
        | ExistsRule(_, r)
        | ForallRule(_, r) -> isNonLinearClause r
    let isNonLinearCommand = function
        | TransformedCommand r -> isNonLinearClause r
        | _ -> false
    List.exists isNonLinearCommand

let private cleanCommands set_logic chcSystem =
    let filt = function
        | OriginalCommand(SetLogic _)
        | OriginalCommand(GetInfo _)
        | OriginalCommand GetModel
        | OriginalCommand CheckSat
        | OriginalCommand Exit -> false
        | _ -> true
    let chcSystem = chcSystem |> List.filter filt
    let commands = OriginalCommand set_logic :: chcSystem @ [OriginalCommand CheckSat]
    if containsExistentialClauses commands then [] else [commands]

type ITransformer =
    abstract member TransformBenchmark : bool -> bool -> bool -> bool -> string -> string option -> unit
    abstract member TransformClauses : transformedCommand list -> transformedCommand list list

[<AbstractClass>]
type IDirectoryTransformer<'directory> () =
    abstract member GenerateClauses : bool -> bool -> bool -> bool -> string -> 'directory
    abstract member TransformClauses : transformedCommand list -> transformedCommand list list

    member x.TransformBenchmarkAndReturn performTransform tipToHorn quiet force directory =
        let outputDirectory = x.GenerateClauses performTransform tipToHorn quiet force directory
        if not quiet then printfn $"CHC systems of directory %s{directory} are preprocessed and saved in {outputDirectory}"
        outputDirectory

    interface ITransformer with
        member x.TransformBenchmark performTransform tipToHorn quiet force path outputPath =
            match () with
            | _ when File.Exists(path) ->
                let outputFiles = x.GenerateClausesSingle performTransform tipToHorn path outputPath
                match outputFiles with
                | [] -> printfn "unknown"
                | [outputFile] ->
                    if not quiet then printfn $"CHC system in %s{path} is preprocessed and saved in %s{outputFile}"
                | _ ->
                    if not quiet then printfn $"Preprocessing of %s{path} produced %d{List.length outputFiles} files:"
                    if not quiet then List.iter (printfn "%s") outputFiles
                x.GenerateClausesSingle performTransform tipToHorn path outputPath |> ignore
            | _ when Directory.Exists(path) -> x.TransformBenchmarkAndReturn performTransform tipToHorn quiet force path |> ignore
            | _ -> failwithf $"There is no such file or directory: %s{path}"
        member x.TransformClauses ts = x.TransformClauses ts

    abstract FileExtension : string
    default x.FileExtension = ".smt2"

    abstract Name : string
    default x.Name = "Transformed"

    member x.DirectoryForTransformed directory = directory + "." + x.Name

    abstract CommandsToStrings : transformedCommand list -> string list list
    default x.CommandsToStrings commands = [List.map toString commands]

    member x.CodeTransformation performTransform tipToHorn commands =
        let chcSystem = SMTcode.toClauses performTransform tipToHorn commands
        (x :> ITransformer).TransformClauses chcSystem

    member x.SaveClauses directory dst commands =
        let lines = List.collect x.CommandsToStrings commands
        for testIndex, newTest in List.indexed lines do
            let path = Path.ChangeExtension(dst, $".%d{testIndex}%s{x.FileExtension}")
//            let linearityPostfix = if isNonLinearCHCSystem newTest then ".NonLin" else ".Lin"
//            let fullPath = directory + linearityPostfix + cleanPath path
            let fullPath = Path.Join(x.DirectoryForTransformed directory, path)
            Directory.CreateDirectory(Path.GetDirectoryName(fullPath)) |> ignore
            File.WriteAllLines(fullPath, newTest)
        List.length lines

    member x.GenerateClausesSingle performTransform tipToHorn filename outputPath =
        let outputPath =
            match outputPath with
            | Some outputPath ->
                fun (path : string) -> Path.Join(outputPath, Path.GetFileName(path))
            | None -> id
        let exprs = SMTExpr.parseFile filename
        let transformed = x.CodeTransformation performTransform tipToHorn exprs
        let paths =
            seq {
                let lines = List.collect x.CommandsToStrings transformed
                for testIndex, newTest in List.indexed lines do
                    let path = Path.ChangeExtension(filename, $".%s{x.Name}.%d{testIndex}%s{x.FileExtension}")
                    let fullPath = outputPath path
                    File.WriteAllLines(fullPath, newTest)
                    yield fullPath
            } |> List.ofSeq
        paths

let private generateClauses (x : IDirectoryTransformer<string>) performTransform tipToHorn quiet force directory =
    let referenceDirectory = $"%s{directory}.Z3.Z3Answers"
    let shouldCompareResults = false //TODO
    let shouldBeTransformed (src : string) dst =
        let ext = Path.GetExtension(src)
        ext = ".smt2" &&
        (not shouldCompareResults ||
            let referenceFile = Path.ChangeExtension(Path.Join(referenceDirectory, dst), sprintf ".0.smt2")
            File.Exists(referenceFile))
    let mutable files = 0
    let mutable successful = 0
    let mutable total_generated = 0
    let mapFile (src : string) dst =
        if shouldBeTransformed src dst then
            if not quiet then printfn $"Transforming: %s{src}"
            files <- files + 1
            let exprs = SMTExpr.parseFile src
            try
                if force || not <| isBadBenchmark exprs then
                    let newTests = x.CodeTransformation performTransform tipToHorn exprs
                    total_generated <- total_generated + x.SaveClauses directory dst newTests
                successful <- successful + 1
            with e -> if not quiet then printfn $"Exception in %s{src}: {e.Message}"
    walk_through directory "" mapFile |> ignore
    if not quiet then printfn $"All files:       %d{files}"
    if not quiet then printfn $"Successful:      %d{successful}"
    if not quiet then printfn $"Total generated: %d{total_generated}"
    x.DirectoryForTransformed directory

[<AbstractClass>]
type IConcreteTransformer () =
    inherit IDirectoryTransformer<string>()

    override x.GenerateClauses performTransform tipToHorn quiet force directory =
        generateClauses x performTransform tipToHorn quiet force directory

let private sortTransformClauses chcSystem =
    let noADTSystem = SMTcode.DatatypesToSorts.datatypesToSorts chcSystem
    let set_logic_all = SetLogic "ALL"
    cleanCommands set_logic_all noADTSystem

let private adtTransformClauses chcSystem =
    let set_logic_horn = SetLogic "HORN"
    cleanCommands set_logic_horn chcSystem

type SortHornTransformer () =
    inherit IConcreteTransformer ()
    override x.TransformClauses chcSystem = sortTransformClauses chcSystem

type ADTHornTransformer () =
    inherit IConcreteTransformer ()
    override x.TransformClauses chcSystem = adtTransformClauses chcSystem

type ISolver =
    inherit ITransformer
    abstract member TransformAndRunOnBenchmark : bool -> bool -> bool -> bool -> string -> string option -> unit
    abstract member Solve : string -> SolverResult

[<AbstractClass>]
type IDirectorySolver<'directory>() =
    inherit IDirectoryTransformer<'directory>()
    let cleanPath (path : string) =
        let newpath = Regex.Replace(path, "[^a-zA-Z0-9_./]", "")
        newpath

    let takeCommandsBeforeFirstCheckSat = List.takeWhile (function Command CheckSat -> false | _ -> true)
    let takeOnlyQueryAcrossAssertsInTIPBenchmark = List.filter (function Assert(Not _) -> true | Assert _ -> false | _ -> true)

    abstract member InterpretResult : string -> string -> SolverResult
    abstract member BinaryName : string
    abstract member BinaryOptions : string -> string
    abstract member RunOnBenchmarkSet : bool -> bool -> 'directory -> string
    abstract member Solve : string -> SolverResult

    member x.SolveWithTime quiet filename =
        if not quiet then printfn $"Solving %s{filename} with timelimit %d{SECONDS_TIMEOUT} seconds"
        let timer = Stopwatch()
        timer.Start()
        let result = (x :> ISolver).Solve filename
        let time = int timer.ElapsedMilliseconds
        let time = min time (MSECONDS_TIMEOUT ())
        match result with
        | UNKNOWN _ when time = MSECONDS_TIMEOUT () -> TIMELIMIT, time
        | _ -> result, time

    interface ISolver with
        member x.Solve filename = x.Solve filename
        member x.TransformAndRunOnBenchmark performTransform tipToHorn quiet force path outputPath =
            match () with
            | _ when File.Exists(path) ->
                let outputFiles = x.GenerateClausesSingle performTransform tipToHorn path outputPath
                match outputFiles with
                | [] -> printfn "unknown"
                | [outputFile] ->
                    if not quiet then printfn $"CHC system in %s{path} is preprocessed and saved in %s{outputFile}"
                    let result, time = x.SolveWithTime quiet outputFile
                    if quiet then printfn "%s" <| quietModeToString result else
                    printfn $"Solver run on %s{outputFile} and the result is {result} which was obtained in %d{time} msec."
                | _ ->
                    if not quiet then printfn $"Preprocessing of %s{path} produced %d{List.length outputFiles} files:"
                    if not quiet then List.iter (printfn "%s") outputFiles
                    for outputFile in outputFiles do
                        let result, time = x.SolveWithTime quiet outputFile
                        if not quiet then printfn $"Solver run on %s{outputFile} and the result is {result} which was obtained in %d{time} msec."
                x.GenerateClausesSingle performTransform tipToHorn path outputPath |> ignore
            | _ when Directory.Exists(path) ->
                let outputDirectory = x.TransformBenchmarkAndReturn performTransform tipToHorn quiet force path
                let resultsDirectory = x.RunOnBenchmarkSet force quiet outputDirectory
                if not quiet then printfn $"Solver run on {outputDirectory} and saved results in %s{resultsDirectory}"
            | _ -> failwithf $"There is no such file or directory: %s{path}"

[<AbstractClass>]
type IConcreteSolver () =
    inherit IDirectorySolver<string> ()

    override x.GenerateClauses performTransform tipToHorn quiet force directory =
        generateClauses x performTransform tipToHorn quiet force directory

    member x.AnswersDirectory directory = $"%s{directory}.%s{x.Name}Answers"

    abstract member ShouldSearchForBinaryInEnvironment : bool

    member private x.WorkingDirectory (filename : string) =
        if x.ShouldSearchForBinaryInEnvironment
            then Environment.GetEnvironmentVariable(x.BinaryName)
            else filename
        |> Path.GetDirectoryName

    member private x.SetupProcess (psinfo : ProcessStartInfo) filename =
        let path = ref ""
        psinfo.FileName <- if psinfo.Environment.TryGetValue(x.BinaryName, path) then !path else x.BinaryName
        psinfo.Arguments <- x.BinaryOptions filename
        psinfo.WorkingDirectory <- x.WorkingDirectory filename

    override x.Solve (filename : string) =
        use p = new Process()
        p.StartInfo.RedirectStandardOutput <- true
        p.StartInfo.RedirectStandardError <- true
        p.StartInfo.UseShellExecute <- false
        x.SetupProcess p.StartInfo filename
        p.Start() |> ignore
        let output = p.StandardOutput.ReadToEnd()
        let error = p.StandardError.ReadToEnd()
        let exited = p.WaitForExit(MSECONDS_TIMEOUT ())
        if not exited then
            p.Kill()
            TIMELIMIT
        else x.InterpretResult error output

    override x.RunOnBenchmarkSet overwrite quiet dir =
        let run_file (src : string) dst =
            let dst = dir + dst
            Directory.CreateDirectory(Path.GetDirectoryName(dst)) |> ignore
            if Path.GetExtension(src) = x.FileExtension && (overwrite || not <| File.Exists(dst)) then
                try
                    if not quiet then printfn $"Running %s{x.Name} on %s{src}"
                    let answer, time = x.SolveWithTime false src
                    File.WriteAllText(dst, $"%d{time},{answer}")
                with e -> if not quiet then printfn $"Exception in %s{src}: %s{dst}"
            elif not quiet then printfn $"%s{x.Name} skipping %s{src} (answer exists)"
        walk_through dir $".%s{x.Name}Answers" run_file

type CVC4FiniteSolver () =
    inherit IConcreteSolver ()
    override x.ShouldSearchForBinaryInEnvironment = false
    override x.TransformClauses chcSystem = sortTransformClauses chcSystem

    override x.Name = "CVC4Finite"
    override x.BinaryName = "cvc4"
    override x.BinaryOptions filename = $"--finite-model-find --tlimit=%d{MSECONDS_TIMEOUT ()} %s{filename}"

    override x.InterpretResult error raw_output =
        if error <> "" then ERROR(error) else
        let output = Environment.split raw_output
        match output with
        | line::_ when line.StartsWith("(error ") -> ERROR(raw_output)
        | line::_ when line = "sat" -> SAT
        | line::_ when line = "unsat" -> UNSAT
        | line::reason::_ when line = "unknown" && reason = "(:reason-unknown timeout)" -> TIMELIMIT
        | line::reason::_ when line = "unknown" -> UNKNOWN reason
        | _ -> UNKNOWN raw_output

type EldaricaSolver () =
    inherit IConcreteSolver ()
    override x.ShouldSearchForBinaryInEnvironment = true
    override x.TransformClauses chcSystem = adtTransformClauses chcSystem

    override x.Name = "Eldarica"
    override x.BinaryName = "eld"
    override x.BinaryOptions filename = $"-horn -hsmt -t:%d{SECONDS_TIMEOUT} %s{filename}"

    override x.InterpretResult error raw_output =
        let output = Environment.split raw_output
        match output with
        | line::_ when line.StartsWith("(error") -> ERROR raw_output
        | line::_ when line = "unknown" -> UNKNOWN raw_output
        | line::_ when line = "sat" -> SAT
        | line::_ when line = "unsat" -> UNSAT
        | _ -> UNKNOWN (error + " &&& " + raw_output)

type Z3Solver () =
    inherit IConcreteSolver ()
    override x.ShouldSearchForBinaryInEnvironment = false
    override x.TransformClauses chcSystem = adtTransformClauses chcSystem

    override x.Name = "Z3"
    override x.BinaryName = "z3"
    override x.BinaryOptions filename = $"-smt2 -nw -memory:%d{MEMORY_LIMIT_MB} -T:%d{SECONDS_TIMEOUT} %s{filename}"

    override x.InterpretResult error raw_output =
        let output = Environment.split raw_output
        match output with
        | line::_ when line = "timeout" -> TIMELIMIT
        | line::_ when line = "unsat" -> UNSAT
        | line::_ when line = "sat" -> SAT
        | _ when error = "" && raw_output = "" -> OUTOFMEMORY
        | ["unknown"; ""] -> UNKNOWN ""
        | _ -> UNKNOWN (error + " &&& " + raw_output)

type CVC4IndSolver () =
    inherit IConcreteSolver ()
    override x.ShouldSearchForBinaryInEnvironment = false
    override x.TransformClauses chcSystem = adtTransformClauses chcSystem

    override x.Name = "CVC4Ind"
    override x.BinaryName = "cvc4"
    override x.BinaryOptions filename =
        $"--quant-ind --quant-cf --conjecture-gen --conjecture-gen-per-round=3 --full-saturate-quant --tlimit=%d{MSECONDS_TIMEOUT ()} %s{filename}"

    override x.InterpretResult error raw_output =
        if error <> "" then ERROR(error) else
        let output = Environment.split raw_output
        match output with
        | line::_ when line.StartsWith("(error ") -> ERROR(raw_output)
        | line::_ when line = "sat" -> SAT
        | line::_ when line = "unsat" -> UNSAT
        | line::reason::_ when line = "unknown" && reason = "(:reason-unknown timeout)" -> TIMELIMIT
        | line::reason::_ when line = "unknown" -> UNKNOWN reason
        | _ -> UNKNOWN raw_output

type VeriMAPiddtSolver () =
    inherit IConcreteSolver ()

    let isRule =
        let rec isRule = function
            | ExistsRule _
            | BaseRule(_, Bot) -> false
            | ForallRule(_, r) -> isRule r
            | BaseRule _ -> true
        function
        | TransformedCommand r -> isRule r
        | _ -> true

    let binaryName = "VeriMAP-iddt"

    override x.ShouldSearchForBinaryInEnvironment = true
    override x.Name = binaryName
    override x.BinaryName = binaryName
    override x.BinaryOptions filename = $"--timeout=%d{SECONDS_TIMEOUT} --check-sat %s{filename}"
    override x.FileExtension = ".pl"
    override x.TransformClauses chcSystem = adtTransformClauses chcSystem

    override x.CommandsToStrings commands =
        if PrintToProlog.isFirstOrderPrologProgram commands then [PrintToProlog.toPrologFile commands] else []

    override x.InterpretResult error raw_output =
        if error <> "" then ERROR(error) else
        let output = Environment.split raw_output
        match output with
        | _::line::_ when line.Contains("Answer") && line.EndsWith("true") -> SAT
        | _::line::_ when line.Contains("Answer") && line.EndsWith("false") -> UNSAT
        | _ -> UNKNOWN raw_output

type VampireSolver () =
    inherit IConcreteSolver ()

    override x.ShouldSearchForBinaryInEnvironment = true
    override x.Name = "Vampire"
    override x.BinaryName = "vampire"
    override x.BinaryOptions filename =
        $"--input_syntax smtlib2 --output_mode smtcomp --memory_limit {MEMORY_LIMIT_MB} --time_limit {SECONDS_TIMEOUT}s %s{filename}"

    override x.TransformClauses chcSystem =
        let chcs = adtTransformClauses chcSystem
        let setlogic = OriginalCommand <| SetLogic "UFDT"
        List.map (List.map (function OriginalCommand (SetLogic _) -> setlogic | c -> c)) chcs

    override x.InterpretResult error raw_output =
        if error <> "" then ERROR(error) else
        let output = Environment.split raw_output
        match output with
        | _ when raw_output = "" -> TIMELIMIT
        | "unknown"::_ -> UNKNOWN ""
        | "unsat"::_ -> UNSAT
        | "sat"::_ -> SAT
        | _ -> UNKNOWN raw_output

type AllSolver () =
    inherit IDirectorySolver<string list>()
    let solvers : IConcreteSolver list = [Z3Solver(); EldaricaSolver(); CVC4IndSolver(); CVC4FiniteSolver(); VeriMAPiddtSolver(); VampireSolver()]

    override x.Name = "AllSolvers"
    override x.BinaryName = "AllSolvers"
    override x.BinaryOptions _ = __unreachable__()
    override x.InterpretResult _ _ = __unreachable__()
    override x.TransformClauses _ = __unreachable__()

    override x.Solve filename =
        for solver in solvers do (solver :> ISolver).Solve(filename) |> ignore
        UNKNOWN "All solvers"

    override x.GenerateClauses performTransform tipToHorn quiet force directory =
        let forceGenerateClauses (solver : IConcreteSolver) =
            if not quiet then printfn $"Generating clauses for %s{solver.Name}"
            solver.GenerateClauses performTransform tipToHorn quiet false directory
        let paths =
            if force
                then solvers |> List.map forceGenerateClauses
                else solvers |> List.map (fun solver -> solver.DirectoryForTransformed directory)
        paths

    override x.RunOnBenchmarkSet overwrite quiet runs =
        let results =
            if overwrite
                then List.map2 (fun (solver : IConcreteSolver) path -> solver.RunOnBenchmarkSet false quiet path) solvers runs
                else List.map2 (fun (solver : IConcreteSolver) path -> solver.AnswersDirectory path) solvers runs
        let names = solvers |> List.map (fun solver -> solver.Name)
        let exts = solvers |> List.map (fun solver -> solver.FileExtension)
        let directory = ResultTable.GenerateReadableResultTable names exts results
        if not quiet then printfn "LaTeX table: %s" <| ResultTable.GenerateLaTeXResultTable names exts results
        directory
