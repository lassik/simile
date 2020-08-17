exception EvalErr of string;

datatype SValue
  = SNull
  | SPair of (SValue * SValue)
  | SBoolean of bool
  | SInteger of int
  | SChar of char
  | SString of string
  | SSymbol of string
  | SClosure of (RTE -> SValue)
and CTE = NullCte
        | Cte of (CTE ref * string array)
and RTE = NullRte
        | Rte of (RTE ref * SValue array);

type CLOSURE = (RTE -> SValue);

val STrue = SBoolean true;
val SFalse = SBoolean false;

fun writtenEscape s =
    s;

fun written (SBoolean false) = "#f"
  | written (SBoolean true) = "#t"
  | written SNull = "()"
  | written (SPair (car, cdr)) = "(" ^ (written car) ^ (writtenTail cdr)
  | written (SSymbol s) = s
  | written (SString s) = "\"" ^ (writtenEscape s) ^ "\""
  | written (SInteger i) = Int.toString i
and writtenTail SNull = ")"
  | writtenTail (SPair (car, cdr)) = " " ^ (written car) ^ (writtenTail cdr)
  | writtenTail obj = " . " ^ (written obj) ^ ")";

val written = written;

fun printLine s = print (s ^ "\n");
fun printValue v = printLine (written v);

val debug = false;
fun printDebug s = if debug then printLine s else ();

fun indexOf (goalName, names) =
    let val n = Array.length names
        fun search i =
            if i = n then
                NONE
            else if (Array.sub (names, i)) = goalName then
                SOME i
            else
                search (i + 1)
    in
        search 0
    end;

fun lookup (goalName, cte: CTE) =
    let fun ascend (Cte (parent, names), up) =
            case indexOf (goalName, names) of
                SOME index => (up, index)
              | NONE => ascend (!parent, up + 1)
    in
        (ascend (cte, 0)) : (int * int)
    end;

fun compileFetch (name, cte : CTE) =
    (case lookup (name, cte)
      of (up, over) =>
         fn rte =>
            let fun go_up 0 (Rte (_, vals)) =
                    Array.sub (vals, over)
                  | go_up n (Rte (parent, _)) =
                    go_up (n - 1) (!parent)
            in go_up up rte end) : CLOSURE;

fun mapSList (mapfn, SNull) = []
  | mapSList (mapfn, SPair (car, cdr)) =
    (mapfn car) :: (mapSList (mapfn, cdr));

fun op_string_append [] = SString ""
  | op_string_append ((SString a)::[]) = SString a
  | op_string_append ((SString a)::(SString b)::[]) = SString (a ^ b)
  | op_string_append xs =
    let fun loop acc [] = acc
          | loop acc ((SString s)::xs) = loop (acc ^ s) xs
    in SString (loop "" xs) end;

fun symbolNames ids =
    Array.fromList (mapSList ((fn x => case x of SSymbol name => name),
                              ids));

fun compileApply (headExpr : SValue, argsExpr: SValue, cte : CTE) =
    ((printDebug ("compile apply head " ^ (written headExpr)));
     let val head = compile (headExpr, cte)
         val args = mapSList ((fn argExpr => compile (argExpr, cte)),
                              argsExpr)
     in
         (fn rte => let val headVal = (head rte) : SValue
                        val argVals = List.map (fn arg => arg rte) args
                        val newRte  = Rte ((ref NullRte),
                                           (Array.fromList argVals))
                    in
                        case headVal
                         of SClosure f => f newRte
                          | _ =>
                            raise EvalErr("Trying to apply non-procedure")
                    end) : CLOSURE
     end)
and compileBegin (body : SValue, cte: CTE) =
    let val closures = mapSList ((fn part => compile (part, cte)),
                                 body)
    in (fn rte => List.foldl (fn (closure, value) => closure rte)
                             SFalse
                             closures)
    end
and compileLambda (tail : SValue, cte : CTE) =
    (case tail
      of SPair (ids, body) =>
         ((printDebug ("compile lambda" ^
                      " formals " ^ (written ids) ^
                      " body " ^ (written body)));
          let val closure =
                  compileBegin (body, Cte (ref cte, symbolNames ids))
          in (fn rte: RTE => SClosure (fn act: RTE =>
                                          ((case act
                                             of Rte (parent, _) =>
                                                parent := rte);
                                           (closure act)))) : CLOSURE
          end)
       | _ => raise EvalErr("Bad lambda"))
and compile (obj : SValue, cte : CTE) =
    ((printDebug ("compile eval " ^ (written obj)));
     (case obj of
          SNull => raise EvalErr("Empty application in source")
        | SPair (SSymbol "lambda", tail) => compileLambda (tail, cte)
        | SPair (head, tail) => compileApply (head, tail, cte)
        | SSymbol name => compileFetch (name, cte)
        | _ => (fn rte => obj))) : CLOSURE;

fun listFromArray array =
    let fun loop 0 acc = acc
          | loop i acc = loop (i - 1) ((Array.sub (array, (i - 1))) :: acc)
    in loop (Array.length array) [] end;

val primitives =
    [("string-append", op_string_append)];

fun closureForPrimitive prim =
    SClosure (fn Rte (_, args) => prim (listFromArray args));

fun getInitialEnvironments () =
    let fun loop (cte, rte, []) = (Cte (ref NullCte, (Array.fromList cte)),
                                   Rte (ref NullRte, (Array.fromList rte)))
          | loop (cte, rte, ((pname,pfunc)::ps)) =
            loop ((pname::cte), ((closureForPrimitive pfunc)::rte), ps)
    in loop ([], [], primitives) end;

fun SList [] = SNull
  | SList (x::xs) = SPair (x, SList xs);

fun demo () =
    let val (initCte, initRte) = getInitialEnvironments ()
        val program =
            compile ((SList [(SList [(SSymbol "lambda"),
                                     (SList [SSymbol "x"]),
                                     (SSymbol "x")]),
                             (SString "coloring between the lines")]),
                     initCte)
    in
        printValue (program initRte)
    end;

fun main () =
    demo ()
    handle EvalErr s => printLine s;

main ();
