exception CompileErr of string;
exception EvalErr of string;
val ProperListExpected = EvalErr "Proper list expected";

datatype SValue
  = SNull
  | SPair of (SValue * SValue)
  | SBoolean of bool
  | SInteger of int
  | SChar of char
  | SString of string
  | SSymbol of string
  | SVector of SValue list
  | SClosure of (RTE -> SReturn)
and CTE = NullCte
        | Cte of (CTE ref * string array)
and RTE = NullRte
        | Rte of (RTE ref * SValue array)
and SReturn
    = Return of SValue
    | ReturnValues of SValue list
    | RaiseException of SValue
    | BadArgs;

type CLOSURE = (RTE -> SReturn);

datatype SBinding
  = Prim of (SValue list -> SReturn)
  | PrimSyntax of (SValue list -> SReturn)
  | UserSyntax;

val STrue = SBoolean true;
val SFalse = SBoolean false;
val NullString = SString "";
val ReturnNoValues = ReturnValues [];

val RaiseProperListExpected = RaiseException (SString "Proper list expected");

fun writtenEscape s =
    s;

fun written (SBoolean false) = "#f"
  | written (SBoolean true) = "#t"
  | written SNull = "()"
  | written (SPair (car, cdr)) = "(" ^ (written car) ^ (writtenTail cdr)
  | written (SSymbol s) = s
  | written (SString s) = "\"" ^ (writtenEscape s) ^ "\""
  | written (SInteger i) = Int.toString i
  | written (SChar c) = "#\\" ^ (Char.toString c)
  | written (SVector v) =
    "#(" ^ (String.concatWith " " (List.map written v)) ^ ")"
  | written (SClosure c) = "#<procedure>"
and writtenTail SNull = ")"
  | writtenTail (SPair (car, cdr)) = " " ^ (written car) ^ (writtenTail cdr)
  | writtenTail obj = " . " ^ (written obj) ^ ")";

fun printLine s = print (s ^ "\n");
fun printReturn (Return v) =
    printLine (written v)
  | printReturn (ReturnValues vs) =
    printLine (String.concatWith "; " (List.map written vs))
  | printReturn (RaiseException ex) =
    printLine ("Exception " ^ (written ex))
  | printReturn _ =
    printLine "#<???>";

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
            (case indexOf (goalName, names) of
                 SOME index => (up, index)
               | NONE => ascend (!parent, up + 1))
          | ascend (NullCte, up) =
            raise CompileErr goalName
    in
        (ascend (cte, 0)) : (int * int)
    end;

fun compileFetch (name, cte : CTE) =
    (case lookup (name, cte)
      of (up, over) =>
         fn rte =>
            let fun go_up 0 (Rte (_, vals)) =
                    Return (Array.sub (vals, over))
                  | go_up n (Rte (parent, _)) =
                    go_up (n - 1) (!parent)
                  | go_up n NullRte =
                    raise CompileErr name
            in go_up up rte end) : CLOSURE;

fun mapSList (mapfn, SNull) = []
  | mapSList (mapfn, SPair (car, cdr)) =
    (mapfn car) :: (mapSList (mapfn, cdr))
  | mapSList (mapfn, _) =
    raise ProperListExpected

fun reverse xs =
    let fun loop (acc, SNull) = acc
          | loop (acc, SPair (a, d)) = loop ((SPair (a, acc)), d)
          | loop (acc, _) = raise ProperListExpected
    in loop (SNull, xs) end;

fun listToSchemeList xs =
    let fun loop (acc, []) = reverse acc
          | loop (acc, (x::xs)) = loop ((SPair (x, acc)), xs)
    in loop (SNull, xs) end;

val featureList = ["r7rs", "simile"];

(* String utilities *)

fun assertStringIndex (s, start) =
    if (start < 0) orelse (start >= (String.size s)) then
        raise EvalErr "string index out of bounds"
    else
        ();

fun assertStringBounds (s, start, end_) =
    (assertStringIndex (s, start);
     if (end_ < 0) orelse (end_ > (String.size s)) then
         raise EvalErr "substring end position out of bounds"
     else
         ());

fun stringCompare (cmp, strings) =
    let fun loop _ [] = Return STrue
          | loop NONE ((SString this)::ss) =
            loop (SOME this) ss
          | loop (SOME last) ((SString this)::ss) =
            if cmp (last, this) then loop (SOME this) ss else Return SFalse
          | loop _ _ = BadArgs
    in loop NONE strings end;

fun charFoldcase c = Char.toLower c;

fun stringUpcase   s = String.map Char.toUpper s;
fun stringDowncase s = String.map Char.toLower s;
fun stringFoldcase s = stringDowncase s;

(* 4.2.9. Case-lambda *)

fun syntax_case_lambda _ = BadArgs;

(* 6.4. Pairs and lists *)

(* 6.6. Characters *)

fun prim_char_alphabetic_p [(SChar c)] = Return (SBoolean (Char.isAlpha c))
  | prim_char_alphabetic_p _ = BadArgs;

fun prim_char_lower_case_p [(SChar c)] = Return (SBoolean (Char.isLower c))
  | prim_char_lower_case_p _ = BadArgs;

fun prim_char_numeric_p [(SChar c)] = Return (SBoolean (Char.isDigit c))
  | prim_char_numeric_p _ = BadArgs;

fun prim_char_upper_case_p [(SChar c)] = Return (SBoolean (Char.isUpper c))
  | prim_char_upper_case_p _ = BadArgs;

fun prim_char_whitespace_p [(SChar c)] = Return (SBoolean (Char.isSpace c))
  | prim_char_whitespace_p _ = BadArgs;

fun prim_char_ge_p [(SChar a), (SChar b)] = Return (SBoolean (a >= b))
  | prim_char_ge_p _ = BadArgs;

fun prim_char_lt_p [(SChar a), (SChar b)] = Return (SBoolean (a < b))
  | prim_char_lt_p _ = BadArgs;

fun prim_char_eq_p [(SChar a), (SChar b)] = Return (SBoolean (a = b))
  | prim_char_eq_p _ = BadArgs;

fun prim_char_ge_p [(SChar a), (SChar b)] = Return (SBoolean (a >= b))
  | prim_char_ge_p _ = BadArgs;

fun prim_char_gt_p [(SChar a), (SChar b)] = Return (SBoolean (a > b))
  | prim_char_gt_p _ = BadArgs;

fun prim_char_downcase [(SChar c)] = Return (SChar (Char.toLower c))
  | prim_char_downcase _ = BadArgs;

fun prim_char_foldcase [(SChar c)] = Return (SChar (charFoldcase c))
  | prim_char_foldcase _ = BadArgs;

fun prim_char_upcase [(SChar c)] = Return (SChar (Char.toUpper c))
  | prim_char_upcase _ = BadArgs;

fun prim_digit_value [(SChar c)] =
    if c >= #"0" andalso c <= #"9" then
        Return (SChar (Char.chr ((Char.ord c) - (Char.ord #"0"))))
    else
        Return SFalse
  | prim_digit_value _ = BadArgs;

(* 6.7. Strings *)

fun prim_string_p [(SString a)] = Return STrue
  | prim_string_p [_] = Return SFalse
  | prim_string_p _ = BadArgs;

fun prim_make_string [k] = prim_make_string [k, (SChar #" ")]
  | prim_make_string [(SInteger k), (SChar char)] =
    Return (SString (CharVector.tabulate (k, (fn _ => char))))
  | prim_make_string _ = BadArgs;

fun prim_string chars =
    let fun loop acc [] = Return (SString acc)
          | loop acc ((SChar char)::chars) =
            loop (acc ^ (Char.toString char)) chars
          | loop acc _ = BadArgs
    in loop "" chars end;

fun prim_string_length [(SString s)] = Return (SInteger (String.size s))
  | prim_string_length _ = BadArgs;

fun prim_string_ref [(SString s), (SInteger k)] =
    (assertStringIndex (s, k); Return (SChar (String.sub (s, k))))
  | prim_string_ref _ = BadArgs;

fun prim_string_equals_p strings =
    stringCompare ((fn (a, b) => a = b), strings);

fun prim_string_ci_equals_p strings =
    stringCompare ((fn (a, b) => stringFoldcase(a) = stringFoldcase(b)),
                   strings);

fun prim_string_ci_le_p strings =
    stringCompare ((fn (a, b) => stringFoldcase(a) <= stringFoldcase(b)),
                   strings);

fun prim_string_ci_lt_p strings =
    stringCompare ((fn (a, b) => stringFoldcase(a) < stringFoldcase(b)),
                   strings);

fun prim_string_ci_eq_p strings =
    stringCompare ((fn (a, b) => stringFoldcase(a) = stringFoldcase(b)),
                   strings);

fun prim_string_ci_ge_p strings =
    stringCompare ((fn (a, b) => stringFoldcase(a) >= stringFoldcase(b)),
                   strings);

fun prim_string_ci_gt_p strings =
    stringCompare ((fn (a, b) => stringFoldcase(a) > stringFoldcase(b)),
                   strings);

fun prim_string_upcase [(SString s)] = Return (SString (stringUpcase s))
  | prim_string_upcase _ = BadArgs;

fun prim_string_downcase [(SString s)] = Return (SString (stringDowncase s))
  | prim_string_downcase _ = BadArgs;

fun prim_string_foldcase [(SString s)] = Return (SString (stringFoldcase s))
  | prim_string_foldcase _ = BadArgs;

fun prim_string_to_list [(SString s)] =
    let fun loop acc 0 = Return acc
          | loop acc i = loop (SPair (SChar (String.sub (s, (i - 1))), acc))
                              (i - 1)
    in loop SNull (String.size s) end
  | prim_string_to_list _ = BadArgs;

fun prim_string_append [] = Return NullString
  | prim_string_append ((SString a)::[]) = Return (SString a)
  | prim_string_append ((SString a)::(SString b)::[]) =
    Return (SString (a ^ b))
  | prim_string_append xs =
    let fun loop acc [] = Return (SString acc)
          | loop acc ((SString s)::xs) = loop (acc ^ s) xs
          | loop acc _ = BadArgs
    in loop "" xs end;

fun stringToList (s, start, end_) =
    let fun loop (acc, end_) =
            if end_ > start then
                loop ((SPair ((SChar (String.sub (s, (end_ - 1)))),
                              acc)),
                      (end_ - 1))
            else
                Return acc
    in loop (SNull, end_) end;

fun prim_string_to_list [(SString s)] =
    stringToList (s, 0, (String.size s))
  | prim_string_to_list [(SString s), (SInteger start)] =
    ((assertStringIndex (s, start));
     (stringToList (s, start, (String.size s))))
  | prim_string_to_list [(SString s), (SInteger start), (SInteger end_)] =
    ((assertStringBounds (s, start, end_));
     (stringToList (s, start, end_)))
  | prim_string_to_list _ = BadArgs;

fun prim_list_to_string [list] =
    let fun loop (acc, SNull) = Return (SString acc)
          | loop (acc, SPair ((SChar char), tail)) =
            loop ((acc ^ (Char.toString char)), tail)
          | loop _ = RaiseProperListExpected
    in loop ("", list) end
  | prim_list_to_string _ = BadArgs;

fun prim_string_copy [(SString s)] =
    Return (SString (String.substring (s, 0, (String.size s))))
  | prim_string_copy [(SString s), (SInteger start)] =
    ((assertStringIndex (s, start));
     Return (SString (String.substring (s, start, (String.size s) - start))))
  | prim_string_copy [(SString s), (SInteger start), (SInteger end_)] =
    ((assertStringBounds (s, start, end_));
     Return (SString (String.substring (s, start, end_ - start))))
  | prim_string_copy _ = BadArgs;

fun prim_substring [s, start, end_] = prim_string_copy [s, start, end_]
  | prim_substring _ = BadArgs;

(* 6.8. Vectors *)

fun prim_vector_p [(SVector a)] = Return STrue
  | prim_vector_p [_] = Return SFalse
  | prim_vector_p _ = BadArgs;

(* 6.14. System interface *)

fun prim_features [] =
    Return (listToSchemeList (List.map (fn s => SSymbol s) featureList))
  | prim_features _ = BadArgs;

(* *)

fun symbolNames ids =
    Array.fromList
        (mapSList ((fn x => case x of
                                SSymbol name => name
                              | _ => raise CompileErr "Not a symbol"),
                   ids));

fun compileApply (exprs: SValue, cte: CTE) =
    let val compiled = (mapSList ((fn expr => compile (expr, cte)),
                                  exprs))
    in
        (fn rte =>
            let fun loop acc (x::xs) =
                    (case x rte of
                         Return value => loop (value :: acc) xs
                       | ReturnValues [] => loop (SFalse :: acc) xs
                       | ReturnValues (v::vs) => loop (v :: acc) xs
                       | failure => failure)
                  | loop acc [] =
                    (case List.rev acc of
                         [] => raise EvalErr "Trying to apply empty list"
                       | (headVal::argVals) =>
                         (case headVal of
                              SClosure f =>
                              (let val newRte = Rte ((ref NullRte),
                                                     (Array.fromList argVals))
                               in f newRte end)
                            | _ => raise EvalErr
                                         ("Trying to apply non-procedure "
                                          ^ (written headVal))))
            in loop [] compiled end)
    end
and compileBegin (exprs: SValue, cte: CTE) =
    let val compiled = (mapSList ((fn expr => compile (expr, cte)),
                                  exprs))
    in
        (fn rte =>
            let fun loop [] = ReturnNoValues
                  | loop (x::[]) = x rte
                  | loop (x::xs) =
                    (case x rte of
                         Return _ => loop xs
                       | ReturnValues _ => loop xs
                       | failure => failure)
            in loop compiled end)
    end
and compileLambda (tail : SValue, cte : CTE) =
    (case tail
      of SPair (ids, body) =>
         ((printDebug ("compile lambda" ^
                       " formals " ^ (written ids) ^
                       " body " ^ (written body)));
          let val closure =
                  compileBegin (body, Cte (ref cte, symbolNames ids))
          in (fn rte: RTE =>
                 Return (SClosure
                             (fn act: RTE =>
                                 ((case act
                                    of Rte (parent, _) =>
                                       parent := rte
                                     | NullRte => raise EvalErr "No such");
                                  (closure act))))) : CLOSURE
          end)
       | _ => raise EvalErr "Bad lambda")
and compile (obj : SValue, cte : CTE) =
    ((printDebug ("compile eval " ^ (written obj)));
     (case obj of
          SNull => raise EvalErr "Empty application in source"
        | SPair (SSymbol "lambda", tail) => compileLambda (tail, cte)
        | SPair _ => compileApply (obj, cte)
        | SSymbol name => compileFetch (name, cte)
        | _ => (fn rte => Return obj))) : CLOSURE;

fun listFromArray array =
    let fun loop 0 acc = acc
          | loop i acc = loop (i - 1) ((Array.sub (array, (i - 1))) :: acc)
    in loop (Array.length array) [] end;

val libraries = [

    (["scheme", "base"],
     [("features", Prim prim_features),
      ("list->string", Prim prim_list_to_string),
      ("make-string", Prim prim_make_string),
      ("string", Prim prim_string),
      ("string->list", Prim prim_string_to_list),
      ("string-append", Prim prim_string_append),
      ("string-copy", Prim prim_string_copy),
      ("string-length", Prim prim_string_length),
      ("string-ref", Prim prim_string_ref),
      ("string=?", Prim prim_string_equals_p),
      ("string?", Prim prim_string_p),
      ("substring", Prim prim_string_copy),
      ("vector?", Prim prim_vector_p)]),

    (["scheme", "case-lambda"],
     [("case-lambda", PrimSyntax syntax_case_lambda)]),

    (["scheme", "char"],
     [("char-alphabetic?", Prim prim_char_alphabetic_p),
      ("char-ci<=?", Prim prim_char_ge_p),
      ("char-ci<?", Prim prim_char_lt_p),
      ("char-ci=?", Prim prim_char_eq_p),
      ("char-ci>=?", Prim prim_char_ge_p),
      ("char-ci>?", Prim prim_char_gt_p),
      ("char-downcase", Prim prim_char_downcase),
      ("char-foldcase", Prim prim_char_foldcase),
      ("char-lower-case?", Prim prim_char_lower_case_p),
      ("char-numeric?", Prim prim_char_numeric_p),
      ("char-upcase", Prim prim_char_upcase),
      ("char-upper-case?", Prim prim_char_upper_case_p),
      ("char-whitespace?", Prim prim_char_whitespace_p),
      ("digit-value", Prim prim_digit_value),
      ("string-ci<=?", Prim prim_string_ci_le_p),
      ("string-ci<?", Prim prim_string_ci_lt_p),
      ("string-ci=?", Prim prim_string_ci_eq_p),
      ("string-ci>=?", Prim prim_string_ci_ge_p),
      ("string-ci>?", Prim prim_string_ci_gt_p),
      ("string-downcase", Prim prim_string_downcase),
      ("string-foldcase", Prim prim_string_foldcase),
      ("string-upcase", Prim prim_string_upcase)]),

    (["scheme", "cxr"],
     []),

    (["scheme", "eval"],
     [])

];

fun closureForPrimitiveFun pfun =
    SClosure (fn rte =>
                 case rte of
                     Rte (_, args) => pfun (listFromArray args)
                   | NullRte => raise EvalErr "No such");

fun appendMap mapfun xs =
    let fun loop acc [] = acc
          | loop acc (x::xs) = loop (acc @ (mapfun x)) xs
    in loop [] xs end;

fun primitives () =
    appendMap (fn (libName, libPrims) => libPrims)
              libraries;

fun getInitialEnvironments () =
    let fun loop (cte, rte, []) = (Cte (ref NullCte, (Array.fromList cte)),
                                   Rte (ref NullRte, (Array.fromList rte)))
          | loop (cte, rte, ((pname, Prim pfun)::ps)) =
            loop ((pname::cte),
                  ((closureForPrimitiveFun pfun)::rte),
                  ps)
          | loop (cte, rte, (_::ps)) =
            loop (cte, rte, ps)
    in loop ([], [], (primitives ())) end;

fun SList [] = SNull
  | SList (x::xs) = SPair (x, SList xs);

fun demo () =
    let val (initCte, initRte) = getInitialEnvironments ()
        val sourceCode =
            SList [(SList [(SSymbol "lambda"),
                           (SList [(SSymbol "a"),
                                   (SSymbol "b")]),
                           (SList [(SSymbol "string-append"),
                                   (SSymbol "a"),
                                   (SSymbol "b")])]),
                   (SString "This is easier than"),
                   (SList [(SSymbol "string-append"),
                           (SList [(SSymbol "make-string"),
                                   (SInteger 10),
                                   (SChar #"X")]),
                           (SString "coloring between the lines!")])]
        val compiledCode = compile (sourceCode, initCte)
    in
        printReturn (compiledCode initRte)
    end;

fun main () =
    demo ()
    handle EvalErr s => printLine s;

main ();
