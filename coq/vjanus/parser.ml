(* parser.ml — recursive-descent parser for jana2014 into Ast.

   jana2014 has no statement terminators; statement lists are delimited by the
   enclosing construct's keywords (else/fi/loop/until/end/delocal/procedure/EOF),
   and expressions are maximal-munch over operators (they stop at an identifier
   or keyword that is not an operator).  This matches jana_py/parser_jana2014.py
   closely enough for the corpus; unsupported surface forms raise Ast.Error. *)

open Ast
open Lexer

type st = { a : token array; mutable p : int }

let mk toks = { a = Array.of_list toks; p = 0 }
let peek s = s.a.(s.p)
let peek2 s = if s.p + 1 < Array.length s.a then s.a.(s.p + 1) else s.a.(Array.length s.a - 1)
let adv s = s.p <- s.p + 1
let err s m = let tk = peek s in raise (Ast.Error (m, tk.line, tk.col))

let at_op s o = match (peek s).t with OP x -> x = o | _ -> false
let at_kw s k = match (peek s).t with KW x -> x = k | _ -> false
let eat_op s o = if at_op s o then adv s else err s (Printf.sprintf "expected '%s'" o)
let eat_kw s k = if at_kw s k then adv s else err s (Printf.sprintf "expected '%s'" k)
let opt_op s o = if at_op s o then (adv s; true) else false

let ident s = match (peek s).t with
  | ID x -> adv s; x
  | KW x -> adv s; x   (* allow keyword-like field/proc names where the grammar does *)
  | _ -> err s "expected identifier"

(* ----- expressions (precedence climbing) ----- *)

let binop_level = function
  | "||" -> Some 1
  | "&&" -> Some 2
  | "=" | "==" | "!=" | "#" | "<" | "<=" | ">" | ">=" -> Some 3
  | "+" | "-" -> Some 4
  | "*" | "/" | "%" -> Some 5
  | _ -> None

let norm_op = function "=" -> "==" | "#" -> "!=" | o -> o

let rec expr s = expr_bin s 1
and expr_bin s minl =
  let left = ref (expr_unary s) in
  let continue = ref true in
  while !continue do
    (match (peek s).t with
     | OP o ->
       (match binop_level o with
        | Some l when l >= minl ->
          adv s;
          let right = expr_bin s (l + 1) in
          left := Bin (norm_op o, !left, right)
        | _ -> continue := false)
     | _ -> continue := false)
  done;
  !left
and expr_unary s =
  if at_op s "!" then (adv s; Not (expr_unary s))
  else if at_op s "-" then (adv s; Bin ("-", Num 0, expr_unary s))
  else expr_atom s
and expr_atom s =
  match (peek s).t with
  | NUM n -> adv s; Num n
  | OP "(" -> adv s; let e = expr s in eat_op s ")"; e
  | KW "true" -> adv s; Num 1
  | KW "false" -> adv s; Num 0
  | KW "nil" -> adv s; err s "nil is only valid as a stack initializer"
  | KW "top" -> adv s; eat_op s "("; let n = ident s in eat_op s ")"; Top n
  | KW "empty" -> adv s; eat_op s "("; let n = ident s in eat_op s ")"; Empty n
  | KW "size" -> adv s; eat_op s "("; let n = ident s in eat_op s ")"; Size n
  | ID _ | KW _ -> Lv (lval s)
  | _ -> err s "expected expression"
and lval s =
  let nm = ident s in
  let sels = ref [] in
  while at_op s "[" do adv s; let e = expr s in eat_op s "]"; sels := e :: !sels done;
  { lname = nm; sels = List.rev !sels }

(* ----- statements ----- *)

let stop_kw s set = match (peek s).t with
  | KW k -> List.mem k set
  | EOF -> true
  | _ -> false

let rec stmt s =
  match (peek s).t with
  | KW "skip" -> adv s; Skip
  | KW "if" -> if_stmt s
  | KW "from" -> from_stmt s
  | KW "iterate" -> iterate_stmt s
  | KW "local" -> local_stmt s
  | KW "call" -> adv s; let n, a = call_target s in Call (n, a)
  | KW "uncall" -> adv s; let n, a = call_target s in Uncall (n, a)
  | KW "push" -> adv s; eat_op s "("; let x = lval s in eat_op s ","; let st = ident s in eat_op s ")"; Push (x, st)
  | KW "pop" -> adv s; eat_op s "("; let x = lval s in eat_op s ","; let st = ident s in eat_op s ")"; Pop (x, st)
  | (KW "printf" | KW "print" | KW "show" | KW "read" | KW "write" | KW "error") ->
      print_like s; Skip
  | ID _ -> assign_or_swap s
  | _ -> err s "expected statement"

and stmts s set =
  let acc = ref [] in
  while not (stop_kw s set) do acc := stmt s :: !acc done;
  List.rev !acc

and assign_or_swap s =
  let l = lval s in
  match (peek s).t with
  | OP "<=>" -> adv s; let r = lval s in Swap (l, r)
  | OP ("+=" | "-=" | "^=" as o) -> adv s; let e = expr s in Assign (l, o, e)
  | _ -> err s "expected '+=', '-=', '^=' or '<=>'"

and if_stmt s =
  eat_kw s "if"; let entry = expr s in
  ignore (opt_kw s "then");
  let thenp = stmts s ["else"; "fi"] in
  let elsep = if at_kw s "else" then (adv s; stmts s ["fi"]) else [] in
  eat_kw s "fi";
  let exit = if starts_expr s then expr s else entry in
  If (entry, thenp, elsep, exit)

and from_stmt s =
  eat_kw s "from"; let entry = expr s in
  let dop = if at_kw s "do" then (adv s; stmts s ["loop"; "until"]) else [] in
  let loopp = if at_kw s "loop" then (adv s; stmts s ["until"]) else [] in
  eat_kw s "until"; let exit = expr s in
  From (entry, dop, loopp, exit)

and iterate_stmt s =
  eat_kw s "iterate";
  (match (peek s).t with KW "int" -> adv s | _ -> ());     (* optional type *)
  let v = ident s in
  eat_op s "="; let start = expr s in
  let step = if at_kw s "by" then (adv s; expr s) else Num 1 in
  eat_kw s "to"; let endd = expr s in
  let body = stmts s ["end"] in
  eat_kw s "end";
  Iterate (v, start, step, endd, false, body)

and local_stmt s =
  eat_kw s "local"; let d1 = decl s in
  let body = stmts s ["delocal"] in
  eat_kw s "delocal"; let d2 = decl s in
  Local (d1, body, d2)

and decl s =
  let is_stack = if at_kw s "stack" then (adv s; true)
                 else (ignore (opt_kw s "int"); ignore (opt_kw s "bool"); false) in
  let nm = ident s in
  let init = if opt_op s "=" then
      (if at_kw s "nil" then (adv s; None) else Some (expr s))
    else None in
  { dname = nm; dis_stack = is_stack; dinit = init }

and call_target s =
  let n = ident s in
  let args = ref [] in
  if opt_op s "(" then begin
    if not (at_op s ")") then begin
      args := [arg s];
      while opt_op s "," do args := arg s :: !args done
    end;
    eat_op s ")"
  end;
  (n, List.rev !args)

and arg s =
  (* an l-value reference, or a value expression *)
  match (peek s).t with
  | ID _ ->
    let save = s.p in
    let l = lval s in
    (match (peek s).t with
     | OP ("+" | "-" | "*" | "/" | "%" | "=" | "==" | "!=" | "#"
          | "<" | "<=" | ">" | ">=" | "&&" | "||") ->
        s.p <- save; AVal (expr s)              (* it was the start of an expression *)
     | _ -> ALv l)
  | _ -> AVal (expr s)

and print_like s =
  adv s;                                   (* the print keyword *)
  (* consume a balanced (...) or a trailing expression list; we drop prints. *)
  if opt_op s "(" then begin
    let depth = ref 1 in
    while !depth > 0 do
      (match (peek s).t with
       | OP "(" -> incr depth | OP ")" -> decr depth
       | EOF -> err s "unterminated print" | _ -> ());
      adv s
    done
  end else if not (stop_kw s ["procedure"]) then ignore (expr s)

and opt_kw s k = if at_kw s k then (adv s; true) else false
and starts_expr s = match (peek s).t with
  | NUM _ -> true
  | OP ("(" | "!" | "-") -> true
  | KW ("top" | "empty" | "size" | "true" | "false") -> true
  | ID _ -> true
  | _ -> false

(* ----- declarations / procedures / program ----- *)

let typ_kw s =
  match (peek s).t with
  | KW ("int" | "bool") -> adv s; `Int
  | KW "stack" -> adv s; `Stack
  | _ -> err s "expected a type"

let rec vdecl s =
  let k = typ_kw s in
  let nm = ident s in
  let dims = ref [] in
  while at_op s "[" do
    adv s;
    (match (peek s).t with NUM n -> adv s; dims := n :: !dims
     | _ -> err s "array dimension must be a constant");
    eat_op s "]"
  done;
  let init =
    if opt_op s "=" then
      (if at_kw s "nil" then (adv s; None) else Some (vinit s))
    else None in
  { vname = nm; vis_stack = (k = `Stack); vdims = List.rev !dims; vinit = init }

and vinit s =
  if at_op s "{" then begin
    adv s;
    let acc = ref [] in
    if not (at_op s "}") then begin
      acc := [vinit s];
      while opt_op s "," do acc := vinit s :: !acc done
    end;
    eat_op s "}";
    VA (List.rev !acc)
  end else VE (expr s)

let param s =
  let k = typ_kw s in
  let nm = ident s in
  let is_array = ref false in
  while at_op s "[" do                        (* int a[] | int a[5] | int a[][] *)
    adv s;
    (match (peek s).t with NUM _ -> adv s | _ -> ());   (* optional, ignored size *)
    eat_op s "]"; is_array := true
  done;
  { pname = nm; pis_stack = (k = `Stack); pis_array = !is_array }

let params s =
  eat_op s "(";
  let acc = ref [] in
  if not (at_op s ")") then begin
    acc := [param s];
    while opt_op s "," do acc := param s :: !acc done
  end;
  eat_op s ")";
  List.rev !acc

let procedure s =
  eat_kw s "procedure";
  let nm = match (peek s).t with KW "main" -> adv s; "main" | _ -> ident s in
  if nm = "main" then begin
    if at_op s "(" then (eat_op s "("; eat_op s ")");
    let vds = ref [] in
    while (match (peek s).t with KW ("int" | "stack" | "bool") -> true | _ -> false) do
      vds := vdecl s :: !vds
    done;
    let body = stmts s ["procedure"] in
    `Main (List.rev !vds, body)
  end else begin
    let ps = params s in
    let body = stmts s ["procedure"] in
    `Proc { procname = nm; params = ps; body }
  end

let program (toks : token list) : program =
  let s = mk toks in
  let procs = ref [] and main = ref None in
  while not (match (peek s).t with EOF -> true | _ -> false) do
    if not (at_kw s "procedure") then err s "expected 'procedure'";
    match procedure s with
    | `Proc p -> procs := p :: !procs
    | `Main (vds, body) ->
      (match !main with Some _ -> err s "multiple main procedures" | None -> main := Some (vds, body))
  done;
  let mvdecls, mstmts = match !main with Some (v, b) -> v, b | None -> [], [] in
  { procs = List.rev !procs; mvdecls; mstmts }
