(* lexer.ml — tokenizer for the jana2014 dialect (procedure-style, indentation-
   insensitive; newlines are not significant).  Mirrors the token set of
   jana_py/parser_jana2014.py: // and /* */ comments, the swap/compound-assign
   operators, and 0b binary literals.  Strings are lexed (for printf) but the
   parser drops print statements. *)

type tok =
  | KW of string        (* keyword *)
  | ID of string        (* identifier *)
  | NUM of int
  | OP of string        (* operator / punctuation *)
  | STR of string
  | EOF

type token = { t : tok; line : int; col : int }

let keywords =
  [ "procedure"; "main"; "int"; "stack"; "bool"; "struct";
    "if"; "then"; "else"; "fi";
    "from"; "do"; "loop"; "until";
    "iterate"; "by"; "to"; "end";
    "local"; "delocal"; "call"; "uncall"; "external";
    "push"; "pop"; "skip"; "error";
    "printf"; "print"; "show"; "read"; "write";
    "top"; "empty"; "size"; "nil"; "true"; "false" ]

(* multi-char operators, longest first *)
let ops3 = [ "<=>" ]
let ops2 = [ "+="; "-="; "^="; "*="; "/="; "=="; "!="; "<="; ">="; "&&"; "||"; "<<"; ">>"; "**" ]
let ops1 = [ "="; "<"; ">"; "+"; "-"; "*"; "/"; "%"; "^"; "&"; "|"; "!"; "#";
             ","; "."; ":"; "?"; "("; ")"; "["; "]"; "{"; "}"; ";" ]

let is_id_start c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_'
let is_id c = is_id_start c || (c >= '0' && c <= '9') || c = '\''
let is_digit c = c >= '0' && c <= '9'

let tokenize (s : string) : token list =
  let n = String.length s in
  let i = ref 0 and line = ref 1 and col = ref 1 in
  let out = ref [] in
  let adv k = for _ = 1 to k do
      (if !i < n && s.[!i] = '\n' then (incr line; col := 1) else incr col); incr i
    done in
  let starts p = !i + String.length p <= n && String.sub s !i (String.length p) = p in
  while !i < n do
    let c = s.[!i] in
    if c = ' ' || c = '\t' || c = '\r' || c = '\n' then adv 1
    else if starts "//" then (while !i < n && s.[!i] <> '\n' do adv 1 done)
    else if starts "/*" then begin
      adv 2; while !i < n && not (starts "*/") do adv 1 done;
      if !i < n then adv 2
    end
    else if c = '"' then begin
      let l = !line and cc = !col in adv 1;
      let b = Buffer.create 16 in
      while !i < n && s.[!i] <> '"' do
        (if s.[!i] = '\\' && !i + 1 < n then (Buffer.add_char b s.[!i]; adv 1));
        Buffer.add_char b s.[!i]; adv 1
      done;
      if !i < n then adv 1;
      out := { t = STR (Buffer.contents b); line = l; col = cc } :: !out
    end
    else if is_digit c then begin
      let l = !line and cc = !col in
      let v =
        if starts "0b" then begin
          adv 2; let st = !i in
          while !i < n && (s.[!i] = '0' || s.[!i] = '1') do adv 1 done;
          int_of_string ("0b" ^ String.sub s st (!i - st))
        end else begin
          let st = !i in
          while !i < n && is_digit s.[!i] do adv 1 done;
          int_of_string (String.sub s st (!i - st))
        end in
      out := { t = NUM v; line = l; col = cc } :: !out
    end
    else if is_id_start c then begin
      let l = !line and cc = !col and st = !i in
      while !i < n && is_id s.[!i] do adv 1 done;
      let w = String.sub s st (!i - st) in
      let t = if List.mem w keywords then KW w else ID w in
      out := { t; line = l; col = cc } :: !out
    end
    else begin
      let l = !line and cc = !col in
      let pick lst = List.find_opt starts lst in
      match (match pick ops3 with Some _ as r -> r | None ->
             match pick ops2 with Some _ as r -> r | None -> pick ops1) with
      | Some op -> adv (String.length op);
                   out := { t = OP op; line = l; col = cc } :: !out
      | None -> raise (Ast.Error (Printf.sprintf "unexpected character %C" c, l, cc))
    end
  done;
  List.rev ({ t = EOF; line = !line; col = !col } :: !out)
