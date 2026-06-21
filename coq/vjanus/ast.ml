(* ast.ml — vjanus's own jana2014 AST (the subset the verified core covers).
   Kept deliberately close to jana_py/parser_jana2014.py so the lowering in
   lower.ml can mirror coq/harness/differentialar.py. *)

type expr =
  | Num of int
  | Lv of lval
  | Bin of string * expr * expr      (* op in: + - * / % = < > >= <= != & | ^ && || *)
  | Not of expr                      (* ! e *)
  | Top of string                    (* top(s) *)
  | Empty of string                  (* empty(s) *)
  | Size of string                   (* size(a) *)
and lval = { lname : string; sels : expr list }   (* sels = array indices *)

type arg = ALv of lval | AVal of expr

(* local/delocal declaration head: name, whether a stack, initializer (None => 0) *)
type decl = { dname : string; dis_stack : bool; dinit : expr option }

type stmt =
  | Skip
  | Assign of lval * string * expr   (* op in: += -= ^= *)
  | Swap of lval * lval
  | If of expr * stmt list * stmt list * expr      (* entry, then, else, exit *)
  | From of expr * stmt list * stmt list * expr    (* entry, do, loop, until *)
  | Iterate of string * expr * expr * expr * bool * stmt list
        (* var, start, step, end, exclusive(`to`)?, body *)
  | Local of decl * stmt list * decl
  | Call of string * arg list
  | Uncall of string * arg list
  | Push of lval * string            (* push(x, s) *)
  | Pop of lval * string             (* pop(x, s) *)

type vinit = VE of expr | VA of vinit list

type vdecl = { vname : string; vis_stack : bool; vdims : int list; vinit : vinit option }

type param = { pname : string; pis_stack : bool; pis_array : bool }

type proc = { procname : string; params : param list; body : stmt list }

type program = { procs : proc list; mvdecls : vdecl list; mstmts : stmt list }

exception Error of string * int * int   (* message, line, column *)
