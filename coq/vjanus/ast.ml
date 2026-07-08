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
and lval = { lname : string; sels : expr list; fields : string list; fsels : expr list }
        (* sels  = base array indices (before the field path)
           fields = struct field path
           fsels = array indices INTO an array field (after the field), e.g.
             out[j].dist   => { lname="out"; sels=[j]; fields=["dist"]; fsels=[] }
             a.v[i]        => { lname="a";  sels=[];  fields=["v"];    fsels=[i] }
             a.m[i][j]     => { lname="a";  sels=[];  fields=["m"];    fsels=[i;j] } *)

type arg = ALv of lval | AVal of expr

(* local/delocal declaration head: name, whether a stack, struct type (if any),
   array dims ([] => scalar), initializer (None => 0; for a struct local the
   init is an l-value to copy) *)
type decl = { dname : string; dis_stack : bool; dstruct : string option;
              ddims : int list; dinit : expr option }

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
  | Io of string                     (* read/write (jana2014_in_out); keyword kept for the error *)

type vinit = VE of expr | VA of vinit list

(* struct type declaration: `struct Name { int f1; int f2; ... }`.
   jana2014 struct fields are scalars (fdims is kept for forward-compat). *)
type sfield = { fname : string; fdims : int list }
type structdef = { sname : string; sfields : sfield list }

type vdecl = { vname : string; vis_stack : bool; vstruct : string option;
               vdims : int list; vinit : vinit option }

type param = { pname : string; pis_stack : bool; pis_array : bool;
               pstruct : string option }

type proc = { procname : string; params : param list; body : stmt list }

type program = { structs : structdef list; procs : proc list;
                 mvdecls : vdecl list; mstmts : stmt list }

exception Error of string * int * int   (* message, line, column *)
