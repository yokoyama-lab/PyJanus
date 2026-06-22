(* lower_frame.ml — translate the jana2014 Ast into the verified *frame* core's
   stmt/expr (Janus_frame, extracted in RevExtractFrame.v).  Phase 2a parallel to
   lower.ml: instead of one flat global slot per (scope, name), every variable
   reference is classified into the frame core's [ref]:

     - a `main` variable        -> RG n   (global slot, location G n)
     - a procedure formal i     -> RF i   (positional; resolved to the actual's
                                           absolute name at the call site)
     - a local / iterate var    -> RL x   (depth-d local, location L d x)

   Because locals are depth-indexed, a `local` survives recursion (the bug the
   flat lower.ml rejects).  The frame core has no Swap primitive, so swaps and
   the swap-temp calling idiom are expressed as XOR triples (reversible).

   Coverage so far: scalars, arithmetic/comparison, if, from-loop, iterate,
   local/delocal, scalar swap, and procedure call/uncall with by-reference
   scalar and by-value arguments.  Arrays and stacks raise [Unsupported] (the CLI
   turns that into a clean exit-3 "skip"); they are the next increment. *)

module J = Janus_frame
open Ast

exception Unsupported of string

let nat = Glue_frame.nat_of_int
let z = Glue_frame.z_of_int

(* one name-binding environment: a procedure's formals (positional) and the
   locals introduced within it; [is_main] scopes see globals instead of formals *)
type scope = {
  is_main : bool;
  formals : (string, int) Hashtbl.t;   (* formal name -> positional index (RF i) *)
  locals  : (string, int) Hashtbl.t;   (* local  name -> local slot     (RL x)  *)
  mutable nloc : int;
}

type t = {
  globals : (string, int) Hashtbl.t;   (* main var name -> global slot (RG n) *)
  mutable nglob : int;
  procmap : (string, int) Hashtbl.t;   (* proc name -> pname index *)
  mutable ntmp : int;                  (* fresh names for by-value temps *)
}

let create () =
  { globals = Hashtbl.create 64; nglob = 0; procmap = Hashtbl.create 16; ntmp = 0 }

let new_scope is_main =
  { is_main; formals = Hashtbl.create 8; locals = Hashtbl.create 8; nloc = 0 }

let gslot st nm = match Hashtbl.find_opt st.globals nm with
  | Some i -> i
  | None -> let i = st.nglob in Hashtbl.add st.globals nm i; st.nglob <- i + 1; i

let local_slot scp nm = match Hashtbl.find_opt scp.locals nm with
  | Some x -> x
  | None -> let x = scp.nloc in Hashtbl.add scp.locals nm x; scp.nloc <- x + 1; x

let add_formals scp (params : param list) =
  List.iteri (fun i (p : param) ->
    if p.pis_stack then raise (Unsupported "stack parameter");
    if p.pis_array then raise (Unsupported "array parameter");
    Hashtbl.replace scp.formals p.pname i) params

(* classify a scalar/array variable name into a frame [ref] at this scope *)
let ref_of st scp nm : J.ref =
  match Hashtbl.find_opt scp.formals nm with
  | Some i -> J.RF (nat i)
  | None ->
    match Hashtbl.find_opt scp.locals nm with
    | Some x -> J.RL (nat x)
    | None ->
      if scp.is_main then J.RG (nat (gslot st nm))
      else raise (Unsupported ("free variable " ^ nm ^ " in procedure"))

(* ----- expressions ----- *)

let rec reads_name (e : Ast.expr) nm = match e with
  | Lv { lname; sels = [] } -> lname = nm
  | Lv { sels; _ } -> List.exists (fun x -> reads_name x nm) sels
  | Bin (_, a, b) -> reads_name a nm || reads_name b nm
  | Not a -> reads_name a nm
  | _ -> false

let rec expr st scp (e : Ast.expr) : J.expr =
  match e with
  | Num n -> J.Cst (z n)
  | Not e -> J.Bin (J.BEq, expr st scp e, J.Cst (z 0))
  | Lv { lname; sels = [] } -> J.Rd (ref_of st scp lname)
  | Lv { sels = _ :: _; _ } -> raise (Unsupported "array read")
  | Top _ | Empty _ | Size _ -> raise (Unsupported "stack expression")
  | Bin (op, a, b) ->
    let l = expr st scp a and r = expr st scp b in
    (match op with
     | "+" -> J.Bin (J.BAdd, l, r) | "-" -> J.Bin (J.BSub, l, r) | "*" -> J.Bin (J.BMul, l, r)
     | "/" -> J.Bin (J.BDiv, l, r) | "%" -> J.Bin (J.BMod, l, r)
     | "==" -> J.Bin (J.BEq, l, r) | "<" -> J.Bin (J.BLt, l, r) | ">" -> J.Bin (J.BLt, r, l)
     | ">=" -> J.Bin (J.BSub, J.Cst (z 1), J.Bin (J.BLt, l, r))
     | "<=" -> J.Bin (J.BSub, J.Cst (z 1), J.Bin (J.BLt, r, l))
     | "!=" -> J.Bin (J.BSub, J.Cst (z 1), J.Bin (J.BEq, l, r))
     | "&&" -> J.Bin (J.BMul, l, r)
     | "||" -> J.Bin (J.BAdd, J.Bin (J.BMul, l, l), J.Bin (J.BMul, r, r))
     | o -> raise (Unsupported ("operator " ^ o)))

let aop = function "+=" -> J.OAdd | "-=" -> J.OSub | "^=" -> J.OXor
  | o -> raise (Unsupported ("assign-op " ^ o))

let target_ref st scp (lv : Ast.lval) : J.ref =
  match lv.sels with [] -> ref_of st scp lv.lname | _ -> raise (Unsupported "array assignment")

(* ----- statements ----- *)

let rec stmt st scp (s : Ast.stmt) : J.stmt =
  match s with
  | Skip -> J.Skip
  | Assign (lv, op, e) -> J.Asn (target_ref st scp lv, aop op, expr st scp e)
  | Swap (a, b) ->
    (* no Swap primitive in the frame core: a^=b; b^=a; a^=b (each reversible) *)
    let ra = target_ref st scp a and rb = target_ref st scp b in
    J.Seq (J.Asn (ra, J.OXor, J.Rd rb),
           J.Seq (J.Asn (rb, J.OXor, J.Rd ra), J.Asn (ra, J.OXor, J.Rd rb)))
  | If (e1, t1, t2, e2) -> J.If (expr st scp e1, seq st scp t1, seq st scp t2, expr st scp e2)
  | From (e1, d, l, e2) -> J.Loop (expr st scp e1, seq st scp d, seq st scp l, expr st scp e2)
  | Iterate (v, start, step, endd, exclusive, body) ->
    let x = local_slot scp v in
    let es = expr st scp start and ep = expr st scp step in
    let stop = if exclusive then expr st scp endd else J.Bin (J.BAdd, expr st scp endd, ep) in
    let xref = J.RL (nat x) in
    let istart = J.Bin (J.BEq, J.Rd xref, es) in
    let istop = J.Bin (J.BEq, J.Rd xref, stop) in
    let incr = J.Asn (xref, J.OAdd, ep) in
    J.Seq (J.Enter (nat x, es),
           J.Seq (J.Loop (istart, J.Skip, J.Seq (seq st scp body, incr), istop), J.Exit (nat x, stop)))
  | Local (d1, body, d2) ->
    if d1.dis_stack then raise (Unsupported "local stack");
    let e0 = match d1.dinit with Some e -> e | None -> Num 0 in
    let e1 = match d2.dinit with Some e -> e | None -> Num 0 in
    if reads_name e0 d1.dname || reads_name e1 d1.dname then
      raise (Unsupported "self-referential local/delocal");
    let x = local_slot scp d1.dname in
    J.Seq (J.Enter (nat x, expr st scp e0),
           J.Seq (seq st scp body, J.Exit (nat x, expr st scp e1)))
  | Push _ | Pop _ -> raise (Unsupported "stack operation")
  | Call (n, args) -> call st scp true n args
  | Uncall (n, args) -> call st scp false n args

and call st scp forward n args =
  let idx = match Hashtbl.find_opt st.procmap n with
    | Some i -> i | None -> raise (Unsupported ("unknown procedure " ^ n)) in
  let refs = ref [] and valwraps = ref [] in
  List.iter (fun a -> match a with
    | ALv { lname; sels = [] } -> refs := ref_of st scp lname :: !refs
    | ALv _ -> raise (Unsupported "array-cell argument")
    | AVal e ->
      st.ntmp <- st.ntmp + 1;
      let x = local_slot scp (Printf.sprintf "__v%d" st.ntmp) in
      valwraps := (x, expr st scp e) :: !valwraps;
      refs := J.RL (nat x) :: !refs) args;
  let refs = List.rev !refs in
  let base =
    if forward then J.Call (nat idx, Glue_frame.ref_list refs)
    else J.Uncall (nat idx, Glue_frame.ref_list refs) in
  (* by-value args: wrap the call in [Enter t = e … Exit t = e] on a fresh local *)
  List.fold_left (fun acc (x, e) -> J.Seq (J.Enter (nat x, e), J.Seq (acc, J.Exit (nat x, e))))
    base !valwraps

and seq st scp (ss : Ast.stmt list) : J.stmt =
  match List.rev_map (stmt st scp) ss with
  | [] -> J.Skip
  | last :: rest -> List.fold_left (fun acc x -> J.Seq (x, acc)) last rest

(* ----- program ----- *)

type layout = {
  scalars : (string * int) list;
  arrays : (string * int * int list) list;
  stks : (string * int * int) list;
}

let program (p : Ast.program) : J.stmt array * J.stmt * layout =
  let st = create () in
  List.iteri (fun i pr -> Hashtbl.replace st.procmap pr.procname i) p.procs;
  (* lower every procedure body in its own scope (formals positional, fresh locals) *)
  let procs = List.map (fun pr ->
    let scp = new_scope false in
    add_formals scp pr.params;
    seq st scp pr.body) p.procs in
  (* main: declared variables are globals; reject arrays/stacks for now *)
  let mscp = new_scope true in
  let scalars = ref [] and inits = ref [] in
  List.iter (fun (vd : Ast.vdecl) ->
    if vd.vis_stack then raise (Unsupported "stack variable");
    if vd.vdims <> [] then raise (Unsupported "array variable");
    let g = gslot st vd.vname in
    scalars := (vd.vname, g) :: !scalars;
    match vd.vinit with
    | None -> ()
    | Some (VE e) -> inits := J.Asn (J.RG (nat g), J.OAdd, expr st mscp e) :: !inits
    | Some (VA _) -> raise (Unsupported "aggregate initializer on scalar")) p.mvdecls;
  let body = seq st mscp p.mstmts in
  let main = List.fold_left (fun acc s0 -> J.Seq (s0, acc)) body !inits in
  (Array.of_list procs, main,
   { scalars = List.rev !scalars; arrays = []; stks = [] })
