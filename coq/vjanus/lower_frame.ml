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
  formals : (string, int) Hashtbl.t;        (* formal name -> positional index (RF i) *)
  fstacks : (string, int * int) Hashtbl.t;  (* stack formal -> (arr index, top index) *)
  locals  : (string, int) Hashtbl.t;        (* local  name -> local slot     (RL x)  *)
  lstacks : (string, int * int) Hashtbl.t;  (* stack local  -> (arr slot, top slot)   *)
  mutable nloc : int;
}

type t = {
  globals : (string, int) Hashtbl.t;        (* main var name -> global slot (RG n) *)
  gstacks : (string, int * int) Hashtbl.t;  (* main stack    -> (arr slot, top slot) *)
  mutable nglob : int;
  procmap : (string, int) Hashtbl.t;        (* proc name -> pname index *)
  mutable ntmp : int;                       (* fresh names for by-value temps *)
}

let create () =
  { globals = Hashtbl.create 64; gstacks = Hashtbl.create 16; nglob = 0;
    procmap = Hashtbl.create 16; ntmp = 0 }

let new_scope is_main =
  { is_main; formals = Hashtbl.create 8; fstacks = Hashtbl.create 8;
    locals = Hashtbl.create 8; lstacks = Hashtbl.create 8; nloc = 0 }

let gslot st nm = match Hashtbl.find_opt st.globals nm with
  | Some i -> i
  | None -> let i = st.nglob in Hashtbl.add st.globals nm i; st.nglob <- i + 1; i

(* a stack needs two slots: the backing array and the top counter *)
let global_stack st nm = match Hashtbl.find_opt st.gstacks nm with
  | Some p -> p
  | None -> let a = st.nglob and t = st.nglob + 1 in st.nglob <- st.nglob + 2;
            Hashtbl.add st.gstacks nm (a, t); (a, t)

let local_slot scp nm = match Hashtbl.find_opt scp.locals nm with
  | Some x -> x
  | None -> let x = scp.nloc in Hashtbl.add scp.locals nm x; scp.nloc <- x + 1; x

let local_stack scp nm = match Hashtbl.find_opt scp.lstacks nm with
  | Some p -> p
  | None -> let a = scp.nloc and t = scp.nloc + 1 in scp.nloc <- scp.nloc + 2;
            Hashtbl.add scp.lstacks nm (a, t); (a, t)

let add_formals scp (params : param list) =
  let i = ref 0 in
  List.iter (fun (p : param) ->
    if p.pis_stack then begin
      (* a stack formal occupies two consecutive positions: arr, then top *)
      Hashtbl.replace scp.fstacks p.pname (!i, !i + 1); i := !i + 2
    end else begin
      (* a scalar/array formal is one positional ref (RF i); ARd/AAsn index it *)
      Hashtbl.replace scp.formals p.pname !i; incr i
    end) params

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

let is_stack st scp nm =
  Hashtbl.mem scp.fstacks nm || Hashtbl.mem scp.lstacks nm
  || (scp.is_main && Hashtbl.mem st.gstacks nm)

(* the (arr, top) ref pair denoting a stack at this scope *)
let stack_refs st scp nm : J.ref * J.ref =
  match Hashtbl.find_opt scp.fstacks nm with
  | Some (a, t) -> (J.RF (nat a), J.RF (nat t))
  | None ->
    match Hashtbl.find_opt scp.lstacks nm with
    | Some (a, t) -> (J.RL (nat a), J.RL (nat t))
    | None ->
      if scp.is_main then let (a, t) = global_stack st nm in (J.RG (nat a), J.RG (nat t))
      else raise (Unsupported ("free stack " ^ nm ^ " in procedure"))

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
  | Lv { lname; sels } -> J.ARd (ref_of st scp lname, index st scp sels)
  | Top nm -> let (a, t) = stack_refs st scp nm in
              J.ARd (a, J.Bin (J.BSub, J.Rd t, J.Cst (z 1)))   (* arr[top-1] *)
  | Empty nm -> let (_, t) = stack_refs st scp nm in J.Bin (J.BEq, J.Rd t, J.Cst (z 0))
  | Size nm -> if is_stack st scp nm then let (_, t) = stack_refs st scp nm in J.Rd t
               else raise (Unsupported "size() of array (no length tracking)")
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

(* multi-dim indices fold to one via an injective Cantor pairing (as lower.ml) *)
and index st scp sels =
  match List.map (expr st scp) sels with
  | [] -> J.Cst (z 0)
  | x :: rest ->
    List.fold_left (fun acc j ->
      let sm = J.Bin (J.BAdd, acc, j) in
      J.Bin (J.BAdd,
             J.Bin (J.BDiv, J.Bin (J.BMul, sm, J.Bin (J.BAdd, sm, J.Cst (z 1))), J.Cst (z 2)), j))
      x rest

(* exact integer Cantor fold, for static (initializer) indices *)
let cantor_val = function
  | [] -> 0
  | x :: rest -> List.fold_left (fun acc j -> (acc + j) * (acc + j + 1) / 2 + j) x rest

let aop = function "+=" -> J.OAdd | "-=" -> J.OSub | "^=" -> J.OXor
  | o -> raise (Unsupported ("assign-op " ^ o))

(* emit `lv op= rhs` as a scalar Asn or an array-cell AAsn *)
let assign_lv st scp (lv : Ast.lval) (o : J.aop) (rhs : J.expr) : J.stmt =
  match lv.sels with
  | [] -> J.Asn (ref_of st scp lv.lname, o, rhs)
  | sels -> J.AAsn (ref_of st scp lv.lname, index st scp sels, o, rhs)

let lv_read st scp (lv : Ast.lval) : J.expr = expr st scp (Lv lv)

(* ----- statements ----- *)

let rec stmt st scp (s : Ast.stmt) : J.stmt =
  match s with
  | Skip -> J.Skip
  | Assign (lv, op, e) -> assign_lv st scp lv (aop op) (expr st scp e)
  | Swap (a, b) ->
    (* no Swap primitive in the frame core: a^=b; b^=a; a^=b (each reversible),
       working for scalars and array cells alike *)
    J.Seq (assign_lv st scp a J.OXor (lv_read st scp b),
           J.Seq (assign_lv st scp b J.OXor (lv_read st scp a),
                  assign_lv st scp a J.OXor (lv_read st scp b)))
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
  | Local (d1, body, d2) when d1.dis_stack ->
    (* local stack: only the top counter is a scalar local to Enter/Exit; the
       backing array cells live in the same depth-d frame and are clean (0) on
       entry and exit (the stack is emptied before delocal) *)
    let (_, t) = local_stack scp d1.dname in
    J.Seq (J.Enter (nat t, J.Cst (z 0)), J.Seq (seq st scp body, J.Exit (nat t, J.Cst (z 0))))
  | Local (d1, body, d2) ->
    let e0 = match d1.dinit with Some e -> e | None -> Num 0 in
    let e1 = match d2.dinit with Some e -> e | None -> Num 0 in
    if reads_name e0 d1.dname || reads_name e1 d1.dname then
      raise (Unsupported "self-referential local/delocal");
    let x = local_slot scp d1.dname in
    J.Seq (J.Enter (nat x, expr st scp e0),
           J.Seq (seq st scp body, J.Exit (nat x, expr st scp e1)))
  | Push (x, s) ->
    (* arr[top] <-> x (XOR swap), then top += 1 *)
    let (a, t) = stack_refs st scp s in
    let cell = J.ARd (a, J.Rd t) and xr = lv_read st scp x in
    let swp = J.Seq (J.AAsn (a, J.Rd t, J.OXor, xr),
                     J.Seq (assign_lv st scp x J.OXor cell, J.AAsn (a, J.Rd t, J.OXor, xr))) in
    J.Seq (swp, J.Asn (t, J.OAdd, J.Cst (z 1)))
  | Pop (x, s) ->
    (* top -= 1, then arr[top] <-> x (XOR swap) — the inverse of push *)
    let (a, t) = stack_refs st scp s in
    let cell = J.ARd (a, J.Rd t) and xr = lv_read st scp x in
    let swp = J.Seq (J.AAsn (a, J.Rd t, J.OXor, xr),
                     J.Seq (assign_lv st scp x J.OXor cell, J.AAsn (a, J.Rd t, J.OXor, xr))) in
    J.Seq (J.Asn (t, J.OSub, J.Cst (z 1)), swp)
  | Call (n, args) -> call st scp true n args
  | Uncall (n, args) -> call st scp false n args

and call st scp forward n args =
  let idx = match Hashtbl.find_opt st.procmap n with
    | Some i -> i | None -> raise (Unsupported ("unknown procedure " ^ n)) in
  let refs = ref [] and valwraps = ref [] and cellswaps = ref [] in
  List.iter (fun a -> match a with
    | ALv { lname; sels = [] } when is_stack st scp lname ->
      (* a stack actual expands to its two refs, arr then top *)
      let (ar, tr) = stack_refs st scp lname in refs := tr :: ar :: !refs
    | ALv { lname; sels = [] } -> refs := ref_of st scp lname :: !refs
    | ALv lv ->
      (* an array-cell actual A[i]: swap it into a fresh local temp, pass the
         temp by reference, swap back after the call (the core has no by-cell
         reference, and no Swap — the exchange is an XOR triple) *)
      st.ntmp <- st.ntmp + 1;
      let x = local_slot scp (Printf.sprintf "__c%d" st.ntmp) in
      cellswaps := (lv, x) :: !cellswaps;
      refs := J.RL (nat x) :: !refs
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
  let base = List.fold_left
    (fun acc (x, e) -> J.Seq (J.Enter (nat x, e), J.Seq (acc, J.Exit (nat x, e))))
    base !valwraps in
  (* array-cell args: wrap the call in [A[i] <-> t … A[i] <-> t] (XOR swap) *)
  let xor_swap lv x =
    let tref = J.RL (nat x) in
    J.Seq (assign_lv st scp lv J.OXor (J.Rd tref),
           J.Seq (J.Asn (tref, J.OXor, lv_read st scp lv),
                  assign_lv st scp lv J.OXor (J.Rd tref))) in
  List.fold_left (fun acc (lv, x) -> J.Seq (xor_swap lv x, J.Seq (acc, xor_swap lv x)))
    base !cellswaps

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
  let scalars = ref [] and arrays = ref [] and stks = ref [] and inits = ref [] in
  (* array initializer: walk the nested aggregate, writing each leaf into the
     Cantor-folded flat cell *)
  let rec emit_init g item prefix = match item with
    | VA items -> List.iteri (fun k sub -> emit_init g sub (prefix @ [k])) items
    | VE e -> inits := J.AAsn (J.RG (nat g), J.Cst (z (cantor_val prefix)), J.OAdd, expr st mscp e) :: !inits in
  List.iter (fun (vd : Ast.vdecl) ->
    if vd.vis_stack then begin
      let (a, t) = global_stack st vd.vname in
      stks := (vd.vname, a, t) :: !stks;
      match vd.vinit with
      | None -> ()                              (* `stack s` / `= nil` -> empty *)
      | Some (VA items) ->                       (* `= {bottom, …, top}` *)
        List.iteri (fun k it -> match it with
          | VE e -> inits := J.AAsn (J.RG (nat a), J.Cst (z k), J.OAdd, expr st mscp e) :: !inits
          | VA _ -> raise (Unsupported "nested stack initializer")) items;
        inits := J.Asn (J.RG (nat t), J.OAdd, J.Cst (z (List.length items))) :: !inits
      | Some (VE _) -> raise (Unsupported "scalar stack initializer")
    end else begin
      let g = gslot st vd.vname in
      if vd.vdims <> [] then begin
        arrays := (vd.vname, g, vd.vdims) :: !arrays;
        match vd.vinit with
        | Some (VA _ as it) -> emit_init g it []
        | Some (VE _) -> raise (Unsupported "array = scalar initializer")
        | None -> ()
      end else begin
        scalars := (vd.vname, g) :: !scalars;
        match vd.vinit with
        | None -> ()
        | Some (VE e) -> inits := J.Asn (J.RG (nat g), J.OAdd, expr st mscp e) :: !inits
        | Some (VA _) -> raise (Unsupported "aggregate initializer on scalar")
      end
    end) p.mvdecls;
  let body = seq st mscp p.mstmts in
  let main = List.fold_left (fun acc s0 -> J.Seq (s0, acc)) body !inits in
  (Array.of_list procs, main,
   { scalars = List.rev !scalars; arrays = List.rev !arrays; stks = List.rev !stks })
