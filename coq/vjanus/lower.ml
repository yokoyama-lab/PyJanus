(* lower.ml — translate the jana2014 Ast into the verified core's [stmt]/[expr]
   (Janus_arr), assigning a global slot to each (scope, variable).  This is an
   OCaml port of coq/harness/differentialar.py: stacks become (array, top-counter)
   pairs; local/delocal become Enter/Exit; call arguments are passed by reference
   (bare l-value), by swap-into-temp (array cell) or by local-wrap (value); and
   multi-dim indices fold to one via an injective Cantor pairing. *)

module J = Janus_arr
open Ast

exception Unsupported of string

let nat = Glue.nat_of_int
let z = Glue.z_of_int

type t = {
  idx : (string * string, int) Hashtbl.t;
  mutable nidx : int;
  procmap : (string, int) Hashtbl.t;
  pforms : (string, string list) Hashtbl.t;   (* proc -> formal names (stacks excluded-expanded) *)
  stacks : (string * string, unit) Hashtbl.t;
  arrlen : (string * string, int) Hashtbl.t;
  mutable tmpn : int;
}

let create () =
  { idx = Hashtbl.create 64; nidx = 0; procmap = Hashtbl.create 16;
    pforms = Hashtbl.create 16; stacks = Hashtbl.create 16;
    arrlen = Hashtbl.create 16; tmpn = 0 }

let gid st sc nm =
  match Hashtbl.find_opt st.idx (sc, nm) with
  | Some i -> i
  | None -> let i = st.nidx in Hashtbl.add st.idx (sc, nm) i; st.nidx <- i + 1; i

let mark_stack st sc nm = Hashtbl.replace st.stacks (sc, nm) ()
let is_stack st sc nm = Hashtbl.mem st.stacks (sc, nm)
(* a stack is two slots: the backing array and the top counter *)
let stack_ids st sc nm = mark_stack st sc nm; (gid st sc (nm ^ "#arr"), gid st sc (nm ^ "#top"))
let fresh st sc = st.tmpn <- st.tmpn + 1; gid st sc (Printf.sprintf "__t%d" st.tmpn)

(* ----- expressions ----- *)

let rec reads_name (e : Ast.expr) nm = match e with
  | Lv { lname; sels = [] } -> lname = nm
  | Lv { sels; _ } -> List.exists (fun x -> reads_name x nm) sels
  | Bin (_, a, b) -> reads_name a nm || reads_name b nm
  | Not a -> reads_name a nm
  | _ -> false

let rec expr st sc (e : Ast.expr) : J.expr =
  match e with
  | Num n -> J.Cst (z n)
  | Not e -> J.Bin (J.OEq, expr st sc e, J.Cst (z 0))
  | Top nm -> let arr, top = stack_ids st sc nm in J.ARd (nat arr, J.Bin (J.OSub, J.Var (nat top), J.Cst (z 1)))
  | Empty nm -> let _, top = stack_ids st sc nm in J.Bin (J.OEq, J.Var (nat top), J.Cst (z 0))
  | Size nm ->
    if is_stack st sc nm then let _, top = stack_ids st sc nm in J.Var (nat top)
    else (match Hashtbl.find_opt st.arrlen (sc, nm) with
          | Some l -> J.Cst (z l) | None -> raise (Unsupported ("size() of unknown-length array " ^ nm)))
  | Lv { lname; sels = [] } -> J.Var (nat (gid st sc lname))
  | Lv { lname; sels } -> J.ARd (nat (gid st sc lname), index st sc sels)
  | Bin (op, a, b) ->
    let l = expr st sc a and r = expr st sc b in
    (match op with
     | "+" -> J.Bin (J.OAdd, l, r) | "-" -> J.Bin (J.OSub, l, r) | "*" -> J.Bin (J.OMul, l, r)
     | "/" -> J.Bin (J.ODiv, l, r) | "%" -> J.Bin (J.OMod, l, r)
     | "==" -> J.Bin (J.OEq, l, r) | "<" -> J.Bin (J.OLt, l, r) | ">" -> J.Bin (J.OLt, r, l)
     | ">=" -> J.Bin (J.OSub, J.Cst (z 1), J.Bin (J.OLt, l, r))
     | "<=" -> J.Bin (J.OSub, J.Cst (z 1), J.Bin (J.OLt, r, l))
     | "!=" -> J.Bin (J.OSub, J.Cst (z 1), J.Bin (J.OEq, l, r))
     | "&&" -> J.Bin (J.OMul, l, r)
     | "||" -> J.Bin (J.OAdd, J.Bin (J.OMul, l, l), J.Bin (J.OMul, r, r))
     | o -> raise (Unsupported ("operator " ^ o)))

and index st sc sels =
  match List.map (expr st sc) sels with
  | [] -> J.Cst (z 0)
  | x :: rest ->
    List.fold_left (fun acc j ->
      let sm = J.Bin (J.OAdd, acc, j) in
      J.Bin (J.OAdd,
             J.Bin (J.ODiv, J.Bin (J.OMul, sm, J.Bin (J.OAdd, sm, J.Cst (z 1))), J.Cst (z 2)), j))
      x rest

(* exact integer Cantor fold, for static (initializer) indices *)
let cantor_val = function
  | [] -> 0
  | x :: rest -> List.fold_left (fun acc j -> (acc + j) * (acc + j + 1) / 2 + j) x rest

let target st sc (lv : Ast.lval) : J.lv =
  match lv.sels with
  | [] -> J.LVs (nat (gid st sc lv.lname))
  | sels -> J.LVa (nat (gid st sc lv.lname), index st sc sels)

let aop = function "+=" -> J.AAdd | "-=" -> J.ASub | "^=" -> J.AXor
  | o -> raise (Unsupported ("assign-op " ^ o))

(* ----- statements ----- *)

let rec stmt st sc (s : Ast.stmt) : J.stmt =
  match s with
  | Skip -> J.Skip
  | Assign (lv, op, e) -> J.Assign (target st sc lv, aop op, expr st sc e)
  | Swap (a, b) -> J.Swap (target st sc a, target st sc b)
  | If (e1, t1, t2, e2) -> J.If (expr st sc e1, seq st sc t1, seq st sc t2, expr st sc e2)
  | From (e1, d, l, e2) -> J.Loop (expr st sc e1, seq st sc d, seq st sc l, expr st sc e2)
  | Iterate (v, start, step, endd, exclusive, body) ->
    let i = gid st sc v in
    let es = expr st sc start and ep = expr st sc step in
    let stop = if exclusive then expr st sc endd else J.Bin (J.OAdd, expr st sc endd, ep) in
    let istart = J.Bin (J.OEq, J.Var (nat i), es) in
    let istop = J.Bin (J.OEq, J.Var (nat i), stop) in
    let incr = J.Assign (J.LVs (nat i), J.AAdd, ep) in
    J.Seq (J.Enter (nat i, es),
           J.Seq (J.Loop (istart, J.Skip, J.Seq (seq st sc body, incr), istop), J.Exit (nat i, stop)))
  | Local (d1, body, d2) ->
    if d1.dis_stack then
      let _, top = stack_ids st sc d1.dname in
      J.Seq (J.Enter (nat top, J.Cst (z 0)), J.Seq (seq st sc body, J.Exit (nat top, J.Cst (z 0))))
    else begin
      let e0 = match d1.dinit with Some e -> e | None -> Num 0 in
      let e1 = match d2.dinit with Some e -> e | None -> Num 0 in
      if reads_name e0 d1.dname || reads_name e1 d1.dname then
        raise (Unsupported "self-referential local/delocal");
      let x = gid st sc d1.dname in
      J.Seq (J.Enter (nat x, expr st sc e0),
             J.Seq (seq st sc body, J.Exit (nat x, expr st sc e1)))
    end
  | Push (x, s) ->
    let arr, top = stack_ids st sc s in
    let sw = J.Swap (J.LVa (nat arr, J.Var (nat top)), target st sc x) in
    J.Seq (sw, J.Assign (J.LVs (nat top), J.AAdd, J.Cst (z 1)))
  | Pop (x, s) ->
    let arr, top = stack_ids st sc s in
    let sw = J.Swap (J.LVa (nat arr, J.Var (nat top)), target st sc x) in
    J.Seq (J.Assign (J.LVs (nat top), J.ASub, J.Cst (z 1)), sw)
  | Call (n, args) -> call st sc true n args
  | Uncall (n, args) -> call st sc false n args

and call st sc forward n args =
  let idx = match Hashtbl.find_opt st.procmap n with
    | Some i -> i | None -> raise (Unsupported ("unknown procedure " ^ n)) in
  let actuals = ref [] and swaps = ref [] and valwraps = ref [] in
  List.iter (fun a -> match a with
    | ALv { lname; sels = [] } when is_stack st sc lname ->
      let arr, top = stack_ids st sc lname in actuals := top :: arr :: !actuals
    | ALv { lname; sels = [] } -> actuals := gid st sc lname :: !actuals
    | ALv lv -> let t = fresh st sc in swaps := (target st sc lv, t) :: !swaps; actuals := t :: !actuals
    | AVal e -> let t = fresh st sc in valwraps := (t, expr st sc e) :: !valwraps; actuals := t :: !actuals)
    args;
  let actuals = List.rev !actuals in
  let base = if forward then J.Call (nat idx, Glue.var_list actuals)
             else J.Uncall (nat idx, Glue.var_list actuals) in
  (* value args: wrap call in Enter t=e … Exit t=e  *)
  let base = List.fold_left (fun acc (t, e) -> J.Seq (J.Enter (nat t, e), J.Seq (acc, J.Exit (nat t, e)))) base !valwraps in
  (* array-cell args: wrap in swap cell <-> temp  *)
  List.fold_left (fun acc (cell, t) -> J.Seq (J.Swap (cell, J.LVs (nat t)), J.Seq (acc, J.Swap (cell, J.LVs (nat t))))) base !swaps

and seq st sc (ss : Ast.stmt list) : J.stmt =
  match List.rev_map (stmt st sc) ss with
  | [] -> J.Skip
  | last :: rest -> List.fold_left (fun acc x -> J.Seq (x, acc)) last rest

(* ----- size() propagation: main array decls -> proc formals via call sites ----- *)

let rec collect_calls sc (ss : Ast.stmt list) acc =
  List.fold_left (fun acc s -> match s with
    | Call (n, a) | Uncall (n, a) -> (sc, n, a) :: acc
    | If (_, t1, t2, _) -> collect_calls sc t1 (collect_calls sc t2 acc)
    | From (_, d, l, _) -> collect_calls sc d (collect_calls sc l acc)
    | Iterate (_, _, _, _, _, b) -> collect_calls sc b acc
    | Local (_, b, _) -> collect_calls sc b acc
    | _ -> acc) acc ss

let resolve_arrlen st (p : Ast.program) =
  List.iter (fun (vd : Ast.vdecl) ->
    if not vd.vis_stack && vd.vdims <> [] then
      Hashtbl.replace st.arrlen ("main", vd.vname) (List.fold_left ( * ) 1 vd.vdims)) p.mvdecls;
  let calls = collect_calls "main" p.mstmts
                (List.fold_left (fun acc pr -> collect_calls pr.procname pr.body acc) [] p.procs) in
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter (fun (sc, callee, args) ->
      match Hashtbl.find_opt st.pforms callee with
      | None -> ()
      | Some formals ->
        List.iteri (fun i a -> match a with
          | ALv { lname; sels = [] } when i < List.length formals ->
            (match Hashtbl.find_opt st.arrlen (sc, lname) with
             | Some l when not (Hashtbl.mem st.arrlen (callee, List.nth formals i)) ->
               Hashtbl.replace st.arrlen (callee, List.nth formals i) l; changed := true
             | _ -> ())
          | _ -> ()) args) calls
  done

(* ----- program ----- *)

type layout = {
  scalars : (string * int) list;
  arrays : (string * int * int list) list;
  stks : (string * int * int) list;          (* name, arr slot, top slot *)
}

(* The flat-slot model has no activation record, so a self-recursive procedure
   that declares a `local` would reuse the same slots across frames.  Detect and
   reject (the verified core does not yet model frame-stacked locals — Phase 2). *)
let rec body_has_local ss = List.exists (function
  | Local _ -> true
  | If (_, a, b, _) | From (_, a, b, _) -> body_has_local a || body_has_local b
  | Iterate (_, _, _, _, _, b) -> body_has_local b
  | Local (_, b, _) -> body_has_local b
  | _ -> false) ss
let rec body_calls name ss = List.exists (function
  | Call (n, _) | Uncall (n, _) -> n = name
  | If (_, a, b, _) | From (_, a, b, _) -> body_calls name a || body_calls name b
  | Iterate (_, _, _, _, _, b) -> body_calls name b
  | Local (_, b, _) -> body_calls name b
  | _ -> false) ss

let program (p : Ast.program) : (int list * J.stmt) array * J.stmt * layout =
  let st = create () in
  List.iter (fun pr ->
    if body_calls pr.procname pr.body && body_has_local pr.body then
      raise (Unsupported "self-recursion with local variables (no frame stack)")) p.procs;
  List.iteri (fun i pr -> Hashtbl.replace st.procmap pr.procname i) p.procs;
  List.iter (fun pr -> Hashtbl.replace st.pforms pr.procname
                (List.map (fun (par : Ast.param) -> par.pname) pr.params)) p.procs;
  resolve_arrlen st p;
  let procs = List.map (fun pr ->
    let formals = List.concat_map (fun (par : Ast.param) ->
      if par.pis_stack then let arr, top = stack_ids st pr.procname par.pname in [arr; top]
      else [gid st pr.procname par.pname]) pr.params in
    (formals, seq st pr.procname pr.body)) p.procs in
  let inits = ref [] and scalars = ref [] and arrays = ref [] and stks = ref [] in
  let rec emit_init g item prefix = match item with
    | VA items -> List.iteri (fun k sub -> emit_init g sub (prefix @ [k])) items
    | VE e -> inits := J.Assign (J.LVa (nat g, J.Cst (z (cantor_val prefix))), J.AAdd, expr st "main" e) :: !inits in
  List.iter (fun (vd : Ast.vdecl) ->
    if vd.vis_stack then begin
      let arr, top = stack_ids st "main" vd.vname in
      stks := (vd.vname, arr, top) :: !stks;
      (match vd.vinit with
       | Some (VA items) ->
         List.iteri (fun k it -> match it with
           | VE e -> inits := J.Assign (J.LVa (nat arr, J.Cst (z k)), J.AAdd, expr st "main" e) :: !inits
           | VA _ -> raise (Unsupported "nested stack initializer")) items;
         inits := J.Assign (J.LVs (nat top), J.AAdd, J.Cst (z (List.length items))) :: !inits
       | Some (VE _) -> raise (Unsupported "scalar stack initializer")
       | None -> ())
    end else begin
      let g = gid st "main" vd.vname in
      if vd.vdims <> [] then begin
        arrays := (vd.vname, g, vd.vdims) :: !arrays;
        (match vd.vinit with Some (VA _ as it) -> emit_init g it [] | Some (VE _) -> raise (Unsupported "array = scalar") | None -> ())
      end else begin
        scalars := (vd.vname, g) :: !scalars;
        (match vd.vinit with
         | None -> () | Some (VE e) -> inits := J.Assign (J.LVs (nat g), J.AAdd, expr st "main" e) :: !inits
         | Some (VA _) -> raise (Unsupported "aggregate initializer on scalar"))
      end
    end) p.mvdecls;
  let body = seq st "main" p.mstmts in
  let main = List.fold_left (fun acc s0 -> J.Seq (s0, acc)) body !inits in
  (Array.of_list procs, main,
   { scalars = List.rev !scalars; arrays = List.rev !arrays; stks = List.rev !stks })
