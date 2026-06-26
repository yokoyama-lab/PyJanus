(* lower.ml — translate the jana2014 Ast into the verified *frame* core's
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

let nat = Glue.nat_of_int
let z = Glue.z_of_int

(* one name-binding environment: a procedure's formals (positional) and the
   locals introduced within it; [is_main] scopes see globals instead of formals *)
type scope = {
  name    : string;                         (* "main" or the procedure's name *)
  is_main : bool;
  formals : (string, int) Hashtbl.t;        (* formal name -> positional index (RF i) *)
  fstacks : (string, int * int) Hashtbl.t;  (* stack formal -> (arr index, top index) *)
  fstructs: (string, string * int) Hashtbl.t;(* struct formal, no array fields -> (struct name, base RF index) *)
  fstructs_flat: (string, string * int) Hashtbl.t;(* struct formal WITH array fields -> (sname, single RF index) *)
  fsarrays: (string, string * int) Hashtbl.t;(* struct-array formal -> (struct name, RF index of base) *)
  locals  : (string, int) Hashtbl.t;        (* local  name -> local slot     (RL x)  *)
  lstacks : (string, int * int) Hashtbl.t;  (* stack local  -> (arr slot, top slot)   *)
  lstructs: (string, string * int) Hashtbl.t;(* struct local -> (struct name, base local slot) *)
  lstructs_flat: (string, string * int) Hashtbl.t;(* struct local with array fields -> (sname, base RL slot) *)
  mutable nloc : int;
}

type t = {
  globals : (string, int) Hashtbl.t;        (* main var name -> global slot (RG n) *)
  gstacks : (string, int * int) Hashtbl.t;  (* main stack    -> (arr slot, top slot) *)
  mutable nglob : int;
  procmap : (string, int) Hashtbl.t;        (* proc name -> pname index *)
  pforms  : (string, string list) Hashtbl.t;(* proc name -> formal names, in order *)
  arrlen  : (string * string, int) Hashtbl.t;(* (scope, array name) -> flat length, for size() *)
  slayout : (string, (string * int * int list) list * int) Hashtbl.t;
                                            (* struct name -> (field, offset, dims) list, total slot count *)
  gstructs: (string, string * int) Hashtbl.t;(* main scalar struct (no array fields) -> (sname, base G slot) *)
  gstructs_flat: (string, string * int) Hashtbl.t;
                                            (* main scalar struct WITH array fields -> (sname, base array slot) *)
  gsarrays: (string, string * int * int) Hashtbl.t;
                                            (* main struct array -> (struct name, base array slot, slot count/elem) *)
  mutable ntmp : int;                       (* fresh names for by-value temps *)
}

let create () =
  { globals = Hashtbl.create 64; gstacks = Hashtbl.create 16; nglob = 0;
    procmap = Hashtbl.create 16; pforms = Hashtbl.create 16;
    arrlen = Hashtbl.create 16; slayout = Hashtbl.create 16;
    gstructs = Hashtbl.create 16; gstructs_flat = Hashtbl.create 16;
    gsarrays = Hashtbl.create 16; ntmp = 0 }

let struct_layout st sname =
  match Hashtbl.find_opt st.slayout sname with
  | Some x -> x | None -> raise (Unsupported ("unknown struct type " ^ sname))

let find_field st sname f =
  let (fields, _) = struct_layout st sname in
  match List.find_opt (fun (g, _, _) -> g = f) fields with
  | Some x -> x
  | None -> raise (Unsupported (Printf.sprintf "no field %s in struct %s" f sname))

(* a field's base slot offset within the struct's flat block *)
let field_offset st sname f = let (_, o, _) = find_field st sname f in o

(* a field's array dimensions ([] for a scalar field) *)
let field_dims st sname f = let (_, _, d) = find_field st sname f in d

(* total slot count of a struct (scalar field = 1 slot; array field reserves
   enough for its Cantor-folded indices — see slayout construction) *)
let struct_size st sname = let (_, sz) = struct_layout st sname in sz

(* the (field, offset, dims) list of a struct, in declaration order *)
let struct_fields st sname = let (fields, _) = struct_layout st sname in fields

(* does any field have array dimensions?  Such structs use the flat array-slot
   (GA) representation, not the consecutive-G-slot one, and are not by-ref. *)
let struct_has_array_field st sname =
  List.exists (fun (_, _, d) -> d <> []) (struct_fields st sname)

let new_scope name is_main =
  { name; is_main; formals = Hashtbl.create 8; fstacks = Hashtbl.create 8;
    fstructs = Hashtbl.create 8; fstructs_flat = Hashtbl.create 8;
    fsarrays = Hashtbl.create 8; locals = Hashtbl.create 8;
    lstacks = Hashtbl.create 8; lstructs = Hashtbl.create 8;
    lstructs_flat = Hashtbl.create 8; nloc = 0 }

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

(* a struct local occupies one local slot per field, consecutively *)
let local_struct st scp sname nm = match Hashtbl.find_opt scp.lstructs nm with
  | Some p -> p
  | None -> let base = scp.nloc in scp.nloc <- scp.nloc + struct_size st sname;
            Hashtbl.add scp.lstructs nm (sname, base); (sname, base)

(* a struct local WITH array fields: one RL slot used as array base;
   each cell is ARd(RL(base), field_offset + Cantor(idx)) *)
let local_struct_flat scp sname nm = match Hashtbl.find_opt scp.lstructs_flat nm with
  | Some p -> p
  | None -> let base = scp.nloc in scp.nloc <- scp.nloc + 1;
            Hashtbl.add scp.lstructs_flat nm (sname, base); (sname, base)

let add_formals st scp (params : param list) =
  let i = ref 0 in
  List.iter (fun (p : param) ->
    if p.pis_stack then begin
      (* a stack formal occupies two consecutive positions: arr, then top *)
      Hashtbl.replace scp.fstacks p.pname (!i, !i + 1); i := !i + 2
    end else match p.pstruct with
      | Some sname when p.pis_array ->
        (* a struct-array formal is one positional ref (the array base), like a
           plain array; element fields index it as elem*nfields + offset *)
        Hashtbl.replace scp.fsarrays p.pname (sname, !i); incr i
      | Some sname when struct_has_array_field st sname ->
        (* struct WITH array fields: one positional ref (the array base);
           fields accessed as ARd(RF(base), field_offset + Cantor(idx)) *)
        Hashtbl.replace scp.fstructs_flat p.pname (sname, !i); incr i
      | Some sname ->
        (* scalar struct: one positional ref per field *)
        Hashtbl.replace scp.fstructs p.pname (sname, !i); i := !i + struct_size st sname
      | None ->
        (* a scalar/array formal is one positional ref (RF i); ARd/AAsn index it *)
        Hashtbl.replace scp.formals p.pname !i; incr i) params

(* classify a scalar/array variable name into a frame [ref] at this scope.
   A whole struct-array name resolves to its base ref (so it can be passed by
   reference like a plain array). *)
let ref_of st scp nm : J.ref =
  match Hashtbl.find_opt scp.formals nm with
  | Some i -> J.RF (nat i)
  | None ->
    match Hashtbl.find_opt scp.fsarrays nm with
    | Some (_, idx) -> J.RF (nat idx)
    | None ->
    match Hashtbl.find_opt scp.locals nm with
    | Some x -> J.RL (nat x)
    | None ->
      if scp.is_main then J.RG (nat (gslot st nm))
      (* an unbound name in a procedure (e.g. a typo'd reference in a dead,
         never-called procedure) becomes a fresh local, as lower.ml's flat slots
         tolerate it; if the procedure is actually run, a value mismatch is
         caught by the conformance test rather than silently passing *)
      else J.RL (nat (local_slot scp nm))

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

(* a struct field access resolves to either a scalar slot (scalar struct var) or
   an array cell (struct-array element field) *)
type faccess = FScalar of J.ref | FCell of J.ref * Janus_frame.expr

(* is [nm] a scalar struct-valued variable in this scope? *)
let is_struct_var st scp nm =
  Hashtbl.mem scp.lstructs nm || Hashtbl.mem scp.lstructs_flat nm
  || Hashtbl.mem scp.fstructs nm || Hashtbl.mem scp.fstructs_flat nm
  || (scp.is_main && (Hashtbl.mem st.gstructs nm || Hashtbl.mem st.gstructs_flat nm))

(* the per-field refs of a scalar struct variable, in field-declaration order
   (used to expand a struct actual into one ref per field at a call site) *)
let struct_var_field_refs st scp nm : J.ref list =
  (* scalar struct (no array fields): expand to one ref per field *)
  let fld base mk sname =
    List.map (fun (_, off, _) -> mk (nat (base + off))) (struct_fields st sname) in
  match Hashtbl.find_opt scp.lstructs nm with
  | Some (sname, base) -> fld base (fun n -> J.RL n) sname
  | None ->
  (* flat structs (with array fields): pass ONE array-base ref *)
  match Hashtbl.find_opt scp.lstructs_flat nm with
  | Some (_, base) -> [J.RL (nat base)]
  | None ->
  match Hashtbl.find_opt scp.fstructs_flat nm with
  | Some (_, base) -> [J.RF (nat base)]
  | None ->
  match Hashtbl.find_opt scp.fstructs nm with
  | Some (sname, base) -> fld base (fun n -> J.RF n) sname
  | None ->
    match Hashtbl.find_opt st.gstructs nm with
    | Some (sname, base) when scp.is_main -> fld base (fun n -> J.RG n) sname
    | _ ->
      match Hashtbl.find_opt st.gstructs_flat nm with
      | Some (_, base) when scp.is_main -> [J.RG (nat base)]
      | _ -> raise (Unsupported ("struct value " ^ nm))

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
  | Lv ({ fields = _ :: _; _ } as lv) ->
    (match field_access st scp lv with
     | FScalar r -> J.Rd r
     | FCell (b, i) -> J.ARd (b, i))
  | Lv { lname; sels = []; _ } -> J.Rd (ref_of st scp lname)
  | Lv { lname; sels; _ } -> J.ARd (ref_of st scp lname, index st scp sels)
  | Top nm -> let (a, t) = stack_refs st scp nm in
              J.ARd (a, J.Bin (J.BSub, J.Rd t, J.Cst (z 1)))   (* arr[top-1] *)
  | Empty nm -> let (_, t) = stack_refs st scp nm in J.Bin (J.BEq, J.Rd t, J.Cst (z 0))
  | Size nm -> if is_stack st scp nm then let (_, t) = stack_refs st scp nm in J.Rd t
               else (match Hashtbl.find_opt st.arrlen (scp.name, nm) with
                     | Some l -> J.Cst (z l)
                     | None -> raise (Unsupported ("size() of unknown-length array " ^ nm)))
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

(* resolve a struct field access (main-scope, single field) to a scalar slot
   (scalar struct var) or an array cell.  `lv.fsels` index into an array field;
   the field offset within an element is field_offset + Cantor(fsels). *)
and field_access st scp (lv : Ast.lval) : faccess =
  let f = match lv.fields with [f] -> f | _ -> raise (Unsupported "nested struct field access") in
  (* offset of this field's accessed cell within one struct element *)
  let foff sname = J.Bin (J.BAdd, J.Cst (z (field_offset st sname f)), index st scp lv.fsels) in
  (* a scalar field accessed without an array index — needed for the G-slot /
     by-ref representations, which can't address an array field dynamically *)
  let scalar_off sname =
    if lv.fsels <> [] || field_dims st sname f <> [] then
      raise (Unsupported "array field on a by-ref/local/formal struct (not yet)");
    field_offset st sname f in
  match Hashtbl.find_opt scp.lstructs lv.lname with
  | Some (sname, base) when lv.sels = [] ->     (* struct local: RL(base + offset) *)
    FScalar (J.RL (nat (base + scalar_off sname)))
  | _ ->
  match Hashtbl.find_opt scp.lstructs_flat lv.lname with
  | Some (sname, base) when lv.sels = [] ->     (* flat local (array fields): ARd(RL(base), foff) *)
    FCell (J.RL (nat base), foff sname)
  | _ ->
  match Hashtbl.find_opt scp.fstructs lv.lname with
  | Some (sname, base) when lv.sels = [] ->     (* scalar struct formal: RF(base + offset) *)
    FScalar (J.RF (nat (base + scalar_off sname)))
  | _ ->
  match Hashtbl.find_opt scp.fstructs_flat lv.lname with
  | Some (sname, base) when lv.sels = [] ->   (* flat formal (array fields): ARd(RF(base), foff) *)
    FCell (J.RF (nat base), foff sname)
  | _ ->
  match Hashtbl.find_opt scp.fsarrays lv.lname with
  | Some (sname, idx) ->                         (* struct-array formal element field *)
    let nfields = struct_size st sname in
    let cell = J.Bin (J.BAdd, J.Bin (J.BMul, index st scp lv.sels, J.Cst (z nfields)), foff sname) in
    FCell (J.RF (nat idx), cell)
  | _ ->
  match Hashtbl.find_opt st.gstructs_flat lv.lname with
  | Some (sname, base) when scp.is_main && lv.sels = [] ->  (* scalar struct w/ array fields *)
    FCell (J.RG (nat base), foff sname)
  | _ ->
    match Hashtbl.find_opt st.gsarrays lv.lname with
    | Some (sname, base, nfields) when scp.is_main ->
      let cell = J.Bin (J.BAdd, J.Bin (J.BMul, index st scp lv.sels, J.Cst (z nfields)), foff sname) in
      FCell (J.RG (nat base), cell)
    | _ ->
      (match lv.sels, Hashtbl.find_opt st.gstructs lv.lname with
       | [], Some (sname, base) when scp.is_main ->
         FScalar (J.RG (nat (base + scalar_off sname)))
       | _ -> raise (Unsupported ("struct field access on " ^ lv.lname)))

(* exact integer Cantor fold, for static (initializer) indices *)
let cantor_val = function
  | [] -> 0
  | x :: rest -> List.fold_left (fun acc j -> (acc + j) * (acc + j + 1) / 2 + j) x rest

(* the constant signed step by which [nm] is incremented at top level of [stmts]
   (`nm += c` -> +c, `nm -= c` -> -c); None if there is no such single step *)
let rec find_step nm = function
  | [] -> None
  | Ast.Assign ({ lname; sels = []; fields = []; _ }, "+=", Ast.Num c) :: _ when lname = nm -> Some c
  | Ast.Assign ({ lname; sels = []; fields = []; _ }, "-=", Ast.Num c) :: _ when lname = nm -> Some (- c)
  | _ :: rest -> find_step nm rest

(* Recognise the counter idiom `from i=START do {…; i += STEP} loop … until COND`
   (a single from-loop incrementing [nm] by a constant), returning (STEP, COND).
   This is what a self-referential `delocal i = i` frees: knowing STEP and COND
   lets us count [nm] back down to START with a clean reverse loop, so the local
   is freed at the non-self-referential value START — no closed form needed. *)
let counter_idiom nm (body : Ast.stmt list) : (int * Ast.expr) option =
  match body with
  | [Ast.From (_entry, do_s, loop_s, until)] ->
    (match find_step nm do_s with
     | Some step -> Some (step, until)
     | None -> (match find_step nm loop_s with Some step -> Some (step, until) | None -> None))
  | _ -> None

(* Static check: reject self-referential local/delocal that is NOT the counter
   idiom.  Such programs cannot be lowered to a clean Enter/Exit pair:
   - `local i = f(i)`: i is not in scope at the point of initialisation.
   - `delocal i = f(i)` (non-counter): the freed value references the dying cell;
     a sound lowering would require keeping history or non-local uncomputation.
   Both are rejected with Ast.Error (exit 1) so the corpus test does not skip
   them as "unsupported" but fails, matching the language-level error semantics. *)
let rec check_stmts stmts = List.iter check_stmt stmts
and check_stmt = function
  | Ast.Local (d1, body, d2) ->
    let nm = d1.Ast.dname in
    let e_init = match d1.Ast.dinit with Some e -> e | None -> Ast.Num 0 in
    let e_delocal = match d2.Ast.dinit with Some e -> e | None -> Ast.Num 0 in
    if reads_name e_init nm then
      raise (Ast.Error (Printf.sprintf
        "local '%s': initialiser must not read '%s' (variable not yet in scope)" nm nm, 0, 0));
    if reads_name e_delocal nm && counter_idiom nm body = None then
      raise (Ast.Error (Printf.sprintf
        "delocal '%s': self-referential delocal is only valid for loop counters \
         (single from-loop stepping '%s' by a constant)" nm nm, 0, 0));
    check_stmts body
  | Ast.If (_, t, f, _) -> check_stmts t; check_stmts f
  | Ast.From (_, do_s, loop_s, _) -> check_stmts do_s; check_stmts loop_s
  | Ast.Iterate (_, _, _, _, _, body) -> check_stmts body
  | _ -> ()

let check_program (prog : Ast.program) =
  List.iter (fun p -> check_stmts p.Ast.body) prog.Ast.procs;
  check_stmts prog.Ast.mstmts

let aop = function "+=" -> J.OAdd | "-=" -> J.OSub | "^=" -> J.OXor
  | o -> raise (Unsupported ("assign-op " ^ o))

(* emit `lv op= rhs` as a scalar Asn, an array-cell AAsn, or a struct-field
   Asn/AAsn (scalar struct field vs. struct-array element field) *)
let assign_lv st scp (lv : Ast.lval) (o : J.aop) (rhs : J.expr) : J.stmt =
  match lv.fields, lv.sels with
  | _ :: _, _ ->
    (match field_access st scp lv with
     | FScalar r -> J.Asn (r, o, rhs)
     | FCell (b, i) -> J.AAsn (b, i, o, rhs))
  | [], [] -> J.Asn (ref_of st scp lv.lname, o, rhs)
  | [], sels -> J.AAsn (ref_of st scp lv.lname, index st scp sels, o, rhs)

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
  | Local (d1, body, d2) when d1.dstruct <> None ->
    (* struct local `local struct S e = src`:
       - scalar struct (no array fields): copy each field into an RL slot;
         lowered to Enter/Exit per field.
       - struct WITH array fields: use a single RL slot as array base;
         lowered to AAsn(OAdd)/AAsn(OSub) per statically-enumerated cell. *)
    let sname = match d1.dstruct with Some s -> s | None -> assert false in
    let src_lv = function
      | Some (Ast.Lv lv) -> lv
      | _ -> raise (Unsupported "struct local initializer must be an l-value") in
    let s1 = src_lv d1.dinit and s2 = src_lv d2.dinit in
    if struct_has_array_field st sname then begin
      let (_, base) = local_struct_flat scp sname d1.dname in
      let body' = seq st scp body in
      let base_ref = J.RL (nat base) in
      (* enumerate every cell: (flat_cell_offset, field_name, static_idx_list) *)
      let all_cells = List.concat_map (fun (f, off, dims) ->
        if dims = [] then [(off, f, [])]
        else
          let rec enum = function
            | [] -> [[]]
            | d :: rest ->
              List.concat_map
                (fun i -> List.map (fun t -> i :: t) (enum rest))
                (List.init d (fun i -> i))
          in
          List.map (fun idxs -> (off + cantor_val idxs, f, idxs)) (enum dims))
        (struct_fields st sname) in
      let field_cell lv f idxs =
        expr st scp (Ast.Lv { lv with fields = lv.fields @ [f];
                                       fsels  = List.map (fun i -> Ast.Num i) idxs }) in
      List.fold_left (fun acc (cell_off, f, idxs) ->
          J.Seq (J.AAsn (base_ref, J.Cst (z cell_off), J.OAdd, field_cell s1 f idxs),
                 J.Seq (acc,
                        J.AAsn (base_ref, J.Cst (z cell_off), J.OSub, field_cell s2 f idxs))))
        body' all_cells
    end else begin
      let (_, base) = local_struct st scp sname d1.dname in
      let body' = seq st scp body in
      let field_src lv f = expr st scp (Ast.Lv { lv with fields = lv.fields @ [f] }) in
      List.fold_left (fun acc (f, off, _) ->
          J.Seq (J.Enter (nat (base + off), field_src s1 f),
                 J.Seq (acc, J.Exit (nat (base + off), field_src s2 f))))
        body' (struct_fields st sname)
    end
  | Local (d1, body, d2)
    when (let e1 = match d2.dinit with Some e -> e | None -> Num 0 in
          reads_name e1 d1.dname                          (* self-referential delocal *)
          && not (reads_name (match d1.dinit with Some e -> e | None -> Num 0) d1.dname)
          && counter_idiom d1.dname body <> None) ->
    (* Loop-aware lowering of `local i=START; from i=START do {…; i += STEP} …
       until COND; delocal i = i`.  Freeing a loop counter at its dynamic final
       value is not statement-reversible directly (the delocal value references
       the freed variable).  Instead, after the loop we count i back down to
       START with a clean reverse loop — `from COND do {i -= STEP} until i=START`
       — which touches nothing but i, then free it at START (a live, non-self-
       referential value).  The reverse loop is an ordinary reversible from-loop;
       its inverse counts i back up to the final value, so the whole composite is
       reversible without any closed form for the loop bound. *)
    let nm = d1.dname in
    let step, until = match counter_idiom nm body with Some x -> x | None -> assert false in
    let start = match d1.dinit with Some e -> e | None -> Num 0 in
    let x = local_slot scp nm in
    let xref = J.RL (nat x) in
    let start_e = expr st scp start in
    let main = seq st scp body in                         (* i: START -> final *)
    let dec = J.Asn (xref, J.OSub, J.Cst (z step)) in     (* i -= STEP (signed) *)
    let back = J.Loop (expr st scp until, dec, J.Skip,    (* i: final -> START *)
                       J.Bin (J.BEq, J.Rd xref, start_e)) in
    J.Seq (J.Enter (nat x, start_e),
           J.Seq (main, J.Seq (back, J.Exit (nat x, start_e))))
  | Local (d1, body, d2) ->
    let e0 = match d1.dinit with Some e -> e | None -> Num 0 in
    let e1 = match d2.dinit with Some e -> e | None -> Num 0 in
    (* self-referential local/delocal is caught statically by check_program
       (Ast.Error, exit 1) before lowering; reaching here means it is safe. *)
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
    | ALv { lname; sels = []; fields = [] } when is_stack st scp lname ->
      (* a stack actual expands to its two refs, arr then top *)
      let (ar, tr) = stack_refs st scp lname in refs := tr :: ar :: !refs
    | ALv { lname; sels = []; fields = [] } when is_struct_var st scp lname ->
      (* a struct actual expands to one ref per field, in order *)
      refs := List.rev_append (struct_var_field_refs st scp lname) !refs
    | ALv { lname; sels = []; fields = [] } -> refs := ref_of st scp lname :: !refs
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
    if forward then J.Call (nat idx, Glue.ref_list refs)
    else J.Uncall (nat idx, Glue.ref_list refs) in
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

(* ----- size() propagation: main array decls -> proc formals via call sites ----- *)

let rec collect_calls sc (ss : Ast.stmt list) acc =
  List.fold_left (fun acc s -> match s with
    | Call (n, a) | Uncall (n, a) -> (sc, n, a) :: acc
    | If (_, t1, t2, _) -> collect_calls sc t1 (collect_calls sc t2 acc)
    | From (_, d, l, _) -> collect_calls sc d (collect_calls sc l acc)
    | Iterate (_, _, _, _, _, b) -> collect_calls sc b acc
    | Local (_, b, _) -> collect_calls sc b acc
    | _ -> acc) acc ss

(* fixpoint: an array passed to a formal gives that formal the same length *)
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
  stks : (string * int * int) list;
  structs : (string * int * (string * int) list) list;  (* scalar struct (no array fields): var, base G slot, (field, offset) *)
  flatstructs : (string * int * (string * int * int list) list) list;
                                          (* scalar struct WITH array fields: var, base array slot, (field, offset, dims) *)
  sarrays : (string * int * int list * int * (string * int * int list) list) list;
                                          (* struct array: var, base array slot, dims, slots/elem, (field, offset, dims) *)
  mbody : J.stmt;                         (* main's body WITHOUT the decl-init prefix, for `-inverse`:
                                             PyJanus `--inverse` re-seeds decls with the final store and
                                             inverts only the body, so we invert [mbody] (not the inits). *)
}

let program (p : Ast.program) : J.stmt array * J.stmt * layout =
  let st = create () in
  (* struct layouts: fields laid out consecutively.  A scalar field takes one
     slot; an array field reserves enough slots for its Cantor-folded indices
     (max Cantor index + 1), so `field += Cantor(idx)` never overruns the next
     field. Offsets are cumulative; the total is the struct's slot count. *)
  List.iter (fun (sd : Ast.structdef) ->
    let (offsets, total) = List.fold_left (fun (acc, off) (f : Ast.sfield) ->
      let sz = match f.fdims with
        | [] -> 1
        | ds -> cantor_val (List.map (fun d -> d - 1) ds) + 1 in
      ((f.fname, off, f.fdims) :: acc, off + sz)) ([], 0) sd.sfields in
    Hashtbl.replace st.slayout sd.sname (List.rev offsets, total)) p.structs;
  List.iteri (fun i pr -> Hashtbl.replace st.procmap pr.procname i) p.procs;
  List.iter (fun pr -> Hashtbl.replace st.pforms pr.procname
                (List.map (fun (par : Ast.param) -> par.pname) pr.params)) p.procs;
  resolve_arrlen st p;
  (* lower every procedure body in its own scope (formals positional, fresh locals) *)
  let procs = List.map (fun pr ->
    let scp = new_scope pr.procname false in
    add_formals st scp pr.params;
    seq st scp pr.body) p.procs in
  (* main: declared variables are globals; reject arrays/stacks for now *)
  let mscp = new_scope "main" true in
  let scalars = ref [] and arrays = ref [] and stks = ref [] and structs = ref []
  and flatstructs = ref [] and sarrays = ref [] and inits = ref [] in
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
    end else if vd.vstruct <> None then begin
      let sname = match vd.vstruct with Some s -> s | None -> assert false in
      let (offsets, size) = match Hashtbl.find_opt st.slayout sname with
        | Some x -> x | None -> raise (Unsupported ("unknown struct type " ^ sname)) in
      if vd.vdims <> [] then begin
        (* array of structs: one base array slot; cell GA(base, elem*size + offset) *)
        let base = gslot st vd.vname in
        Hashtbl.replace st.gsarrays vd.vname (sname, base, size);
        sarrays := (vd.vname, base, vd.vdims, size, offsets) :: !sarrays;
        (match vd.vinit with None -> () | Some _ -> raise (Unsupported "struct array initializer (not yet)"))
      end else if struct_has_array_field st sname then begin
        (* scalar struct WITH array fields: one base array slot, GA-addressed *)
        let base = gslot st vd.vname in
        Hashtbl.replace st.gstructs_flat vd.vname (sname, base);
        flatstructs := (vd.vname, base, offsets) :: !flatstructs;
        (match vd.vinit with None -> () | Some _ -> raise (Unsupported "struct initializer (not yet)"))
      end else begin
        (* pure scalar struct: consecutive scalar slots G(base .. base+size-1) *)
        let base = st.nglob in st.nglob <- st.nglob + size;
        Hashtbl.replace st.gstructs vd.vname (sname, base);
        structs := (vd.vname, base, List.map (fun (f, o, _) -> (f, o)) offsets) :: !structs;
        (match vd.vinit with None -> () | Some _ -> raise (Unsupported "struct initializer (not yet)"))
      end
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
   { scalars = List.rev !scalars; arrays = List.rev !arrays; stks = List.rev !stks;
     structs = List.rev !structs; flatstructs = List.rev !flatstructs;
     sarrays = List.rev !sarrays; mbody = body })
