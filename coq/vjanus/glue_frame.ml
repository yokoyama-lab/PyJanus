(* glue_frame.ml — int <-> Coq-numeral glue plus a thin runner over the verified
   *frame-stacked* interpreter [Janus_frame.run] (extracted in RevExtractFrame.v).

   It mirrors glue.ml but targets the Phase 2a core: locations are G/L/GA/LA
   (global vs. depth-d local, scalar vs. array cell), the procedure table is a
   bare [nat -> stmt] (formals are positional [RF i], resolved at the call site),
   and [run] threads a starting frame depth.  This is the runtime substrate the
   frame-aware lowering will sit on; for now it is exercised by frame_smoke.ml. *)

type 'a olist = 'a list  (* the predefined OCaml list, before [open] shadows it *)

open Janus_frame

let rec nat_of_int n = if n <= 0 then O else S (nat_of_int (n - 1))
let rec int_of_nat = function O -> 0 | S n -> 1 + int_of_nat n

let rec pos_of_int n =
  if n <= 1 then XH
  else if n land 1 = 1 then XI (pos_of_int (n asr 1)) else XO (pos_of_int (n asr 1))
let z_of_int n = if n = 0 then Z0 else if n > 0 then Zpos (pos_of_int n) else Zneg (pos_of_int (-n))
let rec int_of_pos = function XH -> 1 | XO p -> 2 * int_of_pos p | XI p -> 2 * int_of_pos p + 1
let int_of_z = function Z0 -> 0 | Zpos p -> int_of_pos p | Zneg p -> - (int_of_pos p)

let rec list_of : 'a olist -> 'a Janus_frame.list = function
  | [] -> Nil
  | x :: r -> Cons (x, list_of r)

let ref_list (rs : ref olist) : ref Janus_frame.list = list_of rs

(* Procedure table: [bodies.(i)] is procedure [i]'s body.  [gamma] maps a [pname]
   (a [nat]) to its body, falling back to a no-op for out-of-range. *)
let gamma_of (bodies : stmt array) : nat -> stmt =
  fun p ->
    let i = int_of_nat p in
    if i >= 0 && i < Array.length bodies then bodies.(i) else Skip

let default_fuel = 3_000_000

(* Run [main] under [bodies] from frame depth 0; return the final store as an
   int-valued function on [loc], or None if the interpreter ran out of fuel /
   got stuck (e.g. a non-reversible step). *)
let run_program ?(fuel = default_fuel) (bodies : stmt array) (main : stmt)
    : (loc -> int) option =
  let init : store = fun _ -> Z0 in
  match run (gamma_of bodies) (nat_of_int fuel) O main init with
  | Some f -> Some (fun l -> int_of_z (f l))
  | None -> None

let read_global (f : loc -> int) (slot : int) : int = f (G (nat_of_int slot))
let read_global_cell (f : loc -> int) (slot : int) (idx : int) : int =
  f (GA (nat_of_int slot, z_of_int idx))
