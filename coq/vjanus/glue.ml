(* glue.ml — conversions between OCaml ints and the extracted Coq numerals,
   plus a thin runner around the verified [Janus_arr.run].  The numeral glue
   mirrors coq/harness/driverar.ml (the proven core uses unary [nat] and binary
   [positive]/[z]). *)

type 'a olist = 'a list  (* capture the predefined OCaml list before [open] shadows it *)

open Janus_arr

let rec nat_of_int n = if n <= 0 then O else S (nat_of_int (n - 1))
let rec int_of_nat = function O -> 0 | S n -> 1 + int_of_nat n

let rec pos_of_int n =
  if n <= 1 then XH
  else if n land 1 = 1 then XI (pos_of_int (n asr 1)) else XO (pos_of_int (n asr 1))
let z_of_int n = if n = 0 then Z0 else if n > 0 then Zpos (pos_of_int n) else Zneg (pos_of_int (-n))
let rec int_of_pos = function XH -> 1 | XO p -> 2 * int_of_pos p | XI p -> 2 * int_of_pos p + 1
let int_of_z = function Z0 -> 0 | Zpos p -> int_of_pos p | Zneg p -> - (int_of_pos p)

let rec list_of : 'a olist -> 'a Janus_arr.list = function
  | [] -> Nil
  | x :: r -> Cons (x, list_of r)

let var_list (xs : int olist) : var Janus_arr.list = list_of (List.map nat_of_int xs)

(* Procedure table: [procs.(i) = (formal-vars, body)].  gamma maps a [pname]
   (a [nat]) to its entry, falling back to an empty no-op for out-of-range. *)
let gamma_of (procs : (int olist * stmt) array) : pname -> (var Janus_arr.list, stmt) prod =
  fun p ->
    let i = int_of_nat p in
    if i >= 0 && i < Array.length procs then
      let (fs, body) = procs.(i) in Pair (var_list fs, body)
    else Pair (Nil, Skip)

let default_fuel = 3_000_000

(* Run [main] under [procs]; return the final store as an int-valued function on
   (slot, optional index), or None if the interpreter ran out of fuel / got stuck. *)
let run_program ?(fuel = default_fuel) (procs : (int olist * stmt) array) (main : stmt)
    : (loc -> int) option =
  let init : store = fun _ -> Z0 in
  match run (nat_of_int fuel) (gamma_of procs) main init with
  | Some f -> Some (fun l -> int_of_z (f l))
  | None -> None

let read_scalar (f : loc -> int) (slot : int) : int = f (LS (nat_of_int slot))
let read_cell   (f : loc -> int) (slot : int) (idx : int) : int = f (LA (nat_of_int slot, z_of_int idx))
