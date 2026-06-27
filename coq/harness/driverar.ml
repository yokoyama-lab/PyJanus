(* driverar.ml — run the extracted *array* verified interpreter (Janus_arr.run).

   Like driverp.ml, with l-values and array reads:
     expr: (c N) | (v X) | (ar A E) | (b BOP E E)
     lval: (ls X) | (la A E)
     asgn: (asgn <lval> OP E)
   (procedures/calls as in driverp.ml). *)

open Janus_arr

let read_all ic =
  let b = Buffer.create 4096 in
  (try while true do Buffer.add_char b (input_char ic) done with End_of_file -> ());
  Buffer.contents b

let tokenize s =
  let b = Buffer.create (2 * String.length s) in
  String.iter (fun c -> match c with
    | '(' | ')' -> Buffer.add_char b ' '; Buffer.add_char b c; Buffer.add_char b ' '
    | _ -> Buffer.add_char b c) s;
  List.filter (fun t -> t <> "") (String.split_on_char ' ' (Buffer.contents b))

let nat_of_int n = let rec go acc n = if n <= 0 then acc else go (S acc) (n - 1) in go O n
let rec int_of_nat = function O -> 0 | S n -> 1 + int_of_nat n
let rec pos_of_int n =
  if n <= 1 then XH
  else if n land 1 = 1 then XI (pos_of_int (n asr 1)) else XO (pos_of_int (n asr 1))
let z_of_int n = if n = 0 then Z0 else if n > 0 then Zpos (pos_of_int n) else Zneg (pos_of_int (-n))
let rec int_of_pos = function XH -> 1 | XO p -> 2 * int_of_pos p | XI p -> 2 * int_of_pos p + 1
let int_of_z = function Z0 -> 0 | Zpos p -> int_of_pos p | Zneg p -> - (int_of_pos p)
let rec list_of_nats = function [] -> Nil | x :: r -> Cons (nat_of_int x, list_of_nats r)

let toks = ref []
let next () = match !toks with t :: r -> toks := r; t | [] -> failwith "unexpected eof"
let nexti () = int_of_string (next ())
let aop_of = function "add" -> AAdd | "sub" -> ASub | "xor" -> AXor | s -> failwith ("aop " ^ s)
let bop_of = function
  | "add" -> OAdd | "sub" -> OSub | "mul" -> OMul | "eq" -> OEq | "lt" -> OLt
  | "div" -> ODiv | "mod" -> OMod
  | "xor" -> OXor | "and" -> OAnd | "or" -> OOr | s -> failwith ("bop " ^ s)
let read_nats n = let l = ref [] in for _ = 1 to n do l := nexti () :: !l done; List.rev !l

let rec pexpr () =
  ignore (next ());
  let kw = next () in
  let e = match kw with
    | "c" -> Cst (z_of_int (nexti ()))
    | "v" -> Var (nat_of_int (nexti ()))
    | "ar" -> let a = nat_of_int (nexti ()) in let idx = pexpr () in ARd (a, idx)
    | "b" -> let o = bop_of (next ()) in let a = pexpr () in let b = pexpr () in Bin (o, a, b)
    | _ -> failwith ("expr " ^ kw) in
  ignore (next ()); e

let plv () =
  ignore (next ());
  let kw = next () in
  let l = match kw with
    | "ls" -> LVs (nat_of_int (nexti ()))
    | "la" -> let a = nat_of_int (nexti ()) in let idx = pexpr () in LVa (a, idx)
    | _ -> failwith ("lv " ^ kw) in
  ignore (next ()); l

let rec pstmt () =
  ignore (next ());
  let kw = next () in
  let s = match kw with
    | "skip" -> Skip
    | "asgn" -> let l = plv () in let o = aop_of (next ()) in let e = pexpr () in Assign (l, o, e)
    | "swap" -> let a = plv () in let b = plv () in Swap (a, b)
    | "enter" -> let x = nat_of_int (nexti ()) in let e = pexpr () in Enter (x, e)
    | "exit" -> let x = nat_of_int (nexti ()) in let e = pexpr () in Exit (x, e)
    | "seq" -> let a = pstmt () in let b = pstmt () in Seq (a, b)
    | "if" -> let e1 = pexpr () in let s1 = pstmt () in let s2 = pstmt () in let e2 = pexpr () in If (e1, s1, s2, e2)
    | "loop" -> let e1 = pexpr () in let s1 = pstmt () in let s2 = pstmt () in let e2 = pexpr () in Loop (e1, s1, s2, e2)
    | "call" -> let p = nexti () in let n = nexti () in Call (nat_of_int p, list_of_nats (read_nats n))
    | "uncall" -> let p = nexti () in let n = nexti () in Uncall (nat_of_int p, list_of_nats (read_nats n))
    | _ -> failwith ("stmt " ^ kw) in
  ignore (next ()); s

let () =
  toks := tokenize (read_all stdin);
  let nvars = nexti () in
  let nprocs = nexti () in
  let procs = Array.make (max nprocs 1) (Pair (Nil, Skip)) in
  for i = 0 to nprocs - 1 do
    let nf = nexti () in
    let fs = read_nats nf in
    let body = pstmt () in
    procs.(i) <- Pair (list_of_nats fs, body)
  done;
  let main = pstmt () in
  let gamma p = let i = int_of_nat p in if i >= 0 && i < nprocs then procs.(i) else Pair (Nil, Skip) in
  ignore nvars;
  let init : store = fun _ -> Z0 in
  let fuel = nat_of_int 3000000 in
  match run fuel gamma main init with
  | Some f ->
      (* report list: NREPORT then (rs GID) | (ra GID IDX) — print one value/line *)
      let nrep = nexti () in
      for _ = 1 to nrep do
        ignore (next ());
        let kw = next () in
        (match kw with
         | "rs" -> Printf.printf "%d\n" (int_of_z (f (LS (nat_of_int (nexti ())))))
         | "ra" -> let g = nat_of_int (nexti ()) in let i = nexti () in
                   Printf.printf "%d\n" (int_of_z (f (LA (g, z_of_int i))))
         | _ -> failwith ("report " ^ kw));
        ignore (next ())
      done
  | None -> print_string "NONE\n"
