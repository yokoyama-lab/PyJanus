(* driverp.ml — run the extracted *parameterized* verified interpreter
   (Janus_param.run) on an s-expression program with procedures.

   Format:
     NVARS NPROCS <proc_0> ... <proc_{NPROCS-1}> <main>
     <proc> := NFORMALS f_0 ... f_{NFORMALS-1} <stmt>
   Statements add parameterized calls:
     (call P NARGS a_0 ... a_{NARGS-1}) | (uncall P NARGS a_0 ...)
   (other forms as in driver.ml). *)

open Janus_param

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
  | "add" -> OAdd | "sub" -> OSub | "mul" -> OMul | "eq" -> OEq | "lt" -> OLt | s -> failwith ("bop " ^ s)

let read_nats n = let l = ref [] in for _ = 1 to n do l := nexti () :: !l done; List.rev !l

let rec pexpr () =
  ignore (next ());
  let kw = next () in
  let e = match kw with
    | "c" -> Cst (z_of_int (nexti ()))
    | "v" -> Var (nat_of_int (nexti ()))
    | "b" -> let o = bop_of (next ()) in let a = pexpr () in let b = pexpr () in Bin (o, a, b)
    | _ -> failwith ("expr " ^ kw) in
  ignore (next ()); e

let rec pstmt () =
  ignore (next ());
  let kw = next () in
  let s = match kw with
    | "skip" -> Skip
    | "asgn" -> let v = nat_of_int (nexti ()) in let o = aop_of (next ()) in let e = pexpr () in Assign (v, o, e)
    | "swap" -> let a = nat_of_int (nexti ()) in let b = nat_of_int (nexti ()) in Swap (a, b)
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
  let init : store = fun _ -> Z0 in
  let fuel = nat_of_int 3000000 in
  match run fuel gamma main init with
  | Some f -> for i = 0 to nvars - 1 do Printf.printf "%d=%d\n" i (int_of_z (f (nat_of_int i))) done
  | None -> print_string "NONE\n"
