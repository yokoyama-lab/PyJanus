(* driver.ml — run the extracted, *verified* Janus interpreter on a program.

   Reads an s-expression program on stdin:

     NVARS NPROCS <body_0> ... <body_{NPROCS-1}> <main>

   where each body/main is a statement s-expr:
     (skip) | (asgn V OP E) | (swap V V) | (seq S S)
     | (if E S S E) | (loop E S S E) | (call P) | (uncall P)
   OP in {add,sub,xor}; expr:  (c N) | (v V) | (b BOP E E),  BOP in {add,sub,mul,eq,lt}.

   Runs [Janus_verified.run] (proved sound vs. the big-step semantics) and prints
   the final store as  i=value  lines for variables 0..NVARS-1. *)

open Janus_verified

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

(* int <-> Coq nat / Z *)
let nat_of_int n = let rec go acc n = if n <= 0 then acc else go (S acc) (n - 1) in go O n
let rec int_of_nat = function O -> 0 | S n -> 1 + int_of_nat n
let rec pos_of_int n =
  if n <= 1 then XH
  else if n land 1 = 1 then XI (pos_of_int (n asr 1)) else XO (pos_of_int (n asr 1))
let z_of_int n = if n = 0 then Z0 else if n > 0 then Zpos (pos_of_int n) else Zneg (pos_of_int (-n))
let rec int_of_pos = function XH -> 1 | XO p -> 2 * int_of_pos p | XI p -> 2 * int_of_pos p + 1
let int_of_z = function Z0 -> 0 | Zpos p -> int_of_pos p | Zneg p -> - (int_of_pos p)

let toks = ref []
let next () = match !toks with t :: r -> toks := r; t | [] -> failwith "unexpected eof"
let aop_of = function "add" -> AAdd | "sub" -> ASub | "xor" -> AXor | s -> failwith ("aop " ^ s)
let bop_of = function
  | "add" -> OAdd | "sub" -> OSub | "mul" -> OMul | "eq" -> OEq | "lt" -> OLt | s -> failwith ("bop " ^ s)

let rec pexpr () =
  ignore (next ()) (* ( *);
  let kw = next () in
  let e = match kw with
    | "c" -> Cst (z_of_int (int_of_string (next ())))
    | "v" -> Var (nat_of_int (int_of_string (next ())))
    | "b" -> let o = bop_of (next ()) in let a = pexpr () in let b = pexpr () in Bin (o, a, b)
    | _ -> failwith ("expr " ^ kw) in
  ignore (next ()) (* ) *); e

let rec pstmt () =
  ignore (next ()) (* ( *);
  let kw = next () in
  let s = match kw with
    | "skip" -> Skip
    | "asgn" -> let v = nat_of_int (int_of_string (next ())) in
                let o = aop_of (next ()) in let e = pexpr () in Assign (v, o, e)
    | "swap" -> let a = nat_of_int (int_of_string (next ())) in
                let b = nat_of_int (int_of_string (next ())) in Swap (a, b)
    | "seq" -> let a = pstmt () in let b = pstmt () in Seq (a, b)
    | "if" -> let e1 = pexpr () in let s1 = pstmt () in let s2 = pstmt () in let e2 = pexpr () in
              If (e1, s1, s2, e2)
    | "loop" -> let e1 = pexpr () in let s1 = pstmt () in let s2 = pstmt () in let e2 = pexpr () in
                Loop (e1, s1, s2, e2)
    | "call" -> Call (nat_of_int (int_of_string (next ())))
    | "uncall" -> Uncall (nat_of_int (int_of_string (next ())))
    | _ -> failwith ("stmt " ^ kw) in
  ignore (next ()) (* ) *); s

let () =
  toks := tokenize (read_all stdin);
  let nvars = int_of_string (next ()) in
  let nprocs = int_of_string (next ()) in
  let procs = Array.make (max nprocs 1) Skip in
  for i = 0 to nprocs - 1 do procs.(i) <- pstmt () done;
  let main = pstmt () in
  let gamma p = let i = int_of_nat p in if i >= 0 && i < nprocs then procs.(i) else Skip in
  let init : store = fun _ -> Z0 in
  let fuel = nat_of_int 1000000 in
  match run fuel gamma main init with
  | Some f -> for i = 0 to nvars - 1 do Printf.printf "%d=%d\n" i (int_of_z (f (nat_of_int i))) done
  | None -> print_string "NONE\n"
