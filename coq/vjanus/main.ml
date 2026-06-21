(* main.ml — the `vjanus` CLI: run a jana2014 program through the verified core.

   Usage:  vjanus [-s] FILE.ja      run and print the final store (default)
   The store is printed in PyJanus's `-s` format so results can be compared. *)

let read_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic; s

(* flat index of a multi-dim cell, by the same Cantor pairing lower.ml uses *)
let cantor (combo : int list) : int =
  match combo with
  | [] -> 0
  | x :: rest -> List.fold_left (fun acc j -> (acc + j) * (acc + j + 1) / 2 + j) x rest

let rec ranges dims = match dims with
  | [] -> [[]]
  | d :: rest -> let tails = ranges rest in
                 List.concat_map (fun i -> List.map (fun t -> i :: t) tails) (List.init d (fun k -> k))

(* print one array in PyJanus's nested-brace format *)
let print_array f slot name dims =
  let buf = Buffer.create 64 in
  let rec go prefix dims = match dims with
    | [] -> Buffer.add_string buf (string_of_int (Glue.read_cell f slot (cantor (List.rev prefix))))
    | d :: rest ->
      Buffer.add_char buf '{';
      for i = 0 to d - 1 do
        if i > 0 then Buffer.add_string buf ", ";
        go (i :: prefix) rest
      done;
      Buffer.add_char buf '}'
  in
  go [] dims;
  let dimtag = String.concat "" (List.map (fun d -> Printf.sprintf "[%d]" d) dims) in
  Printf.printf "%s%s = %s\n" name dimtag (Buffer.contents buf)

let () =
  let args = Array.to_list Sys.argv |> List.tl in
  let file = ref None in
  List.iter (fun a -> match a with
    | "-s" -> ()
    | "-i" -> prerr_string "vjanus: -i (invert) not yet implemented\n"; exit 2
    | "-h" | "--help" -> print_string "usage: vjanus [-s] FILE.ja\n"; exit 0
    | _ when String.length a > 0 && a.[0] = '-' ->
      Printf.eprintf "vjanus: unknown option %s\n" a; exit 2
    | _ -> file := Some a) args;
  let path = match !file with Some p -> p | None -> prerr_string "usage: vjanus [-s] FILE.ja\n"; exit 2 in
  try
    let src = read_file path in
    let toks = Lexer.tokenize src in
    let prog = Parser.program toks in
    let procs, main, layout = Lower.program prog in
    (match Glue.run_program procs main with
     | None -> prerr_string "vjanus: interpreter returned NONE (out of fuel or stuck)\n"; exit 1
     | Some f ->
       List.iter (fun (name, slot) -> Printf.printf "%s = %d\n" name (Glue.read_scalar f slot)) layout.Lower.scalars;
       List.iter (fun (name, slot, dims) -> print_array f slot name dims) layout.Lower.arrays;
       (* stacks: print top-first as `<t, …, b]`, or `nil` when empty *)
       List.iter (fun (name, arr, top) ->
         let depth = Glue.read_scalar f top in
         if depth <= 0 then Printf.printf "%s = nil\n" name
         else begin
           let cells = List.init depth (fun k -> Glue.read_cell f arr (depth - 1 - k)) in
           Printf.printf "%s = <%s]\n" name (String.concat ", " (List.map string_of_int cells))
         end) layout.Lower.stks)
  with
  | Lower.Unsupported m -> Printf.eprintf "vjanus: unsupported: %s\n" m; exit 3
  | Ast.Error (m, l, c) -> Printf.eprintf "vjanus: %s (line %d, col %d)\n" m l c; exit 3
