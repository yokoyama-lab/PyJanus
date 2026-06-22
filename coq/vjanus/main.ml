(* main.ml — the `vjanus` CLI: run a jana2014 program through the verified
   frame core (depth-indexed locals, so recursion-with-locals works).

   Usage:  vjanus [-s] FILE.ja     run and print the final store (PyJanus `-s`
   format), so results compare directly.  Programs outside the frame core's
   current coverage exit 3 ("unsupported" — the conformance test skips them). *)

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

(* print one global array in PyJanus's nested-brace format *)
let print_array f slot name dims =
  let buf = Buffer.create 64 in
  let rec go prefix dims = match dims with
    | [] -> Buffer.add_string buf (string_of_int (Glue.read_global_cell f slot (cantor (List.rev prefix))))
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
    | "-h" | "--help" -> print_string "usage: vjanus [-s] FILE.ja\n"; exit 0
    | _ when String.length a > 0 && a.[0] = '-' ->
      Printf.eprintf "vjanus: unknown option %s\n" a; exit 2
    | _ -> file := Some a) args;
  let path = match !file with
    | Some p -> p | None -> prerr_string "usage: vjanus [-s] FILE.ja\n"; exit 2 in
  try
    let src = read_file path in
    let toks = Lexer.tokenize src in
    let prog = Parser.program toks in
    let procs, main, layout = Lower.program prog in
    (match Glue.run_program procs main with
     | None -> prerr_string "vjanus: interpreter returned NONE (out of fuel or stuck)\n"; exit 1
     | Some f ->
       List.iter (fun (name, slot) ->
         Printf.printf "%s = %d\n" name (Glue.read_global f slot)) layout.Lower.scalars;
       List.iter (fun (name, slot, dims) -> print_array f slot name dims) layout.Lower.arrays;
       (* stacks: print top-first as `<t, …, b]`, or `nil` when empty *)
       List.iter (fun (name, arr, top) ->
         let depth = Glue.read_global f top in
         if depth <= 0 then Printf.printf "%s = nil\n" name
         else begin
           let cells = List.init depth (fun k -> Glue.read_global_cell f arr (depth - 1 - k)) in
           Printf.printf "%s = <%s]\n" name (String.concat ", " (List.map string_of_int cells))
         end) layout.Lower.stks;
       (* scalar structs: `name = {f1 = v1, f2 = v2, …}` *)
       List.iter (fun (name, base, offsets) ->
         let body = String.concat ", "
           (List.map (fun (fld, off) -> Printf.sprintf "%s = %d" fld (Glue.read_global f (base + off))) offsets) in
         Printf.printf "%s = {%s}\n" name body) layout.Lower.structs)
  with
  | Lower.Unsupported m -> Printf.eprintf "vjanus: unsupported: %s\n" m; exit 3
  | Ast.Error (m, l, c) -> Printf.eprintf "vjanus: %s (line %d, col %d)\n" m l c; exit 3
