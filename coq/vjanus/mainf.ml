(* mainf.ml — the `vjanusf` CLI: run a jana2014 program through the verified
   *frame* core (depth-indexed locals), the Phase 2a sibling of main.ml/`vjanus`.

   Usage:  vjanusf [-s] FILE.ja     run and print the final store (PyJanus `-s`
   format), so results compare directly.  Programs outside the frame core's
   current coverage exit 3 ("unsupported" — the conformance test skips them). *)

let read_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic; s

let () =
  let args = Array.to_list Sys.argv |> List.tl in
  let file = ref None in
  List.iter (fun a -> match a with
    | "-s" -> ()
    | "-h" | "--help" -> print_string "usage: vjanusf [-s] FILE.ja\n"; exit 0
    | _ when String.length a > 0 && a.[0] = '-' ->
      Printf.eprintf "vjanusf: unknown option %s\n" a; exit 2
    | _ -> file := Some a) args;
  let path = match !file with
    | Some p -> p | None -> prerr_string "usage: vjanusf [-s] FILE.ja\n"; exit 2 in
  try
    let src = read_file path in
    let toks = Lexer.tokenize src in
    let prog = Parser.program toks in
    let procs, main, layout = Lower_frame.program prog in
    (match Glue_frame.run_program procs main with
     | None -> prerr_string "vjanusf: interpreter returned NONE (out of fuel or stuck)\n"; exit 1
     | Some f ->
       List.iter (fun (name, slot) ->
         Printf.printf "%s = %d\n" name (Glue_frame.read_global f slot)) layout.Lower_frame.scalars)
  with
  | Lower_frame.Unsupported m -> Printf.eprintf "vjanusf: unsupported: %s\n" m; exit 3
  | Ast.Error (m, l, c) -> Printf.eprintf "vjanusf: %s (line %d, col %d)\n" m l c; exit 3
