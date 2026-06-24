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

(* ---- a dependency-free JSON value, just enough for `-inverse` stores:
   an object {name: value}, nested integer arrays, and integers (no strings as
   values, no floats/bools).  Matches PyJanus `--inverse`'s JSON shape. ---- *)
type jv = JInt of int | JArr of jv list | JObj of (string * jv) list

let parse_json (s : string) : jv =
  let n = String.length s and pos = ref 0 in
  let peek () = if !pos < n then s.[!pos] else '\000' in
  let skip_ws () =
    while !pos < n && (match s.[!pos] with ' '|'\t'|'\n'|'\r' -> true | _ -> false)
    do incr pos done in
  let expect c =
    skip_ws (); if peek () = c then incr pos
    else failwith (Printf.sprintf "json: expected '%c'" c) in
  let number () =
    let start = !pos in
    if peek () = '-' then incr pos;
    while !pos < n && s.[!pos] >= '0' && s.[!pos] <= '9' do incr pos done;
    int_of_string (String.sub s start (!pos - start)) in
  let str () =
    expect '"';
    let b = Buffer.create 16 in
    while peek () <> '"' do Buffer.add_char b (peek ()); incr pos done;
    incr pos; Buffer.contents b in
  let rec value () =
    skip_ws ();
    match peek () with
    | '{' -> obj () | '[' -> arr ()
    | c when c = '-' || (c >= '0' && c <= '9') -> JInt (number ())
    | _ -> failwith "json: unexpected token"
  and obj () =
    expect '{'; skip_ws ();
    if peek () = '}' then (incr pos; JObj [])
    else begin
      let acc = ref [] in
      let rec loop () =
        skip_ws (); let k = str () in expect ':'; let v = value () in
        acc := (k, v) :: !acc; skip_ws ();
        if peek () = ',' then (incr pos; loop ()) else expect '}' in
      loop (); JObj (List.rev !acc)
    end
  and arr () =
    expect '['; skip_ws ();
    if peek () = ']' then (incr pos; JArr [])
    else begin
      let acc = ref [] in
      let rec loop () =
        let v = value () in acc := v :: !acc; skip_ws ();
        if peek () = ',' then (incr pos; loop ()) else expect ']' in
      loop (); JArr (List.rev !acc)
    end in
  value ()

let rec print_jv buf = function
  | JInt v -> Buffer.add_string buf (string_of_int v)
  | JArr xs ->
    Buffer.add_char buf '[';
    List.iteri (fun i x -> if i > 0 then Buffer.add_string buf ", "; print_jv buf x) xs;
    Buffer.add_char buf ']'
  | JObj kvs ->
    Buffer.add_char buf '{';
    List.iteri (fun i (k, v) ->
      if i > 0 then Buffer.add_string buf ", ";
      Buffer.add_string buf (Printf.sprintf "\"%s\": " k); print_jv buf v) kvs;
    Buffer.add_char buf '}'

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

(* print an array of structs: each element is `{f = v, ...}`, nested by dims *)
let print_struct_array f base name dims nfields offsets =
  let buf = Buffer.create 64 in
  let rec go prefix dims = match dims with
    | [] ->
      let elem = cantor (List.rev prefix) in
      let body = String.concat ", "
        (List.map (fun (fld, off) ->
           Printf.sprintf "%s = %d" fld (Glue.read_global_cell f base (elem * nfields + off))) offsets) in
      Buffer.add_string buf (Printf.sprintf "{%s}" body)
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

(* `-inverse JSON`: given main's FINAL store as JSON, run the verified inverter
   (invert main, then run from the seeded store) and print the INITIAL store as
   JSON — output-compatible with PyJanus `--inverse`.  Only main scalars and
   (multi-dim) arrays are representable; a stack/struct main makes this exit 3. *)
let run_inverse procs main layout (jv : jv) =
  if layout.Lower.stks <> [] || layout.Lower.structs <> [] || layout.Lower.sarrays <> [] then
    raise (Lower.Unsupported "inverse: stack/struct final stores not supported");
  let obj = match jv with
    | JObj o -> o
    | _ -> raise (Lower.Unsupported "inverse: top-level JSON must be an object") in
  (* seed main's scalar / array cells from the given final values *)
  let scalars = ref [] and cells = ref [] in
  List.iter (fun (name, v) ->
    match List.assoc_opt name layout.Lower.scalars with
    | Some slot ->
      (match v with JInt x -> scalars := (slot, x) :: !scalars
       | _ -> raise (Lower.Unsupported ("inverse: scalar " ^ name ^ " needs an integer")))
    | None ->
      match List.find_opt (fun (n, _, _) -> n = name) layout.Lower.arrays with
      | Some (_, slot, dims) ->
        let rec go prefix dims v = match dims, v with
          | [], JInt x -> cells := (slot, cantor (List.rev prefix), x) :: !cells
          | d :: rest, JArr xs when List.length xs = d ->
            List.iteri (fun i x -> go (i :: prefix) rest x) xs
          | _ -> raise (Lower.Unsupported ("inverse: array " ^ name ^ " shape mismatch")) in
        go [] dims v
      | None -> ()  (* ignore keys that aren't main variables *)) obj;
  (* invert only main's BODY (not the decl-init prefix): the seed already
     stands in for PyJanus's "re-declare with the final store" step, so running
     invert(body) reconstructs the pre-body (= declared-initial) state. *)
  match Glue.run_seeded procs (Glue.invert_main layout.Lower.mbody) !scalars !cells with
  | None -> prerr_string "vjanus: interpreter returned NONE (out of fuel or stuck)\n"; exit 1
  | Some f ->
    (* read back the INITIAL store: every main scalar and array, as JSON *)
    let scalar_kvs = List.map (fun (name, slot) ->
      (name, JInt (Glue.read_global f slot))) layout.Lower.scalars in
    let array_kvs = List.map (fun (name, slot, dims) ->
      (* PyJanus `--inverse` flattens a multi-dim array row-major, so emit the
         cells in row-major index order (each folded to its cell via [cantor]) *)
      let rec combos = function
        | [] -> [[]]
        | d :: rest ->
          let tails = combos rest in
          List.concat (List.init d (fun i -> List.map (fun t -> i :: t) tails)) in
      let cells = List.map (fun idx -> JInt (Glue.read_global_cell f slot (cantor idx)))
                    (combos dims) in
      (name, JArr cells)) layout.Lower.arrays in
    let buf = Buffer.create 64 in
    print_jv buf (JObj (scalar_kvs @ array_kvs));
    print_string (Buffer.contents buf); print_newline ()

let () =
  let args = Array.to_list Sys.argv |> List.tl in
  let file = ref None and inverse = ref None in
  let rec parse = function
    | [] -> ()
    | "-s" :: r -> parse r
    | ("-h" | "--help") :: _ ->
      print_string "usage: vjanus [-s] [-inverse JSON] FILE.ja\n"; exit 0
    | "-inverse" :: j :: r -> inverse := Some j; parse r
    | a :: _ when String.length a > 0 && a.[0] = '-' ->
      Printf.eprintf "vjanus: unknown option %s\n" a; exit 2
    | a :: r -> file := Some a; parse r in
  parse args;
  let path = match !file with
    | Some p -> p | None -> prerr_string "usage: vjanus [-s] [-inverse JSON] FILE.ja\n"; exit 2 in
  try
    let src = read_file path in
    let toks = Lexer.tokenize src in
    let prog = Parser.program toks in
    let procs, main, layout = Lower.program prog in
    begin match !inverse with
    | Some json -> run_inverse procs main layout (parse_json json)
    | None ->
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
         Printf.printf "%s = {%s}\n" name body) layout.Lower.structs;
       (* arrays of structs: `name[N] = {{f = v, …}, …}` *)
       List.iter (fun (name, base, dims, nfields, offsets) ->
         print_struct_array f base name dims nfields offsets) layout.Lower.sarrays)
    end
  with
  | Lower.Unsupported m -> Printf.eprintf "vjanus: unsupported: %s\n" m; exit 3
  | Ast.Error (m, l, c) -> Printf.eprintf "vjanus: %s (line %d, col %d)\n" m l c; exit 3
