(* frame_smoke.ml — run the *extracted* frame core on the one case the flat
   (janus_arr) model provably cannot: a local that is live across a recursive-
   style call.  This is the OCaml analogue of RevFrame.v's
   [frames_avoid_local_alias] / [demo_runs]:

     proc 0 :  local x0 = 5 ; delocal x0 = 5          (* its own depth-1 frame *)
     main   :  local x0 = 3 ; call proc0 ; delocal x0 = 3   (* depth-0 frame   *)

   The outer [Enter 0] lives at [L 0 0] and the inner one at [L 1 0]: distinct
   slots, so both dead-cell preconditions hold and the program runs, restoring
   the store.  In the flat model both would be [LS 0] and the inner [Enter]
   would get stuck (run = None).  We also run the inverse to confirm uncall.

   Purpose: validate the OCaml <-> extracted-frame-core boundary (numeral glue,
   [nat -> stmt] gamma, depth-threaded [run]) before the vjanus lowering targets
   it.  Built and executed by build.sh; failure exits non-zero. *)

open Janus_frame

let n i = Glue.nat_of_int i
let c i = Cst (Glue.z_of_int i)

(* proc 0: enter then exit its own local 0 with value 5 (net no-op on the store) *)
let demo_gamma : stmt array = [| Seq (Enter (n 0, c 5), Exit (n 0, c 5)) |]

(* main: enter local 0 = 3, call proc 0 (which enters its *own* local 0 one frame
   deeper), then exit local 0 = 3 *)
let demo : stmt =
  Seq (Enter (n 0, c 3), Seq (Call (n 0, Nil), Exit (n 0, c 3)))

let fail msg = prerr_endline ("frame_smoke FAIL: " ^ msg); exit 1

let () =
  (match Glue.run_program demo_gamma demo with
   | None -> fail "forward demo returned None (recursion-with-locals not handled)"
   | Some f ->
     let g0 = Glue.read_global f 0 in
     if g0 <> 0 then fail (Printf.sprintf "store not restored: G0 = %d (expected 0)" g0));
  (* the inverse program (Uncall internally inverts gamma 0) must also run *)
  (match Glue.run_program demo_gamma (invert demo) with
   | None -> fail "inverse demo returned None"
   | Some _ -> ());
  print_endline "frame_smoke: OK (local live across a call runs through the verified frame core)"
