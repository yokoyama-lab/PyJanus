(** * RevExtractFrame.v — extract the frame-stacked verified interpreter

    [RevFrame.v] is the Phase 2a evaluation core: depth-indexed local frames
    (so a procedure that recurses while declaring a [local] gets fresh storage
    per activation) plus arrays and by-reference calls.  Its fuel interpreter
    [run] is proved sound vs. [RevFrame.exec] ([run_sound]), and [exec] is proved
    reversible ([exec_rev]/[exec_iff]/[exec_det]/[exec_injective]).

    This module just re-exports [run]/[invert] to OCaml ([janus_frame.ml]); the
    standalone [vjanus] interpreter links against it.  No new proof obligations
    live here — it is the extraction boundary, mirroring [RevExtractAr.v]. *)

From Stdlib Require Import ZArith Bool Extraction.
Require Import RevFrame.
Import RevFrame.

Extraction Language OCaml.
Extraction "janus_frame.ml" run invert.
