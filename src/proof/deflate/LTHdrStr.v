(** * The header part of the deflate laws' theory: the NAME_STATE / COMMENT_STATE string loop

    [str_stage]: [c_deflate_str h o reset] (the zero-terminated string [o] = gz_name / gz_comment of [h],
    starting at header byte [base] of [H], [gzindex] of its bytes already put) either puts the rest of the
    string (and the HCRC_UPDATE) and falls through (needs [0 <= base]: LTHdrStrNN.v), or returns Z_OK with pending_buf full and the output space
    full in the middle of the string.  Kit: LTHdrKit.v (dput_byte_mid, hcrc_update_mid, flush_mid,
    loop_measure). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTHdrKit Zlib.proof.deflate.LTHdrStrNN.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma str_stage : forall s0 z0 H k0 s z h o reset base,
  hmid s0 z0 H k0 s z (base + d_gzindex s) -> d_gzhead s = Some h -> bytes H -> cstr_ok o -> 0 <= base ->
  (match o with Some l => 0 <= d_gzindex s < Zlength l | None => d_gzindex s = 0 end) ->
  base + Zlength (cstr_bytes o) <= Zlength H ->
  sublist base (base + Zlength (cstr_bytes o)) H = cstr_bytes o ->
  z_adler z = hadler h H (base + d_gzindex s) ->
  exists s' z' r, c_deflate_str h o reset s z = Some (s', z', r) /\
    d_status s' = d_status s /\ d_gzhead s' = d_gzhead s /\ d_wrap s' = d_wrap s /\
    match r with
    | None => hmid s0 z0 H k0 s' z' (base + Zlength (cstr_bytes o)) /\
              (reset = true -> d_gzindex s' = 0) /\
              z_adler z' = hadler h H (base + Zlength (cstr_bytes o))
    | Some c => c = Z_OK /\ o <> None /\ 0 <= d_gzindex s' < Zlength (cstr_bytes o) /\
                hret s0 z0 H k0 s' z' (base + d_gzindex s') /\ z_adler z' = hadler h H (base + d_gzindex s')
    end.
Proof. exact str_stage_nn. Qed.
