(* The hypotheses and statements of the switch cases, version 5 (Delta_cases5, case_post2 over Model2.v,
   invariant mwf3):
   - frame_ok5: frame_ok + flush is an int (C compares it as an int);
   - the header cases FLAGS .. COMMENT (indices 1..7) hold the application's zero-size header buffers'
     malloc tokens (hdr_tok: `head->extra != Z_NULL` needs a valid pointer) and know
     that a header field marked present has a non-NULL buffer (hd_ok);
   - cases_all5: every case, the header cases with the tokens. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate.CaseKit5.
Require Export Zlib.proof.inflate.CaseHyps.
Require Export Zlib.proof.inflate.Cover3.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Definition frame_ok5 (F: frame) : Prop :=
  frame_ok F /\ Int.min_signed <= f_flush F <= Int.max_signed.

(* the malloc token of a non-NULL header buffer of size 0 *)
Definition btok (b: val) (n: Z) : mpred :=
  if eq_dec b nullval then emp else if zeq n 0 then malloc_token Ews (tarray tuchar 0) b else emp.

Definition hdr_tok (F: frame) (m: mst) : mpred :=
  if i_head (m_s m) then
    btok (f_xb F) (h_extra_max (m_h m)) * btok (f_nb F) (h_name_max (m_h m)) * btok (f_cb F) (h_comm_max (m_h m))
  else emp.

(* a header field marked present has a buffer *)
Definition hd_ok (F: frame) (m: mst) : Prop :=
  i_head (m_s m) = true ->
  (h_xp (m_h m) = true -> f_xb F <> nullval) /\ (h_np (m_h m) = true -> f_nb F <> nullval) /\
  (h_cp (m_h m) = true -> f_cb F <> nullval).

(* the lemma of a header case: with the tokens framed in *)
Definition case_okT5 {Espec: OracleKind} (F: frame) (Y: Z) (i: nat) : Prop :=
  forall m', m_mode m' = Y -> m_leave m' = 0 -> mwf3 m' -> hd_ok F m' ->
    semax Delta_cases5 (loop_state F m' * (fun _ => hdr_tok F m'))
      (seq_of_labeled_statement (ls_drop i inflate_LS))
      (frame_ret_assert (switch_ret_assert (case_post2 F m')) (fun _ => hdr_tok F m')).

Lemma case_okT5_of_ok5 {Espec: OracleKind} (F: frame) (Y: Z) (i: nat):
  case_ok5 F Y i -> case_okT5 F Y i.
Proof.
  intros H m' A B C D. apply semax_frame; [ | apply H; auto].
  intros rho te _. reflexivity.
Qed.

(* the fixed tables are valid, the length table with the length bound *)
Definition fixed_ok5 : Prop :=
  forall s, tvalid_len lenfix_list distfix_list s TLenfix 9 /\ tvalid DISTS lenfix_list distfix_list s TDistfix 5.

(* every case: the header cases (indices 1..7) with the tokens *)
Definition cases_all5 : Prop :=
  forall {Espec: OracleKind} (F: frame), frame_ok5 F ->
    (forall i, (i < 32)%nat -> (i < 1 \/ 7 < i)%nat -> case_ok5 F (HEAD + Z.of_nat i) i) /\
    (forall i, (1 <= i <= 7)%nat -> case_okT5 F (HEAD + Z.of_nat i) i).

(* one pass of the switch (Model2.v) preserves mwf3 *)
Definition stepf2_mwf3_stmt : Prop :=
  forall flush m, mwf3 m -> m_leave m = 0 ->
  match stepf2 flush lenfix_list distfix_list m with IBrk m' => mwf3 m' | IRet _ m' => mwf3 m' end.
