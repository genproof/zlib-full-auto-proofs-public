(** * Model facts for the body proof of deflateInit2_. *)
From Coq Require Import ZArith List Lia Bool.
Require Import Zlib.proof.deflate.DModel3.
Import ListNotations.
Local Open Scope Z_scope.

Lemma bind_some {A B} (x : option A) (f : A -> option B) r :
  bind x f = Some r -> exists v, x = Some v /\ f v = Some r.
Proof. destruct x; simpl; [eauto | discriminate]. Qed.

Ltac bsome H :=
  match type of H with
  | bind ?x ?f = Some _ =>
      let v := fresh "v" in let Hx := fresh "Hx" in
      destruct (bind_some x f _ H) as (v & Hx & ?); clear H
  end.

(** deflateResetKeep on a state whose status passes deflateStateCheck returns Z_OK (when the model succeeds). *)
Lemma resetkeep_code s z r : c_deflateResetKeep s z = Some r -> status_ok (d_status s) = true -> snd r = Z_OK.
Proof.
  intros H Hs. unfold c_deflateResetKeep, bad_state, c_deflateStateCheck in H.
  rewrite Hs in H. cbn [Z.eqb Pos.eqb negb] in H.
  bsome H. match goal with H' : _ = Some r |- _ => bsome H' end.
  match goal with H' : Some _ = Some r |- _ => inversion H'; reflexivity end.
Qed.

(** deflateReset on such a state returns Z_OK. *)
Lemma reset_code s z r : c_deflateReset s z = Some r -> status_ok (d_status s) = true -> snd r = Z_OK.
Proof.
  intros H Hs. unfold c_deflateReset in H. bsome H.
  destruct v as [[s1 z1] ret].
  pose proof (resetkeep_code s z _ Hx Hs) as E. cbn in E. subst ret.
  cbn in H0. bsome H0. match goal with H' : Some _ = Some r |- _ => inversion H'; reflexivity end.
Qed.

(** The parameters after deflateInit2_'s first checks. *)
Definition i_lv (level : Z) : Z := if level =? -1 then 6 else level.
Definition i_wb (wbits : Z) : Z := if wbits <? 0 then - wbits else if wbits >? 15 then wbits - 16 else wbits.
Definition i_wr (wbits : Z) : Z := if wbits <? 0 then 0 else if wbits >? 15 then 2 else 1.
Definition i_bad (level method wbits mem strategy : Z) : bool :=
  (mem <? 1) || (mem >? 9) || negb (method =? 8) || (i_wb wbits <? 8) || (i_wb wbits >? 15) ||
  (i_lv level <? 0) || (i_lv level >? 9) || (strategy <? 0) || (strategy >? 4) ||
  ((i_wb wbits =? 8) && negb (i_wr wbits =? 1)).
Definition i_wb9 (wbits : Z) : Z := if i_wb wbits =? 8 then 9 else i_wb wbits.

(** The state handed to deflateReset. *)
Definition i_state (level method wbits mem strategy : Z) : dstate :=
  let lit_bufsize := Z.shiftl 1 (mem + 6) in
  let s := init_dstate (i_wr wbits) (i_wb9 wbits) (mem + 7) lit_bufsize in
  let s := set_d_tr s (mkTS (tr_ltree (d_tr s)) (tr_dtree (d_tr s)) (tr_bltree (d_tr s)) 0 0 0 (tr_wk (d_tr s))
                            (tr_out (d_tr s)) 0 (u32 ((lit_bufsize - 1) * 3)) 0 lit_bufsize (i_lv level) strategy 0) in
  set_d_method s (u8 method).

Lemma end_finish s z : c_deflateEnd (set_d_status s FINISH_STATE) z = Some (None, z, Z_OK).
Proof. reflexivity. Qed.

Local Opaque c_deflateReset c_deflateEnd init_dstate.

Lemma init_wb_some wbits : -15 <= wbits ->
  (if wbits <? 0 then if wbits <? -15 then None else Some (- wbits, 0)
   else if wbits >? 15 then Some (wbits - 16, 2) else Some (wbits, 1)) = Some (i_wb wbits, i_wr wbits).
Proof.
  intros. unfold i_wb, i_wr. destruct (wbits <? 0) eqn:E.
  - rewrite (proj2 (Z.ltb_ge wbits (-15))) by lia. reflexivity.
  - destruct (wbits >? 15); reflexivity.
Qed.

Lemma init_bad_err level method wbits mem strategy a1 a2 a3 a4 a5 z :
  -15 <= wbits -> i_bad level method wbits mem strategy = true ->
  c_deflateInit2_ true true false level method wbits mem strategy a1 a2 a3 a4 a5 z =
  Some (None, set_z_msg z None, Z_STREAM_ERROR).
Proof.
  intros Hw Hb. unfold c_deflateInit2_. cbn [negb orb]. rewrite (init_wb_some wbits Hw).
  unfold i_bad, i_lv in Hb. unfold Z_DEFAULT_COMPRESSION, MAX_MEM_LEVEL, Z_DEFLATED, Z_FIXED. rewrite Hb. reflexivity.
Qed.

Lemma init_mem1 level method wbits mem strategy a2 a3 a4 a5 z :
  -15 <= wbits -> i_bad level method wbits mem strategy = false ->
  c_deflateInit2_ true true false level method wbits mem strategy false a2 a3 a4 a5 z =
  Some (None, set_z_msg z None, Z_MEM_ERROR).
Proof.
  intros Hw Hb. unfold c_deflateInit2_. cbn [negb orb]. rewrite (init_wb_some wbits Hw).
  unfold i_bad, i_lv in Hb. unfold Z_DEFAULT_COMPRESSION, MAX_MEM_LEVEL, Z_DEFLATED, Z_FIXED. rewrite Hb. reflexivity.
Qed.

Definition i_end_state (wbits mem : Z) : dstate :=
  set_d_status (init_dstate (i_wr wbits) (i_wb9 wbits) (mem + 7) (Z.shiftl 1 (mem + 6))) FINISH_STATE.

Lemma init_mem2 level method wbits mem strategy a2 a3 a4 a5 z :
  -15 <= wbits -> i_bad level method wbits mem strategy = false -> (a2 && a3 && a4 && a5) = false ->
  c_deflateInit2_ true true false level method wbits mem strategy true a2 a3 a4 a5 z =
  bind (c_deflateEnd (i_end_state wbits mem) (set_z_msg (set_z_msg z None) (Some Z_MEM_ERROR)))
       (fun '(os, z, _) => Some (os, z, Z_MEM_ERROR)).
Proof.
  intros Hw Hb Ha. unfold c_deflateInit2_. cbn [negb orb]. rewrite (init_wb_some wbits Hw).
  unfold i_bad, i_lv in Hb. unfold Z_DEFAULT_COMPRESSION, MAX_MEM_LEVEL, Z_DEFLATED, Z_FIXED. rewrite Hb.
  cbn [andb negb]. rewrite Ha. reflexivity.
Qed.

Lemma init_ok level method wbits mem strategy z :
  -15 <= wbits -> i_bad level method wbits mem strategy = false ->
  c_deflateInit2_ true true false level method wbits mem strategy true true true true true z =
  bind (c_deflateReset (i_state level method wbits mem strategy) (set_z_msg z None))
       (fun '(s, z, r) => Some (Some s, z, r)).
Proof.
  intros Hw Hb. unfold c_deflateInit2_. cbn [negb orb]. rewrite (init_wb_some wbits Hw).
  unfold i_bad, i_lv in Hb. unfold Z_DEFAULT_COMPRESSION, MAX_MEM_LEVEL, Z_DEFLATED, Z_FIXED. rewrite Hb.
  cbn [andb negb]. reflexivity.
Qed.
