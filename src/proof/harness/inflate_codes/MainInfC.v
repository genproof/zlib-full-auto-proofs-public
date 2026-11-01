(* Law inflate_codes, main, branch `op >= 24`, part C (MainInfKit.v): the updates of final and in_dict, pos += used. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessRef Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_codes.LawCS Zlib.proof.harness.inflate_codes.Globals
               Zlib.proof.harness.inflate_codes.Facts Zlib.proof.harness.inflate_codes.MainKit.
Require Import Zlib.harness.x_inflate_codes.code.
Require Import Zlib.proof.harness.inflate_codes.MainInfKit.

Lemma mic_eq r c: Int.min_signed <= r <= Int.max_signed -> Int.min_signed <= c <= Int.max_signed ->
  Int.eq (Int.repr r) (Int.repr c) = (r =? c).
Proof.
  intros. destruct (Z.eqb_spec r c).
  - subst. apply Int.eq_true.
  - apply Int.eq_false. intro E. apply repr_inj_signed in E; auto.
Qed.

Ltac mic_repl t v Q :=
  match Q with
  | temp t _ :: ?Q' => constr:(temp t v :: Q')
  | ?x :: ?Q' => let Q'' := mic_repl t v Q' in constr:(x :: Q'')
  end.

Ltac mic_cases r :=
  repeat rewrite mic_eq by rep_lia; cbn [Z.opp] in *;
  repeat match goal with |- context [r =? ?c] => destruct (Z.eqb_spec r c) end;
  simpl; first [reflexivity | exfalso; lia].

Ltac mic_absurd := exfalso;
  match goal with
  | X: Int.repr 0 <> Int.zero |- _ => apply X; reflexivity
  | X: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact X
  end.

Ltac mic_fin r :=
  unfold final_after, indict_after in *; unfold Z_STREAM_END, Z_DATA_ERROR, Z_MEM_ERROR, Z_NEED_DICT in *;
  repeat rewrite mic_eq by rep_lia; cbn [Z.opp] in *;
  repeat match goal with
   | |- context [r =? ?c] => destruct (Z.eqb_spec r c)
   | H: context [r =? ?c] |- _ => destruct (Z.eqb_spec r c)
   end;
  cbn [orb negb Z.b2z] in *; subst; first [reflexivity | exfalso; lia | mic_absurd].

Lemma mi_C_ok {Espec: OracleKind} gv vs vo vosn vb vdl w srcp src pos final indict ain aout flush innull outnull
    stop ibp obp r z' sp Rest (Post: ret_assert) :
  mi_facts w src pos final indict ain aout flush innull outnull r z' ->
  semax Delta_m
    (mi_pre_B gv vs vo vosn vb vdl w srcp src pos final indict ain aout innull outnull stop ibp obp r z' sp Rest)
    seg_inf_C
    (overridePost
       (mi_post_C gv vs vo vosn vb vdl w srcp src (pos + (ain - zf_ai z'))
          (final_after (mi_bad innull outnull ain) final r) (indict_after (mi_bad innull outnull ain) indict r)
          stop ibp obp z' sp Rest)
       Post).
Proof.
  intros MF.
  unfold mi_facts in MF. cbv zeta in MF.
  destruct MF as (Hw & Hpos & Hain & Hpa & Hsrc & Hsb & Haout & Hfl & Hin & Hout & Hfr & Hidr & Hz' & Hcode & Hai & Hao
                  & Hbad & Hok & Hbuf & Hdata & Hfin & Hnd).
  assert (Hr: -5 <= r <= 2).
  { unfold code_okb in Hcode. repeat rewrite orb_true_iff in Hcode.
    repeat match goal with H: _ \/ _ |- _ => destruct H end; apply Z.eqb_eq in H; subst; cbv; split; congruence. }
  unfold mi_pre_B, seg_inf_C, mi_post_C.
  destruct Post as [Pn Pb Pc Pr]. unfold overridePost.
  destruct (mi_bad innull outnull ain) eqn:EB.
  - ifsame.
    + exfalso. match goal with X: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact X end.
    + forward. entailer!.
    + forward. unfold final_after, indict_after. entailer!.
  - match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
      let Q1 := mic_repl _final (Vint (Int.repr (final_after false final r))) Q in
      let Q2 := mic_repl _in_dict (Vint (Int.repr (indict_after false indict r))) Q1 in
      forward_if (PROPx [] (LOCALx Q2 (SEPx R))) end.
    + ifpost _t'49 (Int.repr (if orb (r =? 1) (r =? -3) then 1 else 0)).
      * forward. entailer!; mic_cases r.
      * forward. entailer!; mic_cases r.
      * ifpost _t'50 (Int.repr (if orb (orb (r =? 1) (r =? -3)) (r =? -4) then 1 else 0)).
        { forward. entailer!. destruct (orb (r =? 1) (r =? -3)); [reflexivity | mic_absurd]. }
        { forward. entailer!. destruct (orb (r =? 1) (r =? -3)) eqn:E; [mic_absurd | ]. simpl. mic_cases r. }
        match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
          let Q1 := mic_repl _final (Vint (Int.repr (final_after false final r))) Q in
          forward_if (PROPx [] (LOCALx Q1 (SEPx R))) end.
        { forward. entailer!. mic_fin r. }
        { forward. entailer!. mic_fin r. }
        forward. entailer!. mic_fin r.
    + exfalso. apply H; reflexivity.
    + forward. entailer!.
Qed.
