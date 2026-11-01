(* Law inflate_reset, main: one iteration of the loop (IRMainKit.seg_loop): the nondet draws, the four objects
   (exact_copy x2, exact_space x2), a's inflate() call (IRFacts.rf_inflate1 in phase 1), phase 2's part
   (ph2_stmt), pos += used, the six free()s, `if (stop == 0) { if (phase == 2) break; <reset> }` (rst_stmt).
   The parts' statements are hypotheses (proved in IRMainPh2.v / IRMainRst.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_reset.IRLawCS Zlib.proof.harness.inflate_reset.IRGlobals
               Zlib.proof.harness.inflate_reset.IRFacts Zlib.proof.harness.inflate_reset.IRMainKit.
Require Import Zlib.harness.x_inflate_reset.code.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.adler32.Ptr.
Require Import Zlib.proof.harness.inflate_reset.IRMainLoopKit Zlib.proof.harness.inflate_reset.IRMainLoopCall
               Zlib.proof.harness.inflate_reset.IRMainLoopTail.

Lemma loop_of : ph2_stmt -> rst_stmt -> loop_stmt.
Proof.
  intros PH2 RST. unfold loop_stmt. intros Espec I1 I2 gv va vb vsa vsb w srcp src rb ph pos w2 za La zb Lb GF.
  unfold seg_loop, Delta_m, Gmain_k, POST_m. simplify_func_tycontext. abbreviate_semax.
  unfold inv_at. Intros.
  pose proof GF as GF0. destruct GF as (RF & Wok & Hw & Hn & Hsb & Psrc & Hrb).
  forward_call tt. Intros nlim.
  forward_call tt. Intros aout.
  forward_call tt. Intros flu.
  forward_call tt. Intros wsl.
  forward_call tt. Intros stop.
  forward_call tt. Intros how.
  assert (Ef: Int.repr flu = Int.repr (Int.signed (Int.repr flu))) by (rewrite Int.repr_signed; auto).
  rewrite Ef. clear Ef. set (flush := Int.signed (Int.repr flu)).
  assert (Hfl: Int.min_signed <= flush <= Int.max_signed) by apply Int.signed_range. clearbody flush.
  assert (Ew: Int.repr wsl = Int.repr (Int.signed (Int.repr wsl))) by (rewrite Int.repr_signed; auto).
  rewrite Ew. clear Ew. set (wsel := Int.signed (Int.repr wsl)).
  assert (Hws: Int.min_signed <= wsel <= Int.max_signed) by apply Int.signed_range. clearbody wsel.
  ifpost _t'11 (Int.repr (if andb (pos <=? nlim) (nlim <=? Zlength src) then 1 else 0)).
  { forward. entailer!. arg_cmp. }
  { forward. entailer!. arg_cmp. }
  forward_call (Int.repr (if andb (pos <=? nlim) (nlim <=? Zlength src) then 1 else 0)).
  assumed. apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
  forward_call (Int.repr (if aout <=? 2 ^ 20 then 1 else 0)).
  { entailer!. arg_cmp. }
  assumed. apply Z.leb_le in E.
  forward.
  rewrite sub_repr. set (ain := nlim - pos).
  assert (Hain: 0 <= ain /\ pos + ain <= Zlength src) by (subst ain; lia). clearbody ain.
  forward_call (offset_val pos srcp, Ews, srcp, pos, Zlength src, bytes_rep src, ain,
                sublist pos (pos + ain) src, gv).
  { rewrite bytes_adler_cs. cancel. }
  { apply cbuf_ok_slice; auto; lia. }
  Intros iap.
  forward_call (offset_val pos srcp, Ews, srcp, pos, Zlength src, bytes_rep src, ain,
                sublist pos (pos + ain) src, gv).
  { apply cbuf_ok_slice; auto; lia. }
  Intros ibp.
  forward_call (aout, vsa, Tsh, gv).
  { rewrite ptr_adler_cs_. cancel. }
  Intros vret. destruct vret as [[oap qa] bsa]. simpl fst in *. simpl snd in *.
  forward_call (aout, vsb, Tsh, gv).
  { rewrite ptr_adler_cs_. cancel. }
  Intros vret. destruct vret as [[obp qb] bsb]. simpl fst in *. simpl snd in *.
  rewrite !ptr_adler_cs.
  destruct (eq_dec iap nullval) as [N1|N1].
  { subst iap.
    ifpost _t'16 (Int.repr 1). { forward. entailer!. } { infeas. }
    ifpost _t'17 (Int.repr 1). { forward. entailer!. } { infeas. }
    ifpost _t'18 (Int.repr 1). { forward. entailer!. } { infeas. }
    forward_if. { ret0m. } { infeas. } }
  destruct (eq_dec iap nullval); [contradiction | ]. Intros.
  assert_PROP (isptr iap) as Piap by fcp iap.
  rewrite (bytes_adler_cs Ews ain _ iap), (tok_adler_cs Ews ain iap).
  destruct (eq_dec ibp nullval) as [N2|N2].
  { subst ibp.
    ifpost _t'16 (Int.repr 1). { infeas. } { forward. cmpz. }
    ifpost _t'17 (Int.repr 1). { forward. entailer!. } { infeas. }
    ifpost _t'18 (Int.repr 1). { forward. entailer!. } { infeas. }
    forward_if. { ret0m. } { infeas. } }
  destruct (eq_dec ibp nullval); [contradiction | ]. Intros.
  assert_PROP (isptr ibp) as Pibp by fcp ibp.
  rewrite (bytes_adler_cs Ews ain _ ibp), (tok_adler_cs Ews ain ibp).
  destruct (eq_dec oap nullval) as [N3|N3].
  { subst oap. rewrite (H10 eq_refl) in *.
    ifpost _t'16 (Int.repr 0). { infeas. } { forward. cmpz. }
    ifpost _t'17 (Int.repr 1). { infeas. } { forward. cmpz. }
    ifpost _t'18 (Int.repr 1). { forward. entailer!. } { infeas. }
    forward_if. { ret0m. } { infeas. } }
  Intros. assert_PROP (isptr oap) as Poap by fcp oap.
  rewrite (bytes_adler_cs Ews aout _ oap), (tok_adler_cs Ews aout oap),
    (bytes_adler_cs Ews aout _ qa), (tok_adler_cs Ews aout qa).
  destruct (eq_dec obp nullval) as [N4|N4].
  { subst obp. rewrite (H13 eq_refl) in *.
    ifpost _t'16 (Int.repr 0). { infeas. } { forward. cmpz. }
    ifpost _t'17 (Int.repr 0). { infeas. } { forward. cmpz. }
    ifpost _t'18 (Int.repr 1). { infeas. } { forward. cmpz. }
    forward_if. { ret0m. } { infeas. } }
  Intros. assert_PROP (isptr obp) as Pobp by fcp obp.
  rewrite (bytes_adler_cs Ews aout _ obp), (tok_adler_cs Ews aout obp),
    (bytes_adler_cs Ews aout _ qb), (tok_adler_cs Ews aout qb).
  ifpost _t'16 (Int.repr 0). { infeas. } { forward. cmpz. }
  ifpost _t'17 (Int.repr 0). { infeas. } { forward. cmpz. }
  ifpost _t'18 (Int.repr 0). { infeas. } { forward. cmpz. }
  forward_if. { infeas. }
  assert_PROP (isptr va /\ isptr vb) as Pv by entailer!. destruct Pv as [Pva Pvb].
  assert_PROP (isptr qa) as Pqa by fcp qa.
  assert_PROP (isptr qb) as Pqb by fcp qb.
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply (call_of I1 I2 gv va vb vsa vsb w srcp src rb ph pos w2 aout flush wsel stop how ain
                                 iap ibp oap obp qa qb bsa bsb za La zb Lb PH2 (tail_of RST)) ].
  { unfold call_pre. entailer!. }
  unfold call_facts. repeat match goal with |- _ /\ _ => split end; auto; try rep_lia.
Qed.
