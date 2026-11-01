(* Law inflate_check, main: the check `if (r == Z_STREAM_END && !raw) { s.total_out == tout; gzip: pos >= 18,
   le32(src + pos - 8) == rc, le32(src + pos - 4) == (tout & 0xffffffff), s.adler == rc; zlib: pos >= 6,
   be32(src + pos - 4) == ra, s.adler == ra }` (IKMainKit.v seg_L3 up to seg_L4); then seg_L4 (given). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessRef Zlib.proof.adler32.MainLib.
Require Zlib.proof.crc32.HarnessRef.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib Zlib.proof.harness.inflate_common.HarnessLe32.
Require Import Zlib.proof.harness.inflate_check.IKLawCS Zlib.proof.harness.inflate_check.IKGlobals
               Zlib.proof.harness.inflate_check.IKFacts.
Require Import Zlib.harness.x_inflate_check.code.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.inflate_check.IKMainKit.
Local Open Scope logic.

Ltac ifpostv t v := match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx [] (LOCALx (temp t v :: Q) (SEPx R))) end.
(* the argument src + pos - k *)
Ltac ptrk p k := entailer!; destruct p; try contradiction; simpl; f_equal;
  change (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr k))) with (Ptrofs.repr k);
  rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc; f_equal; rewrite <- Ptrofs.sub_add_opp; unfold Ptrofs.sub;
  rewrite !Ptrofs.unsigned_repr by rep_lia; reflexivity.

Ltac chk2_fin G := entailer!; unfold ik_gzv; rewrite G; replace (0 <=? _) with true by lia; reflexivity.

Ltac gpa := forward_call (Int.repr 1); [ solve [entailer!; try reflexivity] .. | ].

Lemma chk2_ok {Espec: OracleKind} gv vs vosn w srcp src adler0 pos' out' r stop ibp obp z' sp Rest
    (Post: ret_assert) :
  ik_mid_facts w srcp src adler0 pos' out' r z' ->
  semax Delta_m (ik_mid gv vs vosn w srcp src adler0 pos' out' r stop ibp obp z' sp Rest) seg_L4 Post ->
  semax Delta_m (ik_mid gv vs vosn w srcp src adler0 pos' out' r stop ibp obp z' sp Rest) seg_L3 Post.
Proof.
  intros MF H4.
  unfold seg_L3.
  eapply semax_seq; [ | exact H4].
  unfold ik_mid.
  destruct Post as [Pn Pb Pc Pr]. unfold overridePost.
  abbreviate_semax.
  destruct MF as (Hw & Hpos & Hn & Hsb & Psrc & Ha0 & Hob & Hz & Hr & Hraw & Hhdr & Hchk & Hend).
  destruct (Z.eq_dec r 1) as [R1 | R1]; [destruct (Z_lt_dec w 0) as [W0 | W0] | ].
  - ifpostv _t'27 (Vint Int.zero).
    + forward. entailer!. unfold ik_raw. destruct (w <? 0) eqn:E; [reflexivity | lia].
    + exfalso. auto.
    + forward_if.
      { exfalso. auto. }
      { forward. entailer!. }
  - ifpostv _t'27 (Vint Int.one).
    + forward. entailer!. unfold ik_raw. destruct (w <? 0) eqn:E; [lia | reflexivity].
    + exfalso. auto.
    + forward_if; [ | exfalso; apply Int.one_not_zero; assumption].
      subst r. destruct (Hend ltac:(lia) eq_refl) as [Htout Htr].
      specialize (Hchk ltac:(lia) (or_intror eq_refl)).
      forward.
      forward_call (Int.repr 1).
      { entailer!. rewrite Htout. rewrite <- Int64.unsigned_repr_eq, Int64.repr_unsigned, Int64.eq_true. reflexivity. }
      unfold ik_gzv. replace (0 <=? w) with true by lia.
      unfold ik_trailer in Htr. unfold ik_chk in Hchk.
      destruct (ik_gz w src) eqn:G.
      * destruct Htr as (H18 & Hc & Hl).
        forward_if.
        2: { exfalso. apply Int.one_not_zero. assumption. }
        forward_call (Int.repr 1).
        { entailer!. unfold Int.ltu. rewrite !Int.unsigned_repr by rep_lia.
          destruct (zlt pos' 18); [lia | reflexivity]. }
        rewrite <- (ik_bytes_adler_cs Ews (Zlength src) (bytes_rep src) srcp).
        forward_call (offset_val (pos'-8) srcp, Ews, srcp, pos'-8, Zlength src, bytes_rep src, sublist (pos'-8) (pos'-4) src).
        { ptrk srcp 8. }
        { unfold cbuf_ok. split3; [reflexivity | auto with share | ]. split3; [lia | lia | ].
          split3; [rewrite Zlength_sublist by lia; lia | apply is_bytes_sublist; auto | rewrite sublist_bytes_rep; f_equal; f_equal; lia]. }
        rewrite Hc.
        forward_call (Int.repr 1).
        { entailer!. rewrite Int64.eq_true. reflexivity. }
        forward_call (offset_val (pos'-4) srcp, Ews, srcp, pos'-4, Zlength src, bytes_rep src, sublist (pos'-4) pos' src).
        { ptrk srcp 4. }
        { unfold cbuf_ok. split3; [reflexivity | auto with share | ]. split3; [lia | lia | ].
          split3; [rewrite Zlength_sublist by lia; lia | apply is_bytes_sublist; auto | rewrite sublist_bytes_rep; f_equal; f_equal; lia]. }
        rewrite Hl.
        forward_call (Int.repr 1).
        { entailer!. change (Int.unsigned (Int.repr (-1))) with (Z.ones 32). rewrite Z.land_ones by lia.
          rewrite Int64.eq_true. reflexivity. }
        try rewrite (ik_bytes_adler_cs Ews (Zlength src) (bytes_rep src) srcp).
        forward.
        forward_call (Int.repr 1).
        { entailer!. rewrite Hchk, Int64.eq_true. reflexivity. }
        chk2_fin G.
      * destruct Htr as (H6 & Hb).
        forward_if.
        { exfalso. match goal with X: _ <> Int.zero |- _ => apply X; reflexivity end. }
        forward_call (Int.repr 1).
        { entailer!. unfold Int.ltu. rewrite !Int.unsigned_repr by rep_lia.
          destruct (zlt pos' 6); [lia | reflexivity]. }
        rewrite <- (ik_bytes_adler_cs Ews (Zlength src) (bytes_rep src) srcp).
        forward_call (offset_val (pos'-4) srcp, Ews, srcp, pos'-4, Zlength src, bytes_rep src, sublist (pos'-4) pos' src).
        { ptrk srcp 4. }
        { unfold cbuf_ok. split3; [reflexivity | auto with share | ]. split3; [lia | lia | ].
          split3; [rewrite Zlength_sublist by lia; lia | apply is_bytes_sublist; auto | rewrite sublist_bytes_rep; f_equal; f_equal; lia]. }
        rewrite Hb.
        forward_call (Int.repr 1).
        { entailer!. rewrite Int64.eq_true. reflexivity. }
        try rewrite (ik_bytes_adler_cs Ews (Zlength src) (bytes_rep src) srcp).
        forward.
        forward_call (Int.repr 1).
        { entailer!. rewrite Hchk, Int64.eq_true. reflexivity. }
        chk2_fin G.
  - ifpostv _t'27 (Vint Int.zero).
    + exfalso. auto.
    + forward. entailer!.
    + forward_if.
      { exfalso. auto. }
      { forward. entailer!. }
Qed.
