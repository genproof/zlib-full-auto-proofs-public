(* Law uncompress_any, main: seg_rest (UAMainKit.v): d2 = exact_space(cap, &snap2) (NULL: return 0);
   dlen2 = cap; r2 = uncompress(d2, &dlen2, src, n); if (r2 != Z_MEM_ERROR) gp_assert(r2 == Z_OK && dlen2 == dlen
   && bytes_same(d2, dst, dlen)).  The call of uncompress at the uncompr unit's compspecs: as uncompress2's in
   UAMain.v (ua_bytes_uncompr & co. before, ua_law after; ua_ig_to for inflate_globals). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.HarnessRef
               Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.uncompr.USpec5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.uncompress_any.UALawCS Zlib.proof.harness.uncompress_any.UAGlobals
               Zlib.proof.harness.uncompress_any.UAFacts.
Require Import Zlib.harness.x_uncompress_any.code.
Require Import Zlib.proof.harness.uncompress_any.UAMainKit.
Local Open Scope logic.

Lemma ua_rest_slice (c: list val) cap out:
  Zlength out <= cap -> sublist 0 (0 + Zlength out) (dest_after c cap out) = bytes_rep out.
Proof.
  intros Hc. pose proof (Zlength_nonneg out). unfold dest_after. rewrite Z.add_0_l.
  rewrite sublist_app1 by (rewrite ?Zlength_byte_vals; lia).
  rewrite sublist_same; [reflexivity | lia | rewrite Zlength_byte_vals; lia].
Qed.

Lemma ua_rest_ok {Espec: OracleKind} gv vsnap vdlen vslen vsnap2 vdlen2 srcp src dstp snapq cap bs slen dlen out :
  ua_ok_facts srcp src dstp cap bs slen dlen out ->
  semax Delta_m (ua_okpre gv vsnap vdlen vslen vsnap2 vdlen2 srcp src dstp snapq cap bs slen dlen out) seg_rest
    (overridePost (ua_join gv vsnap vdlen vslen vsnap2 vdlen2) POST_m).
Proof.
  intros F. unfold ua_okpre, seg_rest.
  destruct F as (Hsb & Hsn & Hcap & Hbs & Hbsb & Pdst & Psrc & Hslen & Hdlen & Hdc & Hob & H6 & Hhdr & Hbe & Hrel).
  rewrite <- (ua_ptr_adler_ Tsh vsnap2).
  forward_call (cap, vsnap2, Tsh, gv).
  Intros vret. destruct vret as [[d2 q2] bs2]. simpl fst in *; simpl snd in *.
  destruct (eq_dec d2 nullval) as [PD|PD].
  { subst d2. forward_if. { ret0. } { contradiction. } }
  Intros.
  forward_if.
  { eapply (@malloc_test_eq Zlib.units.Adler32.CS _ (Zlength bs)); [rep_lia|].
    sep_apply (@data_at_data_at_ Zlib.units.Adler32.CS Ews (tarray tuchar (Zlength bs)) (bytes_rep bs2) d2). cancel. }
  { contradiction. }
  Intros. ua_law.
  forward.
  rewrite !Int.unsigned_repr by rep_lia.
  assert_PROP (isptr d2) as Pd2 by entailer!.
  rewrite <- (ua_bytes_uncompr Ews cap (bytes_rep bs2) d2), <- (ua_tok_uncompr Ews cap d2),
          <- (ua_bytes_uncompr Ews (Zlength src) (bytes_rep src) srcp), <- (ua_tok_uncompr Ews (Zlength src) srcp),
          <- (ua_ulong_uncompr Tsh _ vdlen2).
  forward_call (gv, Ews, d2, cap, bytes_rep bs2, cap, vdlen2, true, true,
                Ews, srcp, Zlength src, bytes_rep src, src, Ers, Ers).
  { rewrite !Zlength_bytes_rep, sublist_same by (rewrite ?Zlength_bytes_rep; lia). auto. }
  Intros vret. destruct vret as [[[r2 slen2] dlen2] out2]. simpl fst in *; simpl snd in *.
  ua_law.
  destruct (Z.eq_dec r2 Z_MEM_ERROR) as [RM|RM].
  { subst r2. forward_if. { discriminate. }
    unfold abbreviate in POSTCONDITION. subst POSTCONDITION.
    eapply semax_pre; [| apply semax_skip].
    change (RA_normal _) with (ua_join gv vsnap vdlen vslen vsnap2 vdlen2).
    unfold ua_join. entailer!. }
  destruct (Hrel _ _ _ _ H3 RM) as (-> & -> & ->).
  forward_if; [| discriminate].
  forward_if (temp _t'18 (Vint (Int.repr 1))).
  { forward. forward. forward. destruct (zeq dlen dlen); [|congruence]. entailer!. }
  { exfalso. apply H5. reflexivity. }
  forward_if (temp _t'19 (Vint (Int.repr 1))).
  { forward.
    rewrite <- (ua_bytes_adler Ews cap _ d2), <- (ua_bytes_adler Ews cap _ dstp).
    forward_call (d2, Ews, d2, 0, cap, dest_after (bytes_rep bs2) cap out, out,
                  dstp, Ews, dstp, 0, cap, dest_after (bytes_rep bs) cap out, out, dlen).
    { unfold cbuf_ok. subst dlen. rewrite !isptr_offset_val_zero by auto.
      repeat split; try apply ua_rest_slice; auto; try lia. }
    ua_law. destruct (list_eq_dec Z.eq_dec out out); [|congruence].
    forward. entailer!. }
  { discriminate. }
  forward_call (Int.repr 1).
  change (RA_normal _) with (ua_join gv vsnap vdlen vslen vsnap2 vdlen2).
  unfold ua_join. entailer!.
Qed.
