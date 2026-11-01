(* Law inflate_dict, main encoder half: the block loop (the stored / fixed branches, the symbol loop of a fixed
   block), from the segment lemmas of the stored block, the literal and the back-reference. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessRef Zlib.proof.adler32.HarnessBytes
               Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_common.DRefSpec.
Require Import Zlib.proof.harness.inflate_dict.ITLawCS Zlib.proof.harness.inflate_dict.ITGlobals
               Zlib.proof.harness.inflate_dict.ITFacts Zlib.proof.harness.inflate_dict.ITMainKit
               Zlib.proof.harness.inflate_dict.ITEncKit.
Require Import Zlib.harness.x_inflate_dict.code.
Require Import Zlib.proof.crc32.Spec.

Lemma Zlength_pack B : Zlength (pack B) = (Zlength B + 7) / 8.
Proof.
  unfold pack. rewrite Zlength_map, Zlength_correct, length_seq.
  rewrite Z2Nat.id; [auto | ]. pose proof (Zlength_nonneg B). apply Z.div_pos; lia.
Qed.

Lemma bw_at_fold sh bsh B cap buf w c :
  bw_bytes_ok B cap c ->
  data_at sh (Tstruct _bw noattr) (buf, (Vint (Int.repr (Zlength B / 8)), Vint (Int.repr (Zlength B mod 8)))) w *
  data_at bsh (tarray tuchar cap) c buf |-- bw_at sh bsh B cap buf w.
Proof. intros H. rewrite bw_at_law. Exists c. entailer!. Qed.

(* the room left in the bit writer: |B| / 8 <= cap *)
Lemma bw_ok_len B cap c : bw_bytes_ok B cap c -> Zlength B / 8 <= cap.
Proof.
  intros (_ & H & _). rewrite Zlength_pack in H. pose proof (Zlength_nonneg B).
  assert (Zlength B / 8 <= (Zlength B + 7) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.

Lemma bits_le_len v n : 0 <= n -> Zlength (bits_le v n) = n.
Proof. intros. unfold bits_le. rewrite Zlength_map, Zlength_correct, length_seq. lia. Qed.

Lemma room_le x k : 0 <= x -> 0 <= k -> (x + k + 7) / 8 <= x / 8 + (k + 7) / 8 + 1.
Proof. intros. Z.div_mod_to_equations. lia. Qed.

(* the rest of the symbol loop's ret_assert (break: the room after the loop) *)
Definition X_sym (E: ectx) (bs: list block) (last: Z) : ret_assert :=
  overridePost (EX syms0: list sym, EX d0: list val, sym_room E bs last syms0 d0)
    (normal_ret_assert (EX b: block, EX dcont': list val, blk_done E bs last b dcont')).

Lemma fixed_block_bits E bs last syms p : last = 0 \/ last = 1 ->
  sym_bits E bs last syms ++ send_sym fixed_ll 256 = blk_bits E bs ++ enc_block p (last =? 1) (Fixed syms).
Proof.
  intros Hl. unfold sym_bits, enc_block, send_syms. rewrite <- !app_assoc. f_equal.
  destruct Hl; subst; reflexivity.
Qed.

Lemma end_bits E bs b :
  blk_bits E bs ++ enc_block (Zlength (enc_nf 0 bs)) (1 =? 1) b = bytes_bits (hdr_bytes E) ++ enc_blocks 0 (bs ++ [b]).
Proof. unfold blk_bits. rewrite enc_blocks_snoc, <- app_assoc. reflexivity. Qed.

Lemma nf_bits E bs b :
  blk_bits E bs ++ enc_block (Zlength (enc_nf 0 bs)) (0 =? 1) b = blk_bits E (bs ++ [b]).
Proof. unfold blk_bits. rewrite enc_nf_snoc, <- app_assoc. reflexivity. Qed.

Lemma enc_ok_snoc E bs b :
  enc_ok E bs -> nondyn b -> block_ok (2 ^ e_wb E) (expand (e_dict E) bs) b -> enc_ok E (bs ++ [b]).
Proof.
  intros [H1 H2] H3 H4. split.
  - apply Forall_app. split; auto.
  - apply blocks_ok_snoc. auto.
Qed.

Lemma seg_loop_ok {Espec: OracleKind} :
  seg_stored_stmt ->
  (forall E bs last syms dcont,
     semax Delta_m (sym_room E bs last syms dcont) seg_lit (normal_ret_assert (sym_inv E bs last))) ->
  seg_ref_stmt ->
  forall E, (forall bs dcont, semax Delta_m (blk_end E bs dcont) S_trl POST_m) ->
  semax Delta_m (blk_inv E) S_loop POST_m.
Proof.
  intros HS HL HR E KT.
  rewrite S_loop_eq.
  forward_loop (blk_inv E) break: (EX bs: list block, EX dcont: list val, blk_end E bs dcont).
  { apply ENTAIL_refl. }
  { unfold blk_inv. Intros bs dcont. unfold seg_blk.
    unfold blk_at. Intros.
    forward_call tt. Intros more.
    forward_call tt. Intros btype.
    forward.
    rewrite bw_at_law. Intros wc.
    forward.
    pose proof (bw_ok_len _ _ _ H4) as HL4.
    assert (0 <= Zlength (blk_bits E bs) / 8) by (apply Z.div_pos; [apply Zlength_nonneg | lia]).
    forward_call (Int.repr (if Zlength (blk_bits E bs) / 8 + 8 <=? 2 ^ 19 then 1 else 0)).
    { entailer!. change (Int.shl (Int.repr 1) (Int.repr 19)) with (Int.repr (2 ^ 19)).
      change (let (q, _) := Z.div_eucl (Zlength (blk_bits E bs)) 8 in q) with (Zlength (blk_bits E bs) / 8).
      set (q := Zlength (blk_bits E bs) / 8) in *. clearbody q. arg_cmp. }
    assumed. apply Z.leb_le in E0.
    sep_apply (bw_at_fold Tsh Ews (blk_bits E bs) (2 ^ 19) (e_srcp E) (e_vw E) wc H4).
    set (lastz := Z.b2z (zeq more 0)).
    assert (Hlast: lastz = 0 \/ lastz = 1) by (unfold lastz; destruct (zeq more 0); simpl; auto).
    clearbody lastz.
    forward_call (Tsh, Ews, blk_bits E bs, 2 ^ 19, e_srcp E, e_vw E, lastz, 1).
    { unfold bw_room. repeat split; try lia; try rep_lia.
      assert ((Zlength (blk_bits E bs) + 1 + 7) / 8 = Zlength (blk_bits E bs) / 8 + 1) as ->.
      { replace (Zlength (blk_bits E bs) + 1 + 7) with (Zlength (blk_bits E bs) + 1 * 8) by lia. apply Z.div_add. lia. }
      lia. }
    forward_if (EX b: block, EX dcont': list val, blk_done E bs lastz b dcont').
    { unfold abbreviate in POSTCONDITION, MORE_COMMANDS. subst POSTCONDITION MORE_COMMANDS.
      eapply semax_pre; [ | eapply semax_post; [ | | | | apply (HS E bs dcont lastz (normal_ret_assert FF)) ] ].
      - unfold blk_mid. entailer!.
      - simpl RA_normal. apply andp_left2. intros rho. apply exp_left; intro l. apply exp_left; intro d.
        apply (exp_right (Stored l)). apply (exp_right d). apply derives_refl.
      - simpl RA_break. apply andp_left2. apply derives_refl.
      - simpl RA_continue. apply andp_left2. apply derives_refl.
      - intros vl. simpl RA_return. apply andp_left2. apply derives_refl. }
    { (* a fixed block *)
      forward_call (Tsh, Ews, blk_bits E bs ++ bits_le lastz 1, 2 ^ 19, e_srcp E, e_vw E, 1, 2).
      { unfold bw_room. rewrite Zlength_app, bits_le_len by lia.
        pose proof (room_le (Zlength (blk_bits E bs)) 3 (Zlength_nonneg _) ltac:(lia)).
        change ((3 + 7) / 8) with 1 in *.
        replace (Zlength (blk_bits E bs) + 1 + 2 + 7) with (Zlength (blk_bits E bs) + 3 + 7) by lia.
        repeat split; try lia; rep_lia. }
      replace ((blk_bits E bs ++ bits_le lastz 1) ++ bits_le 1 2) with (sym_bits E bs lastz [])
        by (unfold sym_bits; simpl flat_map; rewrite app_nil_r, app_assoc; auto).
      forward_loop (sym_inv E bs lastz) break: (EX syms: list sym, EX d: list val, sym_room E bs lastz syms d).
      { unfold sym_inv. Exists (@nil sym) dcont. unfold sym_at, edata. rewrite data_fixed_nil.
        unfold edata in H1. entailer!. }
      { unfold sym_inv, sym_at. Intros syms d.
        forward.
        forward_call tt. Intros kind.
        rewrite bw_at_law. Intros wc2.
        match goal with Hw: bw_bytes_ok (sym_bits _ _ _ _) _ wc2 |- _ => rename Hw into Hwc2 end.
        forward.
        pose proof (bw_ok_len _ _ _ Hwc2) as HL9.
        assert (0 <= Zlength (sym_bits E bs lastz syms) / 8) by (apply Z.div_pos; [apply Zlength_nonneg | lia]).
        forward_call (Int.repr (if Zlength (sym_bits E bs lastz syms) / 8 + 8 <=? 2 ^ 19 then 1 else 0)).
        { entailer!. change (Int.shl (Int.repr 1) (Int.repr 19)) with (Int.repr (2 ^ 19)).
          change (let (q, _) := Z.div_eucl (Zlength (sym_bits E bs lastz syms)) 8 in q)
            with (Zlength (sym_bits E bs lastz syms) / 8).
          set (q := Zlength (sym_bits E bs lastz syms) / 8) in *. clearbody q. arg_cmp. }
        assumed. apply Z.leb_le in E1.
        sep_apply (bw_at_fold Tsh Ews (sym_bits E bs lastz syms) (2 ^ 19) (e_srcp E) (e_vw E) wc2 Hwc2).
        ifsame.
        { forward. Exists syms d. unfold sym_room. entailer!. }
        { forward. entailer!. }
        forward_if.
        { unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS.
          eapply semax_pre; [ | apply (HL E bs lastz syms d) ]. unfold sym_room. entailer!. }
        { unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
          eapply semax_pre; [ | eapply semax_post; [ | | | | apply (HR E bs lastz syms d (X_sym E bs lastz)) ] ].
          - unfold sym_room. entailer!.
          - apply andp_left2. apply derives_refl.
          - apply andp_left2. apply derives_refl.
          - apply andp_left2. apply derives_refl.
          - intros vl. apply andp_left2. apply derives_refl. } }
      Intros syms d. unfold sym_room. Intros.
      forward_call (Tsh, Ews, sym_bits E bs lastz syms, 2 ^ 19, e_srcp E, e_vw E, 256).
      { unfold bw_room.
        pose proof (room_le (Zlength (sym_bits E bs lastz syms)) 9 (Zlength_nonneg _) ltac:(lia)).
        change ((9 + 7) / 8) with 2 in *. repeat split; try lia; rep_lia. }
      Exists (Fixed syms) d. unfold blk_done.
      rewrite (fixed_block_bits E bs lastz syms (Zlength (enc_nf 0 bs)) Hlast).
      entailer!. }
    Intros b d'. unfold blk_done. Intros.
    forward_if.
    { forward. assert (lastz = 1) as -> by (destruct Hlast; subst; auto; contradiction).
      Exists (bs ++ [b]) d'. unfold blk_end. rewrite end_bits.
      entailer!. split; [destruct bs; discriminate | apply enc_ok_snoc; auto]. }
    { forward. assert (lastz = 0) as -> by (destruct Hlast; subst; auto; discriminate).
      Exists (bs ++ [b]) d'. unfold blk_at. rewrite nf_bits.
      entailer!. apply enc_ok_snoc; auto. } }
  { Intros bs dcont. apply KT. }
Qed.
