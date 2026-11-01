(** * deflate(): the zlib header stage (e9, [if (s->status == INIT_STATE) { ... }]) against its model [c_zlib2]. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.DeflateKit.
#[export] Existing Instance DCS.CS.
Open Scope cmodel_scope.

(** ** The zlib header, computed as the C does *)
Definition lflags (s : dstate) : Z :=
  if orb (d_strategy s >=? Z_HUFFMAN_ONLY) (d_level s <? 2) then 0
  else if d_level s <? 6 then 1 else if d_level s =? 6 then 2 else 3.

Definition hdr0 (s : dstate) : Z := u32 (Z.shiftl (u32 (Z_DEFLATED + u32 (Z.shiftl (u32 (d_w_bits s - 8)) 4))) 8).
Definition hdr1 (s : dstate) : Z := Z.lor (hdr0 s) (Z.shiftl (lflags s) 6).
Definition hdr2 (s : dstate) : Z := if d_strstart s =? 0 then hdr1 s else Z.lor (hdr1 s) PRESET_DICT.

Lemma zlib_header_eq s : zlib_header s = u32 (hdr2 s + u32 (31 - hdr2 s mod 31)).
Proof. reflexivity. Qed.

Lemma shl_repr a k : 0 <= k < 32 -> Int.shl (Int.repr a) (Int.repr k) = Int.repr (Z.shiftl (u32 a) k).
Proof.
  intros Hk. unfold Int.shl. rewrite !Int.unsigned_repr_eq. unfold u32.
  rewrite (Z.mod_small k) by (unfold Int.modulus, two_power_nat; simpl; lia). reflexivity.
Qed.

Lemma or_repr a b : Int.or (Int.repr a) (Int.repr b) = Int.repr (Z.lor (u32 a) (u32 b)).
Proof. unfold Int.or. rewrite !Int.unsigned_repr_eq. reflexivity. Qed.

Lemma u32_add_u32 a b : u32 (a + u32 b) = u32 (a + b).
Proof. unfold u32. rewrite Zplus_mod_idemp_r. reflexivity. Qed.

Lemma hdr0_int w : Int.shl (Int.add (Int.repr 8) (Int.shl (Int.sub (Int.repr w) (Int.repr 8)) (Int.repr 4))) (Int.repr 8) =
  Int.repr (u32 (Z.shiftl (u32 (Z_DEFLATED + u32 (Z.shiftl (u32 (w - 8)) 4))) 8)).
Proof.
  rewrite sub_repr, shl_repr, add_repr, shl_repr by lia. rewrite repr_u32. unfold Z_DEFLATED.
  rewrite u32_add_u32. reflexivity.
Qed.

Lemma hdr0_range s : 0 <= hdr0 s <= Int.max_unsigned.
Proof. apply u32_range. Qed.

Lemma lflags_range s : 0 <= lflags s <= 3.
Proof. unfold lflags. repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia. Qed.

Lemma lor_range32 a b : 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned -> 0 <= Z.lor a b <= Int.max_unsigned.
Proof.
  intros Ha Hb. pose proof (lor_lt_pow2 a b 32 ltac:(rep_lia) ltac:(rep_lia)). rep_lia.
Qed.

Lemma hdr1_range s : 0 <= hdr1 s <= Int.max_unsigned.
Proof.
  unfold hdr1. apply lor_range32; [apply hdr0_range|].
  pose proof (lflags_range s). rewrite Z.shiftl_mul_pow2 by lia. rep_lia.
Qed.

Lemma hdr2_range s : 0 <= hdr2 s <= Int.max_unsigned.
Proof. unfold hdr2. destruct (_ =? _); [apply hdr1_range | apply lor_range32; [apply hdr1_range | unfold PRESET_DICT; rep_lia]]. Qed.

Lemma hdr1_int s : Int.or (Int.repr (hdr0 s)) (Int.shl (Int.repr (lflags s)) (Int.repr 6)) = Int.repr (hdr1 s).
Proof.
  pose proof (lflags_range s). pose proof (hdr0_range s).
  rewrite shl_repr, or_repr by lia. unfold hdr1. rewrite (u32_small (hdr0 s)) by auto.
  rewrite (u32_small (lflags s)) by rep_lia. rewrite u32_small; auto.
  rewrite Z.shiftl_mul_pow2 by lia. rep_lia.
Qed.

Lemma hdr2_int_dict s : d_strstart s <> 0 -> Int.or (Int.repr (hdr1 s)) (Int.repr 32) = Int.repr (hdr2 s).
Proof.
  intros E. unfold hdr2. rewrite (proj2 (Z.eqb_neq _ _) E). pose proof (hdr1_range s).
  rewrite or_repr. rewrite !u32_small by rep_lia. reflexivity.
Qed.

Lemma hdr2_int_nodict s : d_strstart s = 0 -> hdr2 s = hdr1 s.
Proof. intros E. unfold hdr2. rewrite E. reflexivity. Qed.

Lemma hdr3_int s : Int.add (Int.repr (hdr2 s)) (Int.sub (Int.repr 31) (Int.modu (Int.repr (hdr2 s)) (Int.repr 31))) =
  Int.repr (zlib_header s).
Proof.
  pose proof (hdr2_range s). rewrite zlib_header_eq.
  unfold Int.modu. rewrite !Int.unsigned_repr by rep_lia.
  rewrite sub_repr, add_repr, repr_u32. pose proof (Z.mod_pos_bound (hdr2 s) 31).
  rewrite (u32_small (31 - _)) by rep_lia. reflexivity.
Qed.

Lemma zmm64 a : 0 <= a <= Int64.max_unsigned -> Int64.Z_mod_modulus a = a.
Proof. intros. rewrite Int64.Z_mod_modulus_eq. apply Z.mod_small. rep_lia. Qed.

Lemma shiftr_range a k : 0 <= a -> 0 <= k -> 0 <= Z.shiftr a k <= a.
Proof.
  intros Ha Hk. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]|].
  apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|].
  assert (1 <= 2 ^ k) by (apply Z.pow_le_mono_r with (a := 2) (b := 0) in Hk; [simpl in Hk; lia | lia]). nia.
Qed.

Lemma land_range16 a : 0 <= a -> 0 <= Z.land a 65535 < 65536.
Proof.
  intros. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
  apply Z.mod_pos_bound. reflexivity.
Qed.

Lemma zr_status s om st : dstate_ranges s -> s32_ok st -> dstate_ranges (set_d_status (set_d_out s om) st).
Proof. unfold dstate_ranges. intros Hd Hs. dsimpl. tauto. Qed.

Lemma zr_lf s x : dstate_ranges s -> s32_ok x -> dstate_ranges (set_d_last_flush s x).
Proof. unfold dstate_ranges. intros Hd Hs. dsimpl. tauto. Qed.

Lemma lf_comm s o po x : set_d_last_flush (set_d_po (set_d_out s o) po) x = set_d_po (set_d_out (set_d_last_flush s x) o) po.
Proof. reflexivity. Qed.

Lemma out_at_fold o m sp pbp : out_ok o m ->
  @field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._pending) (vl (o_pending o)) sp *
  @field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._pending_buf) pbp sp *
  @field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._bi_buf) (vi (o_bi_buf o)) sp *
  @field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._bi_valid) (vi (o_bi_valid o)) sp *
  @field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._bi_used) (vi (o_bi_used o)) sp *
  @data_at DCS.CS Ews (tarray tuchar (Zlength (o_buf o))) (pb_vals (o_buf o) m) pbp
  |-- out_at o m sp pbp.
Proof. intros. unfold out_at. entailer!. Qed.

Lemma set_lf_same s om st : set_d_last_flush (set_d_status (set_d_out s om) st) (d_last_flush s) =
  set_d_status (set_d_out s om) st.
Proof. destruct s; reflexivity. Qed.

(** The end of the stage: back to [dfull] after flush_pending, with [s->status = BUSY_STATE] and
    [s->last_flush = lf]. *)
Lemma zlib_close s om z z3 ob3 m3 po3 lf p pin pout ish R msgv gv :
  dstate_ranges s -> readable_share ish -> s32_ok lf -> strm_ranges z3 -> msg_ok (z_msg z3) msgv ->
  z_in z3 = z_in z -> 0 <= po3 ->
  strm_at z3 (p_s p) (p_strm p) pin pout msgv gv * out_space z3 pout (rest_after (set_z_adler z 1) z3 R) *
  @field_at DCS.CS Ews t_ds (DOT _pending_out) (offset_val po3 (p_pbuf p)) (p_s p) *
  out_at ob3 m3 (p_s p) (p_pbuf p) * match_at s p * lvl_at (d_tr s) (p_s p) * win_at s p *
  ltree_at (tr_ltree (d_tr s)) (p_s p) * dtree_at (tr_dtree (d_tr s)) (p_s p) *
  sym_at (d_tr s) (p_s p) (p_pbuf p) * dtype_at (d_tr s) (p_s p) (p_strm p) *
  trees_rest (d_tr s) (p_s p) (p_strm p) gv * hash_at s p * cfg_at s p *
  @field_at DCS.CS Ews t_ds (DOT _status) (vi BUSY_STATE) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf_size) (vl (d_pending_buf_size s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _wrap) (vi (d_wrap s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _gzhead) (p_gzhead p) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _gzindex) (vl (d_gzindex s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _method) (vi (d_method s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _last_flush) (vi lf) (p_s p) *
  in_obj ish z pin
  |-- dfull (set_d_po (set_d_out (set_d_last_flush (set_d_status (set_d_out s om) BUSY_STATE) lf) (ob3, m3)) po3)
        z3 p pin pout ish (rest_after z z3 R) msgv gv.
Proof.
  intros Hd Hsh Hlf Hz3 Hm3 Ein Hpo.
  assert (Hd0 : dstate_ranges (set_d_last_flush (set_d_status (set_d_out s om) BUSY_STATE) lf)).
  { apply zr_lf; auto. apply zr_status; auto. unfold s32_ok, BUSY_STATE. rep_lia. }
  eapply derives_trans; [| apply (dfull_out_close _ z z3 ob3 m3 po3 p pin pout ish (rest_after z z3 R) msgv gv); auto].
  change (rest_after (set_z_adler z 1) z3 R) with (rest_after z z3 R).
  unfold flush_frame.
  set (s1 := set_d_last_flush (set_d_status (set_d_out s om) BUSY_STATE) lf) in *.
  change (win_at s1 p) with (win_at s p). change (hash_at s1 p) with (hash_at s p).
  change (match_at s1 p) with (match_at s p). change (cfg_at s1 p) with (cfg_at s p).
  change (tr_ltree (d_tr s1)) with (tr_ltree (d_tr s)). change (tr_dtree (d_tr s1)) with (tr_dtree (d_tr s)).
  change (sym_at (d_tr s1)) with (sym_at (d_tr s)). change (dtype_at (d_tr s1)) with (dtype_at (d_tr s)).
  change (lvl_at (d_tr s1)) with (lvl_at (d_tr s)). change (trees_rest (d_tr s1)) with (trees_rest (d_tr s)).
  change (d_status s1) with BUSY_STATE. change (d_pending_buf_size s1) with (d_pending_buf_size s).
  change (d_wrap s1) with (d_wrap s). change (d_gzindex s1) with (d_gzindex s).
  change (d_method s1) with (d_method s). change (d_last_flush s1) with lf.
  entailer!.
Qed.

Lemma stage_zlib : stage_ok S_zlib (fun _ => c_zlib2).
Proof.
  intros Espec p pin pout ish R msgv gv flush s z X res Hfl Hc. cbv beta in Hc.
  unfold stage_pre, stage_post, df_locals.
  cbv [S_zlib nth_stmt df_body f_deflate fn_body].
  sep_apply (dfull_flush_open s z p pin pout ish R msgv gv). Intros.
  unfold flush_frame. Intros.
  forward.
  destruct res as [[s' z'] o].
  forward_if (EX msgv' : val, PROP (o = None)
    LOCAL (temp _strm (p_strm p); temp _s (p_s p); temp _flush (vi flush); gvars gv)
    SEP (dfull s' z' p pin pout ish (rest_after z z' R) msgv' gv; deflate_globals gv; X)).
  - (* INIT_STATE *)
    assert (Est : d_status s = INIT_STATE).
    { unfold INIT_STATE. open_dranges H1. apply repr_inj_signed; auto; rep_lia. }
    unfold c_zlib2 in Hc. rewrite Est, Z.eqb_refl in Hc.
    unfold win_at, lvl_at. Intros.
    forward. forward. forward.
    forward_if_temp _t'20 (vi (if orb (d_strategy s >=? Z_HUFFMAN_ONLY) (d_level s <? 2) then 1 else 0)).
    { forward. entailer!. unfold d_strategy, d_level, Z_HUFFMAN_ONLY; zfin. }
    { forward. forward. entailer!. unfold d_strategy, d_level, Z_HUFFMAN_ONLY; zfin. }
    forward_if_temp _level_flags (vi (lflags s)).
    { forward. entailer!. unfold lflags.
      match goal with |- context [if ?b then _ else _] => destruct b end; [reflexivity | contradiction]. }
    { assert (Hb : orb (d_strategy s >=? Z_HUFFMAN_ONLY) (d_level s <? 2) = false).
      { match goal with H : Int.repr (if ?b then 1 else 0) = Int.zero |- _ =>
          destruct b; [apply repr_inj_unsigned in H; rep_lia | reflexivity] end. }
      forward. forward_if.
      { forward. entailer!. unfold lflags. rewrite Hb. unfold d_level. zfin. }
      forward. forward_if.
      { forward. entailer!. unfold lflags. rewrite Hb. unfold d_level. zfin. }
      { forward. entailer!. unfold lflags. rewrite Hb. unfold d_level. zfin. } }
    forward.
    rewrite hdr0_int. fold (hdr0 s). rewrite hdr1_int.
    unfold match_at. Intros.
    forward.
    forward_if_set _header (Vint (Int.repr (hdr2 s))).
    { forward. entailer!. unfold hdr2. rewrite (proj2 (Z.eqb_neq _ _)); [reflexivity|].
      intro E; rewrite E in *; contradiction. }
    { forward. entailer!. rewrite hdr2_int_nodict; auto. open_dranges H1. apply repr_inj_unsigned; auto; rep_lia. }
    forward. rewrite hdr3_int.
    sep_apply (win_at_fold s p). sep_apply (match_at_fold s p). sep_apply (lvl_at_fold (d_tr s) (p_s p)); auto.
    inv_bind Hc. rename x into s0, Ha into Hs0. rewrite c_putShortMSB_eq in Hs0.
    inv_bind Hs0. rename x into om1, Ha into Hp1. inversion Hs0; subst s0; clear Hs0.
    forward_call (p_s p, p_pbuf p, tr_out (d_tr s), d_pbm s, zlib_header s, om1).
    { rewrite zlib_header_eq. pose proof (u32_range (hdr2 s + u32 (31 - hdr2 s mod 31))). auto. }
    inv_bind Hc. rename x into s1, Ha into Hs1.
    change (d_strstart (set_d_out s om1)) with (d_strstart s) in Hs1.
    unfold match_at. Intros.
    forward.
    sep_apply (match_at_fold s p).
    rewrite strm_at_open. Intros.
    forward_if_sep (out_at (fst om1) (snd om1) (p_s p) (p_pbuf p)) (out_at (tr_out (d_tr s1)) (d_pbm s1) (p_s p) (p_pbuf p)).
    + (* strstart <> 0 *)
      rewrite (proj2 (Z.eqb_neq _ _)) in Hs1 by (intro E; rewrite E in *; contradiction).
      inv_bind Hs1. rename x into s1a, Ha into Hs1a.
      rewrite c_putShortMSB_eq, d_out_set_d_out in Hs1a. inv_bind Hs1a. rename x into om2, Ha into Hp2.
      inversion Hs1a; subst s1a; clear Hs1a.
      rewrite c_putShortMSB_eq, d_out_set_d_out in Hs1. inv_bind Hs1. rename x into om3, Ha into Hp3.
      inversion Hs1; subst s1; clear Hs1.
      forward.
      assert (Ha : 0 <= z_adler z <= Int64.max_unsigned) by (open_zranges H; auto).
      pose proof (shiftr_range (z_adler z) 16 ltac:(lia) ltac:(lia)) as Hsh.
      pose proof (land_range16 (z_adler z) ltac:(lia)) as Hla.
      forward_call (p_s p, p_pbuf p, fst om1, snd om1, u32 (Z.shiftr (z_adler z) 16), om2).
      { entailer!. simpl.
        rewrite (zmm64 (z_adler z)) by rep_lia. rewrite zmm64 by rep_lia. unfold vi. rewrite repr_u32. reflexivity. }
      { split; [apply u32_range | destruct om1; exact Hp2]. }
      forward.
      forward_call (p_s p, p_pbuf p, fst om2, snd om2, u32 (Z.land (z_adler z) 65535), om3).
      { entailer!. simpl. rewrite zmm64 by rep_lia. unfold vi. rewrite repr_u32. reflexivity. }
      { split; [apply u32_range | destruct om2; exact Hp3]. }
      entailer!.
    + assert (E : d_strstart s = 0) by (open_dranges H1; apply repr_inj_unsigned; auto; rep_lia).
      rewrite E, Z.eqb_refl in Hs1. inversion Hs1; subst s1; clear Hs1.
      forward. entailer!.
    + assert (Hs1e : s1 = set_d_out s (d_out s1)).
      { case_if Hs1.
        - inversion Hs1; subst s1. rewrite d_out_set_d_out. reflexivity.
        - inv_bind Hs1. rewrite c_putShortMSB_eq in Ha, Hs1. inv_bind Ha. inversion Ha; subst x; clear Ha.
          inv_bind Hs1. inversion Hs1; subst s1; clear Hs1.
          rewrite !d_out_set_d_out, !set_d_out_out. reflexivity. }
      set (om := d_out s1) in Hs1e. clearbody om. subst s1. clear Hs1.
      forward_call (0, nullval, 0, true, Ews, nullval, 0, 0, @nil val, @nil Z, false, Ews).
      { cancel. }
      forward.
      sep_apply (strm_at_set_adler z 1 (p_s p) (p_strm p) pin pout msgv gv).
      forward.
      unfold c_flush_or_return in Hc. inv_bind Hc. destruct x as [s3 z3]. rename Ha into Hf.
      set (s0 := set_d_status (set_d_out s om) BUSY_STATE) in Hf.
      change (out_space z pout R) with (out_space (set_z_adler z 1) pout R).
      change (out_at (tr_out (d_tr (set_d_out s om))) (d_pbm (set_d_out s om))) with (out_at (tr_out (d_tr s0)) (d_pbm s0)).
      assert (Hz1 : strm_ranges (set_z_adler z 1)) by (apply strm_ranges_set_adler; auto; rep_lia).
      forward_call (p_strm p, p_s p, p_pbuf p, pin, pout, msgv, R, s0, set_z_adler z 1, (s3, z3), gv).
      cbn [fst snd].
      destruct (c_flush_pending_same _ _ _ _ Hf) as (Ein & Emsg & _).
      destruct (c_flush_pending_inv _ _ _ _ Hz1 Hf) as ([ob3 m3] & po3 & -> & Hpo & Hr).
      assert (Hd0 : dstate_ranges s0) by (apply zr_status; auto; unfold s32_ok, BUSY_STATE; rep_lia).
      assert (Hpo3 : 0 <= po3) by (apply Hpo; open_dranges Hd0; auto).
      change (tr_out (d_tr (set_d_po (set_d_out s0 (ob3, m3)) po3))) with ob3.
      change (d_pbm (set_d_po (set_d_out s0 (ob3, m3)) po3)) with m3.
      change (d_po (set_d_po (set_d_out s0 (ob3, m3)) po3)) with po3.
      change (d_pending (set_d_po (set_d_out s0 (ob3, m3)) po3)) with (o_pending ob3) in Hc.
      unfold out_at. Intros.
      destruct (Hr ltac:(auto)) as [Hz3 _].
      assert (Hm3 : msg_ok (z_msg z3) msgv) by (rewrite Emsg; exact H0).
      forward.
      sep_apply (out_at_fold ob3 m3 (p_s p) (p_pbuf p)); auto.
      forward_if.
      { assert (Ep : (o_pending ob3 =? 0) = false).
        { apply Z.eqb_neq. intro E. rewrite E in *. contradiction. }
        rewrite Ep in Hc. cbn in Hc. inversion Hc; subst s' z' o; clear Hc.
        forward.
        unfold POSTCONDITION, abbreviate.
        eapply semax_pre; [| apply semax_return].
        apply andp_right.
        { entailer!. }
        go_lowerx. simpl RA_return.
        Exists msgv. rewrite lf_comm. unfold s0.
        change (Vint (Int.neg (Int.repr 1))) with (vi (-1)). change (Vint (Int.repr 113)) with (vi BUSY_STATE).
        sep_apply (zlib_close s om z z3 ob3 m3 po3 (-1) p pin pout ish R msgv gv); auto.
        { unfold s32_ok; rep_lia. }
        entailer!. }
      assert (Ep : o_pending ob3 = 0).
      { destruct H6 as (_ & _ & Hp & _). apply repr_inj_unsigned64 in H7; auto; rep_lia. }
      rewrite Ep, Z.eqb_refl in Hc. cbn in Hc. inversion Hc; subst s' z' o; clear Hc.
      forward.
      Exists msgv. unfold s0. rewrite <- (set_lf_same s om BUSY_STATE).
      change (Vint (Int.repr 113)) with (vi BUSY_STATE).
      sep_apply (zlib_close s om z z3 ob3 m3 po3 (d_last_flush s) p pin pout ish R msgv gv).
      { destruct H1 as (_ & _ & _ & _ & _ & _ & Hl & _). exact Hl. }
      entailer!.
  - (* not INIT_STATE *)
    forward.
    unfold c_zlib2 in Hc. rewrite (proj2 (Z.eqb_neq _ _)) in Hc by (unfold INIT_STATE; intro E; rewrite E in *; contradiction).
    inversion Hc; subst s' z' o; clear Hc.
    Exists msgv. rewrite rest_after_refl.
    sep_apply (flush_frame_fold s z p pin ish gv); auto.
    sep_apply (dfull_flush_back s z p pin pout ish R msgv gv); auto.
    entailer!.
  - Intros msgv'. subst o. Exists msgv'. entailer!.
Qed.
