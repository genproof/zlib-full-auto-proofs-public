(* Law rfc_stored, the padding simulation: the passes TYPE and TYPEDO.  At the start of a stored block the bit
   buffer is empty (the block is byte-aligned); TYPEDO pulls the block's first byte, keeps BFINAL and BTYPE (its
   three low bits, the same in both inputs) and drops them: the real machine is then the canonical one but for
   the input and hold (the padding bits, five of them in both), and the mode is STORED.  Every other way through
   these passes (the end of the stream, Z_BLOCK / Z_TREES, the input running out) reads nothing. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.harness.rfc_stored.RSSimKit.
Require Import Zlib.proof.rfc1951.DecKit Zlib.proof.rfc1951.DecType.
Import ListNotations.
Local Open Scope Z_scope.

(* TYPEDO with an empty bit buffer, BFINAL = 0 so far and input left: it pulls the byte b at nx; when its
   BTYPE bits are 0 (b mod 8 < 2) the pass keeps BFINAL = b mod 2 and goes to STORED with the five bits b >> 3 *)
Lemma rs_tydo_form flush m b :
  i_last (m_s m) = 0 -> m_leave m = 0 -> m_bits m = 0 -> m_hold m = 0 -> m_have m <> 0 ->
  Znth (m_nx m) (m_inp m) = b -> 0 <= b < 256 -> b mod 8 < 2 ->
  c_TYPEDO flush m =
    IBrk (dropbits 2 (set_mode (dropbits 1 (upd_s (pull m) (fun s => set_i_last s (b mod 2)))) STORED)).
Proof.
  intros L0 Lv B0 H0 Hv Eb Bb B8. unfold c_TYPEDO. rewrite L0. cbn [negb Z.eqb].
  assert (Bp : m_bits (pull m) = 8) by (unfold pull, u32; cbn; rewrite B0; reflexivity).
  assert (N : needbits 3 m = pull m).
  { unfold needbits. cbn [needbits_f]. rewrite B0. apply Z.eqb_neq in Hv. rewrite Hv.
    cbn [Z.ltb Z.compare]. cbn [needbits_f]. rewrite Bp. reflexivity. }
  rewrite N.
  assert (Hp : m_hold (pull m) = b).
  { unfold pull, u64. cbn. rewrite H0, B0, Eb. rewrite Z.mod_small; lia. }
  replace (m_leave (pull m)) with 0 by (rewrite <- Lv; reflexivity). cbn [Z.eqb].
  replace (bitsn (pull m) 1) with (b mod 2) by (unfold bitsn; rewrite Hp; reflexivity).
  assert (Bt : bitsn (dropbits 1 (upd_s (pull m) (fun s => set_i_last s (b mod 2)))) 2 = 0).
  { unfold bitsn. cbn [m_hold dropbits upd_s set_m_bits set_m_hold set_m_s]. rewrite Hp, Z.shiftr_div_pow2 by lia.
    change (2 ^ 1) with 2. change (2 ^ 2) with 4. Z.to_euclidean_division_equations; lia. }
  rewrite Bt. reflexivity.
Qed.

(* the five padding bits left in the hold after BFINAL and BTYPE of a pulled byte: nothing above them *)
Lemma rs_pad5 b : 0 <= b < 256 -> Z.shiftr (Z.shiftr (Z.shiftr (u64 (0 + b * 2 ^ 0)) 1) 2) 5 = 0.
Proof.
  intros Hb. rewrite !Z.shiftr_shiftr by lia. unfold u64. change (2 ^ 0) with 1.
  rewrite Z.mul_1_r, Z.add_0_l, Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia.
  apply Z.div_small. cbn. lia.
Qed.

(* the passes commute with the change of input; the hold of the pulled byte aside *)
Lemma rs_hold_id m : set_m_hold m (m_hold m) = m.
Proof. destruct m; reflexivity. Qed.

Lemma rs_check_inp m x : set_mode (bytebits (set_m_inp m x)) CHECK =
  set_m_hold (set_m_inp (set_mode (bytebits m) CHECK) x) (m_hold (set_mode (bytebits m) CHECK)).
Proof. destruct m; reflexivity. Qed.

Lemma rs_tydo_inp m x c :
  dropbits 2 (set_mode (dropbits 1 (upd_s (pull (set_m_inp m x)) (fun s => set_i_last s c))) STORED) =
  set_m_hold (set_m_inp (dropbits 2 (set_mode (dropbits 1 (upd_s (pull m) (fun s => set_i_last s c))) STORED)) x)
    (Z.shiftr (Z.shiftr (u64 (m_hold m + Znth (m_nx m) x * 2 ^ m_bits m)) 1) 2).
Proof. destruct m; reflexivity. Qed.

(* TYPEDO with an empty bit buffer and no input: it leaves *)
Lemma rs_tydo_leave flush m : i_last (m_s m) = 0 -> m_bits m = 0 -> m_have m = 0 ->
  c_TYPEDO flush m = IBrk (set_leave m).
Proof.
  intros L B H. unfold c_TYPEDO, needbits. rewrite L. cbn [negb Z.eqb needbits_f]. rewrite B, H. reflexivity.
Qed.

(* three bits from a block's start: BFINAL, then BTYPE = 0 for a stored block *)
Lemma rs_stored_3 p f bytes : bval (sublist 0 3 (enc_block p f (Stored bytes))) = Z.b2z f.
Proof. destruct f; reflexivity. Qed.


(* TYPEDO (also reached from TYPE): the real pass is the canonical one but for the input and, when it reads the
   block's first byte, the hold *)
Lemma rs_typedo_pass : rs_lay_stmt ->
  forall G pos x inp' ob flush m',
    dctx_ok7a G -> rs_stored_only G -> 0 <= pos -> pos + Zlength inp' <= Zlength (dc_src G) ->
    inp' = sublist pos (pos + Zlength inp') (dc_src G) -> rs_xrel G pos x inp' ->
    Kd G pos inp' ob m' -> mwf3W m' -> m_leave m' = 0 ->
    (m_mode m' = Zlib.proof.inflate.Model.TYPE \/ m_mode m' = TYPEDO) ->
    exists m1' h,
      c_TYPEDO flush m' = IBrk m1' /\
      c_TYPEDO flush (set_m_inp m' x) = IBrk (set_m_hold (set_m_inp m1' x) h) /\
      (h = m_hold m1' \/
       (m_mode m1' = STORED /\ m_leave m1' = 0 /\
        Z.shiftr h (m_bits m1' mod 8) = Z.shiftr (m_hold m1') (m_bits m1' mod 8))).
Proof.
  intros LAY G pos x inp' ob flush m' Gok So Hp Hl Hinp Hx K W L0 M.
  destruct Hx as (Hxl & Hxb & Hxe).
  pose proof (kd_inp _ _ _ _ _ K) as Ki. pose proof (kd_at _ _ _ _ _ K) as A.
  pose proof (mwW_nx _ (proj1 W)) as Hnx. rewrite Ki in Hnx.
  assert (Bs : bytes_ok (dc_src G)) by (destruct Gok as (_ & _ & _ & _ & _ & _ & B & _); exact B).
  assert (Nb : 1 <= nblk G).
  { destruct Gok as ((_ & _ & _ & (NE & _)) & _). unfold nblk.
    destruct (dc_bs G) as [|b r]; [congruence|]. rewrite Zlength_cons. pose proof (Zlength_nonneg r). lia. }
  destruct (dt_at_type _ _ _ _ _ _ A M) as [Hh (k & Hk & Hq & Ho & Hb & Hlast)].
  pose proof (rl_align LAY G k So Hk) as Al.
  pose proof Hh as (Hh1 & Hh2 & Hh3).
  (* the block starts on a byte boundary: the bit buffer is empty *)
  assert (B0 : m_bits m' = 0) by (Z.to_euclidean_division_equations; lia).
  assert (H0 : m_hold m' = 0) by (rewrite Hh3, B0, Z.sub_0_r, sublist_nil; reflexivity).
  assert (Lx : Zlength x = Zlength (m_inp m')) by (rewrite Ki; exact Hxl).
  destruct (Z.eqb_spec (i_last (m_s m')) 0) as [Lz|Lnz].
  2: { exists (set_mode (bytebits m') CHECK), (m_hold (set_mode (bytebits m') CHECK)).
       unfold c_TYPEDO. change (m_s (set_m_inp m' x)) with (m_s m'). apply Z.eqb_neq in Lnz. rewrite Lnz.
       cbn [negb]. split; [reflexivity|]. split; [rewrite rs_check_inp; reflexivity|left; reflexivity]. }
  assert (Hk1 : k < nblk G).
  { destruct (Z.eqb_spec k (nblk G)) as [E|E]; [|lia]. exfalso. rewrite Hlast in Lz.
    destruct (Z.eqb_spec k 0); [lia|]. unfold lastflag in Lz. rewrite E, Z.eqb_refl in Lz. discriminate. }
  destruct (Z.eqb_spec (m_have m') 0) as [Hv|Hv].
  - (* no input: both leave *)
    exists (set_leave m'), (m_hold (set_leave m')).
    rewrite (rs_tydo_leave flush m') by assumption.
    rewrite (rs_tydo_leave flush (set_m_inp m' x)) by first [exact Lz | exact B0 | rewrite (rs_have_inp m' x Lx); exact Hv].
    split; [reflexivity|]. split; [|left; reflexivity].
    change (m_hold (set_leave m')) with (m_hold (set_m_inp (set_leave m') x)).
    rewrite rs_hold_id, rs_leave_inp. reflexivity.
  - unfold m_have in Hv. rewrite Ki in Hv.
    set (i := m_nx m') in *.
    assert (Bx : 0 <= Znth i x < 256).
    { pose proof (Forall_Znth _ x i ltac:(lia) Hxb) as F. cbn in F. lia. }
    assert (Ei : Znth i inp' = Znth (pos + i) (dc_src G)) by (rewrite Hinp, Znth_sublist by lia; f_equal; lia).
    assert (Bi : 0 <= Znth i inp' < 256).
    { rewrite Ei. pose proof (Forall_Znth _ (dc_src G) (pos + i) ltac:(lia) Bs) as F. cbn in F. lia. }
    assert (E8 : Znth i x mod 8 = Znth i inp' mod 8).
    { destruct (Hxe i ltac:(lia)) as [E|(_ & E & _)]; [rewrite E|]; reflexivity || exact E. }
    (* the canonical byte: BFINAL, then BTYPE = 0 *)
    assert (C8 : Znth i inp' mod 8 < 2).
    { destruct (rl_stored LAY G k So ltac:(lia)) as (bytes & Ebk).
      destruct (rl_blk LAY G k bytes Gok So ltac:(lia) Ebk) as (Eb1 & _ & _ & Sb).
      assert (Bp0 : 0 <= bpos G k).
      { pose proof (rl_D0 LAY G k ltac:(lia)). unfold D0 in *. pose proof (Zlength_nonneg (hdr_bytes (dc_w G))). lia. }
      pose proof (Zlength_nonneg bytes).
      pose proof (dk_pull dkit G (pos + i) (m_hold m') (m_bits m') Hh ltac:(lia) ltac:(lia) Bs) as P.
      rewrite H0, B0 in P.
      pose proof (dk_bitsn dkit _ _ _ _ 3 P ltac:(lia)) as HB.
      change (2 ^ 0) with 1 in HB. rewrite Z.mul_1_r, Z.add_0_l, (Z.mod_small (Znth (pos + i) (dc_src G))) in HB by (rewrite <- Ei; lia).
      replace (8 * (pos + i + 1) - (0 + 8)) with (bpos G k) in HB by lia.
      rewrite (dt_sub_in _ _ _ _ _ _ Sb) in HB by lia. rewrite Z.sub_diag, Z.add_simpl_l, rs_stored_3 in HB.
      change (2 ^ 3) with 8 in HB. rewrite Ei, HB. destruct (lastflag G k =? 1); cbn; lia. }
    assert (E2 : Znth i x mod 2 = Znth i inp' mod 2).
    { clear -E8 Bx Bi. Z.to_euclidean_division_equations; lia. }
    rewrite (rs_tydo_form flush m' (Znth i inp')) by
      first [exact Lz | exact L0 | exact B0 | exact H0 | (unfold m_have; rewrite Ki; lia) |
             (rewrite Ki; reflexivity) | lia].
    rewrite (rs_tydo_form flush (set_m_inp m' x) (Znth i x)) by
      first [exact Lz | exact L0 | exact B0 | exact H0 | (unfold m_have; cbn [m_inp m_nx set_m_inp]; lia) |
             reflexivity | lia | (rewrite E8; lia)].
    rewrite E2.
    eexists _, _. split; [reflexivity|]. split; [rewrite rs_tydo_inp; reflexivity|right].
    cbn [m_hold m_bits m_mode m_leave m_s dropbits set_mode upd_s pull set_m_bits set_m_hold set_m_s set_m_nx
         i_mode set_i_mode set_i_last].
    split; [reflexivity|]. split; [exact L0|].
    change (m_hold (set_m_inp m' x)) with (m_hold m'). change (m_bits (set_m_inp m' x)) with (m_bits m').
    change (m_nx (set_m_inp m' x)) with i. change (m_inp (set_m_inp m' x)) with x.
    fold i. rewrite Ki, B0, H0. change (u32 (u32 (u32 (0 + 8) - 1) - 2) mod 8) with 5.
    rewrite !rs_pad5 by lia. reflexivity.
Qed.

Lemma rs_pass_type : rs_lay_stmt -> dc_step7a_stmt ->
  forall G pos x inp' ob flush m',
    dctx_ok7a G -> rs_stored_only G -> 0 <= pos -> pos + Zlength inp' <= Zlength (dc_src G) ->
    inp' = sublist pos (pos + Zlength inp') (dc_src G) -> rs_xrel G pos x inp' ->
    Kd G pos inp' ob m' -> mwf3W m' -> m_leave m' = 0 ->
    (m_mode m' = Zlib.proof.inflate.Model.TYPE \/ m_mode m' = TYPEDO) ->
    exists m1' h,
      stepf2 flush lenfix_list distfix_list m' = IBrk m1' /\
      stepf2 flush lenfix_list distfix_list (set_m_inp m' x) = IBrk (set_m_hold (set_m_inp m1' x) h) /\
      (h = m_hold m1' \/
       (m_mode m1' = STORED /\ m_leave m1' = 0 /\
        Z.shiftr h (m_bits m1' mod 8) = Z.shiftr (m_hold m1') (m_bits m1' mod 8))).
Proof.
  intros LAY STEP G pos x inp' ob flush m' Gok So Hp Hl Hinp Hx K W L0 M.
  pose proof (rs_typedo_pass LAY G pos x inp' ob flush m' Gok So Hp Hl Hinp Hx K W L0 M) as TD.
  destruct M as [E|E].
  - replace (stepf2 flush lenfix_list distfix_list m') with (c_TYPE flush m')
      by (unfold stepf2, step2; rewrite E; reflexivity).
    replace (stepf2 flush lenfix_list distfix_list (set_m_inp m' x)) with (c_TYPE flush (set_m_inp m' x))
      by (unfold stepf2, step2; change (m_mode (set_m_inp m' x)) with (m_mode m'); rewrite E; reflexivity).
    unfold c_TYPE. destruct ((flush =? Z_BLOCK) || (flush =? Z_TREES)).
    + exists (set_leave m'), (m_hold (set_leave m')).
      split; [reflexivity|]. split; [destruct m'; reflexivity|left; reflexivity].
    + exact TD.
  - replace (stepf2 flush lenfix_list distfix_list m') with (c_TYPEDO flush m')
      by (unfold stepf2, step2; rewrite E; reflexivity).
    replace (stepf2 flush lenfix_list distfix_list (set_m_inp m' x)) with (c_TYPEDO flush (set_m_inp m' x))
      by (unfold stepf2, step2; change (m_mode (set_m_inp m' x)) with (m_mode m'); rewrite E; reflexivity).
    exact TD.
Qed.
