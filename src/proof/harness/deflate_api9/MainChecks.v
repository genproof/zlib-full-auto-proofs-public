(* Law deflate_api, main: the checks of the output after the run (zlib: Adler-32, header, FDICT; gzip: CRC-32,
   header, trailer), MainKit.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.HarnessRef.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.harness.deflate_api.ApiCS Zlib.proof.harness.deflate_api9.RunSpec
               Zlib.proof.harness.deflate_api9.ApiConv Zlib.proof.harness.deflate_api9.RunKit
               Zlib.proof.harness.deflate_api9.MainKit.
Require Import Zlib.harness.x_deflate_api.code.
#[local] Existing Instance ApiCS.CS.
Local Open Scope logic.

Lemma mc_bytes_is l : bytes l -> is_bytes l.
Proof. unfold bytes, is_bytes. intro B. eapply Forall_impl; [|exact B]. simpl; intros; rep_lia. Qed.

(* a slice of an object holding the bytes l followed by anything *)
Lemma mc_cbuf p l rest lo len n :
  isptr p -> bytes l -> 0 <= lo -> 0 <= len -> lo + len <= Zlength l -> n = Zlength l + Zlength rest ->
  cbuf_ok false (offset_val lo p) Ews p lo n len (map vi l ++ rest) (sublist lo (lo + len) l).
Proof.
  intros P B L0 L1 L2 E. unfold cbuf_ok.
  split; [reflexivity|]. split; [auto|]. split; [lia|]. split.
  { pose proof (Zlength_nonneg rest). lia. }
  split; [rewrite Zlength_sublist; lia|]. split.
  - apply is_bytes_sublist, mc_bytes_is; auto.
  - rewrite sublist_app1 by (rewrite ?Zlength_map; lia).
    rewrite sublist_map. reflexivity.
Qed.

Lemma mc_cbufL p l lo len :
  isptr p -> bytes l -> 0 <= lo -> 0 <= len -> lo + len <= Zlength l ->
  cbuf_ok false (offset_val lo p) Ews p lo (Zlength l) len (map vi l) (sublist lo (lo + len) l).
Proof.
  intros. pose proof (mc_cbuf p l [] lo len (Zlength l)) as X. rewrite app_nil_r in X.
  apply X; auto. rewrite Zlength_nil; lia.
Qed.

Lemma mc_add_long p n : isptr p -> 0 <= n <= Ptrofs.max_unsigned ->
  force_val (sem_add_ptr_long tuchar p (vl n)) = offset_val n p.
Proof.
  intros P N. destruct p; try contradiction. unfold vl. simpl.
  unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by rep_lia.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. reflexivity.
Qed.

Lemma mc_cbuf4 p l lo hi :
  isptr p -> bytes l -> 0 <= lo -> lo + 4 = hi -> hi <= Zlength l ->
  cbuf_ok false (offset_val lo p) Ews p lo (Zlength l) 4 (map vi l) (sublist lo hi l).
Proof. intros. subst hi. apply mc_cbufL; auto; lia. Qed.

Lemma mc_ptrofs i L k : 0 <= L <= Int64.max_unsigned -> 0 <= k <= 100 ->
  Ptrofs.sub (Ptrofs.add i (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Int64.repr L))))
             (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr k))) =
  Ptrofs.add i (Ptrofs.repr (L - k)).
Proof.
  intros. change (Ptrofs.repr 1) with Ptrofs.one.
  rewrite !(Ptrofs.mul_commut Ptrofs.one), !Ptrofs.mul_one.
  unfold Ptrofs.of_int64, Ptrofs.of_ints. rewrite Int64.unsigned_repr, Int.signed_repr by rep_lia.
  rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc, Ptrofs.neg_repr, ptrofs_add_repr. reflexivity.
Qed.

Lemma mc_cbuf0 p l len :
  isptr p -> bytes l -> 0 <= len <= Zlength l ->
  cbuf_ok false p Ews p 0 (Zlength l) len (map vi l) (sublist 0 len l).
Proof.
  intros P B L. pose proof (mc_cbuf p l [] 0 len (Zlength l) P B) as X.
  rewrite app_nil_r, isptr_offset_val_zero in X by auto.
  replace (0 + len) with len in X by lia. apply X; auto; try lia. rewrite Zlength_nil; lia.
Qed.

Lemma mc_znth (O : list Z) (rest : list val) i :
  0 <= i < Zlength O -> Znth i (map vi O ++ rest) = vi (Znth i O).
Proof. intros. rewrite Znth_app1 by (rewrite Zlength_map; lia). apply Znth_map; lia. Qed.

Lemma mc_byte l i : bytes l -> 0 <= i < Zlength l -> 0 <= Znth i l < 256.
Proof. intros B Hi. unfold bytes in B. rewrite Forall_forall in B. apply B, Znth_In; auto. Qed.

Ltac mc_tc := entailer!; unfold vi; simpl; try rewrite Int.unsigned_repr by rep_lia; rep_lia.
Ltac mc_fwd := forward; lazymatch goal with |- semax _ _ _ _ => idtac | _ => mc_tc end.

Lemma mc_and a b : 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int.and (Int.repr a) (Int.repr b) = Int.repr (Z.land a b).
Proof. intros. unfold Int.and. rewrite !Int.unsigned_repr by auto. reflexivity. Qed.

Lemma mc_shr a : 0 <= a < 256 -> Int.shr (Int.repr a) (Int.repr 4) = Int.repr (Z.shiftr a 4).
Proof. intros. unfold Int.shr. rewrite Int.signed_repr, Int.unsigned_repr by rep_lia. reflexivity. Qed.

Lemma mc_lor_add h x l : 0 <= l -> 0 <= h < 2 ^ l -> 0 <= x ->
  (Z.lor h (Z.shiftl x l) = h + x * 2 ^ l)%Z.
Proof.
  intros. rewrite Z.shiftl_mul_pow2 by lia.
  assert (E: Z.land h (x * 2 ^ l) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_le_dec n l).
    - rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    - rewrite <- (Z.mod_small h (2 ^ l)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
  rewrite <- Z.lxor_lor by auto. rewrite <- Z.add_nocarry_lxor by auto. reflexivity.
Qed.

Lemma mc_hdr31 a b : 0 <= a < 256 -> 0 <= b < 256 -> ((a * 256 + b) mod 31 = 0)%Z ->
  Int.eq (Int.modu (Int.or (Int.shl (Int.repr a) (Int.repr 8)) (Int.repr b)) (Int.repr 31)) (Int.repr 0) = true.
Proof.
  intros Ha Hb H31.
  assert (E : Int.or (Int.shl (Int.repr a) (Int.repr 8)) (Int.repr b) = Int.repr (a * 256 + b)%Z).
  { unfold Int.or, Int.shl. rewrite (Int.unsigned_repr a), (Int.unsigned_repr 8) by rep_lia.
    rewrite (Int.unsigned_repr b) by rep_lia.
    assert (S : Z.shiftl a 8 = (a * 256)%Z) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
    rewrite S, Int.unsigned_repr by rep_lia. rewrite Z.lor_comm, <- S, mc_lor_add by lia.
    f_equal. change (2 ^ 8) with 256. lia. }
  rewrite E. unfold Int.modu. rewrite !Int.unsigned_repr by rep_lia. rewrite H31. apply Int.eq_true.
Qed.

Lemma mc_land_range a b : 0 <= a < 256 -> 0 <= b -> 0 <= Z.land a b < 256.
Proof.
  intros. assert (0 <= Z.land a b) by (apply Z.land_nonneg; lia). split; auto.
  destruct (Z.eq_dec (Z.land a b) 0) as [E | E]; [rewrite E; lia | ].
  change 256 with (2 ^ 8).
  apply (proj2 (Z.log2_lt_pow2 (Z.land a b) 8 ltac:(lia))).
  pose proof (Z.log2_land a b ltac:(lia) ltac:(lia)).
  destruct (Z.eq_dec a 0) as [-> | ]; [rewrite Z.land_0_l in E; congruence | ].
  assert (Z.log2 a < 8) by (apply (proj1 (Z.log2_lt_pow2 a 8 ltac:(lia))); lia).
  lia.
Qed.

(* comp_at's array: the output O, then the undefined rest *)
Lemma mc_comp_split O p :
  Zlength O <= COMP_MAX ->
  data_at Ews (tarray tuchar COMP_MAX) (map vi O ++ Zrepeat Vundef (COMP_MAX - Zlength O)) p =
  !! field_compatible (tarray tuchar COMP_MAX) [] p &&
  (data_at Ews (tarray tuchar (Zlength O)) (map vi O) p *
   data_at Ews (tarray tuchar (COMP_MAX - Zlength O)) (Zrepeat Vundef (COMP_MAX - Zlength O))
     (offset_val (Zlength O) p)).
Proof.
  intros HO. pose proof (Zlength_nonneg O).
  assert (ZL : Zlength (map vi O ++ Zrepeat Vundef (COMP_MAX - Zlength O)) = COMP_MAX)
    by (rewrite Zlength_app, Zlength_map, Zlength_Zrepeat by lia; lia).
  assert (E1 : sublist 0 (Zlength O) (map vi O ++ Zrepeat Vundef (COMP_MAX - Zlength O)) = map vi O)
    by (rewrite sublist0_app1 by (rewrite Zlength_map; lia); apply sublist_same; rewrite ?Zlength_map; lia).
  assert (E2 : sublist (Zlength O) COMP_MAX (map vi O ++ Zrepeat Vundef (COMP_MAX - Zlength O)) =
               Zrepeat Vundef (COMP_MAX - Zlength O)).
  { rewrite sublist_app2 by (rewrite Zlength_map; lia). rewrite Zlength_map.
    apply sublist_same; rewrite ?Zlength_Zrepeat; lia. }
  apply pred_ext.
  - assert_PROP (field_compatible (tarray tuchar COMP_MAX) [] p) as FC by entailer!.
    unfold tarray. rewrite (split2_data_at_Tarray_tuchar Ews COMP_MAX (Zlength O)) by lia.
    rewrite E1, E2. rewrite field_address0_offset by auto with field_compatible.
    simpl. rewrite Z.mul_1_l. entailer!.
  - Intros. unfold tarray. rewrite (split2_data_at_Tarray_tuchar Ews COMP_MAX (Zlength O)) by lia.
    rewrite E1, E2. rewrite field_address0_offset by auto with field_compatible.
    simpl. rewrite Z.mul_1_l. cancel.
Qed.

Lemma main_checks_ok {Espec : OracleKind} I Iend rf vR vs vb gv :
  semax (Delta_m I Iend) (MA I Iend rf vR vs vb gv) msuf4 POST_m ->
  semax (Delta_m I Iend) (MA I Iend rf vR vs vb gv) msuf1 POST_m.
Proof.
  intros Hk.
  unfold Delta_m, MA, msuf1, POST_m. simplify_func_tycontext. Intros.
  pose proof H as HR. unfold rf_ok in HR.
  destruct HR as (RS & HIend & Hmsgv & FIN & Hnf & HOlen & Hd & Hh).
  pose proof RS as RS'.
  destruct RS' as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&Hn&Hdl&_&_&_&Bd&Bdict&_&_&_&Pd&Pdict&_&_&_&Pc).
  assert (Hw : 0 <= rf_wrap rf <= 2)
    by (unfold rf_wrap, wrap_of; destruct (_ <? 0); [lia | destruct (_ >? 15); lia]).
  unfold run_ok_at, drun_rest. Intros.
  forward. forward. forward.
  forward_if (PROP (rf_ok Iend vR rf; api_facts I Iend)
    LOCAL (lvar _R t_drun vR; lvar _s t_strmL vs; lvar _b (tarray tuchar 1) vb; gvars gv)
    SEP (run_ok_at rf vR vs gv; mem_mgr gv; deflate_globals gv;
         data_at_ (Share.comp Ews) t_drun vR; data_at_ (Share.comp Ews) t_strmL vs;
         data_at_ Tsh (tarray tuchar 1) vb)).
  - (* zlib *)
    rename H1 into W1.
    destruct FIN as (BO & F1 & _). specialize (F1 W1).
    destruct F1 as (Fad & Flen & Fh0 & Fh1 & Fh2 & Fdict & Fdid & Ftr).
    forward. forward.
    unfold obj at 1. Intros.
    rewrite (bytes_cs CS Zlib.units.Adler32.CS Ews (Zlength (rs_data (rf_rs rf)))).
    forward_call (1, rs_datap (rf_rs rf), Ews, rs_datap (rf_rs rf), 0, Zlength (rs_data (rf_rs rf)),
                  map vi (rs_data (rf_rs rf)), rf_nf rf, sublist 0 (rf_nf rf) (rs_data (rf_rs rf))).
    { apply mc_cbuf0; auto. }
    rewrite <- (bytes_cs CS Zlib.units.Adler32.CS Ews (Zlength (rs_data (rf_rs rf)))).
    rewrite <- Fad.
    forward.
    rewrite api_fields_L. unfold api_fieldsL. Intros.
    forward.
    forward_call (Int.one).
    { apply prop_right. unfold vl. simpl. rewrite Int64.eq_true. reflexivity. }
    assert (Hds : 0 <= rf_dset rf <= 1) by (destruct Hd as [(-> & _) | (-> & _)]; lia).
    forward.
    forward_if (temp _t'4 (vi (4 * rf_dset rf))).
    { forward. replace (rf_dset rf) with 1 by lia. entailer!. }
    { forward.
      assert (E: rf_dset rf = 0) by (destruct (Z.eq_dec (rf_dset rf) 0) as [|n]; [auto |
        replace (rf_dset rf) with 1 in * by lia; apply Int.one_not_zero in H6; contradiction]).
      rewrite E. entailer!. }
    assert (HL : 6 + 4 * rf_dset rf <= Zlength (rf_O rf)).
    { destruct Hd as [(E1 & E2 & E3) | (E1 & E2)]; rewrite E1; rewrite E2 in Flen; [|lia].
      destruct (rs_dict (rf_rs rf)); [contradiction | lia]. }
    forward_call (Int.one).
    { apply prop_right. unfold vl, vi. simpl. unfold COMP_MAX in HOlen.
      rewrite add_repr, Int.signed_repr by rep_lia. unfold Int64.ltu.
      rewrite !Int64.unsigned_repr by rep_lia. rewrite zlt_false by lia. reflexivity. }
    unfold comp_at. rewrite (mc_comp_split (rf_O rf) (rs_compp (rf_rs rf)) HOlen). Intros.
    pose proof (mc_byte (rf_O rf) 0 BO ltac:(lia)) as B0.
    pose proof (mc_byte (rf_O rf) 1 BO ltac:(lia)) as B1.
    mc_fwd.
    forward_if (temp _t'5 (Vint Int.one)).
    { mc_fwd. forward. entailer!.
      rewrite mc_shr by lia. unfold Int.lt.
      assert (0 <= Z.shiftr (Znth 0 (rf_O rf)) 4) by (apply Z.shiftr_nonneg; lia).
      rewrite !Int.signed_repr by rep_lia. rewrite zlt_false by lia. reflexivity. }
    { exfalso. match goal with H : Int.and _ _ <> _ |- _ => apply H end.
      rewrite mc_and by rep_lia. rewrite Fh0. reflexivity. }
    forward_if (temp _t'6 (Vint Int.one)).
    { mc_fwd. mc_fwd. forward. entailer!. rewrite mc_hdr31 by lia. reflexivity. }
    { exfalso. match goal with H : Int.one = Int.zero |- _ => apply Int.one_not_zero; exact H end. }
    forward_call (Int.one).
    mc_fwd. forward.
    forward_call (Int.one).
    { entailer!.
      assert (LR : 0 <= Z.land (Znth 1 (rf_O rf)) 32 < 256) by (apply mc_land_range; lia).
      destruct Hd as [(E1 & E2 & E3) | (E1 & E2)]; rewrite E1.
      - assert (Z.land (Znth 1 (rf_O rf)) 32 <> 0) by (apply Fdict; congruence).
        rewrite (Int.eq_false (Int.repr (Z.land (Znth 1 (rf_O rf)) 32)) (Int.repr 0))
          by (intro X; apply repr_inj_unsigned in X; rep_lia). reflexivity.
      - assert (E : Z.land (Znth 1 (rf_O rf)) 32 = 0)
          by (destruct (Z.eq_dec (Z.land (Znth 1 (rf_O rf)) 32) 0) as [|n]; [auto | apply Fdict in n; congruence]).
        rewrite E. reflexivity. }
    forward.
    forward_if True.
    { rewrite (bytes_cs CS DCS.CS Ews (Zlength (rf_O rf))).
      forward_call (offset_val 2 (rs_compp (rf_rs rf)), Ews, rs_compp (rf_rs rf), 2, Zlength (rf_O rf),
                    map vi (rf_O rf), sublist 2 6 (rf_O rf)).
      { apply mc_cbufL; auto; lia. }
      forward. forward.
      unfold obj at 1. Intros.
      rewrite (bytes_cs CS Zlib.units.Adler32.CS Ews (Zlength (rs_dict (rf_rs rf)))).
      forward_call (1, rs_dictp (rf_rs rf), Ews, rs_dictp (rf_rs rf), 0, Zlength (rs_dict (rf_rs rf)),
                    map vi (rs_dict (rf_rs rf)), Zlength (rs_dict (rf_rs rf)),
                    sublist 0 (Zlength (rs_dict (rf_rs rf))) (rs_dict (rf_rs rf))).
      { apply mc_cbuf0; auto; pose proof (Zlength_nonneg (rs_dict (rf_rs rf))); lia. }
      rewrite sublist_same by lia.
      assert (Ed : rf_dict rf = rs_dict (rf_rs rf) /\ rf_dict rf <> []).
      { destruct Hd as [(E1 & E2 & E3) | (E1 & E2)]; [split; congruence | ].
        match goal with H : Int.repr (rf_dset rf) <> Int.zero |- _ => rewrite E1 in H; contradiction end. }
      destruct Ed as [Ed1 Ed2]. specialize (Fdid Ed2). rewrite Ed1 in Fdid.
      forward_call (Int.one).
      { apply prop_right. unfold vl. rewrite Fdid. simpl. rewrite Int64.eq_true. reflexivity. }
      rewrite <- (bytes_cs CS Zlib.units.Adler32.CS Ews (Zlength (rs_dict (rf_rs rf)))).
      rewrite <- (bytes_cs CS DCS.CS Ews (Zlength (rf_O rf))).
      entailer!. unfold obj. cancel. }
    { forward. entailer!. }
    Intros.
    rewrite (bytes_cs CS DCS.CS Ews (Zlength (rf_O rf))).
    forward_call (offset_val (Zlength (rf_O rf) - 4) (rs_compp (rf_rs rf)), Ews, rs_compp (rf_rs rf),
                  Zlength (rf_O rf) - 4, Zlength (rf_O rf), map vi (rf_O rf),
                  sublist (Zlength (rf_O rf) - 4) (Zlength (rf_O rf)) (rf_O rf)).
    { unfold COMP_MAX in *. rewrite mc_add_long by (auto; rep_lia). auto. }
    { entailer!. destruct (rs_compp (rf_rs rf)) eqn:Ep; try contradiction. unfold vl. simpl.
      rewrite mc_ptrofs by (unfold COMP_MAX in *; rep_lia). reflexivity. }
    { apply mc_cbuf4; auto; lia. }
    rewrite Ftr.
    forward_call (Int.one).
    { apply prop_right. unfold vl. simpl. rewrite Int64.eq_true. reflexivity. }
    rewrite <- (bytes_cs CS DCS.CS Ews (Zlength (rf_O rf))).
    unfold run_ok_at, drun_rest, comp_at, obj. rewrite api_fields_L. unfold api_fieldsL.
    rewrite (mc_comp_split (rf_O rf) (rs_compp (rf_rs rf)) HOlen).
    entailer!.
  - forward.
    forward_if.
    + (* gzip *)
      assert (W2 : rf_wrap rf = 2) by lia.
      destruct FIN as (BO & _ & F2). specialize (F2 W2).
      destruct F2 as (Fk & Flen & Fhd & Ft1 & Ft2).
      forward. forward.
      unfold obj at 1. Intros.
      rewrite (bytes_cs CS Zlib.units.Crc32.CS Ews (Zlength (rs_data (rf_rs rf)))).
      forward_call (0, rs_datap (rf_rs rf), Ews, rs_datap (rf_rs rf), 0, Zlength (rs_data (rf_rs rf)),
                    map vi (rs_data (rf_rs rf)), rf_nf rf, sublist 0 (rf_nf rf) (rs_data (rf_rs rf))).
      { apply mc_cbuf0; auto. }
      rewrite <- (bytes_cs CS Zlib.units.Crc32.CS Ews (Zlength (rs_data (rf_rs rf)))).
      rewrite <- Fk.
      forward.
      rewrite api_fields_L. unfold api_fieldsL. Intros.
      forward.
      forward_call (Int.one).
      { apply prop_right. unfold vl. simpl. rewrite Int64.eq_true. reflexivity. }
      forward_call (Int.one).
      { apply prop_right. unfold vl, vi. simpl. unfold COMP_MAX in HOlen.
        rewrite ?Int.signed_repr by rep_lia.
        unfold Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia. rewrite zlt_false by lia. reflexivity. }
      unfold comp_at. rewrite (mc_comp_split (rf_O rf) (rs_compp (rf_rs rf)) HOlen). Intros.
      assert (G : forall i, 0 <= i < 3 -> Znth i (rf_O rf) = Znth i [31; 139; 8])
        by (intros; rewrite <- Fhd, Znth_sublist by lia; f_equal; lia).
      assert (G0 : Znth 0 (rf_O rf) = 31) by (rewrite (G 0) by lia; reflexivity).
      assert (G1 : Znth 1 (rf_O rf) = 139) by (rewrite (G 1) by lia; reflexivity).
      assert (G2 : Znth 2 (rf_O rf) = 8) by (rewrite (G 2) by lia; reflexivity).
      clear G.
      pose proof (mc_byte (rf_O rf) 0 BO ltac:(lia)) as B0.
      pose proof (mc_byte (rf_O rf) 1 BO ltac:(lia)) as B1.
      pose proof (mc_byte (rf_O rf) 2 BO ltac:(lia)) as B2.
      mc_fwd.
      forward_if (temp _t'11 (Vint Int.one)).
      { mc_fwd. forward. entailer!; rewrite ?G1; reflexivity. }
      { exfalso. rewrite G0 in *. match goal with H : ?a <> ?a |- _ => apply H; reflexivity end. }
      forward_if (temp _t'12 (Vint Int.one)).
      { mc_fwd. forward. entailer!; rewrite ?G2; reflexivity. }
      { exfalso. match goal with H : Int.one = Int.zero |- _ => apply Int.one_not_zero; exact H end. }
      forward_call (Int.one).
      rewrite (bytes_cs CS DCS.CS Ews (Zlength (rf_O rf))).
      forward_call (offset_val (Zlength (rf_O rf) - 8) (rs_compp (rf_rs rf)), Ews, rs_compp (rf_rs rf),
                    Zlength (rf_O rf) - 8, Zlength (rf_O rf), map vi (rf_O rf),
                    sublist (Zlength (rf_O rf) - 8) (Zlength (rf_O rf) - 4) (rf_O rf)).
      { unfold COMP_MAX in *. rewrite mc_add_long by (auto; rep_lia). auto. }
      { entailer!. destruct (rs_compp (rf_rs rf)) eqn:Ep; try contradiction. unfold vl. simpl.
        rewrite mc_ptrofs by (unfold COMP_MAX in *; rep_lia). reflexivity. }
      { apply mc_cbuf4; auto; lia. }
      rewrite Ft1.
      forward_if (temp _t'14 (Vint Int.one)).
      { forward_call (offset_val (Zlength (rf_O rf) - 4) (rs_compp (rf_rs rf)), Ews, rs_compp (rf_rs rf),
                      Zlength (rf_O rf) - 4, Zlength (rf_O rf), map vi (rf_O rf),
                      sublist (Zlength (rf_O rf) - 4) (Zlength (rf_O rf)) (rf_O rf)).
        { unfold COMP_MAX in *. rewrite mc_add_long by (auto; rep_lia). auto. }
        { entailer!. destruct (rs_compp (rf_rs rf)) eqn:Ep; try contradiction. unfold vl. simpl.
          rewrite mc_ptrofs by (unfold COMP_MAX in *; rep_lia). reflexivity. }
        { apply mc_cbuf4; auto; lia. }
        rewrite Ft2.
        forward. forward. entailer!.
        rewrite Z.land_m1_r, Zlength_sublist by lia. rewrite Z.sub_0_r, Z.mod_small by rep_lia.
        rewrite Int.unsigned_repr by rep_lia. unfold Int64.cmpu. rewrite Int64.eq_true. reflexivity. }
      { exfalso. match goal with H : ?a <> ?a |- _ => apply H; reflexivity end. }
      forward_call (Int.one).
      rewrite <- (bytes_cs CS DCS.CS Ews (Zlength (rf_O rf))).
      unfold run_ok_at, drun_rest, comp_at, obj. rewrite api_fields_L. unfold api_fieldsL.
      rewrite (mc_comp_split (rf_O rf) (rs_compp (rf_rs rf)) HOlen).
      entailer!.
    + (* raw *)
      forward. unfold run_ok_at, drun_rest. entailer!.
  - exact Hk.
Qed.
