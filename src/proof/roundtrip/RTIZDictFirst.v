(* RT-I, part rti_zdict: the first inflate() call on a zlib FDICT stream after inflateInit2(0):
   HEAD (any valid FLG with FDICT, also FCHECK = 31), DICTID, DICT: Z_NEED_DICT after exactly 6 bytes. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTIZDictDefs.
Import ListNotations.
Local Open Scope Z_scope.

Lemma rtz_pull s h inp ao nx ow hold bits nin out ret lv adl msg tin tout snx sow :
  pull (MS s h inp ao nx ow hold bits nin out ret lv adl msg tin tout snx sow) =
  MS s h inp ao (nx + 1) ow (u64 (hold + Znth nx inp * 2 ^ bits)) (u32 (bits + 8)) nin out ret lv adl msg tin tout snx sow.
Proof. reflexivity. Qed.

Lemma rtz_nb_step k n m : m_bits m < n -> m_have m <> 0 -> needbits_f (S k) n m = needbits_f k n (pull m).
Proof.
  intros B H. cbn [needbits_f]. rewrite (proj2 (Z.ltb_lt _ _) B), (proj2 (Z.eqb_neq _ _) H). reflexivity.
Qed.

Lemma rtz_nb_stop k n m : n <= m_bits m -> needbits_f (S k) n m = m.
Proof. intros B. cbn [needbits_f]. rewrite (proj2 (Z.ltb_ge _ _) B). reflexivity. Qed.

Ltac rtz_bits := cbn [m_bits]; vm_compute; first [reflexivity | intro; discriminate].

Ltac rtz_side :=
  unfold m_have; cbn [m_bits m_inp m_nx]; rewrite ?Zlength_cons;
  match goal with |- context[Zlength ?l] => pose proof (Zlength_nonneg l) | _ => idtac end;
  unfold u32; change (2 ^ 32) with 4294967296; rewrite ?Z.mod_small by lia; lia.

Ltac rtz_nb := first
  [ rewrite rtz_nb_step by first [rtz_bits | rtz_side]; rewrite rtz_pull
  | rewrite rtz_nb_stop by rtz_bits ].

Lemma rtz_nb16 s h c flg t ao nin out ret adl msg tin tout :
  0 <= c < 256 -> 0 <= flg < 256 ->
  needbits 16 (MS s h (c :: flg :: t) ao 0 [] 0 0 nin out ret 0 adl msg tin tout 0 0) =
  MS s h (c :: flg :: t) ao 2 [] (c + flg * 256) 16 nin out ret 0 adl msg tin tout 0 0.
Proof.
  intros Hc Hf. unfold needbits. rtz_nb. rtz_nb. rtz_nb.
  f_equal. change (Znth 0 (c :: flg :: t)) with c. change (Znth (0 + 1) (c :: flg :: t)) with flg.
  change (u32 (0 + 8)) with 8. unfold u64. change (2 ^ 64) with 18446744073709551616.
  change (2 ^ 0) with 1. change (2 ^ 8) with 256.
  rewrite (Z.mod_small (0 + c * 1)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Ltac rtz_u32 := repeat match goal with |- context[u32 ?x] => let v := eval vm_compute in (u32 x) in change (u32 x) with v end.

Lemma rtz_nb32 s h c f i0 i1 i2 i3 t ao nin out ret adl msg tin tout snx sow :
  0 <= i0 < 256 -> 0 <= i1 < 256 -> 0 <= i2 < 256 -> 0 <= i3 < 256 ->
  needbits 32 (MS s h (c :: f :: i0 :: i1 :: i2 :: i3 :: t) ao 2 [] 0 0 nin out ret 0 adl msg tin tout snx sow) =
  MS s h (c :: f :: i0 :: i1 :: i2 :: i3 :: t) ao 6 [] (i0 + i1 * 256 + i2 * 65536 + i3 * 16777216) 32 nin out ret 0
     adl msg tin tout snx sow.
Proof.
  intros H0 H1 H2 H3. unfold needbits. rtz_nb. rtz_nb. rtz_nb. rtz_nb. cbn [needbits_f].
  f_equal. rtz_u32.
  change (Znth 2 _) with i0. change (Znth (2 + 1) _) with i1. change (Znth (2 + 1 + 1) _) with i2.
  change (Znth (2 + 1 + 1 + 1) _) with i3. unfold u64. change (2 ^ 64) with 18446744073709551616.
  change (2 ^ 0) with 1. change (2 ^ 8) with 256. change (2 ^ 16) with 65536. change (2 ^ 24) with 16777216.
  rewrite (Z.mod_small (0 + i0 * 1)) by lia. rewrite (Z.mod_small (0 + i0 * 1 + i1 * 256)) by lia.
  rewrite (Z.mod_small (0 + i0 * 1 + i1 * 256 + i2 * 65536)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* the header tests of c_HEAD2 on hold = CMF + 256 FLG, checked for every wb and FLG *)
Definition rtz_hok (wb flg: Z) : bool :=
  let hv := RF.zcmf wb + flg * 256 in
  Bool.eqb (((hv mod 256) * 256 + Z.shiftr hv 8) mod 31 =? 0) ((RF.zcmf wb * 256 + flg) mod 31 =? 0) &&
  (hv mod 16 =? 8) && (Z.shiftr hv 4 mod 16 + 8 =? wb) &&
  Bool.eqb (Z.land (Z.shiftr hv 4) 512 =? 0) (negb (Z.testbit flg 5)) && (0 <=? RF.zcmf wb) && (RF.zcmf wb <? 256).

Lemma rtz_hok_tab :
  forallb (fun wb => forallb (fun flg => rtz_hok wb flg) (map Z.of_nat (seq 0 256))) (map Z.of_nat (seq 9 7)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rtz_hok_all wb flg : 9 <= wb <= 15 -> 0 <= flg < 256 -> rtz_hok wb flg = true.
Proof.
  intros Hw Hf. pose proof rtz_hok_tab as T. rewrite forallb_forall in T.
  assert (Iw : In wb (map Z.of_nat (seq 9 7))).
  { rewrite <- (Z2Nat.id wb) by lia. apply in_map, in_seq. lia. }
  specialize (T wb Iw). rewrite forallb_forall in T. apply T.
  rewrite <- (Z2Nat.id flg) by lia. apply in_map, in_seq. lia.
Qed.

Lemma rtz_hdr wb flg : 9 <= wb <= 15 -> RF.zflg_ok wb true flg ->
  let hv := RF.zcmf wb + flg * 256 in
  (((hv mod 256) * 256 + Z.shiftr hv 8) mod 31 =? 0) = true /\ (hv mod 16 =? 8) = true /\
  Z.shiftr hv 4 mod 16 + 8 = wb /\ (Z.land (Z.shiftr hv 4) 512 =? 0) = false /\ 0 <= RF.zcmf wb < 256.
Proof.
  intros Hw (Hf & H31 & Hb). pose proof (rtz_hok_all wb flg Hw Hf) as T. unfold rtz_hok in T. cbv zeta in *.
  repeat rewrite andb_true_iff in T. destruct T as [[[[[A B] C] D] E] F].
  apply Bool.eqb_prop in A, D. rewrite Hb in D. rewrite H31, Z.eqb_refl in A. apply Z.eqb_eq in C.
  apply Z.leb_le in E. apply Z.ltb_lt in F. repeat split; auto; lia.
Qed.

(* c_HEAD2 on the state of inflateInit2(windowBits 0): wrap 13, the zlib wrapper 5 with bit 3 (patch F8) *)
Lemma rtz_head fl fx dx s h wb flg t ao nin adl msg tin tout :
  i_mode s = HEAD -> i_wrap s = 13 -> i_wbits s = 0 -> i_head s = false -> 9 <= wb <= 15 -> RF.zflg_ok wb true flg ->
  stepf2 fl fx dx (MS s h (RF.zcmf wb :: flg :: t) ao 0 [] 0 0 nin ao Z_OK 0 adl msg tin tout 0 0) =
  IBrk (MS (set_i_mode (set_i_check (set_i_flags (set_i_dmax (set_i_wbits s wb) (2 ^ wb)) 0) 1) DICTID)
           h (RF.zcmf wb :: flg :: t) ao 2 [] 0 0 nin ao Z_OK 0 1 msg tin tout 0 0).
Proof.
  intros Hm Hw Hb Hh Hwb Hf.
  pose proof (rtz_hdr wb flg Hwb Hf) as (H1 & H2 & H3 & H4 & Hc). cbv zeta in H1, H2, H3, H4.
  pose proof Hf as (Hf8 & _).
  unfold stepf2, step2. unfold m_mode. cbn [m_s]. rewrite Hm. change (HEAD =? HEAD) with true. cbv beta iota.
  unfold c_HEAD2. cbn [m_s]. rewrite Hw. change (13 =? 0) with false. cbv beta iota.
  rewrite rtz_nb16 by lia.
  cbn [m_s m_leave m_hold m_bits set_mode upd_s set_m_s set_m_hold set_m_bits set_m_adler dropbits initbits].
  rewrite Hh, Hw. change (0 =? 1) with false. change (Z.land 13 2 =? 0) with true. change (Z.land 13 1 =? 0) with false.
  cbv beta iota.
  cbn [m_s m_leave m_hold m_bits set_mode upd_s set_m_s set_m_hold set_m_bits set_m_adler dropbits initbits negb andb orb].
  rewrite H1, H2. cbn [negb orb]. rewrite H3, Hb. change (0 =? 0) with true. cbv beta iota.
  replace (15 <? wb) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb negb andb].
  rewrite H4.
  cbn [m_s m_leave m_hold m_bits set_mode upd_s set_m_s set_m_hold set_m_bits set_m_adler dropbits initbits].
  destruct s; cbn in Hb; subst. reflexivity.
Qed.

Lemma rtz_step_dictid fl fx dx m : m_mode m = DICTID -> stepf2 fl fx dx m = c_DICTID fl m.
Proof. intros H. unfold stepf2, step2. rewrite H. reflexivity. Qed.

Lemma rtz_dictid fl fx dx s h c f i0 i1 i2 i3 t ao nin adl msg tin tout :
  i_mode s = DICTID -> i_havedict s = 0 ->
  0 <= i0 < 256 -> 0 <= i1 < 256 -> 0 <= i2 < 256 -> 0 <= i3 < 256 ->
  let q := swap32 (i0 + i1 * 256 + i2 * 65536 + i3 * 16777216) in
  exists tin', stepf2 fl fx dx (MS s h (c :: f :: i0 :: i1 :: i2 :: i3 :: t) ao 2 [] 0 0 nin ao Z_OK 0 adl msg tin tout 0 0) =
  IRet Z_NEED_DICT (MS (set_i_bits (set_i_hold (set_i_mode (set_i_check s q) DICT) 0) 0) h
                       (c :: f :: i0 :: i1 :: i2 :: i3 :: t) ao 6 [] 0 0 nin ao Z_OK 0 q msg tin' tout 6 0).
Proof.
  intros Hm Hd H0 H1 H2 H3 q.
  rewrite rtz_step_dictid by exact Hm. unfold c_DICTID. rewrite rtz_nb32 by assumption.
  unfold c_DICT. destruct s; cbn in Hd; subst. eexists. reflexivity.
Qed.

(* ZSWAP32 of the little-endian value of the big-endian bytes of id is id (TheoryDict.td_swap, ITPre.itp_be32) *)
Fixpoint rtz_zup (n: nat) (z: Z) : list Z := match n with O => [] | S n' => z :: rtz_zup n' (z + 1) end.

Lemma rtz_in_zup n : forall z x, z <= x < z + Z.of_nat n -> In x (rtz_zup n z).
Proof.
  induction n as [|n IH]; intros z x H; [lia|]. cbn [rtz_zup].
  destruct (Z.eq_dec x z) as [E|E]; [left; auto|right; apply IH; lia].
Qed.

Lemma rtz_ff00_tab : forallb (fun v => Z.land v 65280 =? v / 256 * 256) (rtz_zup (Z.to_nat 65536) 0) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rtz_ff00 y : Z.land y 65280 = (y mod 65536) / 256 * 256.
Proof.
  change 65280 with (Z.land (Z.ones 16) 65280) at 1. rewrite Z.land_assoc, Z.land_ones by lia.
  change (2 ^ 16) with 65536.
  pose proof rtz_ff00_tab as T. rewrite forallb_forall in T.
  assert (R : 0 <= y mod 65536 < 65536) by (apply Z.mod_pos_bound; lia).
  assert (I : In (y mod 65536) (rtz_zup (Z.to_nat 65536) 0))
    by (apply rtz_in_zup; change (Z.of_nat (Z.to_nat 65536)) with 65536; lia).
  specialize (T _ I). apply Z.eqb_eq in T. exact T.
Qed.

Lemma rtz_swap b0 b1 b2 b3 :
  0 <= b0 <= 255 -> 0 <= b1 <= 255 -> 0 <= b2 <= 255 -> 0 <= b3 <= 255 ->
  swap32 (b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * 0)))) = b0 * 2 ^ 24 + b1 * 2 ^ 16 + b2 * 2 ^ 8 + b3.
Proof.
  intros H0 H1 H2 H3. unfold swap32.
  rewrite !Z.shiftr_div_pow2, !Z.shiftl_mul_pow2 by lia. rewrite !rtz_ff00.
  change (2 ^ 24) with 16777216. change (2 ^ 16) with 65536. change (2 ^ 8) with 256.
  set (x := b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * 0)))).
  assert (E1 : x / 16777216 = b3)
    by (symmetry; apply Z.div_unique with (r := b0 + 256 * b1 + 65536 * b2); [left|]; unfold x; lia).
  assert (E2 : x / 256 = b1 + 256 * b2 + 65536 * b3)
    by (symmetry; apply Z.div_unique with (r := b0); [left|]; unfold x; lia).
  assert (E3 : x mod 65536 = b0 + 256 * b1)
    by (symmetry; apply Z.mod_unique with (q := b2 + 256 * b3); [left|]; unfold x; lia).
  assert (E4 : x mod 256 = b0)
    by (symmetry; apply Z.mod_unique with (q := b1 + 256 * (b2 + 256 * b3)); [left|]; unfold x; lia).
  rewrite E1, E2, E3, E4. clear E1 E2 E3 E4 x.
  assert (E5 : (b1 + 256 * b2 + 65536 * b3) mod 65536 = b1 + 256 * b2)
    by (symmetry; apply Z.mod_unique with (q := b3); [left|]; lia).
  assert (E6 : (b1 + 256 * b2) / 256 = b2) by (symmetry; apply Z.div_unique with (r := b1); [left|]; lia).
  assert (E7 : (b0 + 256 * b1) / 256 = b1) by (symmetry; apply Z.div_unique with (r := b0); [left|]; lia).
  rewrite E5, E6, E7. rewrite (Z.mod_small b3 256) by lia. lia.
Qed.

Lemma rtz_be v : 0 <= v < 2 ^ 32 ->
  (Z.shiftr v (8 * 3) mod 256) * 2 ^ 24 + (Z.shiftr v (8 * 2) mod 256) * 2 ^ 16 +
  (Z.shiftr v (8 * 1) mod 256) * 2 ^ 8 + Z.shiftr v (8 * 0) mod 256 = v.
Proof.
  intros Hv.
  rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ (8 * 0)) with 1. rewrite Z.div_1_r.
  change (2 ^ (8 * 1)) with 256. change (2 ^ (8 * 2)) with 65536. change (2 ^ (8 * 3)) with 16777216.
  change (2 ^ 24) with 16777216. change (2 ^ 16) with 65536. change (2 ^ 8) with 256.
  assert (v / 16777216 < 256) by (apply Z.div_lt_upper_bound; lia).
  rewrite (Z.mod_small (v / 16777216)) by (split; [apply Z.div_pos|]; lia).
  pose proof (Z.div_mod v 256 ltac:(lia)).
  pose proof (Z.div_mod (v / 256) 256 ltac:(lia)).
  pose proof (Z.div_mod (v / 65536) 256 ltac:(lia)).
  assert (D1 : v / 256 / 256 = v / 65536) by (rewrite Z.div_div by lia; reflexivity).
  assert (D2 : v / 65536 / 256 = v / 16777216) by (rewrite Z.div_div by lia; reflexivity).
  rewrite D1 in *. rewrite D2 in *. lia.
Qed.

Lemma rtz_id v : 0 <= v < 2 ^ 32 ->
  swap32 (Z.shiftr v (8 * 3) mod 256 + Z.shiftr v (8 * 2) mod 256 * 256 + Z.shiftr v (8 * 1) mod 256 * 65536 +
          Z.shiftr v (8 * 0) mod 256 * 16777216) = v.
Proof.
  intros Hv.
  pose proof (Z.mod_pos_bound (Z.shiftr v (8 * 3)) 256 ltac:(lia)).
  pose proof (Z.mod_pos_bound (Z.shiftr v (8 * 2)) 256 ltac:(lia)).
  pose proof (Z.mod_pos_bound (Z.shiftr v (8 * 1)) 256 ltac:(lia)).
  pose proof (Z.mod_pos_bound (Z.shiftr v (8 * 0)) 256 ltac:(lia)).
  match goal with |- swap32 (?a + ?b * 256 + ?c * 65536 + ?d * 16777216) = _ =>
    replace (a + b * 256 + c * 65536 + d * 16777216) with (a + 256 * (b + 256 * (c + 256 * (d + 256 * 0)))) by lia;
    rewrite rtz_swap by lia end.
  apply rtz_be; exact Hv.
Qed.

Lemma rtz_first : forall flush wb flg id rest z sp res,
  9 <= wb <= 15 -> RF.zflg_ok wb true flg -> 0 <= id < 2 ^ 32 -> zf_ok z ->
  run2 flush lenfix_list distfix_list (m_init z (init_live sp 0) ([RF.zcmf wb; flg] ++ be_bytes id 4 ++ rest)) res ->
  r_ret res = Z_NEED_DICT /\ m_snx (r_m res) = 6 /\ m_ow (r_m res) = [] /\ m_sow (r_m res) = 0 /\
  m_aout (r_m res) = zf_ao z /\ m_tout (r_m res) = zf_tout z /\ m_adler (r_m res) = id /\
  zd_nd wb id (m_s (r_m res)).
Proof.
  intros flush wb flg id rest z sp res Hwb Hf Hid Hz (o & HL & Ho).
  assert (E : be_bytes id 4 = [Z.shiftr id (8 * 3) mod 256; Z.shiftr id (8 * 2) mod 256; Z.shiftr id (8 * 1) mod 256;
                               Z.shiftr id (8 * 0) mod 256]) by reflexivity.
  rewrite E in HL. cbn [app] in HL.
  pose proof (Z.mod_pos_bound (Z.shiftr id (8 * 3)) 256 ltac:(lia)) as B0.
  pose proof (Z.mod_pos_bound (Z.shiftr id (8 * 2)) 256 ltac:(lia)) as B1.
  pose proof (Z.mod_pos_bound (Z.shiftr id (8 * 1)) 256 ltac:(lia)) as B2.
  pose proof (Z.mod_pos_bound (Z.shiftr id (8 * 0)) 256 ltac:(lia)) as B3.
  pose proof (rtz_id id Hid) as Q.
  set (i0 := Z.shiftr id (8 * 3) mod 256) in *. set (i1 := Z.shiftr id (8 * 2) mod 256) in *.
  set (i2 := Z.shiftr id (8 * 1) mod 256) in *. set (i3 := Z.shiftr id (8 * 0) mod 256) in *.
  clearbody i0 i1 i2 i3. clear E.
  assert (Hs : l_s (init_live sp 0) = init_s 5 0) by reflexivity.
  unfold m_init in HL. rewrite Hs in HL. set (h0 := l_h (init_live sp 0)) in HL. clearbody h0.
  assert (F : i_mode (init_s 5 0) = HEAD /\ i_wrap (init_s 5 0) = 13 /\ i_wbits (init_s 5 0) = 0 /\
              i_head (init_s 5 0) = false /\ i_havedict (init_s 5 0) = 0 /\ i_hold (init_s 5 0) = 0 /\
              i_bits (init_s 5 0) = 0 /\ i_last (init_s 5 0) = 0 /\ i_total (init_s 5 0) = 0 /\
              i_wsize (init_s 5 0) = 0 /\ i_whave (init_s 5 0) = 0 /\ i_wnext (init_s 5 0) = 0 /\
              i_win (init_s 5 0) = false /\ i_wdata (init_s 5 0) = []) by (vm_compute; repeat split).
  remember (init_s 5 0) as s0 eqn:Es. clear Es Hs.
  destruct F as (Fm & Fw & Fb & Fh & Fd & Fho & Fbi & Fl & Ft & Fws & Fwh & Fwn & Fwi & Fwd).
  cbv zeta in HL. rewrite Fm in HL. change (HEAD =? Zlib.proof.inflate.Model.TYPE) with false in HL.
  cbv beta iota in HL. rewrite Fho, Fbi in HL.
  inversion HL as [m r m' S1 | m m' S1 L1 | m m' o' S1 L1 HL2]; clear HL;
    rewrite rtz_head in S1 by assumption.
  - discriminate.
  - injection S1 as <-. cbn in L1. discriminate.
  - injection S1 as <-. clear L1.
    destruct (rtz_dictid flush lenfix_list distfix_list
                (set_i_mode (set_i_check (set_i_flags (set_i_dmax (set_i_wbits s0 wb) (2 ^ wb)) 0) 1) DICTID)
                h0 (RF.zcmf wb) flg i0 i1 i2 i3 rest (zf_ao z) (Zlength (RF.zcmf wb :: flg :: i0 :: i1 :: i2 :: i3 :: rest))
                1 (zf_msg z) (zf_tin z) (zf_tout z)) as (tin' & S2);
      [destruct s0; reflexivity | destruct s0; cbn in Fd |- *; exact Fd | auto.. |].
    rewrite Q in S2.
    inversion HL2 as [n r2 n' S3 | n n' S3 L3 | n n' o'' S3 L3 HL3]; clear HL2; rewrite S2 in S3; try discriminate.
    injection S3 as <- <-. subst. cbn in Ho. subst res. cbn [r_ret r_m m_snx m_ow m_sow m_aout m_tout m_adler m_s].
    do 7 (split; [reflexivity|]).
    unfold zd_nd. destruct s0; cbn in *; subst. repeat split; reflexivity.
Qed.
