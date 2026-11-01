(* Law inflate_codes, theory part: the cases DICTID, DICT, TYPE, TYPEDO *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_codes.TheoryDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* stepf2 per mode                                                                                *)

Lemma td_step_DICTID fl fx dx m : m_mode m = DICTID -> stepf2 fl fx dx m = c_DICTID fl m.
Proof. intros H. unfold stepf2, Zlib.proof.inflate.Model2.step2. rewrite H. reflexivity. Qed.
Lemma td_step_DICT fl fx dx m : m_mode m = DICT -> stepf2 fl fx dx m = c_DICT fl m.
Proof. intros H. unfold stepf2, Zlib.proof.inflate.Model2.step2. rewrite H. reflexivity. Qed.
Lemma td_step_TYPE fl fx dx m : m_mode m = Zlib.proof.inflate.Model.TYPE -> stepf2 fl fx dx m = c_TYPE fl m.
Proof. intros H. unfold stepf2, Zlib.proof.inflate.Model2.step2. rewrite H. reflexivity. Qed.
Lemma td_step_TYPEDO fl fx dx m : m_mode m = TYPEDO -> stepf2 fl fx dx m = c_TYPEDO fl m.
Proof. intros H. unfold stepf2, Zlib.proof.inflate.Model2.step2. rewrite H. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Little-endian values                                                                           *)

Lemma td_le_app l b : le_val (l ++ [b]) = le_val l + b * 2 ^ (8 * Zlength l).
Proof.
  induction l as [|a l IH]; cbn [le_val app].
  - rewrite Zlength_nil. change (2 ^ (8 * 0)) with 1. lia.
  - rewrite IH, Zlength_cons. replace (8 * Z.succ (Zlength l)) with (8 + 8 * Zlength l) by lia.
    rewrite Z.pow_add_r by (pose proof (Zlength_nonneg l); lia). change (2 ^ 8) with 256. lia.
Qed.

Lemma td_le_bound l : Forall (fun b => 0 <= b <= 255) l -> 0 <= le_val l < 2 ^ (8 * Zlength l).
Proof.
  induction l as [|a l IH]; intros F; cbn [le_val].
  - rewrite Zlength_nil. change (2 ^ (8 * 0)) with 1. lia.
  - inversion F; subst. specialize (IH H2). rewrite Zlength_cons.
    replace (8 * Z.succ (Zlength l)) with (8 + 8 * Zlength l) by lia.
    rewrite Z.pow_add_r by (pose proof (Zlength_nonneg l); lia). change (2 ^ 8) with 256. lia.
Qed.

Lemma td_byte src pos inp k :
  ctx_ok src pos inp -> 0 <= k < Zlength inp ->
  Znth k inp = Znth (pos + k) src /\ 0 <= Znth (pos + k) src <= 255.
Proof.
  intros (Hp & Hl & Hb & He) Hk. split; [apply He; auto|].
  unfold bytes_ok in Hb. rewrite Forall_forall in Hb.
  assert (0 <= pos + k < Zlength src) by lia.
  pose proof (Hb (Znth (pos + k) src)) as X. replace Byte.max_unsigned with 255 in X by reflexivity.
  apply X. apply Znth_In; lia.
Qed.

Lemma td_src_bytes src i j : bytes_ok src -> 0 <= i <= j -> j <= Zlength src ->
  Forall (fun b => 0 <= b <= 255) (sublist i j src).
Proof.
  intros Hb Hi Hj. unfold bytes_ok in Hb. apply Forall_sublist.
  replace 255 with Byte.max_unsigned by reflexivity. exact Hb.
Qed.

Lemma td_u32 x : 0 <= x < 2 ^ 32 -> u32 x = x.
Proof. intros. unfold u32. apply Z.mod_small. lia. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* NEEDBITS(32) in DICTID                                                                         *)

Definition td_sh (src: list Z) (pos: Z) (m: mst) (n: Z) : mst :=
  set_m_bits (set_m_hold (set_m_nx m n) (le_val (sublist 2 (pos + n) src))) (8 * (pos + n - 2)).

Lemma td_sh_sh src pos m a b : td_sh src pos (td_sh src pos m a) b = td_sh src pos m b.
Proof. destruct m; reflexivity. Qed.

Lemma td_sh_self src pos m :
  m_hold m = le_val (sublist 2 (pos + m_nx m) src) -> m_bits m = 8 * (pos + m_nx m - 2) ->
  td_sh src pos m (m_nx m) = m.
Proof. destruct m; cbn; intros -> ->; reflexivity. Qed.

Lemma td_pull m src pos :
  ctx_ok src pos (m_inp m) -> 0 <= m_nx m < Zlength (m_inp m) ->
  2 <= pos + m_nx m <= 5 -> m_bits m = 8 * (pos + m_nx m - 2) ->
  m_hold m = le_val (sublist 2 (pos + m_nx m) src) ->
  pull m = td_sh src pos m (m_nx m + 1).
Proof.
  intros Hc Hn Hp Hb Hh.
  destruct (td_byte src pos (m_inp m) (m_nx m) Hc Hn) as [Eb Rb].
  pose proof Hc as (H0 & Hl & Hbo & _).
  unfold pull, td_sh. rewrite Eb, Hb, Hh.
  rewrite (sublist_split 2 (pos + m_nx m) (pos + (m_nx m + 1)) src) by lia.
  rewrite (sublist_one (pos + m_nx m) (pos + (m_nx m + 1)) src) by lia.
  rewrite td_le_app, Zlength_sublist by lia.
  pose proof (td_le_bound (sublist 2 (pos + m_nx m) src) (td_src_bytes src 2 (pos + m_nx m) Hbo ltac:(lia) ltac:(lia))) as LB.
  rewrite Zlength_sublist in LB by lia.
  replace (pos + m_nx m - 2) with (pos + m_nx m - 2) by lia.
  f_equal; [f_equal|].
  - unfold u64. rewrite Z.mod_small; [reflexivity|].
    assert (2 ^ (8 * (pos + m_nx m - 2)) <= 2 ^ 24) by (apply Z.pow_le_mono_r; lia).
    assert (0 <= 2 ^ (8 * (pos + m_nx m - 2))) by (apply Z.pow_nonneg; lia).
    nia.
  - unfold u32. rewrite Z.mod_small; lia.
Qed.

Lemma td_nbS k n m :
  needbits_f (S k) n m = if m_bits m <? n then if m_have m =? 0 then set_leave m else needbits_f k n (pull m) else m.
Proof. reflexivity. Qed.

Lemma td_nbk src pos : forall k m,
  ctx_ok src pos (m_inp m) -> 0 <= m_nx m <= Zlength (m_inp m) ->
  2 <= pos + m_nx m <= 6 -> m_bits m = 8 * (pos + m_nx m - 2) ->
  m_hold m = le_val (sublist 2 (pos + m_nx m) src) -> 6 <= pos + m_nx m + Z.of_nat k ->
  exists nx', m_nx m <= nx' <= Zlength (m_inp m) /\
   ((needbits_f k 32 m = set_leave (td_sh src pos m nx') /\ pos + nx' <= 5) \/
    (needbits_f k 32 m = td_sh src pos m nx' /\ pos + nx' = 6)).
Proof.
  induction k as [|k IH]; intros m Hc Hn Hp Hb Hh Hk.
  - exists (m_nx m). split; [lia|]. right. split; [|lia]. cbn [needbits_f].
    symmetry. apply td_sh_self; auto.
  - rewrite td_nbS. destruct (Z.eq_dec (pos + m_nx m) 6) as [E6|E6].
    { replace (m_bits m <? 32) with false by (symmetry; apply Z.ltb_ge; lia).
      exists (m_nx m). split; [lia|]. right. split; [|lia]. symmetry. apply td_sh_self; auto. }
    replace (m_bits m <? 32) with true by (symmetry; apply Z.ltb_lt; lia).
    destruct (m_have m =? 0) eqn:E0.
    { exists (m_nx m). split; [lia|]. left. split; [|lia]. rewrite td_sh_self; auto. }
    unfold m_have in E0. apply Z.eqb_neq in E0.
    rewrite (td_pull m src pos) by (auto; lia).
    destruct (IH (td_sh src pos m (m_nx m + 1))) as (nx' & Hn' & R); try exact Hc;
      unfold td_sh; cbn [m_nx m_inp m_bits m_hold set_m_bits set_m_hold set_m_nx]; try lia; try reflexivity.
    fold (td_sh src pos m (m_nx m + 1)) in R. rewrite !td_sh_sh in R.
    exists nx'. split; [cbn in Hn'; lia|]. exact R.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* ZSWAP32 of the little-endian dictionary id is its big-endian value                             *)

Fixpoint td_zup (n: nat) (z: Z) : list Z := match n with O => [] | S n' => z :: td_zup n' (z + 1) end.

Lemma td_in_zup n : forall z x, z <= x < z + Z.of_nat n -> In x (td_zup n z).
Proof.
  induction n as [|n IH]; intros z x H; [lia|]. cbn [td_zup].
  destruct (Z.eq_dec x z) as [E|E]; [left; auto|right; apply IH; lia].
Qed.

Lemma td_ff00_tab : forallb (fun v => Z.land v 65280 =? v / 256 * 256) (td_zup (Z.to_nat 65536) 0) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma td_ff00 y : Z.land y 65280 = (y mod 65536) / 256 * 256.
Proof.
  change 65280 with (Z.land (Z.ones 16) 65280) at 1. rewrite Z.land_assoc, Z.land_ones by lia.
  change (2 ^ 16) with 65536.
  pose proof td_ff00_tab as T. rewrite forallb_forall in T.
  assert (R : 0 <= y mod 65536 < 65536) by (apply Z.mod_pos_bound; lia).
  assert (I : In (y mod 65536) (td_zup (Z.to_nat 65536) 0))
    by (apply td_in_zup; change (Z.of_nat (Z.to_nat 65536)) with 65536; lia).
  specialize (T _ I). apply Z.eqb_eq in T. exact T.
Qed.

Lemma td_swap b0 b1 b2 b3 :
  0 <= b0 <= 255 -> 0 <= b1 <= 255 -> 0 <= b2 <= 255 -> 0 <= b3 <= 255 ->
  swap32 (b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * 0)))) = b0 * 2 ^ 24 + b1 * 2 ^ 16 + b2 * 2 ^ 8 + b3.
Proof.
  intros H0 H1 H2 H3. unfold swap32.
  rewrite !Z.shiftr_div_pow2, !Z.shiftl_mul_pow2 by lia. rewrite !td_ff00.
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

Lemma td_dict_id src : bytes_ok src -> 6 <= Zlength src ->
  swap32 (le_val (sublist 2 6 src)) = dict_id src.
Proof.
  intros Hb Hl. unfold dict_id, be32.
  pose proof (td_src_bytes src 2 6 Hb ltac:(lia) ltac:(lia)) as F.
  assert (B : forall k, 0 <= k < 4 -> 0 <= Znth k (sublist 2 6 src) <= 255).
  { intros k Hk. rewrite Forall_forall in F. apply F, Znth_In. rewrite Zlength_sublist; lia. }
  assert (E : sublist 2 6 src = [Znth 0 (sublist 2 6 src); Znth 1 (sublist 2 6 src); Znth 2 (sublist 2 6 src); Znth 3 (sublist 2 6 src)]).
  { rewrite !Znth_sublist by lia.
    rewrite (sublist_split 2 3 6), (sublist_split 3 4 6), (sublist_split 4 5 6) by lia.
    rewrite !sublist_one by lia. reflexivity. }
  rewrite E at 1. cbn [le_val]. apply td_swap; apply B; lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Kc after one of these cases                                                                    *)

Lemma td_Kc wrap src pos inp aout m m' :
  Kc wrap src pos inp aout m ->
  m_inp m' = m_inp m -> m_aout m' = m_aout m -> i_wrap (m_s m') = i_wrap (m_s m) ->
  i_head (m_s m') = i_head (m_s m) -> m_out m' = m_out m -> m_ret m' = Z_OK -> m_nx m <= m_nx m' ->
  m_mode m' <> SYNC -> m_mode m' <> DONE -> m_mode m' <> HEAD ->
  (m_leave m' = 1 -> m_mode m' <> BAD) ->
  (m_mode m' = BAD -> m_msg m' <> None) ->
  (m_mode m' <> BAD -> 0 <= m_bits m' <= 31) ->
  (m_mode m' = DICTID -> Z.land wrap 1 <> 0 /\ hd_dictid src (pos + m_nx m') (m_hold m') (m_bits m')) ->
  (m_mode m' = DICT -> Z.land wrap 1 <> 0 /\ fdict src /\ pos + m_nx m' = 6 /\
                        i_check (m_s m') = dict_id src /\ m_adler m' = dict_id src) ->
  Kc wrap src pos inp aout m'.
Proof.
  intros K Hi Ha Hw Hh Ho Hr Hn Hs Hd Hhd Hlv Hmsg Hb Hdid Hdict.
  constructor.
  - rewrite Hi; apply (kc_inp _ _ _ _ _ _ K).
  - rewrite Ha; apply (kc_aout _ _ _ _ _ _ K).
  - rewrite Hw; apply (kc_wrap _ _ _ _ _ _ K).
  - rewrite Hh; apply (kc_head _ _ _ _ _ _ K).
  - exact Hs.
  - intros _ _. exact Hr.
  - intros L. split; intro E; [contradiction|]. exfalso; exact (Hlv L E).
  - exact Hmsg.
  - intros B _. auto.
  - intros O. rewrite Ho, Ha in O. pose proof (kc_out _ _ _ _ _ _ K O). lia.
  - intros _ E; contradiction.
  - exact Hdid.
  - exact Hdict.
Qed.

Ltac td_red :=
  unfold m_mode; cbn [m_nx m_bits m_hold m_msg m_s m_inp m_aout m_out m_ret m_leave m_adler m_ow m_snx m_sow
       set_mode upd_s set_m_s set_m_h upd_h set_m_nx set_m_hold set_m_bits set_m_msg set_m_adler set_m_tin
       set_leave set_m_leave set_bad initbits dropbits bytebits restore set_m_snx set_m_sow td_sh
       i_mode i_wrap i_head i_check set_i_mode set_i_check set_i_last set_i_lencode set_i_lenbits
       set_i_distcode set_i_distbits set_i_bits set_i_hold].

Ltac td_cst := unfold HEAD, FLAGS, DICTID, TYPEDO, SYNC, DONE, DICT, BAD, MEM, STORED, LEN_, TABLE, CHECK,
                 Zlib.proof.inflate.Model.TYPE.

Lemma td_lv1 x : (m_leave (set_leave x) =? 1) = true.
Proof. reflexivity. Qed.

(* NEEDBITS(3) from bits <= 31 *)
Lemma td_nb3 m : 0 <= m_bits m <= 31 ->
  needbits 3 m = set_leave m \/
  (m_leave (needbits 3 m) = m_leave m /\ 3 <= m_bits (needbits 3 m) <= 31 /\
   m_inp (needbits 3 m) = m_inp m /\ m_s (needbits 3 m) = m_s m /\ m_nx m <= m_nx (needbits 3 m) /\
   m_out (needbits 3 m) = m_out m /\ m_ret (needbits 3 m) = m_ret m /\ m_aout (needbits 3 m) = m_aout m /\
   m_msg (needbits 3 m) = m_msg m).
Proof.
  intros Hb. unfold needbits. rewrite td_nbS.
  destruct (m_bits m <? 3) eqn:E3.
  - apply Z.ltb_lt in E3. destruct (m_have m =? 0); [left; reflexivity|].
    assert (Bp : m_bits (pull m) = m_bits m + 8) by (unfold pull; cbn [m_bits set_m_bits]; apply td_u32; lia).
    assert (E : needbits_f 3 3 (pull m) = pull m).
    { rewrite td_nbS, Bp. replace (m_bits m + 8 <? 3) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
    rewrite E. right. rewrite Bp. unfold pull. cbn [m_leave m_inp m_s m_nx m_out m_ret m_aout m_msg set_m_bits set_m_hold set_m_nx].
    repeat split; lia.
  - apply Z.ltb_ge in E3. right. repeat split; lia.
Qed.

Lemma td_u32_1 b : 1 <= b <= 32 -> u32 (b - 1) = b - 1.
Proof. intros. apply td_u32. lia. Qed.
Lemma td_u32_2 b : 3 <= b <= 32 -> u32 (u32 (b - 1) - 2) = b - 1 - 2.
Proof. intros. rewrite td_u32_1 by lia. apply td_u32. lia. Qed.

Ltac td_side :=
  repeat match goal with x := _ |- _ => subst x end;
  td_red;
  repeat match goal with H : ?a = _ |- context [?a] => progress rewrite H end;
  rewrite ?td_u32_2 by lia; rewrite ?td_u32_1 by lia;
  td_cst; unfold m_mode, HEAD, FLAGS, DICTID, TYPEDO, SYNC, DONE, DICT, BAD, MEM, Zlib.proof.inflate.Model.TYPE in *;
  intros; first [lia | congruence | discriminate | assumption].

Lemma td_typedo wrap src pos inp aout flush m m0 :
  Kc wrap src pos inp aout m -> m_leave m = 0 ->
  (m_mode m = Zlib.proof.inflate.Model.TYPE \/ m_mode m = TYPEDO) ->
  step_post wrap src pos inp aout m0 (c_TYPEDO flush m).
Proof.
  intros K Hl Hmd.
  assert (HB : 0 <= m_bits m <= 31)
    by (apply (kc_bits _ _ _ _ _ _ K); destruct Hmd as [E|E]; rewrite E; td_cst; lia).
  assert (Hr : m_ret m = Z_OK)
    by (apply (kc_ret _ _ _ _ _ _ K); destruct Hmd as [E|E]; rewrite E; td_cst; lia).
  unfold c_TYPEDO.
  destruct (negb (i_last (m_s m) =? 0)).
  { cbn [step_post]. pose proof (Z.mod_pos_bound (m_bits m) 8 ltac:(lia)). pose proof (Z.mod_le (m_bits m) 8 ltac:(lia) ltac:(lia)).
    split; [apply (td_Kc wrap src pos inp aout m); auto; td_side | td_side]. }
  destruct (td_nb3 m HB) as [E|(L3 & B3 & I3 & S3 & N3 & O3 & R3 & A3 & M3)].
  { rewrite E, td_lv1. cbn [step_post].
    split; [apply (td_Kc wrap src pos inp aout m); auto; td_side | td_side]. }
  set (m3 := needbits 3 m) in *. clearbody m3.
  replace (m_leave m3 =? 1) with false by (rewrite L3, Hl; reflexivity).
  cbv zeta.
  destruct (_ =? 0); [|destruct (_ =? 1); [destruct (flush =? Z_TREES)|destruct (_ =? 2)]];
    cbn [step_post]; (split; [apply (td_Kc wrap src pos inp aout m); auto; td_side | td_side]).
Qed.

Lemma td_type wrap src pos inp aout flush m m0 :
  Kc wrap src pos inp aout m -> m_leave m = 0 -> m_mode m = Zlib.proof.inflate.Model.TYPE ->
  step_post wrap src pos inp aout m0 (c_TYPE flush m).
Proof.
  intros K Hl Hmd.
  assert (Hr : m_ret m = Z_OK) by (apply (kc_ret _ _ _ _ _ _ K); rewrite Hmd; td_cst; lia).
  assert (Hmd' : m_mode m = Zlib.proof.inflate.Model.TYPE \/ m_mode m = TYPEDO) by (left; exact Hmd).
  assert (HB : 0 <= m_bits m <= 31) by (apply (kc_bits _ _ _ _ _ _ K); rewrite Hmd; td_cst; lia).
  unfold c_TYPE.
  destruct (orb _ _).
  - cbn [step_post]. split; [apply (td_Kc wrap src pos inp aout m); auto; td_side | td_side].
  - apply td_typedo; auto.
Qed.

(* DICT: Z_NEED_DICT until a dictionary is set, then TYPE *)
Lemma td_dict_case wrap src pos inp aout flush m1 m0 :
  Kc wrap src pos inp aout m1 -> m_leave m1 = 0 -> m_mode m1 = DICT ->
  (m_mode m0 = DICTID \/ m_mode m0 = DICT) -> m_ow m1 = m_ow m0 ->
  step_post wrap src pos inp aout m0 (c_DICT flush m1).
Proof.
  intros K Hl Hmd H0 Ho.
  assert (Hr : m_ret m1 = Z_OK) by (apply (kc_ret _ _ _ _ _ _ K); rewrite Hmd; td_cst; lia).
  destruct (kc_dict _ _ _ _ _ _ K Hmd) as (W1 & Fd & Hp & Hck & Had).
  unfold c_DICT. destruct (i_havedict (m_s m1) =? 0).
  - cbn [step_post]. right. split; [reflexivity|]. split; [exact H0|].
    assert (Hb : 0 <= m_bits m1 <= 31) by (apply (kc_bits _ _ _ _ _ _ K); rewrite Hmd; td_cst; lia).
    unfold m_mode in Hmd.
    split; [td_red; exact Hmd|]. split; [reflexivity|]. split; [reflexivity|].
    split; [td_red; exact Ho|]. split; [td_red; exact Hl|].
    apply (td_Kc wrap src pos inp aout m1); auto; try td_side.
    all: intros _; td_red; rewrite Hck, Had; auto.
  - apply (td_type wrap src pos inp aout flush _ m0); try td_side.
    assert (Hb : 0 <= m_bits m1 <= 31) by (apply (kc_bits _ _ _ _ _ _ K); rewrite Hmd; td_cst; lia).
    unfold m_mode in Hmd.
    apply (td_Kc wrap src pos inp aout m1); auto; td_side.
Qed.

Lemma th_dict : dict_stmt.
Proof.
  intros wrap src pos inp aout flush m Hc K Hw Hl Hmd. unfold md_dict in Hmd.
  pose proof (Inv.mw_nx _ (proj1 Hw)) as Hnx.
  pose proof (kc_inp _ _ _ _ _ _ K) as Hinp. subst inp.
  pose proof Hc as (Hpos & Hsrc & Hbytes & _).
  destruct Hmd as [D|[D|[D|D]]].
  - rewrite td_step_DICTID by exact D. unfold c_DICTID.
    destruct (kc_did _ _ _ _ _ _ K D) as [W1 (Fd & Hp & Hb & Hh)].
    assert (Hr : m_ret m = Z_OK) by (apply (kc_ret _ _ _ _ _ _ K); rewrite D; td_cst; lia).
    destruct (td_nbk src pos 4 m Hc Hnx ltac:(lia) Hb Hh ltac:(cbn; lia)) as (nx' & Hn' & [[E Hp']|[E Hp']]);
      unfold needbits; rewrite E.
    + rewrite td_lv1. cbn [step_post]. unfold m_mode in D.
      split; [apply (td_Kc wrap src pos (m_inp m) aout m); auto; try td_side | td_side].
      all: intros _; split; [exact W1|]; unfold hd_dictid; td_red; split; [exact Fd|]; split; [lia|]; split; reflexivity.
    + replace (m_leave (td_sh src pos m nx') =? 1) with false by (td_red; rewrite Hl; reflexivity).
      cbv zeta.
      assert (Ec : swap32 (m_hold (td_sh src pos m nx')) = dict_id src).
      { td_red. rewrite Hp'. apply td_dict_id; auto. lia. }
      rewrite Ec.
      apply td_dict_case; try (td_red; reflexivity); auto.
      unfold m_mode in D.
      apply (td_Kc wrap src pos (m_inp m) aout m); auto; try td_side.
      all: intros _; td_red; auto.
  - rewrite td_step_DICT by exact D.
    apply td_dict_case; auto.
  - rewrite td_step_TYPE by exact D. apply td_type; auto.
  - rewrite td_step_TYPEDO by exact D. apply td_typedo; auto.
Qed.
