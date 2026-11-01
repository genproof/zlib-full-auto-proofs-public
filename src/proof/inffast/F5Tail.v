(* inflate_fast (BodyF5.v): the 3-byte copy loops (F5Kit s_tail, s_direct). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inffast.code.
Require Import Zlib.proof.inffast.F5Kit.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* the model: copy_bytes one byte at a time                                                       *)

(* the byte at sr (window w, output ow) and the source after it *)
Definition srcbyte (w ow: list Z) (sr: src) : Z := match sr with SWin i => Znth i w | SOut i => Znth i ow end.
Definition adv (sr: src) (k: Z) : src := match sr with SWin i => SWin (i + k) | SOut i => SOut (i + k) end.

Lemma f5t_copy_f_S: forall n w sr ow,
  fst (copy_f (S n) w sr ow) =
  fst (copy_f n w sr ow) ++ [srcbyte w (fst (copy_f n w sr ow)) (adv sr (Z.of_nat n))].
Proof.
  induction n; intros w sr ow.
  - destruct sr; simpl; rewrite Z.add_0_r; reflexivity.
  - destruct sr as [i | i].
    + change (copy_f (S (S n)) w (SWin i) ow) with (copy_f (S n) w (SWin (i + 1)) (ow ++ [Znth i w])).
      change (copy_f (S n) w (SWin i) ow) with (copy_f n w (SWin (i + 1)) (ow ++ [Znth i w])).
      rewrite IHn. cbn [adv]. replace (i + Z.of_nat (S n)) with (i + 1 + Z.of_nat n) by lia. reflexivity.
    + change (copy_f (S (S n)) w (SOut i) ow) with (copy_f (S n) w (SOut (i + 1)) (ow ++ [Znth i ow])).
      change (copy_f (S n) w (SOut i) ow) with (copy_f n w (SOut (i + 1)) (ow ++ [Znth i ow])).
      rewrite IHn. cbn [adv]. replace (i + Z.of_nat (S n)) with (i + 1 + Z.of_nat n) by lia. reflexivity.
Qed.

Lemma f5t_copy_S: forall w sr k ow, 0 <= k ->
  fst (copy_bytes w sr (k + 1) ow) =
  fst (copy_bytes w sr k ow) ++ [srcbyte w (fst (copy_bytes w sr k ow)) (adv sr k)].
Proof.
  intros. unfold copy_bytes. rewrite Z2Nat.inj_add by lia. rewrite Nat.add_1_r.
  rewrite f5t_copy_f_S. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma f5t_copy_0: forall w sr ow, fst (copy_bytes w sr 0 ow) = ow.
Proof. intros. unfold copy_bytes. simpl. destruct sr; reflexivity. Qed.

Lemma f5t_copy_len: forall w sr c ow, 0 <= c -> Zlength (fst (copy_bytes w sr c ow)) = Zlength ow + c.
Proof.
  intros w sr c ow H. unfold copy_bytes.
  assert (forall n sr ow, Zlength (fst (copy_f n w sr ow)) = Zlength ow + Z.of_nat n) as L.
  { induction n; intros; simpl; [lia | ].
    destruct sr0; rewrite IHn, Zlength_app, Zlength_cons, Zlength_nil; lia. }
  rewrite L. lia.
Qed.

Lemma adv_0: forall sr, adv sr 0 = sr.
Proof. destruct sr; simpl; rewrite Z.add_0_r; reflexivity. Qed.

Lemma adv_adv: forall sr a b, adv (adv sr a) b = adv sr (a + b).
Proof. destruct sr; simpl; intros; rewrite Z.add_assoc; reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the machine                                                                                    *)

Lemma mwf_set_ow: forall m ow,
  mwf m -> Zlength (m_ow m) <= Zlength ow <= m_aout m -> bytes_ok ow -> mwf (set_m_ow m ow).
Proof.
  intros m ow W L B. destruct W. constructor; cbn [set_m_ow m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in
    m_out m_ret m_leave m_adler m_msg m_tin m_tout m_snx m_sow]; auto; try lia.
  split; [lia | auto].
Qed.

Lemma rest_mem_ow: forall F m ow, rest_mem F (set_m_ow m ow) = rest_mem F m.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* one byte: *out++ = *from++;                                                                     *)

Definition bstmt (ta tb tc: ident) : statement :=
  Ssequence
    (Ssequence
      (Ssequence
        (Ssequence (Sset ta (Etempvar _out (tptr tuchar)))
          (Sset _out (Ebinop Oadd (Etempvar ta (tptr tuchar)) (Econst_int (Int.repr 1) tint) (tptr tuchar))))
        (Sset tb (Etempvar _from (tptr tuchar))))
      (Sset _from (Ebinop Oadd (Etempvar tb (tptr tuchar)) (Econst_int (Int.repr 1) tint) (tptr tuchar))))
    (Ssequence (Sset tc (Ederef (Etempvar tb (tptr tuchar)) tuchar))
      (Sassign (Ederef (Etempvar ta (tptr tuchar)) tuchar) (Etempvar tc tuchar))).

Lemma f5t_add1: forall p a, isptr p ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tint (offset_val a p) (Vint (Int.repr 1))) = offset_val (a + 1) p.
Proof.
  intros p a P. destruct p; try contradiction. simpl. f_equal.
  rewrite Ptrofs.add_assoc. f_equal. unfold Ptrofs.of_ints. rewrite Int.signed_repr by rep_lia.
  rewrite Ptrofs.mul_one. rewrite ptrofs_add_repr. reflexivity.
Qed.

Lemma f5t_field_address: forall n j p,
  field_compatible (tarray tuchar n) [] p -> 0 <= j < n ->
  offset_val j p = field_address (tarray tuchar n) [ArraySubsc j] p.
Proof.
  intros. rewrite field_address_offset.
  - simpl. f_equal. lia.
  - eapply field_compatible_cons_Tarray; [reflexivity | auto | lia].
Qed.

Lemma f5t_out_znth: forall olo on oc owk j, 0 <= olo <= Zlength oc -> 0 <= j < Zlength owk ->
  Znth (olo + j) (sublist 0 olo oc ++ byte_vals owk ++ sublist (olo + Zlength owk) on oc) = Vint (Int.repr (Znth j owk)).
Proof.
  intros. rewrite app_Znth2 by (rewrite Zlength_sublist; lia).
  rewrite Zlength_sublist by lia. rewrite app_Znth1 by (unfold byte_vals; rewrite Zlength_map; lia).
  unfold byte_vals. rewrite Znth_map by lia. f_equal. f_equal. f_equal. lia.
Qed.

Lemma f5t_win_znth: forall w n j, 0 <= j < Zlength w ->
  Znth j (byte_vals w ++ Zrepeat Vundef n) = Vint (Int.repr (Znth j w)).
Proof.
  intros. rewrite app_Znth1 by (unfold byte_vals; rewrite Zlength_map; lia).
  unfold byte_vals. rewrite Znth_map by lia. reflexivity.
Qed.

Lemma f5t_out_snoc: forall sh p lo n c ow b,
  0 <= lo -> lo + Zlength ow < n -> Zlength c = n ->
  data_at sh (tarray tuchar n)
    (upd_Znth (lo + Zlength ow) (sublist 0 lo c ++ byte_vals ow ++ sublist (lo + Zlength ow) n c)
       (Vint (Int.repr b))) p =
  out_rep (OutBuf sh p lo n c) (ow ++ [b]).
Proof.
  intros. unfold out_rep. f_equal.
  rewrite byte_vals_app. unfold byte_vals at 3. simpl.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  assert (Zlength (byte_vals ow) = Zlength ow) by apply Zlength_byte_vals.
  list_solve.
Qed.

Definition sbyte (m: mst) (sr: src) : Z := srcbyte (i_wdata (m_s m)) (m_ow m) sr.

Definition byte_stmt (ta tb tc: ident) : Prop := forall {Espec: OracleKind} (F: frame) (m: mst) (sr: src) (vl vd: val),
  mwf m -> src_ok m sr 1 -> Zlength (m_ow m) + 1 <= m_aout m -> out_ok (f_ob F) (m_aout m) ->
  semax Delta_fast (fs_state F m [] [temp _from (src_ptr F sr); temp _len vl; temp _dist vd]) (bstmt ta tb tc)
    (normal_ret_assert
      (fs_state F (set_m_ow m (m_ow m ++ [sbyte m sr])) [] [temp _from (src_ptr F (adv sr 1)); temp _len vl; temp _dist vd])).

Ltac byte_win_tac F m i W S R O BOW WL BW WH WS OW0 :=
  let Hwin := fresh "Hwin" in let Hi0 := fresh "Hi0" in let Hi1 := fresh "Hi1" in
  let WS2 := fresh "WS2" in let EOB := fresh "EOB" in
  let osh := fresh "osh" in let op := fresh "op" in let olo := fresh "olo" in let on := fresh "on" in let oc := fresh "oc" in
  let Osh := fresh "Osh" in let Op := fresh "Op" in let Olo := fresh "Olo" in let Oa := fresh "Oa" in
  let On := fresh "On" in let Oc := fresh "Oc" in let Omax := fresh "Omax" in
  let wn := fresh "wn" in let FCw := fresh "FCw" in let Wp := fresh "Wp" in let FCo := fresh "FCo" in
  let BR := fresh "BR" in let ZV := fresh "ZV" in
  destruct S as (Hwin & Hi0 & Hi1);
  assert (WS2: i_wsize (m_s m) = 2 ^ i_wbits (m_s m)) by (destruct WS as [WS | [_ WS]]; [lia | exact WS]);
  unfold out_ptr in *; destruct (f_ob F) as [osh op olo on oc] eqn:EOB;
  destruct O as (Osh & Op & Olo & Oa & On & Oc & Omax);
  unfold out_rep, win_rep; rewrite Hwin; Intros;
  set (wn := 2 ^ i_wbits (m_s m)) in *;
  assert_PROP (field_compatible (tarray tuchar wn) [] (f_winp F)) as FCw by entailer!;
  assert_PROP (isptr (f_winp F)) as Wp by entailer!;
  forward; forward; forward; forward; rewrite !f5t_add1 by auto;
  assert_PROP (field_compatible (tarray tuchar on) [] op) as FCo by entailer!;
  assert (BR: 0 <= Znth i (i_wdata (m_s m)) <= Byte.max_unsigned) by (apply (proj1 (Forall_Znth _ _) BW); lia);
  assert (ZV: Znth i (byte_vals (i_wdata (m_s m)) ++ Zrepeat Vundef (wn - Zlength (i_wdata (m_s m))))
              = Vint (Int.repr (Znth i (i_wdata (m_s m))))) by (apply f5t_win_znth; lia);
  rewrite (f5t_field_address wn i (f_winp F)) by (auto; lia);
  forward;
  [ setoid_rewrite ZV; entailer!; rep_lia
  | setoid_rewrite ZV;
    rewrite (f5t_field_address on (olo + Zlength (m_ow m)) op) by (auto; lia);
    forward;
    rewrite zext8, Z.mod_small by rep_lia;
    rewrite (f5t_out_snoc osh op olo on oc (m_ow m) (Znth i (i_wdata (m_s m)))) by lia;
    unfold fs_state, fs_locals, fs_sep; rewrite rest_mem_ow;
    cbn [set_m_ow m_s m_ow m_inp m_aout m_nx m_hold m_bits src_ptr adv];
    unfold win_rep; rewrite Hwin;
    rewrite Zlength_app, Zlength_cons, Zlength_nil;
    replace (olo + (Zlength (m_ow m) + Z.succ 0)) with (olo + Zlength (m_ow m) + 1) by lia;
    rewrite <- (f5t_field_address wn i (f_winp F)) by (auto; lia);
    entailer! ].

Ltac byte_out_tac F m i W S R O BOW WL BW WH WS OW0 :=
  let EOB := fresh "EOB" in
  let osh := fresh "osh" in let op := fresh "op" in let olo := fresh "olo" in let on := fresh "on" in let oc := fresh "oc" in
  let Osh := fresh "Osh" in let Op := fresh "Op" in let Olo := fresh "Olo" in let Oa := fresh "Oa" in
  let On := fresh "On" in let Oc := fresh "Oc" in let Omax := fresh "Omax" in
  let FCo := fresh "FCo" in let BR := fresh "BR" in let ZV := fresh "ZV" in
  unfold out_ptr in *; destruct (f_ob F) as [osh op olo on oc] eqn:EOB;
  destruct O as (Osh & Op & Olo & Oa & On & Oc & Omax);
  unfold out_rep; forward; forward; forward; forward; rewrite !f5t_add1 by auto;
  assert_PROP (field_compatible (tarray tuchar on) [] op) as FCo by entailer!;
  assert (BR: 0 <= Znth i (m_ow m) <= Byte.max_unsigned) by (apply (proj1 (Forall_Znth _ _) BOW); lia);
  assert (ZV: Znth (olo + i) (sublist 0 olo oc ++ byte_vals (m_ow m) ++ sublist (olo + Zlength (m_ow m)) on oc)
              = Vint (Int.repr (Znth i (m_ow m)))) by (apply f5t_out_znth; lia);
  rewrite (f5t_field_address on (olo + i) op) by (auto; lia);
  forward;
  [ setoid_rewrite ZV; entailer!; rep_lia
  | setoid_rewrite ZV;
    rewrite (f5t_field_address on (olo + Zlength (m_ow m)) op) by (auto; lia);
    forward;
    rewrite zext8, Z.mod_small by rep_lia;
    rewrite (f5t_out_snoc osh op olo on oc (m_ow m) (Znth i (m_ow m))) by lia;
    unfold fs_state, fs_locals, fs_sep; rewrite rest_mem_ow;
    cbn [set_m_ow m_s m_ow m_inp m_aout m_nx m_hold m_bits src_ptr adv];
    rewrite Zlength_app, Zlength_cons, Zlength_nil;
    replace (olo + (i + 1)) with (olo + i + 1) by lia;
    replace (olo + (Zlength (m_ow m) + Z.succ 0)) with (olo + Zlength (m_ow m) + 1) by lia;
    entailer! ].

Ltac byte_tac :=
  let Espec := fresh "Espec" in let F := fresh "F" in let m := fresh "m" in let sr := fresh "sr" in
  let vl := fresh "vl" in let vd := fresh "vd" in let W := fresh "W" in let S := fresh "S" in
  let R := fresh "R" in let O := fresh "O" in let BOW := fresh "BOW" in let WL := fresh "WL" in
  let BW := fresh "BW" in let WH := fresh "WH" in let WS := fresh "WS" in let OW0 := fresh "OW0" in
  let i := fresh "i" in
  intros Espec F m sr vl vd W S R O;
  unfold bstmt, fs_state, fs_locals, fs_sep; cbn [app];
  abbreviate_semax;
  destruct (mw_ow _ W) as [_ BOW]; destruct (sw_wdata _ (mw_s _ W)) as [WL BW];
  pose proof (sw_whave _ (mw_s _ W)) as WH; pose proof (sw_wsize _ (mw_s _ W)) as WS;
  pose proof (Zlength_nonneg (m_ow m)) as OW0;
  destruct sr as [i | i]; cbn [src_ok src_ptr sbyte srcbyte adv] in *;
  [ byte_win_tac F m i W S R O BOW WL BW WH WS OW0 | byte_out_tac F m i W S R O BOW WL BW WH WS OW0 ].

Lemma byte_25 : byte_stmt _t'25 _t'26 _t'56.
Proof. byte_tac. Qed.
Lemma byte_27 : byte_stmt _t'27 _t'28 _t'55.
Proof. byte_tac. Qed.
Lemma byte_29 : byte_stmt _t'29 _t'30 _t'54.
Proof. byte_tac. Qed.
Lemma byte_31 : byte_stmt _t'31 _t'32 _t'53.
Proof. byte_tac. Qed.
Lemma byte_33 : byte_stmt _t'33 _t'34 _t'52.
Proof. byte_tac. Qed.
Lemma byte_35 : byte_stmt _t'35 _t'36 _t'51.
Proof. byte_tac. Qed.
Lemma byte_37 : byte_stmt _t'37 _t'38 _t'50.
Proof. byte_tac. Qed.
Lemma byte_39 : byte_stmt _t'39 _t'40 _t'49.
Proof. byte_tac. Qed.
Lemma byte_41 : byte_stmt _t'41 _t'42 _t'48.
Proof. byte_tac. Qed.
Lemma byte_43 : byte_stmt _t'43 _t'44 _t'47.
Proof. byte_tac. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* byte k of a copy of L bytes from sr                                                            *)

Lemma f5t_znth_byte: forall l j, bytes_ok l -> 0 <= Znth j l <= Byte.max_unsigned.
Proof.
  intros l j B. destruct (zlt j 0); [rewrite Znth_underflow by lia; unfold default, Inhabitant_Z; rep_lia | ].
  destruct (zlt j (Zlength l)); [apply (proj1 (Forall_Znth _ _) B); lia | rewrite Znth_overflow by lia; unfold default, Inhabitant_Z; rep_lia].
Qed.

Lemma f5t_copy_bytes_ok: forall w sr k ow, bytes_ok w -> bytes_ok ow -> bytes_ok (fst (copy_bytes w sr k ow)).
Proof.
  intros w sr k ow BW. unfold copy_bytes. generalize (Z.to_nat k) as n. intros n. revert sr ow.
  induction n; intros sr ow BO; simpl; [exact BO | ].
  destruct sr as [i | i]; apply IHn; unfold bytes_ok; apply Forall_app; split; auto; constructor; auto;
    apply f5t_znth_byte; auto.
Qed.

Definition mk (m: mst) (sr: src) (k: Z) : mst := set_m_ow m (fst (copy_bytes (i_wdata (m_s m)) sr k (m_ow m))).

Lemma byte_step: forall ta tb tc, byte_stmt ta tb tc ->
  forall {Espec: OracleKind} (F: frame) (m: mst) (sr: src) (L k: Z) (vl vd: val),
  mwf m -> 0 <= k < L -> src_ok m sr L -> Zlength (m_ow m) + L <= m_aout m -> out_ok (f_ob F) (m_aout m) ->
  semax Delta_fast (fs_state F (mk m sr k) [] [temp _from (src_ptr F (adv sr k)); temp _len vl; temp _dist vd])
    (bstmt ta tb tc)
    (normal_ret_assert (fs_state F (mk m sr (k + 1)) [] [temp _from (src_ptr F (adv sr (k + 1))); temp _len vl; temp _dist vd])).
Proof.
  intros ta tb tc BS Espec F m sr L k vl vd W K S R O.
  destruct (mw_ow _ W) as [_ BOW]. destruct (sw_wdata _ (mw_s _ W)) as [WL BW].
  pose proof (f5t_copy_len (i_wdata (m_s m)) sr k (m_ow m) ltac:(lia)) as LK.
  pose proof (f5t_copy_bytes_ok (i_wdata (m_s m)) sr k (m_ow m) BW BOW) as BK.
  unfold mk. rewrite f5t_copy_S by lia. rewrite <- adv_adv.
  apply (BS Espec F (mk m sr k) (adv sr k) vl vd).
  - apply mwf_set_ow; auto. pose proof (Zlength_nonneg (m_ow m)). lia.
  - destruct sr as [i | i]; unfold mk, set_m_ow in *; cbn [src_ok adv m_s m_ow] in *;
      [destruct S as (S1 & S2 & S3); split; [exact S1 | lia] | lia].
  - unfold mk, set_m_ow. cbn [m_ow m_aout]. lia.
  - exact O.
Qed.

Lemma set_ow_id: forall m, set_m_ow m (m_ow m) = m.
Proof. destruct m; reflexivity. Qed.

Lemma f5_tail: tail_stmt.
Proof.
  intros Espec F m sr L D FO HL S R O.
  pose proof (fast_ok_mwf _ FO) as W.
  stmt_simpl.
  apply semax_pre with (P' := fs_state F (mk m sr 0) [] [temp _from (src_ptr F (adv sr 0)); temp _len (zv (L - 0)); temp _dist (zv D)]).
  { rewrite adv_0. unfold mk. rewrite f5t_copy_0, set_ow_id. unfold fs_state, fs_locals, fs_sep. cbn [app]. rewrite Z.sub_0_r. entailer!. }
  forward_while (EX k: Z, fs_state F (mk m sr k) [0 <= k <= L] [temp _from (src_ptr F (adv sr k)); temp _len (zv (L - k)); temp _dist (zv D)]).
  - Exists 0. unfold fs_state, fs_locals, fs_sep. cbn [app]. entailer!.
  - unfold fs_state, fs_locals, fs_sep. cbn [app]. entailer!.
  - unfold MORE_COMMANDS, abbreviate.
    eapply semax_seq'. { apply (byte_step _ _ _ byte_25 F m sr L k); auto; lia. }
    eapply semax_seq'. { apply (byte_step _ _ _ byte_27 F m sr L (k + 1)); auto; lia. }
    replace (k + 1 + 1) with (k + 2) by lia.
    eapply semax_seq'. { apply (byte_step _ _ _ byte_29 F m sr L (k + 2)); auto; lia. }
    replace (k + 2 + 1) with (k + 3) by lia.
    unfold fs_state, fs_locals, fs_sep. cbn [app].
    forward.
    Exists (k + 3). unfold fs_state, fs_locals, fs_sep. cbn [app]. entailer!. f_equal. f_equal. lia.
  - unfold fs_state, fs_locals, fs_sep. cbn [app].
    forward_if (fs_state F (mk m sr L) [] [temp _from (src_ptr F (adv sr L)); temp _len (zv (L - k)); temp _dist (zv D)]).
    + unfold MORE_COMMANDS, abbreviate.
      eapply semax_seq'. { apply (byte_step _ _ _ byte_31 F m sr L k); auto; lia. }
      unfold fs_state, fs_locals, fs_sep. cbn [app].
      forward_if.
      * unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
        assert (E: L = k + 1 + 1) by lia. subst L.
        apply (byte_step _ _ _ byte_33 F m sr (k + 1 + 1) (k + 1)); auto; lia.
      * assert (E: L = k + 1) by lia. subst L.
        forward. unfold fs_state, fs_locals, fs_sep. cbn [app]. entailer!.
    + match goal with Hz: Int.repr (L - k) = Int.zero |- _ =>
        change Int.zero with (Int.repr 0) in Hz; apply repr_inj_unsigned in Hz; [ | rep_lia | rep_lia] end.
      assert (E: L = k) by lia. subst L.
      forward. unfold fs_state, fs_locals, fs_sep. cbn [app]. entailer!.
    + change (set_m_ow m (fst (copy_bytes (i_wdata (m_s m)) sr L (m_ow m)))) with (mk m sr L).
      unfold fs_state, fs_locals, fs_sep. cbn [app]. entailer!.
Qed.

Lemma f5t_sub: forall p a D, isptr p -> 0 <= D <= Int.max_unsigned ->
  force_val (sem_binary_operation' Osub (tptr tuchar) tuint (offset_val a p) (Vint (Int.repr D))) = offset_val (a - D) p.
Proof.
  intros p a D P HD. destruct p; try contradiction. simpl. f_equal.
  unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite Int.unsigned_repr by lia.
  rewrite ptrofs_mul_repr, <- (Ptrofs.repr_unsigned i), !ptrofs_add_repr, ptrofs_sub_repr. f_equal. lia.
Qed.

Lemma f5_direct: direct_stmt.
Proof.
  intros Espec F m L D FO HL HD R O.
  pose proof (fast_ok_mwf _ FO) as W.
  stmt_simpl.
  unfold fs_state, fs_locals, fs_sep. cbn [app]. abbreviate_semax.
  assert (Pob: isptr (out_ptr (f_ob F) (Zlength (m_ow m)))).
  { destruct (f_ob F); destruct O as (_ & Op & _). destruct p; try contradiction. simpl. auto. }
  forward.
  set (sr := SOut (Zlength (m_ow m) - D)).
  assert (S: src_ok m sr L) by (unfold sr; cbn [src_ok]; lia).
  apply semax_pre with (P' := fs_state F (mk m sr 0) [] [temp _from (src_ptr F (adv sr 0)); temp _len (zv (L - 0)); temp _dist (zv D)]).
  { rewrite adv_0. unfold mk. rewrite f5t_copy_0, set_ow_id. unfold fs_state, fs_locals, fs_sep. cbn [app].
    rewrite Z.sub_0_r. unfold sr. cbn [src_ptr]. unfold out_ptr in *. destruct (f_ob F).
    pose proof (mw_aout _ W). destruct O as (_ & Op & _).
    rewrite f5t_sub by (auto; rep_lia). replace (lo + Zlength (m_ow m) - D) with (lo + (Zlength (m_ow m) - D)) by lia.
    entailer!. }
  forward_loop (EX k: Z, fs_state F (mk m sr k) [0 <= k; k + 3 <= L] [temp _from (src_ptr F (adv sr k)); temp _len (zv (L - k)); temp _dist (zv D)])
    continue: (EX k: Z, fs_state F (mk m sr k) [0 <= k <= L] [temp _from (src_ptr F (adv sr k)); temp _len (zv (L - k)); temp _dist (zv D)])
    break: (EX k: Z, fs_state F (mk m sr k) [0 <= k <= L; L - k <= 2] [temp _from (src_ptr F (adv sr k)); temp _len (zv (L - k)); temp _dist (zv D)]).
  - Exists 0. unfold fs_state, fs_locals, fs_sep. cbn [app]. entailer!.
  - Intros k. unfold fs_state, fs_locals, fs_sep. cbn [app]. Intros.
    unfold MORE_COMMANDS, abbreviate.
    eapply semax_seq'. { apply (byte_step _ _ _ byte_35 F m sr L k); auto; lia. }
    eapply semax_seq'. { apply (byte_step _ _ _ byte_37 F m sr L (k + 1)); auto; lia. }
    replace (k + 1 + 1) with (k + 2) by lia.
    eapply semax_seq'. { apply (byte_step _ _ _ byte_39 F m sr L (k + 2)); auto; lia. }
    replace (k + 2 + 1) with (k + 3) by lia.
    unfold fs_state, fs_locals, fs_sep. cbn [app].
    forward.
    Exists (k + 3). unfold fs_state, fs_locals, fs_sep. cbn [app]. entailer!. f_equal. f_equal. lia.
  - Intros k. unfold fs_state, fs_locals, fs_sep. cbn [app]. Intros.
    forward_if.
    + forward. Exists k. unfold fs_state, fs_locals, fs_sep. cbn [app]. entailer!.
    + forward. Exists k. unfold fs_state, fs_locals, fs_sep. cbn [app]. entailer!.
  - Intros k. unfold fs_state, fs_locals, fs_sep. cbn [app]. Intros.
    forward_if (fs_state F (mk m sr L) [] [temp _from (src_ptr F (adv sr L)); temp _len (zv (L - k)); temp _dist (zv D)]).
    + unfold MORE_COMMANDS, abbreviate.
      eapply semax_seq'. { apply (byte_step _ _ _ byte_41 F m sr L k); auto; lia. }
      unfold fs_state, fs_locals, fs_sep. cbn [app].
      forward_if.
      * unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
        assert (E: L = k + 1 + 1) by lia. subst L.
        apply (byte_step _ _ _ byte_43 F m sr (k + 1 + 1) (k + 1)); auto; lia.
      * assert (E: L = k + 1) by lia. subst L.
        forward. unfold fs_state, fs_locals, fs_sep. cbn [app]. entailer!.
    + match goal with Hz: Int.repr (L - k) = Int.zero |- _ =>
        change Int.zero with (Int.repr 0) in Hz; apply repr_inj_unsigned in Hz; [ | rep_lia | rep_lia] end.
      assert (E: L = k) by lia. subst L.
      forward. unfold fs_state, fs_locals, fs_sep. cbn [app]. entailer!.
    + change (set_m_ow m (fst (copy_bytes (i_wdata (m_s m)) (SOut (Zlength (m_ow m) - D)) L (m_ow m)))) with (mk m sr L).
      unfold fs_state, fs_locals, fs_sep. cbn [app]. entailer!.
Qed.

Lemma f5_tail_direct : tail_stmt /\ direct_stmt.
Proof. exact (conj f5_tail f5_direct). Qed.


