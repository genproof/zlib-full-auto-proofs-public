(** * deflate_stored, one iteration of the first phase's do-while loop (StoredKit.S_body) against the model's
    iteration DModel2.ds_body: the dummy stored-block header (_tr_stored_block with no data, the four length bytes
    patched in pending_buf), flush_pending, the window bytes copied to next_out (memcpy), the input copied to next_out
    (read_buf).  The two [break]s leave the state unchanged. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.StoredKit.
Require Import Zlib.proof.deflate.StoredFacts.
Require Import Zlib.proof.deflate.StoredBodyKit.
Require Import Zlib.proof.deflate.StoredBodyHdr.
Require Import Zlib.proof.deflate.StoredBodyWin.
Require Import Zlib.proof.deflate.StoredBodyIn.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

Lemma u32_range' x : 0 <= u32 x <= Int.max_unsigned.
Proof. unfold u32. pose proof (Z.mod_pos_bound x 4294967296 ltac:(lia)). rep_lia. Qed.

(** ** Pure facts: the output of each fragment only grows *)

Lemma c_hdr_inv s z len last s1 z1 : 0 <= z_avail_out z -> c_hdr s z len last = Some (s1, z1) -> out_inv z z1.
Proof.
  intros Hz H. unfold c_hdr in H. binv H. binv H. binv H. binv H. binv H.
  eapply flush_pending_inv; [exact Hz | exact H].
Qed.

Lemma c_win_inv s z len left s2 z2 len2 : 0 <= z_avail_out z < 4294967296 ->
  c_win s z len left = Some (s2, z2, len2) -> out_inv z z2.
Proof.
  intros Hz H. unfold c_win in H.
  destruct (left =? 0); [inversion H; subst; apply out_inv_refl; lia|].
  binv H. binv H. binv H. inversion H; subst; clear H.
  apply mb_read_len in Ha. apply out_put_inv in Ha0. destruct Ha0 as [E1 [L1 A1]].
  unfold out_inv; cbn [z_out z_avail_out set_z_total_out set_z_avail_out].
  rewrite <- Ha. pose proof (Zlength_nonneg x).
  rewrite u32_id by lia. split; [eexists; exact E1|]. rewrite E1, Zlength_app. lia.
Qed.

Lemma c_win_len s z len left s2 z2 len2 : 0 <= len <= Int.max_unsigned ->
  c_win s z len left = Some (s2, z2, len2) -> 0 <= len2 <= Int.max_unsigned.
Proof.
  intros Hl H. unfold c_win in H.
  destruct (left =? 0); [inversion H; subst; lia|].
  binv H. binv H. binv H. inversion H; subst; clear H. apply u32_range'.
Qed.

Lemma c_in_inv s z len z3 : 0 <= z_avail_out z < 4294967296 -> c_in s z len = Some z3 -> out_inv z z3.
Proof.
  intros Hz H. unfold c_in in H.
  destruct (len =? 0); [inversion H; subst; apply out_inv_refl; lia|].
  apply bind_some in H; destruct H as [[z4 d] [Hr H]].
  binv H. binv H. inversion H; subst; clear H.
  apply read_buf_out in Hr. destruct Hr as [Eo Ea].
  apply out_put_inv in Ha0. destruct Ha0 as [E1 [L1 A1]].
  unfold guard in Ha. destruct (Zlength d =? len) eqn:Ed; [|discriminate]. apply Z.eqb_eq in Ed.
  unfold out_inv; cbn [z_out z_avail_out set_z_total_out set_z_avail_out].
  pose proof (Zlength_nonneg d).
  rewrite u32_id by lia. split; [exists d; rewrite E1, Eo; auto|].
  rewrite E1, Eo, Zlength_app. lia.
Qed.

Lemma out_inv_grows z z1 : out_inv z z1 -> out_grows z z1.
Proof. intros [G _]. exact G. Qed.

Lemma out_inv_rest' z z1 (rest : list val) : out_inv z z1 -> Zlength rest = z_avail_out z ->
  Zlength (z_out z1) - Zlength (z_out z) <= Zlength rest.
Proof. intros [[b E] [L P]] R. lia. Qed.

Lemma S_body_eq : S_body =
  Ssequence (S_el 0) (Ssequence (S_el 1) (Ssequence (S_el 2) (Ssequence (S_el 3) (Ssequence (S_el 4)
  (Ssequence (S_el 5) (Ssequence (S_el 6) (Ssequence (S_el 7) (Ssequence (S_el 8) S_tail)))))))).
Proof. reflexivity. Qed.

(** ** Arithmetic of the first part *)
Lemma hdr_val a : Int.shru (Int.repr (a + 42)) (Int.repr 3) = Int.repr (Z.shiftr (u32 (u32 a + 42)) 3).
Proof.
  unfold Int.shru. rewrite (Int.unsigned_repr 3) by rep_lia. f_equal. f_equal.
  rewrite Int.unsigned_repr_eq. unfold u32. change Int.modulus with 4294967296.
  rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma hdr_range s : 0 <= stored_hdr s <= Int.max_unsigned.
Proof.
  unfold stored_hdr. pose proof (u32_range' (u32 (o_bi_valid (tr_out (d_tr s))) + 42)).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia].
Qed.

Lemma ltu_repr a b : 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int.unsigned (Int.repr a) < Int.unsigned (Int.repr b) -> a < b.
Proof. intros. rewrite !Int.unsigned_repr in * by lia. lia. Qed.

Lemma geu_repr a b : 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int.unsigned (Int.repr a) >= Int.unsigned (Int.repr b) -> b <= a.
Proof. intros. rewrite !Int.unsigned_repr in * by lia. lia. Qed.

Lemma vi_u32' x : vi (u32 x) = vi x.
Proof.
  unfold vi, u32. f_equal. change 4294967296 with Int.modulus.
  rewrite <- Int.unsigned_repr_eq. apply Int.repr_unsigned.
Qed.

Lemma int_repr_l64 x : Int.repr (Int64.unsigned (Int64.repr x)) = Int.repr x.
Proof.
  rewrite Int64.unsigned_repr_eq. apply Int.eqm_samerepr. unfold Int.eqm, Zbits.eqmod.
  rewrite Z.mod_eq by (pose proof Int64.modulus_pos; lia). remember (x / Int64.modulus) as q.
  exists (- q * 4294967296).
  change Int.modulus with 4294967296. change Int64.modulus with (4294967296 * 4294967296). lia.
Qed.

Lemma u64_small x : 0 <= x <= Int64.max_unsigned -> u64 x = x.
Proof. intros. unfold u64. apply Z.mod_small. rep_lia. Qed.

Lemma len1_then a b : 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned -> a + b < 65535 ->
  vi (if MAX_STORED >? u64 (a + b) then u32 (a + b) else MAX_STORED) = Vint (Int.repr (a + b)).
Proof.
  intros. rewrite u64_small by rep_lia. unfold MAX_STORED.
  destruct (Z.gtb_spec 65535 (a + b)); [|lia]. apply vi_u32'.
Qed.

Lemma len1_else a b : 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned -> 65535 <= a + b ->
  vi (if MAX_STORED >? u64 (a + b) then u32 (a + b) else MAX_STORED) = Vint (Int.repr 65535).
Proof.
  intros. rewrite u64_small by rep_lia. unfold MAX_STORED.
  destruct (Z.gtb_spec 65535 (a + b)); [lia|]. reflexivity.
Qed.

Lemma int_eq_repr_s' a b : Int.min_signed <= a <= Int.max_signed -> Int.min_signed <= b <= Int.max_signed ->
  Int.eq (Int.repr a) (Int.repr b) = (a =? b).
Proof.
  intros. destruct (Z.eqb_spec a b); [subst; apply Int.eq_true|].
  apply Int.eq_false. intro E. apply repr_inj_signed in E; auto.
Qed.

Lemma int_eq_u32 a b : 0 <= a <= Int.max_unsigned -> Int.eq (Int.repr a) (Int.repr b) = (a =? u32 b).
Proof.
  intros. assert (E : Int.repr b = Int.repr (u32 b)) by (pose proof (vi_u32' b) as V; unfold vi in V; congruence).
  rewrite E. pose proof (u32_range' b).
  destruct (Z.eqb_spec a (u32 b)); [subst; apply Int.eq_true|].
  apply Int.eq_false. intro E'. apply repr_inj_unsigned in E'; auto.
Qed.

Lemma typed_true_of_bool (b : bool) : typed_true tint (if b then Vtrue else Vfalse) -> b = true.
Proof. destruct b; [auto | cbv; discriminate]. Qed.
Lemma typed_false_of_bool (b : bool) : typed_false tint (if b then Vtrue else Vfalse) -> b = false.
Proof. destruct b; [cbv; discriminate | auto]. Qed.
Lemma bool2val_eq (b : bool) : bool2val b = Val.of_bool b.
Proof. destruct b; reflexivity. Qed.

Lemma ds_break_eq s z flush mb : ds_break s z flush mb =
  ((ds_len s z <? mb) && ((((ds_len s z =? 0) && negb (flush =? Z_FINISH)) || (flush =? Z_NO_FLUSH)) ||
                          negb (ds_len s z =? u64 (ds_left s + z_avail_in z))))%bool.
Proof. reflexivity. Qed.

(** Fold the pieces back into [dfull]. *)
Ltac refold_dfull :=
  unfold dfull, dstate_at; rewrite sb_trees_at_split, sb_strm_at_split;
  unfold dtype_at, match_at, out_at, d_trm; cbn [fst snd].

(** [forward_if] whose join point sets the temp [id] to [v] (the rest unchanged). *)
Ltac fwd_if_set id v :=
  match goal with |- semax _ (PROPx _ (LOCALx ?L (SEPx ?S))) _ _ =>
    let L' := eval simpl in (remove_localdef_temp id L) in
    forward_if (PROPx [] (LOCALx (temp id v :: L') (SEPx S))) end.

(** ** The tail of the iteration (after [last = ...]): the three fragments *)
Lemma ds_tail_frag {Espec : OracleKind} (p : dptrs) (pin pout : val) (ish : share) (rest : list val)
    (msgv : val) (gv : globals) (s : dstate) (z : strm) (flush min_block used : Z)
    (res : (dstate * strm) + (dstate * strm * Z)) (len left last : Z) s1 z1 s2 z2 len2 z3 :
  Int.min_signed <= flush <= Int.max_signed -> 0 <= min_block <= Int.max_unsigned ->
  0 <= used <= Int.max_unsigned -> 0 <= len <= Int.max_unsigned -> 0 <= left <= Int.max_unsigned ->
  0 <= last <= 1 -> Zlength rest = z_avail_out z -> 0 <= z_avail_out z <= Int.max_unsigned ->
  c_hdr s z len last = Some (s1, z1) ->
  c_win s1 z1 len left = Some (s2, z2, len2) ->
  c_in s2 z2 len2 = Some z3 ->
  res = (if last =? 0 then inl (s2, z3) else inr (s2, z3, last)) ->
  semax Delta_ds
    (PROP () LOCAL (temp _len (vi len); temp _left (vi left); temp _last (vi last); temp _min_block (vi min_block);
                    temp _used (vi used); gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s z p pin pout ish rest msgv gv; deflate_globals gv))
    S_tail (body_post p pin pout ish rest msgv gv s z flush min_block used res).
Proof.
  intros Hf Hm Hu Hl Hleft Hlast Hrest Hz E1 E2 E3 Eres.
  assert (I1 : out_inv z z1) by (eapply c_hdr_inv; [lia | exact E1]).
  pose proof (out_inv_le _ _ I1) as Hz1.
  assert (I2 : out_inv z1 z2) by (eapply c_win_inv; [rep_lia | exact E2]).
  pose proof (out_inv_le _ _ I2) as Hz2.
  assert (I3 : out_inv z2 z3) by (eapply c_in_inv; [rep_lia | exact E3]).
  pose proof (c_win_len _ _ _ _ _ _ _ Hl E2) as Hl2.
  rewrite S_tail_eq. do 5 rewrite seq_assoc.
  eapply semax_seq'.
  { rewrite <- !seq_assoc. exact (sb_hdr_frag p pin pout ish rest msgv gv s z flush min_block used len left last
                                     (s1, z1) Hf Hm Hu Hl Hleft Hlast E1). }
  cbn [fst snd].
  eapply semax_seq'.
  { exact (sb_win_frag p pin pout ish (rest_after z z1 rest) msgv gv s1 z1 flush min_block used len left last
                       (s2, z2, len2) Hf Hm Hu Hl Hleft Hlast E2). }
  cbn [fst snd].
  eapply semax_post_flipped.
  { exact (sb_in_frag p pin pout ish (rest_after z1 z2 (rest_after z z1 rest)) msgv gv s2 z2 flush min_block used
                      len2 last z3 Hf Hm Hu Hl2 Hlast E3). }
  - unfold body_post, normal_ret_assert. cbn [RA_normal].
    Exists s2 z3 last.
    rewrite (rest_after_trans z z1 z2 rest).
    2: { apply out_inv_grows; exact I1. }
    2: { apply out_inv_grows; exact I2. }
    2: { eapply out_inv_rest'; eauto. }
    rewrite (rest_after_trans z z2 z3 rest).
    2: { apply out_inv_grows; exact (out_inv_trans _ _ _ I1 I2). }
    2: { apply out_inv_grows; exact I3. }
    2: { eapply out_inv_rest'; [exact (out_inv_trans _ _ _ I1 I2) | exact Hrest]. }
    entailer!.
  - unfold normal_ret_assert. cbn. intros. apply andp_left2. apply FF_left.
  - unfold normal_ret_assert. cbn. intros. apply andp_left2. apply FF_left.
  - unfold normal_ret_assert. cbn. intros. apply andp_left2. apply FF_left.
Qed.

(* deflate_stored's comparisons of len with (z_size_t)left + avail_in (patch F9): 64 bits *)
Lemma int64_eq_u64 a b : 0 <= a <= Int64.max_unsigned -> Int64.eq (Int64.repr a) (Int64.repr b) = (a =? u64 b).
Proof.
  intros. assert (E : Int64.repr b = Int64.repr (u64 b)).
  { unfold u64. change (2 ^ 64) with Int64.modulus. rewrite <- Int64.unsigned_repr_eq, Int64.repr_unsigned. reflexivity. }
  rewrite E. assert (R : 0 <= u64 b <= Int64.max_unsigned).
  { unfold u64. pose proof (Z.mod_pos_bound b (2 ^ 64) ltac:(lia)). change (2 ^ 64) with Int64.modulus in *. rep_lia. }
  destruct (Z.eqb_spec a (u64 b)); [subst; apply Int64.eq_true|].
  apply Int64.eq_false. intro E'. apply (f_equal Int64.unsigned) in E'.
  rewrite !Int64.unsigned_repr in E' by lia. contradiction.
Qed.

Lemma ds_body_frag {Espec : OracleKind} (p : dptrs) (pin pout : val) (ish : share) (rest : list val)
    (msgv : val) (gv : globals) (s : dstate) (z : strm) (flush min_block used : Z)
    (res : (dstate * strm) + (dstate * strm * Z)) :
  Int.min_signed <= flush <= Int.max_signed -> 0 <= min_block <= Int.max_unsigned ->
  0 <= used <= Int.max_unsigned ->
  ds_body flush min_block (s, z) = Some res ->
  semax Delta_ds
    (PROP () LOCAL (temp _min_block (vi min_block); temp _last (vi 0); temp _used (vi used);
                    gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s z p pin pout ish rest msgv gv; deflate_globals gv))
    S_body (body_post p pin pout ish rest msgv gv s z flush min_block used res).
Proof.
  intros Hf Hm Hu Hb.
  apply ds_body_split in Hb.
  rewrite S_body_eq.
  cbv [S_el ones repeat app sub S_body f_deflate_stored fn_body].
  unfold dfull, dstate_at. rewrite sb_trees_at_split, sb_strm_at_split.
  unfold dtype_at, match_at, out_at. Intros.
  unfold d_trm in *; cbn [fst snd] in *.
  assert (Hz : 0 <= z_avail_out z <= Int.max_unsigned) by (unfold strm_ranges, u32_ok in H; lia).
  assert (Hin : 0 <= z_avail_in z <= Int.max_unsigned) by (unfold strm_ranges, u32_ok in H; lia).
  pose proof (hdr_range s) as Hh.
  assert_PROP (Zlength rest = z_avail_out z) as Hrest by (unfold out_space; entailer!).
  unfold body_post.
  forward. forward. forward. forward. forward.
  rewrite add_repr, hdr_val. fold (stored_hdr s).
  forward_if.
  { 
    destruct Hb as [[_ Hres] | [Hge _]]; [|lia].
    forward. refold_dfull. entailer!. }
  idtac.
  destruct Hb as [[Hlt _] | [_ [Hlong Hb]]]; [lia|].
  assert (Hl64 : Int64.min_signed <= d_strstart s - d_block_start s <= Int64.max_signed)
    by (unfold in_long in Hlong; rewrite andb_true_iff, !Z.leb_le in Hlong; rep_lia).
  assert (Hss : 0 <= d_strstart s <= Int.max_unsigned) by (unfold dstate_ranges, u32_ok in H2; tauto).
  assert (Hbs : Int64.min_signed <= d_block_start s <= Int64.max_signed) by (unfold dstate_ranges, s64_ok in H2; tauto).
  forward. forward. forward. forward. forward. forward.
  rewrite (Int.unsigned_repr (d_strstart s)) by lia. rewrite sub64_repr, int_repr_l64, sub_repr.
  change (Vint (Int.repr (d_strstart s - d_block_start s))) with (vi (d_strstart s - d_block_start s)).
  change (Vint (Int.repr (z_avail_out z - stored_hdr s))) with (vi (z_avail_out z - stored_hdr s)).
  rewrite <- (vi_u32' (d_strstart s - d_block_start s)), <- (vi_u32' (z_avail_out z - stored_hdr s)).
  fold (ds_left s). fold (ds_have s z).
  pose proof (u32_range' (d_strstart s - d_block_start s)) as Hleft. fold (ds_left s) in Hleft.
  pose proof (u32_range' (z_avail_out z - stored_hdr s)) as Hhave. fold (ds_have s z) in Hhave.
  try deadvars!.
  forward. forward.
  set (len1 := if MAX_STORED >? u64 (ds_left s + z_avail_in z) then u32 (ds_left s + z_avail_in z) else MAX_STORED).
  fwd_if_set _len (vi len1).
  { forward. forward. forward. entailer!.
    rewrite !Int.unsigned_repr in H6 by rep_lia. rewrite !Int64.unsigned_repr in H6 by rep_lia.
    apply len1_then; lia. }
  { forward. entailer!.
    rewrite !Int.unsigned_repr in H6 by rep_lia. rewrite !Int64.unsigned_repr in H6 by rep_lia.
    apply len1_else; lia. }
  assert (Hlen1 : 0 <= len1 <= 65535).
  { subst len1. rewrite u64_small by rep_lia. unfold MAX_STORED.
    destruct (Z.gtb_spec 65535 (ds_left s + z_avail_in z)); [rewrite u32_id by rep_lia|]; lia. }
  assert (Elen : ds_len s z = if len1 >? ds_have s z then ds_have s z else len1) by reflexivity.
  assert (Hlen : 0 <= ds_len s z <= 65535).
  { rewrite Elen. destruct (Z.gtb_spec len1 (ds_have s z)); lia. }
  fwd_if_set _len (vi (ds_len s z)).
  { forward. entailer!. rewrite ?Int.unsigned_repr in H6 by rep_lia.
    rewrite Elen. destruct (Z.gtb_spec len1 (ds_have s z)); [reflexivity | lia]. }
  { forward. entailer!. rewrite ?Int.unsigned_repr in H6 by rep_lia.
    rewrite Elen. destruct (Z.gtb_spec len1 (ds_have s z)); [lia | reflexivity]. }
  clear Elen. clearbody len1.
  set (b3 := ((ds_len s z =? 0) && negb (flush =? Z_FINISH))%bool).
  set (b4 := (b3 || (flush =? Z_NO_FLUSH))%bool).
  fwd_if_set _t'2 (Val.of_bool (ds_break s z flush min_block)).
  { fwd_if_set _t'3 (Val.of_bool b3).
    { forward. entailer!. rewrite bool2val_eq, int_eq_repr_s' by rep_lia. unfold b3. rewrite H7. reflexivity. }
    { forward. entailer!. unfold b3. destruct (Z.eqb_spec (ds_len s z) 0); [lia | reflexivity]. }
    fwd_if_set _t'4 (Val.of_bool b4).
    { forward. entailer!. apply typed_true_of_bool in H7. unfold b4. rewrite H7. reflexivity. }
    { forward. entailer!. apply typed_false_of_bool in H7. rewrite bool2val_eq, int_eq_repr_s' by rep_lia.
      unfold b4. rewrite H7. reflexivity. }
    fwd_if_set _t'2 (Val.of_bool (ds_break s z flush min_block)).
    { forward. entailer!. apply typed_true_of_bool in H7. unfold b4, b3 in H7.
      rewrite ds_break_eq, (proj2 (Z.ltb_lt _ _) H6), H7. reflexivity. }
    { forward. forward. forward. forward. entailer!. apply typed_false_of_bool in H7. unfold b4, b3 in H7.
      rewrite bool2val_eq. unfold Int64.cmpu. rewrite int64_eq_u64 by rep_lia.
      rewrite ds_break_eq, (proj2 (Z.ltb_lt _ _) H6), H7. reflexivity. }
    entailer!. }
  { forward. entailer!. rewrite ds_break_eq, (proj2 (Z.ltb_ge _ _) (Z.ge_le _ _ H6)). reflexivity. }
  forward_if.
  { apply typed_true_of_bool in H6.
    destruct Hb as [[_ Hres] | [Hbr _]]; [|congruence].
    forward. refold_dfull. entailer!. }
  apply typed_false_of_bool in H6.
  destruct Hb as [[Hbr _] | [_ [s1 [z1 [s2 [z2 [len2 [z3 [E1 [E2 [E3 Eres]]]]]]]]]]]; [congruence|].
  fwd_if_set _t'5 (Val.of_bool ((flush =? Z_FINISH) && (ds_len s z =? u64 (ds_left s + z_avail_in z)))%bool).
  { forward. forward. forward. entailer!. rewrite bool2val_eq. unfold Int64.cmpu. rewrite int64_eq_u64 by rep_lia. reflexivity. }
  { forward. entailer!. destruct (Z.eqb_spec flush Z_FINISH); [unfold Z_FINISH in *; congruence | reflexivity]. }
  fwd_if_set _t'6 (vi (ds_last s z flush)).
  { forward. entailer!.
    match goal with Ht : typed_true _ _ |- _ => apply typed_true_of_bool in Ht; unfold ds_last; rewrite Ht; reflexivity end. }
  { forward. entailer!.
    match goal with Ht : typed_false _ _ |- _ => apply typed_false_of_bool in Ht; unfold ds_last; rewrite Ht; reflexivity end. }
  forward.
  assert (Hlast : 0 <= ds_last s z flush <= 1) by (unfold ds_last; match goal with |- context [if ?c then _ else _] => destruct c end; lia).
  eapply semax_pre; [| eapply (ds_tail_frag p pin pout ish rest msgv gv s z flush min_block used res
                                 (ds_len s z) (ds_left s) (ds_last s z flush)); eauto; rep_lia].
  refold_dfull. entailer!.
Qed.
