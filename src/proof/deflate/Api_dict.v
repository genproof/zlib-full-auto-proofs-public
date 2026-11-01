(** * Body proof of deflateSetDictionary under the corrected specification
    (the v7 deflateSetDictionary_spec: the dictionary as [opt_obj dsh (Some dict) dp], [is_pointer_or_null nextin]). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require QuickProof.Assembly Zlib.units.Adler32.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.ApiKit.
Require Import Zlib.proof.deflate.DictKit.
Require Import Zlib.proof.deflate.DictClear Zlib.proof.deflate.DictInner Zlib.proof.deflate.DictLoop
  Zlib.proof.deflate.DictFacts.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

(** The dictionary pointer is valid for [dictionary == Z_NULL] (an empty object by its malloc token). *)
Lemma dict_wvp dsh dict dp (R : mpred) : readable_share dsh ->
  (@data_at DCS.CS dsh (tarray tuchar (Zlength dict)) (map vi dict) dp *
   (if Zlength dict =? 0 then @malloc_token DCS.CS Ews (tarray tuchar 0) dp else emp)) * R
  |-- weak_valid_pointer dp.
Proof.
  intros Hsh. apply sepcon_weak_valid_pointer1. destruct (Zlength dict =? 0) eqn:Hz.
  - apply sepcon_weak_valid_pointer2. eapply derives_trans; [|apply valid_pointer_weak].
    apply malloc_token_valid_pointer. simpl. lia.
  - rewrite sepcon_emp. apply Z.eqb_neq in Hz. eapply derives_trans; [|apply valid_pointer_weak].
    apply data_at_valid_ptr.
    + apply readable_nonidentity; auto.
    + simpl. pose proof (Zlength_nonneg dict). rep_lia.
Qed.

Lemma dict_test_eq dsh dict dp (R : mpred) : readable_share dsh -> isptr dp ->
  (@data_at DCS.CS dsh (tarray tuchar (Zlength dict)) (map vi dict) dp *
   (if Zlength dict =? 0 then @malloc_token DCS.CS Ews (tarray tuchar 0) dp else emp)) * R
  |-- denote_tc_test_eq dp (Vlong (Int64.repr 0)).
Proof.
  intros Hsh Hp.
  assert (E : offset_val 0 dp = dp) by (destruct dp; try contradiction; simpl; rewrite Ptrofs.add_zero; auto).
  pose proof (Bytes.cbuf_test_eq_frame R (Zlength dict =? 0) Ews dsh dp 0 (Zlength dict) (map vi dict)) as L.
  rewrite E in L. eapply derives_trans; [|apply L]; auto.
  - cancel. destruct (Zlength dict =? 0) eqn:Hz; [|apply derives_refl].
    apply Z.eqb_eq in Hz. rewrite Hz. apply derives_refl.
  - pose proof (Zlength_nonneg dict); lia.
  - destruct (Zlength dict =? 0) eqn:Hz; [left; auto|right]. apply Z.eqb_neq in Hz. pose proof (Zlength_nonneg dict); lia.
Qed.

(** ** The model of deflateSetDictionary, step by step *)

Definition sd_c1 (s : dstate) : bool :=
  (d_wrap s =? 2) || (d_wrap s =? 1) && negb (d_status s =? INIT_STATE).

Definition sd_cond (s : dstate) : bool :=
  (d_wrap s =? 2) || (d_wrap s =? 1) && negb (d_status s =? INIT_STATE) || negb (d_lookahead s =? 0).

Lemma sd_cond_eq s : sd_cond s = (sd_c1 s || negb (d_lookahead s =? 0))%bool.
Proof. reflexivity. Qed.

Definition sd_z1 (s : dstate) (z : strm) (d : list Z) : strm :=
  if d_wrap s =? 1 then set_z_adler z (Zlib.proof.adler32.Model.adler32_z_val (z_adler z) d) else z.

Definition sd_zd (z1 : strm) (d : list Z) (off len : Z) : strm :=
  mkST d off len (z_total_in z1) (z_out z1) (z_avail_out z1) (z_total_out z1) (z_adler z1) (z_msg z1).

Definition sd_zfin (z zd : strm) : strm :=
  mkST (z_in z) (z_next_in z) (z_avail_in z) (z_total_in zd) (z_out zd) (z_avail_out zd) (z_total_out zd)
       (z_adler zd) (z_msg zd).

Definition sd_final (s2 : dstate) (wrap : Z) : dstate :=
  set_d_wrap (set_d_match_available (set_d_prev_length (set_d_match_length (set_d_lookahead (set_d_insert
    (set_d_block_start (set_d_strstart s2 (u32 (d_strstart s2 + d_lookahead s2)))
       (u32 (d_strstart s2 + d_lookahead s2))) (d_lookahead s2)) 0) 2) 2) 0) wrap.

(** The state and the window of the dictionary before fill_window. *)
Definition sd_pre (s : dstate) (d : list Z) (s3 : dstate) (off len : Z) : Prop :=
  if Zlength d >=? d_w_size s then
    (if d_wrap s =? 0 then exists s2, c_clear_hash (set_d_wrap s 0) = Some s2 /\ s3 = sd_clear_post s2
     else s3 = set_d_wrap s 0) /\ off = Zlength d - d_w_size s /\ len = d_w_size s
  else s3 = set_d_wrap s 0 /\ off = 0 /\ len = Zlength d.

Lemma clear_hash_w_size s s2 : c_clear_hash s = Some s2 -> d_w_size s2 = d_w_size s.
Proof. unfold c_clear_hash. intros H. inv_bind H. inv_bind H. inversion H; reflexivity. Qed.

Lemma sd_bad s z d : status_ok (d_status s) = false ->
  c_deflateSetDictionary s z (Some d) = Some (s, z, Z_STREAM_ERROR).
Proof. intros H. unfold c_deflateSetDictionary, bad_state, c_deflateStateCheck. rewrite H. reflexivity. Qed.

Lemma sd_err s z d : status_ok (d_status s) = true -> sd_cond s = true ->
  c_deflateSetDictionary s z (Some d) = Some (s, z, Z_STREAM_ERROR).
Proof.
  intros H Hc. unfold sd_cond in Hc. unfold c_deflateSetDictionary, bad_state, c_deflateStateCheck. rewrite H.
  cbn - [orb andb]. rewrite Hc. reflexivity.
Qed.

Local Opaque c_fill_window loop c_clear_hash.

Lemma sd_ok_inv s z d s' z' c : status_ok (d_status s) = true -> sd_cond s = false ->
  c_deflateSetDictionary s z (Some d) = Some (s', z', c) ->
  exists s3 off len s4 zd4 s5 zd5,
    sd_pre s d s3 off len /\
    c_fill_window s3 (sd_zd (sd_z1 s z d) d off len) = Some (s4, zd4) /\
    loop FUEL sd_body (s4, zd4) = Some (s5, zd5) /\
    s' = sd_final s5 (d_wrap s) /\ z' = sd_zfin z zd5 /\ c = Z_OK.
Proof.
  intros H Hc Hm. unfold sd_cond in Hc. unfold c_deflateSetDictionary, bad_state, c_deflateStateCheck in Hm.
  rewrite H in Hm. cbn - [orb andb c_fill_window loop c_clear_hash] in Hm. rewrite Hc in Hm.
  inv_bind Hm. destruct x as [[s3 off] len].
  inv_bind Hm. destruct x as [s4 zd4]. inv_bind Hm. destruct x as [s5 zd5]. inversion Hm; subst; clear Hm.
  exists s3, off, len, s4, zd4, s5, zd5. split; [|split; [|split; [|split; [|split]]]]; auto.
  2: destruct (d_wrap s =? 1); reflexivity.
  clear Ha0 Ha1. rename Ha into Hp. unfold sd_pre. destruct (Zlength d >=? d_w_size s).
  - destruct (d_wrap s =? 0).
    + apply bind_inv in Hp. destruct Hp as (y & Hy & Hp). inversion Hp; subst; clear Hp.
      apply bind_inv in Hy. destruct Hy as (y & Hy & Hp). inversion Hp; subst; clear Hp.
      pose proof (clear_hash_w_size _ _ Hy) as Hw. cbn in Hw.
      split; [exists y; split; auto|]. cbn. rewrite Hw. auto.
    + inversion Hp; subst. auto.
  - inversion Hp; subst. auto.
Qed.

Lemma tok_n (n : Z) q : (if n =? 0 then @malloc_token DCS.CS Ews (tarray tuchar 0) q else emp) =
  (if n =? 0 then @malloc_token Zlib.units.Adler32.CS Ews (tarray tuchar n) q else emp).
Proof.
  destruct (n =? 0) eqn:E; auto. apply Z.eqb_eq in E; subst.
  rewrite (@malloc_token_change_composite DCS.CS Zlib.units.Adler32.CS (QuickProof.Assembly.CCE_any _ _) Ews
           (tarray tuchar 0)) by reflexivity. reflexivity.
Qed.

Lemma dict_cs dsh (dict : list Z) dp :
  @data_at DCS.CS dsh (tarray tuchar (Zlength dict)) (map vi dict) dp =
  @data_at Zlib.units.Adler32.CS dsh (tarray tuchar (Zlength dict)) (map vi dict) dp.
Proof. apply QuickProof.Assembly.data_at_tuchar_cs. Qed.

Lemma ranges_set_wrap s w : dstate_ranges s -> s32_ok w -> dstate_ranges (set_d_wrap s w).
Proof. unfold dstate_ranges. cbn. tauto. Qed.

Lemma sd_pre_uniq s d a o l a' o' l' : sd_pre s d a o l -> sd_pre s d a' o' l' -> a = a' /\ o = o' /\ l = l'.
Proof.
  unfold sd_pre. destruct (_ >=? _); [destruct (_ =? 0)|].
  - intros [(s2 & H1 & ->) [-> ->]] [(s2' & H1' & ->) [-> ->]]. rewrite H1 in H1'. inversion H1'. auto.
  - intros [-> [-> ->]] [-> [-> ->]]. auto.
  - intros [-> [-> ->]] [-> [-> ->]]. auto.
Qed.

(** One field of a folded [dstate_at], and a wand giving the state back. *)
Lemma ds_w_size s p gv : dstate_at s p gv |--
  @field_at DCS.CS Ews t_ds (DOT _w_size) (vi (d_w_size s)) (p_s p) *
  (@field_at DCS.CS Ews t_ds (DOT _w_size) (vi (d_w_size s)) (p_s p) -* dstate_at s p gv).
Proof.
  unfold dstate_at, win_at. Intros. cancel. rewrite <- wand_sepcon_adjoint. entailer!.
Qed.

Lemma semax_override {Espec : OracleKind} Delta P c (Q Q' : environ -> mpred) R :
  @semax DCS.CS Espec Delta P c (normal_ret_assert Q') -> ENTAIL Delta, Q' |-- Q ->
  @semax DCS.CS Espec Delta P c (overridePost Q R).
Proof.
  intros H E. eapply semax_post; [ | | | | exact H].
  - destruct R; simpl. exact E.
  - destruct R; simpl. intros. apply andp_left2, FF_left.
  - destruct R; simpl. intros. apply andp_left2, FF_left.
  - destruct R; simpl. intros. apply andp_left2, FF_left.
Qed.

(** ** The dictionary as the stream's input, and the facts of the end *)
Lemma to_dfull s p gv ish msgv d off len tin aout tout adl msg pin :
  strm_ranges (mkST d off len tin [] aout tout adl msg) -> msg_ok msg msgv -> readable_share ish ->
  dstate_at s p gv *
  @field_at DCS.CS Ews t_strm (DOT _next_in) (offset_val off pin) (p_strm p) *
  @field_at DCS.CS Ews t_strm (DOT _avail_in) (vi len) (p_strm p) *
  @field_at DCS.CS Ews t_strm (DOT _total_in) (vl tin) (p_strm p) *
  @field_at DCS.CS Ews t_strm (DOT _msg) msgv (p_strm p) *
  @field_at DCS.CS Ews t_strm (DOT _state) (p_s p) (p_strm p) *
  strm_zfuncs (p_strm p) gv *
  @field_at DCS.CS Ews t_strm (DOT _opaque) nullval (p_strm p) *
  @field_at DCS.CS Ews t_strm (DOT _adler) (vl adl) (p_strm p) *
  @field_at_ DCS.CS Ews t_strm (DOT _reserved) (p_strm p) *
  @data_at DCS.CS ish (tarray tuchar (Zlength d)) (map vi d) pin
  |-- dfull_in s (mkST d off len tin [] aout tout adl msg) p pin ish msgv gv.
Proof.
  intros. unfold dfull_in, strm_in_at, in_obj, strm_zfuncs.
  cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler z_msg]. entailer!.
Qed.

Lemma sd_pre_ranges s d s3 off len : sd_pre s d s3 off len -> 0 <= d_w_size s ->
  0 <= off /\ 0 <= len /\ off + len = Zlength d.
Proof.
  pose proof (Zlength_nonneg d). unfold sd_pre. destruct (Zlength d >=? d_w_size s) eqn:E.
  - apply Z.geb_le in E. intros [_ [-> ->]]. lia.
  - intros (_ & -> & ->). lia.
Qed.

Lemma sd_zd_eq s z d off len :
  sd_zd (sd_z1 s z d) d off len =
  mkST d off len (z_total_in z) (z_out z) (z_avail_out z) (z_total_out z) (z_adler (sd_z1 s z d)) (z_msg z).
Proof. unfold sd_zd, sd_z1. destruct (d_wrap s =? 1); reflexivity. Qed.

Lemma sd_z1_adler s z d : u64_ok (z_adler z) -> Forall (fun b => 0 <= b < 256) d -> u64_ok (z_adler (sd_z1 s z d)).
Proof.
  intros Ha Hd. unfold sd_z1. destruct (d_wrap s =? 1); [|exact Ha]. cbn.
  destruct (Zlib.proof.adler32.Model.adler32_z_val_range (z_adler z) d) as [R _].
  - unfold Bytes.is_bytes. eapply Forall_impl; [|exact Hd]. intros; rep_lia.
  - unfold u64_ok. rep_lia.
Qed.

Lemma dlen_set_wrap s w : dlen s (set_d_wrap s w).
Proof. unfold dlen. repeat split. Qed.

Lemma sd_chain s d s3 off len z s4 zd4 s5 zd5 :
  sd_pre s d s3 off len -> c_fill_window s3 z = Some (s4, zd4) -> loop FUEL sd_body (s4, zd4) = Some (s5, zd5) ->
  dlen s (sd_final s5 (d_wrap s)) /\ zkeep z zd5.
Proof.
  intros Hp Hf Hl. destruct sd_keep_facts as (F1 & F2 & F3).
  destruct (F2 _ _ _ _ Hf) as [D1 K1]. destruct (F3 _ _ _ _ Hl) as [D2 K2].
  assert (D0 : dlen s s3).
  { unfold sd_pre in Hp. destruct (_ >=? _); [destruct (d_wrap s =? 0)|].
    - destruct Hp as [(s2 & Hc & ->) _]. eapply dlen_trans; [apply (dlen_set_wrap s 0)|].
      eapply dlen_trans; [apply (F1 _ _ Hc)|]. unfold dlen. repeat split.
    - destruct Hp as [-> _]. apply dlen_set_wrap.
    - destruct Hp as [-> _]. apply dlen_set_wrap. }
  split; [|eapply zkeep_trans; eauto].
  eapply dlen_trans; [exact D0|]. eapply dlen_trans; [exact D1|]. eapply dlen_trans; [exact D2|].
  unfold dlen. repeat split.
Qed.

Lemma sd_final_ranges s5 w : dstate_ranges s5 -> s32_ok w -> dstate_ranges (sd_final s5 w).
Proof.
  intros H Hw. pose proof (u32_range (d_strstart s5 + d_lookahead s5)) as Hu.
  assert (A1 : u32_ok (u32 (d_strstart s5 + d_lookahead s5))) by exact Hu.
  assert (A2 : s64_ok (u32 (d_strstart s5 + d_lookahead s5))) by (unfold s64_ok; rep_lia).
  assert (A3 : u32_ok 0) by (unfold u32_ok; rep_lia).
  assert (A4 : u32_ok 2) by (unfold u32_ok; rep_lia).
  assert (A5 : s32_ok 0) by (unfold s32_ok; rep_lia).
  unfold dstate_ranges in *. unfold sd_final. dcbn. tauto.
Qed.

Lemma sia_eq z sp q pin msgv gv : strm_in_at z sp q pin msgv gv =
  (@field_at DCS.CS Ews t_strm (DOT _next_in) (offset_val (z_next_in z) pin) q *
   @field_at DCS.CS Ews t_strm (DOT _avail_in) (vi (z_avail_in z)) q *
   @field_at DCS.CS Ews t_strm (DOT _total_in) (vl (z_total_in z)) q *
   @field_at DCS.CS Ews t_strm (DOT _msg) msgv q *
   @field_at DCS.CS Ews t_strm (DOT _state) sp q *
   strm_zfuncs q gv *
   @field_at DCS.CS Ews t_strm (DOT _opaque) nullval q *
   @field_at DCS.CS Ews t_strm (DOT _adler) (vl (z_adler z)) q *
   @field_at_ DCS.CS Ews t_strm (DOT _reserved) q)%logic.
Proof. unfold strm_in_at, strm_zfuncs. apply pred_ext; cancel. Qed.

(** ** Tactics: a forward_if whose postcondition is the precondition with one SEP item replaced. *)
Ltac repl_list R old new :=
  lazymatch R with
  | old :: ?t => constr:(new :: t)
  | ?h :: ?t => let t' := repl_list t old new in constr:(h :: t')
  end.

(** Fold the fields of the deflate_state at [p] into [dstate_at s' p gv]. *)
Ltac drop_ds R p :=
  lazymatch R with
  | nil => constr:(@nil mpred)
  | @field_at _ _ _ _ _ (p_s p) :: ?t => drop_ds t p
  | trees_at _ _ _ _ _ :: ?t => drop_ds t p
  | hash_at _ p :: ?t => drop_ds t p
  | cfg_at _ p :: ?t => drop_ds t p
  | win_at _ p :: ?t => drop_ds t p
  | match_at _ p :: ?t => drop_ds t p
  | stat_at _ p :: ?t => drop_ds t p
  | @data_at _ _ _ _ (p_window p) :: ?t => drop_ds t p
  | ?h :: ?t => let t' := drop_ds t p in constr:(h :: t')
  end.

Ltac fold_ds s' p gv :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    let R' := drop_ds R p in
    apply semax_pre with (PROPx P (LOCALx Q (SEPx (dstate_at s' p gv :: R'))));
    [ unfold dstate_at, stat_at, match_at, win_at; entailer!; try apply derives_refl | ]
  end.

Ltac drop_df R :=
  lazymatch R with
  | nil => constr:(@nil mpred)
  | dfull_in _ _ _ _ _ _ _ :: ?t => drop_df t
  | deflate_globals _ :: ?t => drop_df t
  | ?h :: ?t => let t' := drop_df t in constr:(h :: t')
  end.

Ltac fif_repl old new :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    let R' := repl_list R old new in forward_if (PROPx P (LOCALx Q (SEPx R'))) end.

Lemma body_deflateSetDictionary : ob_deflateSetDictionary.
Proof.
  unfold ob_deflateSetDictionary. start_function. rename H3 into Hni.
  destruct os as [s|].
  2:{ cbn in H2. inv H2.
      sep_apply (dstream_check_none 2 strmp ghp gv). Intros za zf.
      sep_apply (api_fields_ni strmp nextin ain tin nextout aout tout msgv adler).
      forward_call (@None dstate, strmp, nullval, za, zf, nextin, gv). { cancel. }
      sep_apply (mp_wand (dcheck_at None strmp nullval za zf gv) (dstream 2 None strmp ghp gv)).
      sep_apply (mp_wand (@field_at DCS.CS Ews t_strm (DOT _next_in) nextin strmp)
                         (api_fields strmp nextin ain tin nextout aout tout msgv adler)).
      forward_if (PROP () LOCAL (temp _t'2 (vi 1); gvars gv; temp _strm strmp; temp _dictionary dp;
                                 temp _dictLength (vi (Zlength dict)))
                  SEP (dstream 2 None strmp ghp gv; api_fields strmp nextin ain tin nextout aout tout msgv adler;
                       opt_obj dsh (Some dict) dp; deflate_globals gv)).
      - forward. entailer!.
      - discriminate.
      - forward_if; [|discriminate]. forward. Exists msgv. entailer!. apply derives_refl. }
  sep_apply (dstream_check_some 2 s strmp ghp gv). Intros pc.
  forget (gv _zcalloc) as za. forget (gv _zcfree) as zf.
  sep_apply (api_fields_ni strmp nextin ain tin nextout aout tout msgv adler).
  forward_call (Some s, strmp, p_s pc, za, zf, nextin, gv). { cancel. }
  sep_apply (mp_wand (dcheck_at (Some s) strmp (p_s pc) za zf gv) (dstream 2 (Some s) strmp ghp gv)).
  sep_apply (mp_wand (@field_at DCS.CS Ews t_strm (DOT _next_in) nextin strmp)
                     (api_fields strmp nextin ain tin nextout aout tout msgv adler)).
  clear dependent pc. clear dependent za. clear dependent zf.
  unfold on_state, c_on_state in H2.
  destruct (c_deflateSetDictionary s _ _) as [[[s' z'] c]|] eqn:Hm; inv H2.
  destruct (status_ok (d_status s)) eqn:Hst.
  2:{ rewrite sd_bad in Hm by auto. inv Hm. unfold c_deflateStateCheck. rewrite Hst.
      forward_if (temp _t'2 (vi 1)); [forward; entailer! | discriminate |].
      forward_if; [|discriminate]. forward. Exists msgv. entailer!. apply derives_refl. }
  unfold c_deflateStateCheck. rewrite Hst.
  unfold opt_obj. Intros.
  assert_PROP (isptr dp) as Hdp by entailer!.
  forward_if (temp _t'2 (vi 0)); [contradiction | |].
  { forward.
    - entailer!. eapply derives_trans; [|apply (dict_test_eq dsh dict dp); auto]. cancel. apply derives_refl.
    - entailer!. destruct dp; try contradiction. reflexivity. }
  forward_if; [contradiction|].
  rewrite dstream_some_eq. Intros p. rewrite dstate_at'_2. unfold api_fields, dstate_at. Intros.
  unfold stat_at, match_at, win_at. Intros.
  match goal with Hr : dstate_ranges s |- _ => rename Hr into Hrg end.
  match goal with Hr : dsizes s |- _ => rename Hr into Hsz end.
  subst strmp ghp.
  forward. forward.
  assert (Hw : s32_ok (d_wrap s)) by drange Hrg.
  assert (Hs : s32_ok (d_status s)) by drange Hrg.
  assert (Hl : u32_ok (d_lookahead s)) by drange Hrg.
  unfold s32_ok, u32_ok in Hw, Hs, Hl.
  forward_if (temp _t'3 (vi (Z.b2z (sd_c1 s)))).
  { forward. entailer!. unfold sd_c1. match goal with E : d_wrap s = 2 |- _ => rewrite E; reflexivity end. }
  { forward_if (temp _t'3 (vi (Z.b2z (sd_c1 s)))).
    - forward. forward. forward. entailer!.
      unfold sd_c1. match goal with E : d_wrap s = 1 |- _ => rewrite E end.
      rewrite int_eq_s32 by (unfold s32_ok; rep_lia). unfold INIT_STATE. cbn.
      destruct (d_status s =? 42); reflexivity.
    - forward. entailer!. unfold sd_c1.
      match goal with E1 : d_wrap s <> 2, E2 : d_wrap s <> 1 |- _ =>
        rewrite (proj2 (Z.eqb_neq _ _) E1), (proj2 (Z.eqb_neq _ _) E2) end. reflexivity. }
  forward_if (temp _t'4 (vi (Z.b2z (sd_cond s)))).
  { forward. entailer!. rewrite sd_cond_eq.
    destruct (sd_c1 s); [reflexivity|discriminate]. }
  { forward. forward. entailer!. rewrite sd_cond_eq.
    destruct (sd_c1 s); [discriminate|].
    cbn. change Int.zero with (Int.repr 0). rewrite int_eq_u32 by (unfold u32_ok; rep_lia). destruct (d_lookahead s =? 0); reflexivity. }
  forward_if.
  { (* return Z_STREAM_ERROR *)
    destruct (sd_cond s) eqn:Hc; [|try congruence; contradiction].
    rewrite sd_err in Hm by auto. inv Hm.
    forward. Exists msgv. rewrite dstream_some_eq. Exists p. rewrite dstate_at'_2.
    unfold api_fields, dstate_at, stat_at, match_at, win_at, opt_obj. entailer!. }
  destruct (sd_cond s) eqn:Hc; [try congruence; discriminate|].
  set (z0 := zmk [] 0 ain tin aout tout adler msg) in Hm.
  fif_repl (@field_at DCS.CS Ews t_strm (DOT _adler) (vl adler) (p_strm p))
           (@field_at DCS.CS Ews t_strm (DOT _adler) (vl (z_adler (sd_z1 s z0 dict))) (p_strm p)).
  { forward. rewrite (tok_n (Zlength dict) dp), (dict_cs dsh dict dp).
    forward_call (adler, dp, Zlength dict, false, dsh, dp, 0, Zlength dict, map vi dict, dict,
                  Zlength dict =? 0, Ews).
    { split.
      - change (map vi dict) with (Bytes.bytes_rep dict). apply Bytes.cbuf_ok_whole; auto.
        unfold Bytes.is_bytes. eapply Forall_impl; [|exact H1]. intros; rep_lia.
      - intros _ Hz. apply Z.eqb_neq in Hz. pose proof (Zlength_nonneg dict). lia. }
    rewrite <- (tok_n (Zlength dict) dp), <- (dict_cs dsh dict dp).
    forward.
    replace (z_adler (sd_z1 s z0 dict)) with (Model.adler32_z_val adler dict)
      by (unfold sd_z1; match goal with E : d_wrap s = 1 |- _ => rewrite E end; reflexivity).
    entailer!. }
  { forward.
    replace (z_adler (sd_z1 s z0 dict)) with adler
      by (unfold sd_z1; match goal with E : d_wrap s <> 1 |- _ => rewrite (proj2 (Z.eqb_neq _ _) E) end;
          reflexivity).
    entailer!. }
  destruct (sd_ok_inv _ _ _ _ _ _ Hst Hc Hm) as (s3 & off & len & s4 & zd4 & s5 & zd5 & Hpre & Hfw & Hlp & -> & -> & ->).
  clear Hm.
  forward. forward.
  assert (Hr1 : dstate_ranges (set_d_wrap s 0)) by (apply ranges_set_wrap; auto; unfold s32_ok; rep_lia).
  fold_ds (set_d_wrap s 0) p gv.
  assert (Hws : u32_ok (d_w_size s)) by drange Hrg. unfold u32_ok in Hws.
  pose proof (Zlength_nonneg dict) as Hn0.
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx (_ :: ?R')))) _ _ =>
    forward_if (PROP () LOCAL (temp _dictionary (offset_val off dp); temp _dictLength (vi len);
                               temp _s (p_s p); temp _strm (p_strm p); temp _wrap (vi (d_wrap s)); gvars gv)
                (SEPx (dstate_at s3 p gv :: R'))) end.
  { assert (Hge : (Zlength dict >=? d_w_size s) = true) by (apply Z.geb_le; lia).
    unfold sd_pre in Hpre. rewrite Hge in Hpre. destruct Hpre as [Hpre [Hoff Hlen]]. subst off len.
    assert (Hw3 : d_w_size s3 = d_w_size s).
    { destruct (d_wrap s =? 0) in Hpre.
      - destruct Hpre as (s2 & Hcl & ->). apply clear_hash_w_size in Hcl. exact Hcl.
      - subst s3. reflexivity. }
    match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx (_ :: ?R')))) _ _ =>
      forward_if (PROP () LOCAL (temp _dictionary dp; temp _dictLength (vi (Zlength dict));
                                 temp _s (p_s p); temp _strm (p_strm p); temp _wrap (vi (d_wrap s)); gvars gv)
                  (SEPx (dstate_at s3 p gv :: R'))) end.
    - match goal with E : d_wrap s = 0 |- _ => rename E into Hw0 end.
      rewrite Hw0 in Hpre. cbn in Hpre. destruct Hpre as (s2 & Hcl & ->).
      rewrite Hw0.
      match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx (_ :: ?R')))) _ _ =>
        unfold MORE_COMMANDS, POSTCONDITION, abbreviate; eapply semax_override;
        [ eapply semax_pre;
          [| apply (sd_clear Espec p gv (set_d_wrap s 0) s2 (p_strm p) dp (Zlength dict) (fold_right_sepcon R') Hcl)]
        | ] end.
      + cbn [fold_right_sepcon]. entailer!.
      + cbn [fold_right_sepcon]. entailer!.
    - forward.
      match goal with E : d_wrap s <> 0 |- _ => rewrite (proj2 (Z.eqb_neq _ _) E) in Hpre end. subst s3.
      entailer!.
    - sep_apply (ds_w_size s3 p gv). Intros. forward. forward. forward.
      sep_apply (mp_wand (@field_at DCS.CS Ews t_ds (DOT _w_size) (vi (d_w_size s3)) (p_s p)) (dstate_at s3 p gv)).
      rewrite Hw3. entailer!. }
  { forward.
    assert (Hlt : (Zlength dict >=? d_w_size s) = false) by (destruct (Zlength dict >=? d_w_size s) eqn:E; [apply Z.geb_le in E; lia | reflexivity]).
    unfold sd_pre in Hpre. rewrite Hlt in Hpre. destruct Hpre as (-> & -> & ->).
    rewrite isptr_offset_val_zero by auto. entailer!. }
  forward. forward. forward. forward.
  rewrite sd_zd_eq in Hfw. cbv [z0 zmk] in Hfw. cbn [z_total_in z_out z_avail_out z_total_out z_msg] in Hfw.
  destruct (sd_pre_ranges _ _ _ _ _ Hpre ltac:(lia)) as (Ho & Hle & Hol).
  assert (Hrz : strm_ranges (mkST dict off len tin [] aout tout (z_adler (sd_z1 s z0 dict)) msg)).
  { unfold strm_ranges; cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler].
    unfold u32_ok, u64_ok in *. rewrite Zlength_nil.
    pose proof (sd_z1_adler s z0 dict H10 H1) as Ha. unfold u64_ok in Ha.
    repeat split; auto; try lia. }
  sep_apply (to_dfull s3 p gv dsh msgv dict off len tin aout tout (z_adler (sd_z1 s z0 dict)) msg dp Hrz H SH).
  forward_call (s3, mkST dict off len tin [] aout tout (z_adler (sd_z1 s z0 dict)) msg, p, dp, dsh, msgv,
                (s4, zd4), gv).
  Intros msgv4.
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
    let RR := drop_df R in
    eapply semax_seq';
    [ eapply semax_pre;
      [| apply (sd_loop_of sd_inner Espec p dp dsh msgv4 gv s4 zd4 s5 zd5 (p_strm p) nextin (d_wrap s) ain
                 (fold_right_sepcon RR) Hlp)]
    | ] end.
  { cbn [fold_right_sepcon]. entailer!. apply derives_refl. }
  Intros msgv5.
  unfold dfull_in, dstate_at, match_at, stat_at, in_obj. rewrite sia_eq. Intros.
  cbn [fold_right_sepcon]. rewrite sepcon_emp. Intros.
  unfold MORE_COMMANDS, abbreviate. abbreviate_semax.
  forward. forward. forward. forward. forward. forward. forward. forward.
  forward. forward. forward. forward. forward. forward. forward.
  forward.
  destruct (sd_chain _ _ _ _ _ _ _ _ _ _ Hpre Hfw Hlp) as [Hdl Hzk].
  destruct Hzk as (Kin & Kout & Kao & Kto).
  cbn [z_in z_out z_avail_out z_total_out] in Kin, Kout, Kao, Kto.
  pose proof (dlen_dsizes _ _ Hdl Hsz) as Hsz'.
  assert (Hrf : dstate_ranges (sd_final s5 (d_wrap s))) by (apply sd_final_ranges; auto; unfold s32_ok; lia).
  assert (Hbs : Int.unsigned (Int.repr (d_strstart s5 + d_lookahead s5)) = u32 (d_strstart s5 + d_lookahead s5))
    by (unfold u32; rewrite Int.unsigned_repr_eq; reflexivity).
  rewrite Hbs.
  Exists msgv5. rewrite dstream_some_eq. Exists p. rewrite dstate_at'_2.
  rewrite (dlen_dtokens _ _ p Hdl).
  unfold dstate_at. rewrite (prop_true_andp _ _ Hrf).
  unfold stat_at, match_at. dsame s5. unfold sd_final. dcbn.
  unfold api_fields, opt_obj, sd_zfin, z0, zmk. dcbn.
  rewrite Kin, Kao, Kto, !vi_u32.
  entailer!.
  match goal with Hz : strm_ranges zd5 |- _ => unfold strm_ranges in Hz; tauto end.
Qed.
