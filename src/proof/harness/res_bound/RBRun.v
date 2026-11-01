(* Law res_bound, main: part_run (RBKit.v): set_buffer(&strm, data, data_len, compressed, bound), total_in =
   strm.total_in, code = deflate(&strm, Z_FINISH), gp_assert(code == Z_STREAM_END), wrote = strm.next_out -
   compressed, the asserts on wrote, avail_in, next_in, total_in and total_out, return 0 (msuf 35 -> the end). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.LawFactsW Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.deflate.Obligations.
Require Zlib.proof.harness.bound_common.BoundKit Zlib.proof.harness.deflate_bound.MainKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.res_bound.RBCS Zlib.proof.harness.res_bound.RBString Zlib.proof.harness.res_bound.RBKit.
Require Import Zlib.proof.harness.res_bound.RBOffer1 Zlib.proof.harness.res_bound.RBOffer2.
Require Import Zlib.harness.res_bound.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

(** ** Memory lemmas *)

Lemma rr_data_at_ (b : Z) (p : val) :
  0 <= b ->
  @data_at_ DCS.CS Ews (tarray tuchar b) p =
  @data_at DCS.CS Ews (tarray tuchar (Zlength (Zrepeat Vundef b))) (Zrepeat Vundef b) p.
Proof. intros. rewrite Zlength_Zrepeat by lia. reflexivity. Qed.

Lemma rr_dstream_sp (lvl : Z) (os : option dstate) (sp ghp spp : val) (gv : globals) :
  dstream_sp lvl os sp ghp spp gv |-- dstream lvl os sp ghp gv.
Proof. rewrite dstream_sp_eq. Exists spp. cancel. Qed.

(* the stream's memory after the run back to the local's Tsh (BoundKit.dstream_end_data_at_ and the split of
   Tsh into Ews and its complement) *)
Lemma rr_close (s' : dstate) (vs : val) (gv : globals) (nin : val) (ain tin : Z) (nout : val) (aout tout : Z)
    (msgv : val) (adler : Z) :
  dstream_end (Some s') vs gv * api_fields vs nin ain tin nout aout tout msgv adler *
  @data_at_ DCS.CS (Share.comp Ews) t_strm vs * BoundKit.strm_pad vs
  |-- data_at_ Tsh t_strm vs * TT.
Proof.
  sep_apply (BoundKit.dstream_end_data_at_ (Some s') vs gv nin ain tin nout aout tout msgv adler).
  rewrite (BoundKit.data_at__Tsh_split t_strm vs).
  unfold BoundKit.Ecomp; cancel.
Qed.

(* deflate_spec's api_fields with strm->total_in apart (main reads it before the call) *)
Definition af_rest_tin (sp nin : val) (ain : Z) (nout : val) (aout tout : Z) (msgv : val) (adler : Z) : mpred :=
  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_in) nin sp *
  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_in) (vi ain) sp *
  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_out) nout sp *
  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_out) (vi aout) sp *
  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._total_out) (vl tout) sp *
  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._msg) msgv sp *
  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._adler) (vl adler) sp.

Lemma af_tin_open (sp nin : val) (ain tin : Z) (nout : val) (aout tout : Z) (msgv : val) (adler : Z) :
  api_fields sp nin ain tin nout aout tout msgv adler |--
  !! (u32_ok ain /\ u64_ok tin /\ u32_ok aout /\ u64_ok tout /\ u64_ok adler) &&
  (@field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._total_in) (vl tin) sp *
   af_rest_tin sp nin ain nout aout tout msgv adler).
Proof. unfold api_fields, af_rest_tin. entailer!. Qed.

Lemma af_tin_close (sp nin : val) (ain tin : Z) (nout : val) (aout tout : Z) (msgv : val) (adler : Z) :
  u32_ok ain /\ u64_ok tin /\ u32_ok aout /\ u64_ok tout /\ u64_ok adler ->
  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._total_in) (vl tin) sp *
  af_rest_tin sp nin ain nout aout tout msgv adler
  |-- api_fields sp nin ain tin nout aout tout msgv adler.
Proof. intros. unfold api_fields, af_rest_tin. entailer!. Qed.

(* data + data_len: the pointer arithmetic on a byte object *)
Lemma rr_add_ptr (p : val) (n : Z) :
  isptr p -> 0 <= n <= Int64.max_unsigned -> force_val (sem_add_ptr_long tuchar p (vl n)) = offset_val n p.
Proof.
  intros Pp Hn. destruct p; try contradiction. unfold sem_add_ptr_long, vl. simpl.
  f_equal. f_equal. rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_int64.
  rewrite Int64.unsigned_repr by lia. reflexivity.
Qed.

(* the end of a malloc'ed byte object (also of 0 bytes, through its malloc token) is weakly valid, so
   next_in == data + data_len is defined *)
Section TestEq.
Local Transparent denote_tc_test_eq.
Lemma rr_test_eq_end (P : mpred) (n : Z) (l : list val) (q : val) :
  0 <= n ->
  P |-- malloc_token Ews (tarray tuchar n) q * data_at Ews (tarray tuchar n) l q * TT ->
  P |-- denote_tc_test_eq (offset_val n q) (offset_val n q).
Proof.
  intros Hn H. eapply derives_trans; [exact H | ]. clear H.
  sep_apply (data_at_data_at_ Ews (tarray tuchar n) l q).
  assert_PROP (isptr q) as Hq by (saturate_local; entailer!).
  destruct q; try contradiction.
  assert (W : malloc_token Ews (tarray tuchar n) (Vptr b i) * data_at_ Ews (tarray tuchar n) (Vptr b i) * TT
              |-- weak_valid_pointer (offset_val n (Vptr b i))).
  { apply sepcon_weak_valid_pointer1.
    destruct (zlt 0 n).
    - apply sepcon_weak_valid_pointer2. rewrite data_at__memory_block. normalize.
      simpl sizeof. rewrite Z.max_r by lia. rewrite Z.mul_1_l.
      apply memory_block_weak_valid_pointer; auto; lia.
    - assert (n = 0) by lia. subst.
      apply sepcon_weak_valid_pointer1.
      eapply derives_trans; [apply malloc_token_valid_pointer; simpl; lia | ].
      replace (offset_val 0 (Vptr b i)) with (Vptr b i) by (simpl; rewrite ptrofs_add_repr_0_r; auto).
      apply valid_pointer_weak. }
  simpl offset_val in *. unfold denote_tc_test_eq, test_eq_ptrs, sameblock.
  destruct (peq b b) as [E | X]; [ | contradiction]. simpl.
  apply andp_right; (eapply derives_trans; [| exact W]); cancel.
Qed.
End TestEq.

(* the stream's caller fields, read one by one, back as deflate_spec's api_fields *)
Lemma rr_af_fold (sp nin : val) (ain tin : Z) (nout : val) (aout tout : Z) (msgv : val) (adler : Z) :
  u32_ok ain -> u64_ok tin -> u32_ok aout -> u64_ok tout -> u64_ok adler ->
  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_in) nin sp *
  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_in) (vi ain) sp *
  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._total_in) (vl tin) sp *
  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_out) nout sp *
  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_out) (vi aout) sp *
  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._total_out) (vl tout) sp *
  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._msg) msgv sp *
  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._adler) (vl adler) sp
  |-- api_fields sp nin ain tin nout aout tout msgv adler.
Proof. intros. unfold api_fields. entailer!. Qed.

(* wrote = (size_t) (strm.next_out - compressed): the bytes deflate() wrote *)
Lemma rr_sub_ptr (p : val) (L : Z) : isptr p -> 0 <= L <= 4294967295 ->
  force_val (sem_binary_operation' Osub (tptr tuchar) (tptr tuchar) (offset_val L p) p) = vl L.
Proof.
  intros Hp HL. destruct p; try contradiction.
  unfold sem_binary_operation', sem_sub; simpl. unfold sem_sub_pp; simpl.
  destruct (eq_block b b); [|congruence]. simpl.
  unfold vl, Vptrofs; cbv [Archi.ptr64].
  rewrite Ptrofs.sub_add_l, Ptrofs.sub_idem, Ptrofs.add_zero_l. unfold Ptrofs.divs.
  rewrite (Ptrofs.signed_repr 1) by rep_lia. rewrite Ptrofs.signed_repr by rep_lia. rewrite Z.quot_1_r.
  unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr by rep_lia. reflexivity.
Qed.

(* the end of a branch of an [if] whose join point is given: main's postcondition is opaque in it *)
Ltac rr_join := destruct POST_m; cbn [RA_normal]; entailer!.

(* main from set_buffer to the end, from A6 *)
Lemma part_run : part_run_stmt.
Proof.
  intros Espec Bpre Brun gv vh vs rs st ghp hx Hr b obp HBF OA HOB.
  unfold msuf35, A6.
  abbreviate_semax.
  Intros.
  pose proof H as RS.
  destruct RS as (_ & _ & _ & _ & Hn & _ & _ & _ & _ & _ & Hdl & Hdb & _ & _ & _ & _ & _ & _ & _ & _ &
                  Pd & _).
  destruct (proj2 OA (r_n rs) b (st_s st) (st_tin st) (st_tout st) (st_adler st) (r_data rs) (st_msg st)
              H0 (proj2 H1) Hdb Hdl) as (s' & z' & Hrun & Hg & Hai & Hni & Hti & Hao & Hout & Hto).
  rewrite dstream_sp_eq. Intros sp.
  sep_apply (rr_dstream_open (st_s st) vs ghp sp gv).
  unfold srest at 1, st_fields. Intros.
  assert_PROP (u32_ok (MainKit.st_ain st) /\ u64_ok (st_tin st) /\ u32_ok (MainKit.st_aout st) /\ u64_ok (st_tout st) /\
               u64_ok (st_adler st)) as Hf by (unfold api_fields; entailer!).
  sep_apply (rr_offer_pre vs (MainKit.st_ain st) (st_tin st) (MainKit.st_aout st) (st_tout st) (st_msgv st) (st_adler st) sp gv
               (st_s st)).
  remember (gv deflate.code._zcalloc) as zca. remember (gv deflate.code._zcfree) as zcf.
  forward_call (vs, Ews, r_datap rs, r_n rs, obp, b, nullval, vi (MainKit.st_ain st), vl (st_tin st), nullval,
                vi (MainKit.st_aout st), vl (st_tout st), st_msgv st, sp, zca, zcf, nullval, vi (tr_data_type (fst (d_trm (st_s st)))), vl (st_adler st),
                Vundef).
  assert (Hun : u32_ok (r_n rs)) by (unfold u32_ok; rep_lia).
  assert (Hub : u32_ok b) by (unfold u32_ok; rep_lia).
  destruct Hf as (_ & Htin & _ & Htout & Had).
  sep_apply (rr_offer_post vs (r_datap rs) (r_n rs) obp b (st_tin st) (st_tout st) (st_adler st) (st_msgv st) sp
               gv (st_s st) zca zcf Heqzca Heqzcf Hun Htin Hub Htout Had).
  subst zca zcf.
  (* total_in = strm.total_in *)
  sep_apply (af_tin_open vs (r_datap rs) (r_n rs) (st_tin st) obp b (st_tout st) (st_msgv st) (st_adler st)).
  Intros.
  forward.
  sep_apply (af_tin_close vs (r_datap rs) (r_n rs) (st_tin st) obp b (st_tout st) (st_msgv st) (st_adler st)
               ltac:(auto)).
  sep_apply (modus_ponens_wand (rr_own vs sp gv (st_s st)) (dstream_sp 2 (Some (st_s st)) vs ghp sp gv)).
  unfold obj, BoundKit.obj.
  rewrite (rr_data_at_ b obp) by lia.
  change (@malloc_token DCS.CS Ews (tarray tuchar b) obp) with (wv_at (WVtok (tarray tuchar b)) obp).
  replace (api_fields vs (r_datap rs) (r_n rs) (st_tin st) obp b (st_tout st) (st_msgv st) (st_adler st))
    with (api_fields vs (offset_val 0 (r_datap rs)) (r_n rs) (st_tin st) obp (Zlength (Zrepeat Vundef b))
            (st_tout st) (st_msgv st) (st_adler st))
    by (rewrite isptr_offset_val_zero, Zlength_Zrepeat by (auto; lia); reflexivity).
  forward_call (Some (st_s st), vs, ghp, sp, hx, r_datap rs, Ews, r_data rs, 0, r_n rs, st_tin st, obp,
                Zrepeat Vundef b, WVtok (tarray tuchar b), st_tout st, st_msgv st, st_msg st, st_adler st,
                Z_FINISH, (Some s', z', Z_STREAM_END), gv).
  { cancel. }
  { rewrite Zlength_Zrepeat by lia. split; [| split; [| split]].
    - intros ->. simpl. lia.
    - unfold s32_ok, Z_FINISH. rep_lia.
    - unfold strm_ranges, zmk; simpl. rewrite ?Hdl. unfold bytes in Hdb. unfold u32_ok, u64_ok in *.
      rewrite Zlength_nil. repeat split; auto; rep_lia.
    - exists (fun f => f). split; [ apply ef_ok_id | ].
      unfold on_state, c_on_state. rewrite c_deflate_g_id.
      change (zmk ?a ?c ?d ?e ?f ?g ?h ?i) with (zcall a c d e f g h i). rewrite Hrun. reflexivity. }
  simpl fst; simpl snd. Intros msgv'.
  (* gp_assert(code == Z_STREAM_END) *)
  forward_call Int.one.
  rewrite Hai, Hni, Hti, Hto, H2, Z.add_0_l. rewrite Zlength_Zrepeat by lia.
  pose proof (Zlength_nonneg (z_out z')) as HL0.
  assert (HLb : Zlength (z_out z') <= b) by lia.
  unfold api_fields. Intros.
  (* wrote = (size_t) (strm.next_out - compressed) *)
  forward.
  forward.
  { entailer!. apply prop_right. destruct obp; try contradiction. simpl. destruct (peq _ _); [reflexivity | congruence]. }
  rewrite (rr_sub_ptr obp (Zlength (z_out z')) Pobp ltac:(lia)).
  (* wrote <= bound && strm.avail_in == 0 *)
  abbreviate_semax.
  ifpost _t'36 Int.one.
  { forward. forward. rr_join. }
  { exfalso. lia. }
  (* ... && strm.next_in == data + data_len *)
  ifpost _t'37 Int.one.
  { forward. forward.
    { rewrite <- Hdl. entailer!. rewrite (rr_add_ptr (r_datap rs) (Zlength (r_data rs)) Pd ltac:(rep_lia)).
      apply (rr_test_eq_end _ (Zlength (r_data rs)) (map vi (r_data rs)) (r_datap rs) ltac:(lia)). cancel. }
    rr_join.
    rewrite (rr_add_ptr (r_datap rs) (r_n rs) Pd ltac:(rep_lia)). destruct (r_datap rs) as [| | | | | bd od]; try contradiction.
    unfold sem_cmp_pp; simpl. destruct (eq_block bd bd); [|congruence]. rewrite Ptrofs.eq_true. reflexivity. }
  { exfalso. apply Int.one_not_zero. assumption. }
  forward_call Int.one.
  (* strm.total_in == total_in + data_len && strm.total_out == wrote *)
  forward.
  ifpost _t'38 Int.one.
  { forward. forward. rr_join. }
  { (* the uLong sum total_in + data_len is total_in's new value modulo 2^64 *)
    exfalso. match goal with H : Int64.repr _ <> Int64.add _ _ |- _ => apply H end.
    symmetry. apply Int64.eqm_samerepr. apply Int64.eqm_add; apply Int64.eqm_sym; apply Int64.eqm_unsigned_repr. }
  forward_call Int.one.
  (* return 0: the stream's memory back to the local's *)
  sep_apply (rr_af_fold vs (offset_val (r_n rs) (r_datap rs)) 0 (st_tin st + r_n rs)
               (offset_val (Zlength (z_out z')) obp) (z_avail_out z') (Zlength (z_out z')) msgv' (z_adler z')
               H6 H7 H8 H9 H10).
  sep_apply (rr_dstream_sp 2 (Some s') vs ghp sp gv).
  sep_apply (HOB (Some s') vs ghp gv).
  sep_apply (rr_close s' vs gv (offset_val (r_n rs) (r_datap rs)) 0 (st_tin st + r_n rs)
               (offset_val (Zlength (z_out z')) obp) (z_avail_out z') (Zlength (z_out z')) msgv' (z_adler z')).
  sep_apply (H4 (st_s st) eq_refl).
  forward.
  Exists (Int.repr 0). entailer!.
Qed.
