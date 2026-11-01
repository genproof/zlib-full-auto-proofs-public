(* Law deflate_bound, main: part_init (MainKit.v): stream_defaults(&s), r = deflateInit2(...), if (r != Z_OK)
   return 0 (msuf 34 -> msuf 37). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.InitStrm.
Require Zlib.proof.compress.CSpec.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.harness.deflate_bound.MainKit.
Require Import Zlib.harness.x_deflate_bound.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

(* the model of deflateInit2_ (as in deflate_api's RunInit.v): a state only on Z_OK, else Z_STREAM_ERROR or
   Z_MEM_ERROR without a state *)
Lemma pi_keep s z s' z' r :
  c_deflateResetKeep s z = Some (s', z', r) -> bad_state s = false -> r = Z_OK.
Proof.
  unfold c_deflateResetKeep. intros H Hb. rewrite Hb in H.
  destruct (if d_wrap _ <? 0 then _ else _) as [s1|]; [|discriminate].
  simpl in H.
  do 4 (try match type of H with context [bind ?x _] =>
    lazymatch x with Some _ => fail | None => fail | _ => destruct x; simpl in H; try discriminate end end).
  inversion H; reflexivity.
Qed.

Lemma pi_reset s z s' z' r :
  c_deflateReset s z = Some (s', z', r) -> bad_state s = false -> r = Z_OK.
Proof.
  unfold c_deflateReset. intros H Hb.
  destruct (c_deflateResetKeep s z) as [[[a b] c]|] eqn:E; [|discriminate].
  pose proof (pi_keep _ _ _ _ _ E Hb); subst c. simpl in H.
  destruct (c_lm_init a); [|discriminate]. inversion H; reflexivity.
Qed.

Lemma pi_bs_init w b h l t m : bad_state (set_d_method (set_d_tr (init_dstate w b h l) t) m) = false.
Proof. reflexivity. Qed.

Lemma pi_bs_fin s : bad_state (set_d_status s FINISH_STATE) = false.
Proof. reflexivity. Qed.

Lemma pi_end_bind S Z os z' code :
  bind (c_deflateEnd (set_d_status S FINISH_STATE) Z)
    (fun p => let '(os0, z1, _) := p in Some (os0, z1, Z_MEM_ERROR)) = Some (os, z', code) ->
  os = None /\ code = Z_MEM_ERROR.
Proof.
  intros H. unfold c_deflateEnd in H. rewrite pi_bs_fin in H. simpl in H.
  injection H as <- <- <-. split; reflexivity.
Qed.

Lemma pi_reset_bind S Z f os z' code :
  bad_state S = false -> (forall s z0 r, f (s, z0, r) = Some (Some s, z0, r)) ->
  bind (c_deflateReset S Z) f = Some (os, z', code) -> code = Z_OK.
Proof.
  intros Hb Hf H. destruct (c_deflateReset S Z) as [[[a b] c]|] eqn:E; [|discriminate].
  apply pi_reset in E; [|exact Hb]. simpl in H. rewrite Hf in H. injection H as <- <- <-. exact E.
Qed.

Local Opaque c_deflateReset c_deflateEnd init_dstate.
Lemma pi_init_code level method wbits mem strategy a1 a2 a3 a4 a5 z os z' code :
  c_deflateInit2_ true true false level method wbits mem strategy a1 a2 a3 a4 a5 z = Some (os, z', code) ->
  code = Z_OK \/ (os = None /\ (code = Z_STREAM_ERROR \/ code = Z_MEM_ERROR)).
Proof.
  intros H. unfold c_deflateInit2_ in H. cbn [negb orb] in H.
  destruct (if wbits <? 0 then _ else _) as [[wb wr]|];
    [|injection H as <- _ <-; right; split; [reflexivity | left; reflexivity]].
  destruct (_ || _)%bool; [injection H as <- _ <-; right; split; [reflexivity | left; reflexivity]|].
  destruct a1; cbn [negb] in H; [|injection H as <- _ <-; right; split; [reflexivity | right; reflexivity]].
  destruct (a2 && a3 && a4 && a5)%bool; cbn [negb] in H.
  - left. apply pi_reset_bind in H; [exact H | apply pi_bs_init | intros; reflexivity].
  - apply pi_end_bind in H. right. destruct H as [-> ->]. split; [reflexivity | right; reflexivity].
Qed.
Local Transparent c_deflateReset c_deflateEnd init_dstate.

(* local copies of memory lemmas of BoundKit.v (this file does not depend on BoundKit.v): Tsh = Ews + its complement, stream_defaults' postcondition as
   deflateInit2_'s precondition (the padding kept), deflateInit2_'s failure memory back to data_at_ *)
Lemma pi_Tsh_split {cs : compspecs} (t : type) (q : val) :
  @data_at_ cs Tsh t q = @data_at_ cs Ews t q * @data_at_ cs (Share.comp Ews) t q.
Proof.
  symmetry. apply data_at__share_join. apply join_comp_Tsh.
Qed.

Definition pi_strm_pad (sp : val) : mpred :=
  spacer Ews 12 16 sp * spacer Ews 36 40 sp * spacer Ews 92 96 sp.

Lemma pi_defaults_split (sp msg st : val) (tin tout adler dt rs : Z) :
  u64_ok tin -> u64_ok tout -> u64_ok adler ->
  data_at Ews t_strm (nullval, (vi 0, (vl tin, (nullval, (vi 0, (vl tout, (msg, (st,
    (nullval, (nullval, (nullval, (vi dt, (vl adler, vl rs))))))))))))) sp
  |-- api_fields_r sp (mkAF nullval 0 tin nullval 0 tout msg adler) *
      field_at Ews t_strm (DOT deflate.code._zalloc) nullval sp *
      field_at Ews t_strm (DOT deflate.code._zfree) nullval sp *
      field_at Ews t_strm (DOT deflate.code._opaque) nullval sp *
      field_at Ews t_strm (DOT deflate.code._data_type) (vi dt) sp *
      field_at Ews t_strm (DOT deflate.code._state) st sp *
      field_at_ Ews t_strm (DOT deflate.code._reserved) sp * pi_strm_pad sp.
Proof.
  intros. unfold api_fields_r, api_fields, pi_strm_pad; simpl. unfold_data_at (data_at _ _ _ sp). entailer!.
  unfold u32_ok; rep_lia.
Qed.

Lemma pi_strm_fields (sp nin : val) (ain tin : Z) (nout : val) (aout tout : Z) (msgv : val) (adler : Z)
    (st za zf op dt : val) :
  api_fields sp nin ain tin nout aout tout msgv adler *
  field_at Ews t_strm (DOT deflate.code._state) st sp * field_at Ews t_strm (DOT deflate.code._zalloc) za sp *
  field_at Ews t_strm (DOT deflate.code._zfree) zf sp * field_at Ews t_strm (DOT deflate.code._opaque) op sp *
  field_at Ews t_strm (DOT deflate.code._data_type) dt sp *
  field_at_ Ews t_strm (DOT deflate.code._reserved) sp * pi_strm_pad sp
  |-- data_at_ Ews t_strm sp.
Proof.
  unfold api_fields, pi_strm_pad. Intros. unfold_data_at (data_at_ _ _ sp). cancel. unfold field_at_.
  apply derives_refl.
Qed.

Lemma pi_init_fail (sp st za zf op dt : val) (gv : globals) (nin : val) (ain tin : Z)
    (nout : val) (aout tout : Z) (msgv : val) (adler : Z) :
  zfuncs gv * field_at_ Ews t_strm (DOT deflate.code._reserved) sp *
  field_at Ews t_strm (DOT deflate.code._state) st sp * field_at Ews t_strm (DOT deflate.code._zalloc) za sp *
  field_at Ews t_strm (DOT deflate.code._zfree) zf sp * field_at Ews t_strm (DOT deflate.code._opaque) op sp *
  field_at Ews t_strm (DOT deflate.code._data_type) dt sp * api_fields sp nin ain tin nout aout tout msgv adler *
  pi_strm_pad sp
  |-- data_at_ Ews t_strm sp * TT.
Proof.
  sep_apply (pi_strm_fields sp nin ain tin nout aout tout msgv adler st za zf op dt). cancel.
Qed.

Lemma pi_override_normal Delta (P Q : environ -> mpred) (R : ret_assert) :
  ENTAIL Delta, P |-- Q -> ENTAIL Delta, P |-- RA_normal (overridePost Q R).
Proof. intros H. destruct R. exact H. Qed.

(* v9: stream_defaults' postcondition as deflateInit2__spec_v9's precondition pieces (next_in, reset_fields), the
   three fields the spec does not mention (avail_in, next_out, avail_out), the rest and the padding *)
Lemma pi_defaults_split9 (sp msg st : val) (tin tout adler dt rs : Z) :
  data_at Ews t_strm (nullval, (vi 0, (vl tin, (nullval, (vi 0, (vl tout, (msg, (st,
    (nullval, (nullval, (nullval, (vi dt, (vl adler, vl rs))))))))))))) sp
  |-- field_at Ews t_strm (DOT deflate.code._next_in) nullval sp *
      reset_fields sp (vl tin) (vl tout) msg (vl adler) *
      (field_at Ews t_strm (DOT deflate.code._avail_in) (vi 0) sp *
       field_at Ews t_strm (DOT deflate.code._next_out) nullval sp *
       field_at Ews t_strm (DOT deflate.code._avail_out) (vi 0) sp) *
      field_at Ews t_strm (DOT deflate.code._zalloc) nullval sp *
      field_at Ews t_strm (DOT deflate.code._zfree) nullval sp *
      field_at Ews t_strm (DOT deflate.code._opaque) nullval sp *
      field_at Ews t_strm (DOT deflate.code._data_type) (vi dt) sp *
      field_at Ews t_strm (DOT deflate.code._state) st sp *
      field_at_ Ews t_strm (DOT deflate.code._reserved) sp * pi_strm_pad sp.
Proof.
  unfold reset_fields, pi_strm_pad; simpl. unfold_data_at (data_at _ _ _ sp). entailer!.
Qed.

Lemma pi_init_fail9 (sp st za zf op dt : val) (gv : globals) (nin tin tout msgv adler : val) :
  zfuncs gv * field_at_ Ews t_strm (DOT deflate.code._reserved) sp *
  field_at Ews t_strm (DOT deflate.code._state) st sp * field_at Ews t_strm (DOT deflate.code._zalloc) za sp *
  field_at Ews t_strm (DOT deflate.code._zfree) zf sp * field_at Ews t_strm (DOT deflate.code._opaque) op sp *
  field_at Ews t_strm (DOT deflate.code._data_type) dt sp *
  field_at Ews t_strm (DOT deflate.code._next_in) nin sp * reset_fields sp tin tout msgv adler *
  (field_at Ews t_strm (DOT deflate.code._avail_in) (vi 0) sp *
   field_at Ews t_strm (DOT deflate.code._next_out) nullval sp *
   field_at Ews t_strm (DOT deflate.code._avail_out) (vi 0) sp) *
  pi_strm_pad sp
  |-- data_at_ Ews t_strm sp * TT.
Proof.
  unfold reset_fields, pi_strm_pad.
  sep_apply (field_at_field_at_ Ews t_strm (DOT deflate.code._state) st sp).
  sep_apply (field_at_field_at_ Ews t_strm (DOT deflate.code._zalloc) za sp).
  sep_apply (field_at_field_at_ Ews t_strm (DOT deflate.code._zfree) zf sp).
  sep_apply (field_at_field_at_ Ews t_strm (DOT deflate.code._opaque) op sp).
  sep_apply (field_at_field_at_ Ews t_strm (DOT deflate.code._data_type) dt sp).
  sep_apply (field_at_field_at_ Ews t_strm (DOT deflate.code._next_in) nin sp).
  sep_apply (field_at_field_at_ Ews t_strm (DOT deflate.code._total_in) tin sp).
  sep_apply (field_at_field_at_ Ews t_strm (DOT deflate.code._total_out) tout sp).
  sep_apply (field_at_field_at_ Ews t_strm (DOT deflate.code._msg) msgv sp).
  sep_apply (field_at_field_at_ Ews t_strm (DOT deflate.code._adler) adler sp).
  sep_apply (field_at_field_at_ Ews t_strm (DOT deflate.code._avail_in) (vi 0) sp).
  sep_apply (field_at_field_at_ Ews t_strm (DOT deflate.code._next_out) nullval sp).
  sep_apply (field_at_field_at_ Ews t_strm (DOT deflate.code._avail_out) (vi 0) sp).
  unfold_data_at (data_at_ _ _ sp). cancel.
  unfold field_at_. simpl. cancel.
Qed.

(* the OK case: the fields as MainKit.st_fields *)
Lemma pi_ok_fields (sp : val) (tin tout adler : Z) (msgv : val) :
  u64_ok tin -> u64_ok tout -> u64_ok adler ->
  field_at Ews t_strm (DOT deflate.code._next_in) nullval sp * reset_fields sp (vl tin) (vl tout) msgv (vl adler) *
  (field_at Ews t_strm (DOT deflate.code._avail_in) (vi 0) sp *
   field_at Ews t_strm (DOT deflate.code._next_out) nullval sp *
   field_at Ews t_strm (DOT deflate.code._avail_out) (vi 0) sp)
  |-- api_fields sp nullval 0 tin nullval 0 tout msgv adler.
Proof.
  intros. unfold api_fields, reset_fields. entailer!. unfold u32_ok; rep_lia.
Qed.

Lemma part_init {Espec : OracleKind} (Bpre : bpre_inv) (Brun : brun_inv) (gv : globals) (vs vh : val)
    (bs : bsetup) :
  ob_dstream_to_end -> bound_facts Bpre Brun ->
  (forall st, semax Delta_m (A2 Bpre Brun gv vs vh bs st) msuf37 POST_m) ->
  semax Delta_m (A1 gv vs vh bs) msuf34 POST_m.
Proof.
  intros HOB BF HK.
  unfold msuf34, A1.
  abbreviate_semax.
  Intros.
  unfold bs_locals; cbn [app].
  rewrite (pi_Tsh_split t_strm vs). Intros.
  forward_call (vs, Ews, Vundef, Vundef).
  Intros vret. destruct vret as [[[[tin tout] adler] dt] rsv]. cbn [fst snd] in *.
  pose proof H as BS.
  destruct H as (Hlev & Hwb & Hmem & Hstr & Hp & _).
  sep_apply (pi_defaults_split9 vs Vundef Vundef tin tout adler dt rsv).
  Intros.
  unfold version_at.
  pose proof (bf_init _ _ BF (b_level bs) (b_wbits bs) (b_mem bs) (b_strategy bs)) as FIN.
  forward_call (vs, b_level bs, 8, b_wbits bs, b_mem bs, b_strategy bs, gv vlit, Ers,
                [49; 46; 51; 46; 50; 0], 112, nullval, vl tin, vl tout, Vundef, vl adler, nullval, vi dt,
                Vundef, gv).
  { split; [unfold s32_ok; rep_lia|]. split; [unfold s32_ok; rep_lia|]. split; [list_solve|].
    split; [cbn; rep_lia|].
    intros a1 a2 a3 a4 a5. exact (proj1 (FIN a1 a2 a3 a4 a5 _ Hp)). }
  Intros vret. destruct vret as [[[[[a1 a2] a3] a4] a5] [[os z'] code]]. cbn [fst snd] in *.
  match goal with H : c_deflateInit2_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ |- _ => rename H into HI end.
  change (Znth 0 [49; 46; 51; 46; 50; 0] =? 49) with true in HI. change (112 =? 112) with true in HI.
  pose proof (proj2 (FIN a1 a2 a3 a4 a5 _ Hp) _ _ _ HI) as Hok. clear FIN.
  pose proof HI as HC. apply pi_init_code in HC.
  Intros msgv'.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx ((code = 0) :: P) (LOCALx Q (SEPx R))) end.
  { destruct HC as [-> | [-> Hc]]; [contradiction|].
    Intros st za zf op' dt'.
    sep_apply (pi_init_fail9 vs st za zf op' dt' gv nullval (rfv (code =? Z_OK) (z_total_in z') (vl tin))
                 (rfv (code =? Z_OK) (z_total_out z') (vl tout)) msgv' (rfv (code =? Z_OK) (z_adler z') (vl adler))).
    Intros.
    gather_SEP (data_at_ Ews t_strm vs) (data_at_ (Share.comp Ews) t_strm vs).
    rewrite <- pi_Tsh_split.
    forward.
    Exists (Int.repr 0). entailer!. }
  { eapply semax_pre; [| apply semax_skip]. apply pi_override_normal. entailer!.
    destruct HC as [-> | [_ [-> | ->]]]; [reflexivity | |];
      apply (f_equal Int.unsigned) in H5; vm_compute in H5; discriminate. }
  Intros. subst code.
  destruct (Hok eq_refl) as (s & -> & Hgz & HB). clear Hok HC.
  destruct (init_ok_strm _ _ _ _ _ _ _ _ _ _ _ _ _ HI) as (T1 & T2 & T3 & _).
  change (0 =? Z_OK) with true in *. change (0 =? Z_VERSION_ERROR) with false in *. unfold rfv.
  assert (U : u64_ok (z_total_in z') /\ u64_ok (z_total_out z') /\ u64_ok (z_adler z')).
  { rewrite T1, T2. unfold u64_ok. destruct T3 as [-> | ->]; rep_lia. }
  destruct U as (U1 & U2 & U3).
  sep_apply (pi_ok_fields vs (z_total_in z') (z_total_out z') (z_adler z') msgv' U1 U2 U3).
  eapply semax_pre;
    [| apply (HK (mkSt s (z_total_in z') (z_total_out z') (z_adler z') 0 0 (z_msg z') msgv'))].
  unfold A2, st_fields, srest, bs_locals. cbn [app st_s st_tin st_tout st_adler st_ain st_aout st_msg st_msgv].
  change (Zlib.proof.harness.bound_common.BoundKit.strm_pad vs) with (pi_strm_pad vs).
  entailer!.
Qed.
