(* Law res_bound, main: part_init (RBKit.v): new_stream(&strm), code = deflateInit2(...), if (code == Z_MEM_ERROR) return 0, gp_assert(code == Z_OK) (msuf 25 -> msuf 29). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.LawFactsW Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.deflate.Obligations.
Require Zlib.proof.harness.bound_common.BoundKit Zlib.proof.harness.deflate_bound.MainKit.
Require Zlib.proof.deflate.InitStrm.
Require Zlib.proof.harness.rj_deflate_params.RJPMain.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.res_bound.RBCS Zlib.proof.harness.res_bound.RBString Zlib.proof.harness.res_bound.RBKit.
Require Import Zlib.harness.res_bound.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

Module DC := Zlib.deflate.code.

(* The stream lemmas below are those of rj_deflate_params (RJPMain.v: the same local z_stream, new_stream and
   deflateInit2_ calls). *)

(* the local z_stream at the compress unit's compspecs (new_stream's) and at DCS.CS (deflateInit2_'s) *)
Lemma ri_strm_cs sh (v : @reptype Zlib.units.Compress.CS t_zs) (p : val) :
  @data_at Zlib.units.Compress.CS sh t_zs v p = @data_at DCS.CS sh t_strm v p.
Proof.
  apply equal_f. apply (@data_at_change_composite _ _ CC_compress_dcs); [apply JMeq_refl | reflexivity].
Qed.

(* the uninitialized Ews half of the local as new_stream's precondition *)
Lemma ri_strm_undef (p : val) :
  data_at_ Ews t_strm p |--
  @data_at Zlib.units.Compress.CS Ews t_zs
    (zs_val Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef) p.
Proof. rewrite ri_strm_cs. apply derives_refl. Qed.

(* new_stream's postcondition as deflateInit2__spec_v9's precondition pieces, the three fields the spec does not
   mention (avail_in, next_out, avail_out) and the padding *)
Lemma ri_new_stream_split (p : val) :
  @data_at Zlib.units.Compress.CS Ews t_zs
    (zs_val nullval (vi 0) Vundef nullval (vi 0) Vundef Vundef Vundef nullval nullval nullval Vundef Vundef Vundef) p
  |-- field_at Ews t_strm (DOT DC._next_in) nullval p * reset_fields p Vundef Vundef Vundef Vundef *
      (field_at Ews t_strm (DOT DC._avail_in) (vi 0) p * field_at Ews t_strm (DOT DC._next_out) nullval p *
       field_at Ews t_strm (DOT DC._avail_out) (vi 0) p) *
      field_at Ews t_strm (DOT DC._zalloc) nullval p * field_at Ews t_strm (DOT DC._zfree) nullval p *
      field_at Ews t_strm (DOT DC._opaque) nullval p * field_at Ews t_strm (DOT DC._data_type) Vundef p *
      field_at Ews t_strm (DOT DC._state) Vundef p * field_at_ Ews t_strm (DOT DC._reserved) p *
      BoundKit.strm_pad p.
Proof. exact (Zlib.proof.harness.rj_deflate_params.RJPMain.rjp_new_stream_split p). Qed.

(* the stream's fields, whatever their values, back to the whole uninitialized struct *)
Lemma ri_fields_back (p nin tin tout msgv adler ai no ao st za zf op dt : val) :
  field_at Ews t_strm (DOT DC._next_in) nin p * reset_fields p tin tout msgv adler *
  (field_at Ews t_strm (DOT DC._avail_in) ai p * field_at Ews t_strm (DOT DC._next_out) no p *
   field_at Ews t_strm (DOT DC._avail_out) ao p) *
  field_at Ews t_strm (DOT DC._state) st p * field_at Ews t_strm (DOT DC._zalloc) za p *
  field_at Ews t_strm (DOT DC._zfree) zf p * field_at Ews t_strm (DOT DC._opaque) op p *
  field_at Ews t_strm (DOT DC._data_type) dt p * field_at_ Ews t_strm (DOT DC._reserved) p *
  BoundKit.strm_pad p
  |-- data_at_ Ews t_strm p.
Proof. exact (Zlib.proof.harness.rj_deflate_params.RJPMain.rjp_fields_back p nin tin tout msgv adler ai no ao st za zf op dt). Qed.

(* deflateInit2__spec_v9's postcondition, whatever the outcome, back to the struct (the stream's allocations
   and the allocator's function pointers are dropped) *)
Lemma ri_init_back (os : option dstate) (code : Z) (p : val) (gv : globals) :
  ob_dstream_to_end ->
  forall nin tin tout msgv adler ai no ao : val,
  match os with
  | Some _ => dstream 2 os p nullval gv
  | None => EX st : val, EX za : val, EX zf : val, EX op' : val, EX dt' : val,
            !! (code = Z_VERSION_ERROR -> st = Vundef) &&
            (zfuncs gv * field_at_ Ews t_strm (DOT DC._reserved) p *
             field_at Ews t_strm (DOT DC._state) st p * field_at Ews t_strm (DOT DC._zalloc) za p *
             field_at Ews t_strm (DOT DC._zfree) zf p * field_at Ews t_strm (DOT DC._opaque) op' p *
             field_at Ews t_strm (DOT DC._data_type) dt' p)
  end *
  field_at Ews t_strm (DOT DC._next_in) nin p * reset_fields p tin tout msgv adler *
  (field_at Ews t_strm (DOT DC._avail_in) ai p * field_at Ews t_strm (DOT DC._next_out) no p *
   field_at Ews t_strm (DOT DC._avail_out) ao p) *
  BoundKit.strm_pad p
  |-- data_at_ Ews t_strm p * TT.
Proof. exact (Zlib.proof.harness.rj_deflate_params.RJPMain.rjp_init_back os code p gv). Qed.

(* the OK case: the caller's fields as MainKit.st_fields *)
Lemma ri_ok_fields (sp : val) (tin tout adler : Z) (msgv : val) :
  u64_ok tin -> u64_ok tout -> u64_ok adler ->
  field_at Ews t_strm (DOT DC._next_in) nullval sp * reset_fields sp (vl tin) (vl tout) msgv (vl adler) *
  (field_at Ews t_strm (DOT DC._avail_in) (vi 0) sp *
   field_at Ews t_strm (DOT DC._next_out) nullval sp *
   field_at Ews t_strm (DOT DC._avail_out) (vi 0) sp)
  |-- api_fields sp nullval 0 tin nullval 0 tout msgv adler.
Proof.
  intros. unfold api_fields, reset_fields. entailer!. unfold u32_ok; rep_lia.
Qed.

(* the empty else branch of an [if] whose postcondition is given *)
Lemma ri_override_normal Delta (P Q : environ -> mpred) (R : ret_assert) :
  ENTAIL Delta, P |-- Q -> ENTAIL Delta, P |-- RA_normal (overridePost Q R).
Proof. intros H. destruct R. exact H. Qed.

Lemma part_init : part_init_stmt.
Proof.
  intros Espec Bpre Brun I Iend gv vh vs rs hv BF AF TE HK.
  unfold msuf25, A2.
  abbreviate_semax.
  Intros.
  unfold rs_locals; cbn [app].
  rewrite (BoundKit.data_at__Tsh_split t_strm vs).
  Intros.
  sep_apply (ri_strm_undef vs).
  forward_call (vs, Ews, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef, Vundef).
  sep_apply (ri_new_stream_split vs).
  unfold version_at.
  pose proof H as RS. destruct H as (S1 & S2 & S3 & S4 & _).
  assert (S8 : s32 8) by (unfold s32; rep_lia).
  pose proof (fun a1 a2 a3 a4 a5 => af_init _ _ AF (r_level rs) 8 (r_wbits rs) (r_mem rs) (r_strategy rs)
                a1 a2 a3 a4 a5 zrst0 S1 S8 S2 S3 S4) as FIN.
  forward_call (vs, r_level rs, 8, r_wbits rs, r_mem rs, r_strategy rs, gv vlit, Ers, [49; 46; 51; 46; 50; 0],
                112, nullval, Vundef, Vundef, Vundef, Vundef, nullval, Vundef, Vundef, gv).
  { cancel. }
  { split; [list_solve|]. split; [cbn; rep_lia|].
    intros a1 a2 a3 a4 a5. exact (proj1 (FIN a1 a2 a3 a4 a5)). }
  Intros vret. destruct vret as [[[[[a1 a2] a3] a4] a5] [[os z'] code]]. cbn [fst snd] in *.
  match goal with H : c_deflateInit2_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ |- _ => rename H into HI end.
  change (Znth 0 [49; 46; 51; 46; 50; 0] =? 49) with true in HI. change (112 =? 112) with true in HI.
  destruct (proj2 (FIN a1 a2 a3 a4 a5) _ _ _ HI) as (Hc & Hse & Hok). clear FIN.
  Intros msgv'.
  (* the parameters are in zlib.h's ranges (gp_assume(deflate_params_ok(...))): deflateInit2_ returns Z_OK or
     Z_MEM_ERROR, never Z_STREAM_ERROR *)
  assert (Hp : params_ok (r_level rs) 8 (r_wbits rs) (r_mem rs) (r_strategy rs) = true)
    by (unfold rs_ok in RS; tauto).
  assert (Hc2 : code = 0 \/ code = -4).
  { destruct Hc as [E | [E | E]]; [left; exact E | | right; exact E].
    apply Hse in E. congruence. }
  (* if (code == Z_MEM_ERROR) return 0 *)
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx ((code = 0) :: P) (LOCALx Q (SEPx R))) end.
  { (* out of memory: the stream's memory back to the local's *)
    sep_apply (ri_init_back os code vs gv TE).
    gather_SEP 0 5. replace_SEP 0 (data_at_ Tsh t_strm vs * TT).
    { entailer!. rewrite (BoundKit.data_at__Tsh_split t_strm vs). cancel. }
    forward.
    Exists (Int.repr 0). apply andp_right; [apply prop_right; reflexivity|].
    sep_apply (data_at_data_at_ Tsh t_gzh (hval rs hv) vh). cancel. }
  { eapply semax_pre; [| apply semax_skip]. apply ri_override_normal. entailer!.
    destruct Hc2 as [-> | ->]; [reflexivity | contradiction]. }
  Intros. subst code.
  (* gp_assert(code == Z_OK) *)
  forward_call Int.one.
  destruct (Hok eq_refl) as (s & -> & Hgz & HI0). clear Hok.
  destruct (proj2 (bw_init _ _ BF (r_level rs) (r_wbits rs) (r_mem rs) (r_strategy rs) a1 a2 a3 a4 a5 zrst0 Hp)
              _ _ _ HI eq_refl) as (s' & Es & _ & HB).
  injection Es as <-.
  destruct (Zlib.proof.deflate.InitStrm.init_ok_strm _ _ _ _ _ _ _ _ _ _ _ _ _ HI) as (T1 & T2 & T3 & _).
  change (0 =? Z_OK) with true in *. change (0 =? Z_VERSION_ERROR) with false in *. unfold rfv.
  assert (U : u64_ok (z_total_in z') /\ u64_ok (z_total_out z') /\ u64_ok (z_adler z')).
  { rewrite T1, T2. unfold u64_ok. destruct T3 as [-> | ->]; rep_lia. }
  destruct U as (U1 & U2 & U3).
  sep_apply (ri_ok_fields vs (z_total_in z') (z_total_out z') (z_adler z') msgv' U1 U2 U3).
  eapply semax_pre;
    [| apply (HK (MainKit.mkSt s (z_total_in z') (z_total_out z') (z_adler z') 0 0 (z_msg z') msgv'))].
  unfold A3, MainKit.st_fields, srest, rs_locals.
  cbn [app MainKit.st_s MainKit.st_tin MainKit.st_tout MainKit.st_adler MainKit.st_ain MainKit.st_aout
       MainKit.st_msg MainKit.st_msgv].
  entailer!.
Qed.
