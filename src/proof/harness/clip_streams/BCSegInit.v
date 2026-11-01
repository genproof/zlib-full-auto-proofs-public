(* Law rj_bad_checksum, main: statements 11-12 (new_stream(&compressor), deflateInit2(&compressor, level, Z_DEFLATED,
   window_bits, mem_level, strategy) and `return 0` unless Z_OK) (bc_A11 -> bc_A13, DFacts.cd_init). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.DSpec9.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.DFacts.
Require Import Zlib.proof.harness.clip_streams.MainDefs.
Require Import Zlib.proof.harness.clip_streams.BCKit.
Require Import Zlib.proof.harness.clip_streams.BCMem.
Require Zlib.proof.deflate.DSpec9 Zlib.proof.deflate.GlobalsInit Zlib.proof.deflate.InitStrm.
Require Zlib.proof.harness.deflate_bound.MainInit.
Require Zlib.proof.roundtrip.RTBTheory Zlib.proof.huffman.Lemmas.
Require Import Zlib.harness.rj_bad_checksum.code.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

Ltac simplify_remove_localdef_temp ::= bc_rlt.

(* the local z_stream before new_stream(): new_stream's precondition at the compress unit's compspecs *)
Lemma bc_strm_undef sh q :
  @data_at_ CS.CS sh t_zsl q =
  @data_at Zlib.units.Compress.CS sh t_zs
    (zs_val Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef) q.
Proof.
  unfold data_at_. change t_zs with t_zsl. symmetry. apply equal_f.
  apply (@data_at_change_composite _ _ CC_compress); [apply JMeq_refl | reflexivity].
Qed.

(* the 14 members of struct z_stream *)
Definition bc_tuple : Type :=
  (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * val)))))))))))))%type.

Lemma bc_strm_cs_c sh (v : bc_tuple) q :
  @data_at Zlib.units.Compress.CS sh t_zsl v q = @data_at CS.CS sh t_zsl v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_compress); [apply JMeq_refl | reflexivity]. Qed.

Lemma bc_strm_cs_d sh (v : bc_tuple) q :
  @data_at Zlib.proof.deflate.DCS.CS sh t_zsl v q = @data_at CS.CS sh t_zsl v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity]. Qed.

(* the struct after new_stream(), at the deflate API's compspecs *)
Lemma bc_ns_dcs sh q :
  @data_at Zlib.units.Compress.CS sh t_zs
    (zs_val nullval (Vint (Int.repr 0)) Vundef nullval (Vint (Int.repr 0)) Vundef Vundef Vundef nullval nullval
       nullval Vundef Vundef Vundef) q =
  @data_at Zlib.proof.deflate.DCS.CS sh t_strm
    (nullval, (vi 0, (Vundef, (nullval, (vi 0, (Vundef, (Vundef, (Vundef,
     (nullval, (nullval, (nullval, (Vundef, (Vundef, Vundef))))))))))))) q.
Proof.
  change t_zs with t_zsl. change t_strm with t_zsl. unfold zs_val.
  rewrite (bc_strm_cs_c sh (nullval, (Vint (Int.repr 0), (Vundef, (nullval, (Vint (Int.repr 0), (Vundef, (Vundef,
     (Vundef, (nullval, (nullval, (nullval, (Vundef, (Vundef, Vundef)))))))))))))).
  rewrite (bc_strm_cs_d sh (nullval, (vi 0, (Vundef, (nullval, (vi 0, (Vundef, (Vundef, (Vundef,
     (nullval, (nullval, (nullval, (Vundef, (Vundef, Vundef)))))))))))))).
  reflexivity.
Qed.

(* new_stream's Ews half as deflateInit2__spec_v9's precondition pieces, the three fields the spec does not
   mention, and the padding *)
Lemma bc_ns_split (sp : val) :
  @data_at Zlib.proof.deflate.DCS.CS Ews t_strm
    (nullval, (vi 0, (Vundef, (nullval, (vi 0, (Vundef, (Vundef, (Vundef,
     (nullval, (nullval, (nullval, (Vundef, (Vundef, Vundef))))))))))))) sp
  |-- @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_in) nullval sp *
      Zlib.proof.deflate.DSpec9.reset_fields sp Vundef Vundef Vundef Vundef *
      (@field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_in) (vi 0) sp *
       @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_out) nullval sp *
       @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_out) (vi 0) sp) *
      @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT Zlib.deflate.code._zalloc) nullval sp *
      @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT Zlib.deflate.code._zfree) nullval sp *
      @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT Zlib.deflate.code._opaque) nullval sp *
      @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT Zlib.deflate.code._data_type) Vundef sp *
      @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT Zlib.deflate.code._state) Vundef sp *
      @field_at_ Zlib.proof.deflate.DCS.CS Ews t_strm (DOT Zlib.deflate.code._reserved) sp * BoundKit.strm_pad sp.
Proof.
  unfold Zlib.proof.deflate.DSpec9.reset_fields, BoundKit.strm_pad; simpl.
  unfold_data_at (@data_at Zlib.proof.deflate.DCS.CS _ _ _ sp). entailer!.
Qed.


(* the two halves of the local compressor back to its memory *)
Lemma bc_join q :
  @data_at_ Zlib.proof.deflate.DCS.CS Ews t_strm q * @data_at_ CS.CS (Share.comp Ews) t_zsl q
  |-- data_at_ Tsh t_zsl q.
Proof.
  rewrite bc_strm_data_at__cs. rewrite <- (data_at__share_join Ews (Share.comp Ews) Tsh) by apply join_comp_Tsh.
  cancel.
Qed.

Lemma seg_init_ok : seg_init_stmt.
Proof.
  intros Espec J0 J gv vc vd n D dp op level wbits mem strategy C chp DF K.
  unfold bc_seg11, bc_A11, POST_B, POST_bc. abbreviate_semax.
  Intros.
  destruct H as (Hn & HD & HB & Pdp & Pop & Hl & Hw & Hm & Hs).
  rewrite bc_strm_undef.
  forward_call (vc, Tsh, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef).
  rewrite bc_ns_dcs.
  sep_apply (BoundKit.data_at_Tsh_split (cs := Zlib.proof.deflate.DCS.CS) t_strm
    (nullval, (vi 0, (Vundef, (nullval, (vi 0, (Vundef, (Vundef, (Vundef,
     (nullval, (nullval, (nullval, (Vundef, (Vundef, Vundef))))))))))))) vc).
  rewrite bc_strm_data_at__cs.
  sep_apply (bc_ns_split vc).
  unfold R_bc, R_of. Intros.
  unfold GlobalsInit.version_at.
  unfold lit_rt.
  forward_call (vc, level, 8, wbits, mem, strategy, gv ___stringlit_rj_bad_checksum_1, Ers,
                [49; 46; 51; 46; 50; 0], 112, nullval, Vundef, Vundef, Vundef, Vundef, nullval, Vundef, Vundef, gv).
  { unfold s32_ok. split; [rep_lia|]. split; [rep_lia|]. split; [list_solve|]. split; [cbn; rep_lia|].
    intros a1 a2 a3 a4 a5. exact (proj1 (cd_init _ _ DF level wbits mem strategy a1 a2 a3 a4 a5 Hl Hw Hm Hs)). }
  Intros vret. destruct vret as [[[[[a1 a2] a3] a4] a5] [[os z'] code]]. cbn [fst snd] in *.
  match goal with H : c_deflateInit2_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ |- _ => rename H into HI end.
  change (Znth 0 [49; 46; 51; 46; 50; 0] =? 49) with true in HI. change (112 =? 112) with true in HI.
  pose proof (proj2 (cd_init _ _ DF level wbits mem strategy a1 a2 a3 a4 a5 Hl Hw Hm Hs) _ _ _ HI) as Hok.
  pose proof HI as HC. apply MainInit.pi_init_code in HC.
  Intros msgv'.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx ((code = 0) :: P) (LOCALx Q (SEPx R))) end.
  { destruct HC as [-> | [-> Hc]]; [contradiction|].
    Intros st za zf op' dt'.
    change (BoundKit.strm_pad vc) with (MainInit.pi_strm_pad vc).
    sep_apply (MainInit.pi_init_fail9 vc st za zf op' dt' gv nullval
                 (DSpec9.rfv (code =? Z_OK) (z_total_in z') Vundef) (DSpec9.rfv (code =? Z_OK) (z_total_out z') Vundef)
                 msgv' (DSpec9.rfv (code =? Z_OK) (z_adler z') Vundef)).
    sep_apply (bc_join vc).
    ret0. }
  { forward. entailer!.
    destruct HC as [-> | [_ [-> | ->]]]; [reflexivity | |];
      match goal with Hx : Int.repr _ = _ |- _ => apply (f_equal Int.unsigned) in Hx; vm_compute in Hx; discriminate end. }
  Intros. subst code.
  destruct (Hok eq_refl) as (s & -> & HJ0).
  destruct Zlib.proof.huffman.Lemmas.huffman_lemmas as [Hov Hbb].
  destruct (Zlib.proof.roundtrip.RTBTheory.rt_b_facts Hov Hbb) as [Hinit _].
  destruct (Hinit level 8 wbits mem strategy a1 a2 a3 a4 a5 dz0 Hl ltac:(unfold rs32; lia) Hw Hm Hs) as [_ Hcodes].
  destruct (Hcodes _ _ _ HI) as (_ & _ & Hg). destruct (Hg eq_refl) as (s0 & E0 & Hgz).
  inversion E0; subst s0.
  destruct (InitStrm.init_ok_strm _ _ _ _ _ _ _ _ _ _ _ _ _ HI) as (T1 & T2 & T3 & _).
  change (0 =? Z_OK) with true in *. change (0 =? Z_VERSION_ERROR) with false in *. unfold DSpec9.rfv.
  assert (U : u64_ok (z_total_in z') /\ u64_ok (z_total_out z') /\ u64_ok (z_adler z')).
  { rewrite T1, T2. unfold u64_ok. destruct T3 as [-> | ->]; rep_lia. }
  destruct U as (U1 & U2 & U3).
  sep_apply (MainInit.pi_ok_fields vc (z_total_in z') (z_total_out z') (z_adler z') msgv' U1 U2 U3).
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply (K s (z_total_in z') (z_total_out z') (z_adler z') (z_msg z') msgv') ].
  unfold bc_A13, bc_srest, R_bc, R_of, lit_rt.
  change (MainInit.pi_strm_pad vc) with (BoundKit.strm_pad vc).
  assert (HB' : is_bytes D) by exact HB.
  entailer!.
Qed.
