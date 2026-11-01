(* Law rt_session (harness/rt_session.c), main without a header: statements 70-72 (asked = 0,
   decompressor.next_in = input, decompressor.next_out = out), the end of SMKit.segC, from the decompressor
   inflateInit2_ (and, with a raw dictionary, inflateSetDictionary) left, to the inflate loop's invariant II_W at
   position 0 with nothing produced.  The stream's other fields [z] are whatever the calls left them. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SDFacts.
Require Import Zlib.proof.harness.rt_session.SIFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.proof.harness.rt_session.SMCWKit.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

(* statements 70-72 of main's body *)
Definition scw_tail : statement := ltac:(let x := eval cbv beta iota zeta delta [suf segC] in (suf 7 segC) in exact x).

(* the stream's fields with next_in = ni and next_out = no *)
Definition scw_zio (z : zfields) (ni no : val) : zfields :=
  ZF ni (zf_ai z) (zf_tin z) no (zf_ao z) (zf_tout z) (zf_msg z) (zf_dt z) (zf_adler z) (zf_res z).

Lemma scw_tail_ok {Espec : OracleKind} P gv vh vg vc va vd u O c src ip z L :
  su_ok u -> with_head u = false -> sc_ok (scase_of u) (su_data u) O -> Zlength O <= su_cap u -> rbytes O ->
  src_ok O src -> isptr ip ->
  P (scase_of u) (su_data u) O src 0 [] false L (zf_tout z) -> swfW (l_s L) -> i_head (l_s L) = false ->
  semax Delta_s
    (PROPx []
     (LOCALx (temp _compressed_len (vl (Zlength O)) :: temp _after (vl (Zlength src - Zlength O)) ::
              temp _input ip :: c_locals u ++ d_locals u (rts_iw (su_wbits u)) ++ lvs gv vh vg vc va vd)
     (SEPx [istreamA gv Tsh vd z Vundef (Some L);
            @data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength scw_hv)) scw_hv (gv ___stringlit_rt_session_1);
            version_lit gv; mem_mgr gv; zfuncs gv; cstream gv vc (ghp vh u) c;
            Zlib.proof.deflate.DSpec.deflate_globals gv; Zlib.proof.inflate.Rep.tables_rep Ers gv;
            dobj u; cobj u O; oobj u []; data_at_ Tsh t_p va; iobj src ip; hobj vh u; graw vg u; dictobj u;
            dcopy u])))
    scw_tail
    (normal_ret_assert (EX l : ils, II_W gv vh vg vc va vd P u O c src ip l)).
Proof.
  intros Hu NH Hsc HO HbO Hsrc Pip HP SW NHd.
  unfold scw_tail, II_W, c_locals, d_locals, lvs, lv_locals. cbn [app]. abbreviate_semax.
  unfold istreamA at 1, zstrm_atA. Intros. rewrite scw_cs_inflate.
  forward.
  forward.
  forward.
  pose proof Hu as [_ (_ & _ & _ & _ & _ & _ & Pop & _)].
  Exists (mkIL 0 [] false L (scw_zio z ip (su_op u))).
  cbn [il_pos il_out il_asked il_L il_z Z.b2z].
  assert (IL : il_ok P u O src ip (mkIL 0 [] false L (scw_zio z ip (su_op u)))).
  { unfold il_ok, scw_zio; cbn [il_pos il_out il_asked il_L il_z zf_tout zf_ni zf_no].
    rewrite Zlength_nil, !isptr_offset_val_zero by auto.
    pose proof (Zlength_nonneg O). destruct Hsrc as (Hs & _).
    split; [exact HP | split; [exact SW | split; [lia | split; [exists (su_data u); reflexivity | auto]]]]. }
  replace (head_opt (Some L)) with emp by (unfold head_opt, head_mem; rewrite NHd; reflexivity).
  unfold istreamA, zstrm_atA. rewrite <- scw_cs_inflate. unfold Rm. rewrite <- scw_version.
  unfold scw_zio; cbn [zf_ni zf_ai zf_tin zf_no zf_ao zf_tout zf_msg zf_dt zf_adler zf_res].
  entailer!.
Qed.
