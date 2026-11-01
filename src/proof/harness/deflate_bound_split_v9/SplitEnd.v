(* Law deflate_bound_split, main: deflateEnd(&s); return 0; (statements 43, 44) (SplitKit.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.harness.x_deflate_bound_split.code.
Require Import Zlib.proof.harness.deflate_bound_split_v9.SplitMain Zlib.proof.harness.deflate_bound_split_v9.SplitKit.
Require Import Zlib.proof.harness.deflate_bound_split_v9.SplitAf.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

(* the stream's memory before deflateEnd: what its precondition needs, and the rest *)
Lemma pe_live_end (sp hp : val) (gv : globals) (bs : bsetup) (s : dstate) (f : sfields) :
  Obligations.ob_dstream_to_end ->
  live sp hp gv bs true s f
  |-- dstream_end (Some s) sp gv *
      (sf_at sp f * strm_pad sp * data_at_ Ecomp t_strm sp * hdr_at (Some s) (ghp_of hp bs true) (hx_of bs) *
       hmem hp bs true).
Proof.
  intros TE. unfold live.
  eapply derives_trans; [| apply derives_refl].
  rewrite !sepcon_assoc. apply sepcon_derives; [apply TE | cancel].
Qed.

(* the header's memory back to the local h *)
Lemma pe_hdr (hp : val) (bs : bsetup) (s : dstate) :
  d_gzhead s = (if hset bs then Some (hdr_of bs) else None) ->
  hdr_at (Some s) (ghp_of hp bs true) (hx_of bs) * hmem hp bs true |-- data_at_ Tsh t_gzh hp * TT.
Proof.
  intros Hg. unfold hdr_at, ghp_of, hmem, hx_of. cbn [andb]. rewrite Hg.
  destruct (hset bs).
  - sep_apply (gzh_at_back (hdr_of bs) hp
      (if bd_xsel (bs_d bs) =? 0 then nullval else bd_xfp (bs_d bs))
      (if bd_nsel (bs_d bs) =? 0 then nullval else bd_nfp (bs_d bs))
      (if bd_csel (bs_d bs) =? 0 then nullval else bd_cfp (bs_d bs))).
    rewrite (data_at__Tsh_split t_gzh hp). cancel.
  - Intros. cancel.
Qed.

(* the stream's memory after deflateEnd, whatever it returned, back to the local s *)
Lemma pe_strm (o : option dstate) (sp : val) (gv : globals) (s : dstate) (f : sfields) :
  match o with None => dstream 2 None sp nullval gv | Some _ => dstream_end (Some s) sp gv end *
  sf_at sp f * strm_pad sp * data_at_ Ecomp t_strm sp
  |-- data_at_ Tsh t_strm sp * TT.
Proof.
  unfold sf_at. rewrite (data_at__Tsh_split t_strm sp).
  destruct o.
  - sep_apply (dstream_end_data_at_ (Some s) sp gv (sf_nin f) (sf_ain f) (sf_tin f) (sf_nout f) (sf_aout f)
      (sf_tout f) (sf_msgv f) (sf_adler f)). cancel.
  - sep_apply (dstream_none_data_at_ sp nullval gv (sf_nin f) (sf_ain f) (sf_tin f) (sf_nout f) (sf_aout f)
      (sf_tout f) (sf_msgv f) (sf_adler f)). cancel.
Qed.

Lemma part_end {Espec : OracleKind} sp hp vosn gv bs s f :
  semax Delta_m (E sp hp vosn gv bs s f) msuf43 Rm_ret.
Proof.
  unfold msuf43, E.
  abbreviate_semax.
  Intros.
  sep_apply (pe_live_end sp hp gv bs s f H0).
  assert (Hend : exists r, DModel3.c_deflateEnd s (zmk [] 0 0 0 0 0 0 None) = Some r)
    by (unfold DModel3.c_deflateEnd; destruct (bad_state s); eauto).
  destruct Hend as [r Hend].
  Intros.
  rewrite (sf_split sp f). Intros.
  forward_call (Some s, sp, sf_nin f, zmk [] 0 0 0 0 0 0 None, r, gv).
  sep_apply (af_join sp (sf_nin f) (sf_ain f) (sf_tin f) (sf_nout f) (sf_aout f) (sf_tout f) (sf_msgv f) (sf_adler f)).
  fold (sf_at sp f).
  sep_apply (pe_strm (fst (fst r)) sp gv s f).
  sep_apply (pe_hdr hp bs s H1).
  forward.
  Exists (Int.repr 0). entailer!.
Qed.
