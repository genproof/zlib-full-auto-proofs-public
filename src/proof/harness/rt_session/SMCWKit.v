(* Law rt_session (harness/rt_session.c), main's statements 63-72 (SMKit.segC) without a header: the facts on the
   decompressor and the compressor at the law's compspecs that SMSegCW.sm_segC_W uses (rt_stream's USegC.v at
   this law's compspecs SCS.CS): the struct after new_stream() as inflateInit2_'s raw stream, the harness's
   ZLIB_VERSION literal, the struct given back at a return, the decompressor after inflateInit2_ as an istreamA,
   and the stores asked = 0, next_in = input, next_out = out (statements 70-72). *)
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
Require Zlib.proof.deflate.Obligations.
Require Zlib.proof.deflate.Api_toend.
Require Zlib.proof.deflate.GlobalsInit.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SDFacts.
Require Import Zlib.proof.harness.rt_session.SIFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

(** ** The compressor *)

(* the compressor, whatever its state, gives back the local's memory (at a return) *)
Lemma scw_comp_back (gv : globals) (vc ghp : val) (c : cst) : cstream gv vc ghp c |-- data_at_ Tsh t_z vc * TT.
Proof.
  unfold cstream, srest.
  sep_apply (BoundKit.dstream_data_at_ (Some (cs_s c)) vc ghp gv (cs_ni c) (cs_ain c) (cs_tin c) (cs_no c)
               (cs_aout c) (cs_tout c) (cs_msgv c) (cs_adler c) Api_toend.dstream_to_end).
  rewrite (@data_at__change_composite Zlib.proof.deflate.DCS.CS CS CC_dcs Ews Zlib.proof.deflate.Rep.t_strm)
    by reflexivity.
  rewrite (BoundKit.data_at__Tsh_split t_z vc). cancel.
Qed.

(** ** The decompressor at the compspecs of its users *)

(* laws_common's new_stream sees it at the compress unit's compspecs, inflate.c at Inflate.CS, main at the
   law's *)
Lemma scw_cs_compress sh (v : @reptype Zlib.units.Compress.CS t_zs) (p : val) :
  @data_at Zlib.units.Compress.CS sh t_zs v p = @data_at CS sh t_z v p.
Proof. apply equal_f. apply (@data_at_change_composite _ _ CC_compress); [apply JMeq_refl | reflexivity]. Qed.

Lemma scw_cs_inflate sh (v : @reptype Zlib.units.Inflate.CS Zlib.proof.inflate.Rep.t_strm) (p : val) :
  @data_at Zlib.units.Inflate.CS sh Zlib.proof.inflate.Rep.t_strm v p = @data_at CS sh t_z v p.
Proof. apply equal_f. apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.

(* the uninitialized local as new_stream's precondition *)
Lemma scw_undef (p : val) :
  data_at_ Tsh t_z p =
  @data_at Zlib.units.Compress.CS Tsh t_zs
    (zs_val Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef) p.
Proof. unfold data_at_. rewrite scw_cs_compress. reflexivity. Qed.

(* the struct after new_stream(): inflateInit2_'s raw stream *)
Definition scw_ns : rawf :=
  RF nullval (Vint (Int.repr 0)) Vundef nullval (Vint (Int.repr 0)) Vundef Vundef Vundef Vundef.

Lemma scw_ns_raw gv p :
  @data_at Zlib.units.Compress.CS Tsh t_zs
    (zs_val nullval (Vint (Int.repr 0)) Vundef nullval (Vint (Int.repr 0)) Vundef Vundef Vundef nullval nullval
       nullval Vundef Vundef Vundef) p =
  raw_strm gv Tsh p scw_ns Vundef Vundef nullval nullval nullval.
Proof. unfold raw_strm, scw_ns, zs_val; simpl. rewrite scw_cs_compress, scw_cs_inflate. reflexivity. Qed.

(* the harness's "1.3.2" (main's resources Rm) as inflateInit2_ takes it *)
Definition scw_hv : list val := map (fun c => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0].

Lemma scw_version gv :
  Zlib.proof.deflate.GlobalsInit.version_at gv ___stringlit_rt_session_1 =
  @data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength scw_hv)) scw_hv (gv ___stringlit_rt_session_1).
Proof.
  unfold Zlib.proof.deflate.GlobalsInit.version_at, scw_hv. change (Zlength _) with 6.
  transitivity (@data_at CS Ers (tarray tschar 6) (map vi [49; 46; 51; 46; 50; 0]) (gv ___stringlit_rt_session_1)).
  - apply equal_f; apply (@data_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity].
  - symmetry. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity].
Qed.

(* inflateInit2_ failed: the struct goes back to the stack frame *)
Lemma scw_init_fail gv p r ret sp w :
  isptr p -> ret <> Z_OK ->
  init_mem gv Tsh p r Vundef Vundef nullval ret sp w |-- data_at_ Tsh t_z p.
Proof.
  intros Pp Nok. unfold init_mem. rewrite if_false by (intro; subst; contradiction).
  apply Z.eqb_neq in Nok. rewrite Nok.
  destruct (ret =? Z_VERSION_ERROR); [ | destruct (ret =? Z_MEM_ERROR)];
  unfold raw_strm; rewrite scw_cs_inflate; apply data_at_data_at_.
Qed.

(* a live decompressor gives back the local's memory (at a return) *)
Lemma scw_dec_back gv vd z av L : istreamA gv Tsh vd z av (Some L) |-- data_at_ Tsh t_z vd * TT.
Proof.
  unfold istreamA, zstrm_atA. Intros. rewrite scw_cs_inflate.
  sep_apply (data_at_data_at_ Tsh t_z). cancel.
Qed.

(** ** The decompressor after inflateInit2_ returned Z_OK *)

(* its fields: next_in = ni, next_out = no (new_stream's NULLs, then input and out), avail_in/avail_out 0
   (new_stream), totals 0, msg NULL, data_type 0, adler = wrap & 1 for a wrapped stream (a raw stream keeps its
   undefined member) *)
Definition scw_z (ni no : val) (L : live) : zfields :=
  ZF ni 0 0 no 0 0 None 0 (if i_wrap (l_s L) =? 0 then 0 else Z.land (i_wrap (l_s L)) 1) Vundef.

Lemma scw_land1_range x : 0 <= Z.land x 1 <= 1.
Proof.
  change (Z.land x 1) with (Z.land x (Z.ones 1)). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound x (2 ^ 1) ltac:(reflexivity)). simpl in *. lia.
Qed.

(* the stream inflateInit2_ returned (Spec5.istream_raw) as SpecW's istreamA *)
Lemma scw_raw_istreamA gv vd L :
  istream_raw gv Tsh vd (raw_after_init scw_ns (l_s L)) L
  |-- istreamA gv Tsh vd (scw_z nullval nullval L) Vundef (Some L).
Proof.
  unfold istream_raw, raw_strm, istreamA, zstrm_atA, scw_z, adler_v, raw_live, raw_after_init, scw_ns.
  Intros. pose proof (scw_land1_range (i_wrap (l_s L))).
  destruct (i_wrap (l_s L) =? 0); simpl; entailer!; unfold zf_ok; simpl; rep_lia.
Qed.

(* the stores of next_in and next_out, on the struct at the law's compspecs *)
Lemma scw_istreamA_unfold gv vd ni no L :
  istreamA gv Tsh vd (scw_z ni no L) Vundef (Some L) =
  !! live_ok L &&
  (@data_at CS Tsh t_z
    (ni, (Vint (Int.repr 0), (Vlong (Int64.repr 0), (no, (Vint (Int.repr 0), (Vlong (Int64.repr 0),
     (nullval, (l_sp L, (gv Zlib.inflate.code._zcalloc, (gv Zlib.inflate.code._zcfree, (nullval,
     (Vint (Int.repr 0), (if i_wrap (l_s L) =? 0 then Vundef else Vlong (Int64.repr (Z.land (i_wrap (l_s L)) 1)),
      Vundef))))))))))))) vd * state_mem gv vd L).
Proof.
  unfold istreamA, zstrm_atA, scw_z, adler_v, raw_live. rewrite scw_cs_inflate.
  pose proof (scw_land1_range (i_wrap (l_s L))).
  apply pred_ext.
  - Intros. destruct (i_wrap (l_s L) =? 0); simpl; entailer!.
  - Intros. destruct (i_wrap (l_s L) =? 0); simpl; entailer!; unfold zf_ok; simpl; rep_lia.
Qed.

Lemma scw_head_init sp w : head_opt (Some (init_live sp w)) = emp.
Proof.
  unfold head_opt, head_mem, init_live, init_s. destruct (reset2_wb w) as [[wr wb] | ]; reflexivity.
Qed.

(* window_bits after `if (window_bits == 8) window_bits = 9;` *)
Lemma scw_iw_8 w : rs32 w -> Int.repr w = Int.repr 8 -> vi 9 = vi (rts_iw w).
Proof.
  intros Hw E. apply repr_inj_signed in E; [ | unfold rs32 in Hw; rep_lia | rep_lia]. subst. reflexivity.
Qed.

Lemma scw_iw_n8 w : Int.repr w <> Int.repr 8 -> vi w = vi (rts_iw w).
Proof.
  intros N. unfold rts_iw. destruct (w =? 8) eqn:E; [apply Z.eqb_eq in E; subst; contradiction | reflexivity].
Qed.

(** ** inflateSetDictionary of the dictionary's copy *)

(* the copy's bytes and malloc token as inflate.c sees them *)
Lemma scw_bytes_i sh n (v : list val) q :
  @data_at Zlib.units.Inflate.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.

Lemma scw_tok_i sh n q :
  @malloc_token Zlib.units.Inflate.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_inflate). reflexivity. Qed.

Lemma scw_istreamA_opt_ptr gv shs (vs : val) z av st :
  isptr vs -> istreamA_opt gv shs vs z av st = istreamA gv shs vs z av st.
Proof. intros Pv. unfold istreamA_opt. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma scw_is_live_ptr (vs : val) st : isptr vs -> is_live vs st = st.
Proof. intros Pv. unfold is_live. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

(* a precondition whose spatial part implies another one's, with the same PROP (none) and LOCAL *)
Lemma scw_sep_pre {Espec : OracleKind} Delta Q (R R' : list mpred) c Post :
  fold_right_sepcon R |-- fold_right_sepcon R' ->
  semax Delta (PROPx [] (LOCALx Q (SEPx R'))) c Post ->
  semax Delta (PROPx [] (LOCALx Q (SEPx R))) c Post.
Proof.
  intros HR HS. eapply semax_pre; [ | exact HS].
  apply andp_left2. unfold PROPx, LOCALx, SEPx.
  apply andp_derives; [apply derives_refl | apply andp_derives; [apply derives_refl | intro rho; apply HR]].
Qed.
