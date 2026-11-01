(* Laws rfc_level0_size and rfc_level0_blocks (data of any length, given to deflate() in whole-block pieces): the
   pieces of main's proof that do not depend on the harness's Clight (both mains are the same up to the end of
   the deflate loop).  Everything at DCS.CS (deflate.c + trees.c), the
   compspecs of main's body.
   - the moves of laws_common.h's specifications to DCS.CS: the byte objects of any_bytes (adler32 unit's
     compspecs) and the z_stream of new_stream / offer (compress unit's compspecs);
   - the local z_stream strm: new_stream's precondition, the live state's own z_stream fields out of
     dstream_sp (and back, by a wand);
   - deflateInit2_'s model: it always has a result, and its code is Z_OK, Z_STREAM_ERROR or Z_MEM_ERROR;
   - the harness's blocks / head_len / trailer_len / size as Level0Defs' l0_blocks / l0_hlen / l0_tlen /
     l0_size. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.LawFacts.
Require Zlib.proof.deflate.LTBInit Zlib.proof.deflate.LTCInitKit Zlib.proof.deflate.ApiKit.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.units.Adler32 Zlib.units.Compress.
Require Import Zlib.proof.deflate.Level0Defs.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.
Module DC := Zlib.deflate.code.

(** ** The compspecs of laws_common.h's specifications, moved to DCS.CS *)
#[export] Instance CC_adler32_dcs : change_composite_env Zlib.units.Adler32.CS DCS.CS.
  make_cs_preserve Zlib.units.Adler32.CS DCS.CS. Defined.
#[export] Instance CC_compress_dcs : change_composite_env Zlib.units.Compress.CS DCS.CS.
  make_cs_preserve Zlib.units.Compress.CS DCS.CS. Defined.

(* any_bytes' object *)
Lemma l0_bytes_cs sh n (l : list val) (p : val) :
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) l p = @data_at DCS.CS sh (tarray tuchar n) l p.
Proof.
  apply equal_f. apply (@data_at_change_composite _ _ CC_adler32_dcs); [apply JMeq_refl | reflexivity].
Qed.

Lemma l0_token_cs sh n (p : val) :
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) p = @malloc_token DCS.CS sh (tarray tuchar n) p.
Proof.
  apply equal_f. apply (@malloc_token_change_composite _ _ CC_adler32_dcs). reflexivity.
Qed.

Lemma l0_bytes_rep (bs : list Z) : bytes_rep bs = map vi bs.
Proof. reflexivity. Qed.

Lemma l0_is_bytes (bs : list Z) : is_bytes bs -> bytes bs.
Proof.
  intros H. unfold is_bytes, bytes in *. eapply Forall_impl; [| exact H]. cbv beta. intros. rep_lia.
Qed.

(* the z_stream of new_stream and offer *)
Lemma l0_strm_cs sh (v : @reptype Zlib.units.Compress.CS t_zs) (p : val) :
  @data_at Zlib.units.Compress.CS sh t_zs v p = @data_at DCS.CS sh t_strm v p.
Proof.
  apply equal_f. apply (@data_at_change_composite _ _ CC_compress_dcs); [apply JMeq_refl | reflexivity].
Qed.

(** ** The local z_stream *)

(* the uninitialized local (its Ews part) as new_stream's precondition *)
Lemma l0_strm_undef (p : val) :
  data_at_ Ews t_strm p |--
  @data_at Zlib.units.Compress.CS Ews t_zs
    (zs_val Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef) p.
Proof. rewrite l0_strm_cs. apply derives_refl. Qed.

(* The six fields of the z_stream that a live stream's dstream_sp holds: state, zalloc, zfree, opaque,
   data_type (inside the deflate_state's representation) and reserved. *)
Definition strm_own (p sp za zf op dt : val) : mpred :=
  field_at Ews t_strm (DOT DC._state) sp p * field_at Ews t_strm (DOT DC._zalloc) za p *
  field_at Ews t_strm (DOT DC._zfree) zf p * field_at Ews t_strm (DOT DC._opaque) op p *
  field_at Ews t_strm (DOT DC._data_type) dt p * field_at_ Ews t_strm (DOT DC._reserved) p.

Definition l0_dt (s : dstate) : val := vi (tr_data_type (fst (d_trm s))).

Definition strm_own_live (p sp : val) (gv : globals) (s : dstate) : mpred :=
  strm_own p sp (gv DC._zcalloc) (gv DC._zcfree) nullval (l0_dt s).

(* The z_stream fields of a live stream out of dstream_sp, the rest kept as a wand (offer writes the whole
   struct, the fields come back unchanged). *)
Lemma l0_dstream_open (s : dstate) (p ghp sp : val) (gv : globals) :
  dstream_sp 2 (Some s) p ghp sp gv |--
  strm_own_live p sp gv s * (strm_own_live p sp gv s -* dstream_sp 2 (Some s) p ghp sp gv).
Proof.
  unfold dstream_sp at 1. Intros pp. rewrite ApiKit.dstate_at'_2.
  unfold dstate_at, trees_at, dtype_at. Intros.
  unfold strm_own_live, strm_own, l0_dt. subst.
  cancel.
  rewrite <- wand_sepcon_adjoint.
  unfold dstream_sp. Exists pp. rewrite ApiKit.dstate_at'_2.
  unfold dstate_at, trees_at, dtype_at. entailer!.
Qed.

Lemma l0_dstream_close (s : dstate) (p ghp sp : val) (gv : globals) :
  strm_own_live p sp gv s * (strm_own_live p sp gv s -* dstream_sp 2 (Some s) p ghp sp gv)
  |-- dstream_sp 2 (Some s) p ghp sp gv.
Proof. apply modus_ponens_wand. Qed.

(** ** deflateInit2_'s model *)
Lemma l0_init_total level method wbits mem strategy a1 a2 a3 a4 a5 z :
  exists r, c_deflateInit2_ true true false level method wbits mem strategy a1 a2 a3 a4 a5 z = Some r.
Proof.
  rewrite LTBInit.bi_shape.
  destruct (params_ok level method wbits mem strategy) eqn:P; [| eauto].
  destruct a1; [| eauto]. destruct (a2 && a3 && a4 && a5)%bool; [| eauto].
  rewrite (LTCInitKit.init_eq _ _ _ _ _ _ P). eauto.
Qed.

Lemma l0_init_code level method wbits mem strategy a1 a2 a3 a4 a5 z os z' code :
  c_deflateInit2_ true true false level method wbits mem strategy a1 a2 a3 a4 a5 z = Some (os, z', code) ->
  code = Z_OK \/ code = Z_STREAM_ERROR \/ code = Z_MEM_ERROR.
Proof.
  rewrite LTBInit.bi_shape. intros H.
  destruct (params_ok level method wbits mem strategy) eqn:P; [| injection H as _ _ <-; auto].
  destruct a1; [| injection H as _ _ <-; auto].
  destruct (a2 && a3 && a4 && a5)%bool; [| injection H as _ _ <-; auto].
  rewrite (LTCInitKit.init_eq _ _ _ _ _ _ P) in H. injection H as _ _ <-; auto.
Qed.

(** ** The harness's arithmetic *)
Lemma l0_blocks_eq n : 0 <= n -> l0_blocks n = if 0 <? n then (n + 65534) / 65535 else 1.
Proof.
  intros. unfold l0_blocks. destruct (Z.eqb_spec n 0), (Z.ltb_spec 0 n); auto; lia.
Qed.

(* data_len <= PTRDIFF_MAX: at most ceil((2^63 - 1) / 65535) blocks *)
Lemma l0_blocks_range n : 0 <= n <= 9223372036854775807 -> 1 <= l0_blocks n <= 140739635871745.
Proof.
  intros. split; [apply l0_blocks_pos; lia|]. unfold l0_blocks. destruct (Z.eqb_spec n 0); [lia|].
  assert ((n + 65534) / 65535 < 140739635871746) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

(* the two ifs of main on window_bits *)
Lemma l0_hlen_zlib w : 0 <= w <= 15 -> l0_hlen w = 2 /\ l0_tlen w = 4.
Proof. intros. unfold l0_hlen, l0_tlen. destruct (Z.ltb_spec w 0), (Z.gtb_spec w 15); lia. Qed.

Lemma l0_hlen_gzip w : 15 < w -> l0_hlen w = 10 /\ l0_tlen w = 8.
Proof. intros. unfold l0_hlen, l0_tlen. destruct (Z.ltb_spec w 0), (Z.gtb_spec w 15); lia. Qed.

Lemma l0_hlen_raw w : w < 0 -> l0_hlen w = 0 /\ l0_tlen w = 0.
Proof. intros. unfold l0_hlen, l0_tlen. destruct (Z.ltb_spec w 0), (Z.gtb_spec w 15); lia. Qed.

(* size = head_len + 5 * blocks + data_len + trailer_len does not wrap: below SIZE_MAX *)
Lemma l0_size_range w n : 0 <= n <= 9223372036854775807 -> 5 <= l0_size w n <= 9224075735034134550.
Proof.
  intros. pose proof (l0_blocks_range n H). unfold l0_size, l0_hlen, l0_tlen.
  destruct (w <? 0), (w >? 15); lia.
Qed.

(* malloc's object as deflate's output space *)
Lemma l0_data_at_ (b : Z) (p : val) :
  0 <= b ->
  data_at_ Ews (tarray tuchar b) p =
  data_at Ews (tarray tuchar (Zlength (Zrepeat Vundef b))) (Zrepeat Vundef b) p.
Proof. intros. rewrite Zlength_Zrepeat by lia. reflexivity. Qed.

(* deflate_spec's api_fields from its eight fields (after main read one of them) *)
Lemma l0_api_fold (sp ni : val) (ai ti : Z) (no : val) (ao to : Z) (m : val) (ad : Z) :
  u32_ok ai -> u64_ok ti -> u32_ok ao -> u64_ok to -> u64_ok ad ->
  field_at Ews t_strm (DOT DC._next_in) ni sp * field_at Ews t_strm (DOT DC._avail_in) (vi ai) sp *
  field_at Ews t_strm (DOT DC._total_in) (vl ti) sp * field_at Ews t_strm (DOT DC._next_out) no sp *
  field_at Ews t_strm (DOT DC._avail_out) (vi ao) sp * field_at Ews t_strm (DOT DC._total_out) (vl to) sp *
  field_at Ews t_strm (DOT DC._msg) m sp * field_at Ews t_strm (DOT DC._adler) (vl ad) sp
  |-- api_fields sp ni ai ti no ao to m ad.
Proof. intros. unfold api_fields. entailer!. Qed.
