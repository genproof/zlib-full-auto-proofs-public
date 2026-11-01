(* Law res_bound, main: part_bound (RBKit.v): bound = deflateBound(&strm, data_len), gp_assume(bound <= UINT_MAX), compressed = malloc(bound) and its NULL test (msuf 31 -> msuf 35). *)
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
Require Import Zlib.harness.res_bound.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

(* deflateBound takes strm->next_in separately: the caller's z_stream fields without it *)
Definition af_rest (sp : val) (ain tin : Z) (nout : val) (aout tout : Z) (msgv : val) (adler : Z) : mpred :=
  !! (u32_ok ain /\ u64_ok tin /\ u32_ok aout /\ u64_ok tout /\ u64_ok adler) &&
  (@field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_in) (vi ain) sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._total_in) (vl tin) sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_out) nout sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_out) (vi aout) sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._total_out) (vl tout) sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._msg) msgv sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._adler) (vl adler) sp).

Lemma af_split (sp nin : val) (ain tin : Z) (nout : val) (aout tout : Z) (msgv : val) (adler : Z) :
  api_fields sp nin ain tin nout aout tout msgv adler =
  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_in) nin sp * af_rest sp ain tin nout aout tout msgv adler.
Proof.
  unfold api_fields, af_rest. apply pred_ext; entailer!.
Qed.

Lemma af_join (sp nin : val) (ain tin : Z) (nout : val) (aout tout : Z) (msgv : val) (adler : Z) :
  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_in) nin sp * af_rest sp ain tin nout aout tout msgv adler
  |-- api_fields sp nin ain tin nout aout tout msgv adler.
Proof. rewrite af_split. apply derives_refl. Qed.

(* the end of a branch that falls through to the statement after the if *)
Lemma bd_override_normal Delta (P Q : environ -> mpred) (R : ret_assert) :
  ENTAIL Delta, P |-- Q -> ENTAIL Delta, P |-- RA_normal (overridePost Q R).
Proof. intros H. destruct R. exact H. Qed.

(* the return of main after deflateBound: the stream and the header's memory give back main's locals *)
Lemma bnd_ret_close (gv : globals) (vs vh ghp : val) (s : dstate) (hx : share * val * val * val) (Hr : mpred)
    (nin : val) (ain tin : Z) (nout : val) (aout tout : Z) (msgv : val) (adler : Z) :
  ob_dstream_to_end -> hclose vh s ghp hx Hr ->
  dstream 2 (Some s) vs ghp gv * hdr_at (Some s) ghp hx * api_fields vs nin ain tin nout aout tout msgv adler *
  data_at_ (Share.comp Ews) t_strm vs * Hr * BoundKit.strm_pad vs
  |-- data_at_ Tsh t_strm vs * data_at_ Tsh t_gzh vh * TT.
Proof.
  intros HOB HC.
  sep_apply (BoundKit.dstream_data_at_ (Some s) vs ghp gv nin ain tin nout aout tout msgv adler HOB).
  sep_apply (HC s eq_refl).
  rewrite (BoundKit.data_at__Tsh_split t_strm vs). unfold BoundKit.Ecomp. cancel.
Qed.

Lemma part_bound : part_bound_stmt.
Proof.
  intros Espec Bpre Brun gv vh vs rs st ghp hx Hr BF OA HOB HK.
  unfold msuf31, A5.
  abbreviate_semax.
  Intros.
  unfold rs_locals; cbn [app].
  assert (Hn : 0 <= r_n rs <= 4294967295) by (destruct H as (_ & _ & _ & _ & Hn & _); exact Hn).
  (* total_out is 0 after deflateInit2 and deflateSetDictionary / deflateSetHeader *)
  pose proof (proj1 OA _ _ _ _ _ _ _ _ _ H0) as Hto.
  destruct (bw_bound _ _ BF _ _ _ _ _ _ _ _ _ (r_n rs) H0 Hn) as (b & Hb & Hbr & HBr).
  unfold st_fields. rewrite af_split.
  forward_call (Some (st_s st), vs, nullval, ghp, hx, r_n rs, b, gv).
  all: try (cancel; fail). all: try (unfold u64_ok; rep_lia; fail).
  sep_apply (af_join vs nullval (MainKit.st_ain st) (st_tin st) nullval (MainKit.st_aout st) (st_tout st)
               (st_msgv st) (st_adler st)).
  fold (st_fields vs st).
  forward_call (Int.repr (if b <=? 4294967295 then 1 else 0)).
  { entailer!. simpl. unfold Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
    destruct (zlt _ _), (Z.leb_spec b 4294967295); first [reflexivity | lia]. }
  assert (Hb32 : b <= 4294967295) by (destruct (Z.leb_spec b 4294967295); [lia | exfalso; auto]).
  forward_call (tarray tuchar b, gv).
  { simpl; rewrite Z.max_r by lia; rep_lia. }
  Intros obp.
  destruct (eq_dec obp nullval) as [Pob | Pob].
  - subst obp. forward_if False.
    + forward. Exists (Int.repr 0). unfold st_fields, srest. entailer!.
      sep_apply (bnd_ret_close gv vs vh ghp (st_s st) hx Hr nullval (MainKit.st_ain st) (st_tin st) nullval
                   (MainKit.st_aout st) (st_tout st) (st_msgv st) (st_adler st) HOB H2).
      cancel.
    + exfalso. congruence.
  - Intros. forward_if True.
    + exfalso. auto.
    + forward. apply bd_override_normal. entailer!.
    + eapply semax_pre; [| apply (HK b obp)].
      unfold A6. entailer!.
Qed.
