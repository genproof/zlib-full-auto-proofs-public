(* Law api_reset, main: after the do-while of phase 0 (ARMainKit.seg_rst): inflateReset(&used), asserted to
   return Z_OK, and inflateInit2_(&fresh, w) (ARFacts.af_reset, af_init_swf), to the for-loop's continue point. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_reset.ARMainDefs Zlib.proof.harness.api_reset.ARMainKit.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.harness.api_reset.code.

Lemma rst_proof : rst_stmt.
Proof.
  intros E J0 J1 gv va vb w inp src pos za La zb Lb G.
  pose proof G as G'. destruct G' as (AF & Wok & Wr & Hsl & Hsb & Pinp & Pva & Pvb).
  unfold dinv_at, seg_rst, Delta_m, POST_m. simplify_func_tycontext. abbreviate_semax.
  Intros. destruct H as (SWa & RWa & HJ). change (0 =? 0) with true in HJ. cbv iota in HJ.
  destruct HJ as (HJ & ZOKb). unfold fresh_mem. change (0 =? 0) with true. cbv iota.
  assert_PROP (zf_ok za /\ live_ok La) as ZL by (rewrite istreamA_unfold; entailer!). destruct ZL as [ZOK LOK].
  destruct (af_reset _ _ AF w src pos za La HJ LOK ZOK) as (R0 & LOK2 & SW2 & HJ1).
  (* inflateReset(&used) returns Z_OK (af_reset); gp_assert holds *)
  forward_call (gv, Tsh, va, za, Vundef, La). rewrite R0. forward_call (Int.repr 1).
  assert_PROP (zf_ok (snd3 (reset_f za La))) as ZOK2 by (rewrite istreamA_unfold; entailer!).
  assert_PROP (isptr (gv ___stringlit_api_reset_1)) as Pver by (unfold hversion_at; entailer!).
  (* inflateInit2_(&fresh, w, "1.3.2", sizeof(z_stream)): Z_OK exactly when the allocation succeeds *)
  rewrite (fresh_raw_i gv vb zb), (hversion gv).
  forward_call (gv, Tsh, vb, fr_raw zb, Vundef, Vundef, nullval, w, gv ___stringlit_api_reset_1, Ers, hv_list, 49, 112).
  { rewrite if_false by (intro X; subst; contradiction). cancel. }
  { unfold hv_list. simpl. rewrite !Zlength_cons, Zlength_nil. rep_lia. }
  Intros vret. destruct vret as [aok sp]. cbn [fst snd] in *.
  assert (IR: init_ret vb 49 112 w aok = if aok then Z_OK else Z_MEM_ERROR).
  { unfold init_ret. rewrite if_false by (intro X; subst; contradiction). rewrite Wok. destruct aok; reflexivity. }
  rewrite IR. unfold init_mem. rewrite if_false by (intro X; subst; contradiction).
  destruct aok.
  - change (Z_OK =? Z_VERSION_ERROR) with false. change (Z_OK =? Z_MEM_ERROR) with false.
    change (Z_OK =? Z_OK) with true. cbv iota.
    forward_if.
    { discriminate. }
    forward.
    assert_PROP (live_ok (init_live sp w)) as LOKb by (unfold istream_raw; entailer!).
    assert (Psp: isptr sp) by auto.
    (* fresh's model adler: inflateInit2_'s value for windowBits >= 0, used's for a raw stream *)
    set (adl := if w <? 0 then zf_adler (snd3 (reset_f za La)) else Z.land (i_wrap (l_s (init_live sp w))) 1).
    assert (Ha: 0 <= adl <= Int64.max_unsigned).
    { unfold adl. destruct (w <? 0).
      - destruct ZOK2 as (_ & _ & _ & _ & _ & A). exact A.
      - pose proof (land1_range (i_wrap (l_s (init_live sp w)))). rep_lia. }
    assert (Hr: raw_live (Some (init_live sp w)) = false -> adl = Z.land (i_wrap (l_s (init_live sp w))) 1).
    { rewrite init_raw by exact Wok. intros X. unfold adl. rewrite X. reflexivity. }
    sep_apply (fresh_init gv vb zb adl (init_live sp w) ZOKb Ha Hr).
    assert (ZOKi: zf_ok (zf_init zb adl)) by (unfold zf_ok, zf_init in *; simpl; rep_lia).
    assert (HJb: forall src', bytes_ok src' ->
      J1 w src' 0 (snd3 (reset_f za La)) (thd3 (reset_f za La)) (zf_init zb adl) (init_live sp w)).
    { intros src' Hb. apply HJ1; auto.
      - intros X. unfold zf_init, adl. cbn [zf_adler]. destruct (Z.ltb_spec w 0); [reflexivity | lia].
      - intros X. unfold zf_init, adl. cbn [zf_adler]. destruct (Z.ltb_spec w 0); [lia | reflexivity]. }
    assert (OS: ostate J0 J1 w 1 (snd3 (reset_f za La)) (thd3 (reset_f za La)) (zf_init zb adl) (init_live sp w)).
    { unfold ostate. change (1 =? 0) with false. change (1 =? 1) with true. cbv iota.
      refine (conj HJb (conj SW2 (conj (af_init_swf _ _ AF w sp Wok) (conj _ _)))).
      - rewrite reset_raw. exact RWa.
      - apply init_raw. exact Wok. }
    (* the for-loop's continue point: phase 1 is next, both streams live *)
    unfold ocont, oinv_at. Exists 0 (snd3 (reset_f za La)) (thd3 (reset_f za La)) (zf_init zb adl) (init_live sp w).
    change (0 + 1) with 1. unfold fresh_mem. change (1 =? 0) with false. cbv iota.
    clearbody adl. clear HJ1 HJb.
    change (@data_at CS Ers (tarray tschar (Zlength hv_list)) hv_list (gv ___stringlit_api_reset_1))
      with (@hversion_at CS ___stringlit_api_reset_1 gv).
    go_lower.
    apply andp_right; [apply prop_right; rewrite !eqb_type_refl; refine (conj _ (conj OS _)); [lia | repeat split] | ].
    generalize (istreamA gv Tsh vb (zf_init zb adl) Vundef (Some (init_live sp w))); intro.
    generalize (istreamA gv Tsh va (snd3 (reset_f za La)) Vundef (Some (thd3 (reset_f za La)))); intro.
    generalize (@hversion_at CS ___stringlit_api_reset_1 gv); generalize (version_lit gv); intros.
    cancel.
  - (* the allocation failed: `return 0`, both structs back to the stack frame *)
    change (Z_MEM_ERROR =? Z_VERSION_ERROR) with false. change (Z_MEM_ERROR =? Z_MEM_ERROR) with true. cbv iota.
    forward_if.
    2: { discriminate. }
    forward. Exists (Int.repr 0).
    sep_apply (raw_frame gv Tsh vb (fr_raw zb) nullval Vundef (gv Zlib.inflate.code._zcalloc)
                 (gv Zlib.inflate.code._zcfree) nullval).
    sep_apply (a_frame gv va (snd3 (reset_f za La)) Vundef (thd3 (reset_f za La))).
    entailer!.
Qed.
