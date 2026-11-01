(* Law api_reset, main: the whole body from the for-loop's body (obody_stmt): windowBits, new_stream() on
   both streams, inflateInit2_(&used, w) (ARFacts.af_init, af_init_swf; every outcome but Z_OK returns), the
   for-loop over phase (invariant ARMainKit.oinv, exit obrk) and return 0. *)
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

(* a branch that cannot be taken *)
Ltac top_infeas := exfalso; first [ match goal with H: ?a <> ?b |- _ => solve [apply H; reflexivity] end
                              | match goal with H: _ |- _ => solve [discriminate H] end
                              | contradiction
                              | match goal with H: Int.repr _ = Int.repr _ |- _ =>
                                  apply repr_inj_signed in H; [lia | rep_lia | rep_lia] end
                              | lia ].

(* stream fresh at the for-loop's exit (phase 2) given back to the stack frame *)
Lemma fresh_mem2_frame gv vb zb Lb: fresh_mem gv 2 vb zb Lb |-- @data_at_ CS Tsh t_z vb * TT.
Proof. unfold fresh_mem. simpl. apply a_frame. Qed.

Lemma main_of : obody_stmt -> ar_main_stmt.
Proof.
  intros OB J0 J1 AF.
  start_function.
  unfold R_ar, R_of. Intros.
  make_func_ptr Zlib.inflate.code._zcalloc. make_func_ptr Zlib.inflate.code._zcfree.
  gather_SEP (func_ptr' _ (gv inflate.code._zcalloc)) (func_ptr' _ (gv inflate.code._zcfree)).
  fold (zfuncs gv).
  forward_call tt. Intros wb.
  assert (Ew: Int.repr wb = Int.repr (Int.signed (Int.repr wb))) by (rewrite Int.repr_signed; auto).
  rewrite Ew. clear Ew. set (w := Int.signed (Int.repr wb)).
  assert (Hw: Int.min_signed <= w <= Int.max_signed) by apply Int.signed_range. clearbody w.
  change (data_at_ Tsh (Tstruct _z_stream_s noattr) v_used) with (data_at_ Tsh t_z v_used).
  change (data_at_ Tsh (Tstruct _z_stream_s noattr) v_fresh) with (data_at_ Tsh t_z v_fresh).
  rewrite (strm_undef Tsh v_used), (strm_undef Tsh v_fresh).
  forward_call (v_used, Tsh, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef, Vundef).
  forward_call (v_fresh, Tsh, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef, Vundef).
  (* both streams are now the raw struct of zf_new *)
  pose proof (fresh_raw_c v_used zf_new) as Eu. pose proof (fresh_raw_c v_fresh zf_new) as Ef.
  unfold zf_new in Eu, Ef. cbn [zf_ni zf_ai zf_no zf_ao] in Eu, Ef. fold zf_new in Eu, Ef.
  rewrite <- Eu, <- Ef. clear Eu Ef.
  assert_PROP (isptr v_used) as Pa by (unfold fresh_raw; entailer!).
  assert_PROP (isptr v_fresh) as Pb by (unfold fresh_raw; entailer!).
  rewrite (fresh_raw_i gv v_used zf_new).
  (* the version literal at inflate's compspecs (replace_SEP: a `rewrite hversion` on the whole semax goal
     takes minutes) *)
  replace_SEP 7 (@data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength hv_list)) hv_list
    (gv ___stringlit_api_reset_1)).
  { go_lower. rewrite hversion. apply derives_refl. }
  assert_PROP (isptr (gv ___stringlit_api_reset_1)) as Pver by entailer!.
  forward_call (gv, Tsh, v_used, fr_raw zf_new, Vundef, Vundef, nullval, w, gv ___stringlit_api_reset_1, Ers,
                hv_list, 49, 112).
  { rewrite if_false by (intro; subst; contradiction). cancel. }
  { change (Zlength hv_list) with 6; repeat split; auto; rep_lia. }
  Intros vret. destruct vret as [alloc_ok sp]. simpl fst in *; simpl snd in *.
  assert (Hret: init_ret v_used 49 112 w alloc_ok =
                if alloc_ok then (if wbits_ok w then Z_OK else Z_STREAM_ERROR) else Z_MEM_ERROR).
  { unfold init_ret. simpl. rewrite if_false by (intro; subst; contradiction). destruct alloc_ok; reflexivity. }
  rewrite Hret. clear Hret.
  destruct alloc_ok; [destruct (wbits_ok w) eqn:WB | ];
    unfold init_mem; rewrite if_false by (intro; subst; contradiction); simpl Z.eqb; cbv iota.
  2,3: forward_if; [forward; Exists (Int.repr 0); sep_apply raw_frame; sep_apply fresh_frame; entailer! | top_infeas].
  forward_if. { top_infeas. }
  Intros.
  replace_SEP 1 (hversion_at ___stringlit_api_reset_1 gv).
  { go_lower. rewrite hversion. apply derives_refl. }
  set (L0 := init_live sp w) in *.
  assert_PROP (live_ok L0) as HL0 by (unfold istream_raw; entailer!).
  set (adl0 := if w <? 0 then 0 else Z.land (i_wrap (l_s L0)) 1).
  assert (Hr0: raw_live (Some L0) = (w <? 0)) by (apply init_raw; auto).
  assert (Ha0: 0 <= adl0 <= Int64.max_unsigned).
  { unfold adl0. destruct (w <? 0); [rep_lia | pose proof (land1_range (i_wrap (l_s L0))); rep_lia]. }
  assert (Hw0: raw_live (Some L0) = false -> adl0 = Z.land (i_wrap (l_s L0)) 1).
  { intros X. rewrite Hr0 in X. unfold adl0. rewrite X. reflexivity. }
  assert (Zn: zf_ok zf_new) by (unfold zf_ok, zf_new; simpl; rep_lia).
  sep_apply (fresh_init gv v_used zf_new adl0 L0 Zn Ha0 Hw0).
  assert (I0: forall src, bytes_ok src -> J0 w src 0 (zf_init zf_new adl0) L0).
  { intros src Hs. apply (af_init _ _ AF); auto.
    unfold zf_ok, zf_init, zf_new; simpl; rep_lia. }
  forward_loop (oinv J0 J1 gv v_used v_fresh w)
    continue: (ocont J0 J1 gv v_used v_fresh w)
    break: (obrk J0 J1 gv v_used v_fresh w).
  { forward. unfold oinv. Exists 0 (zf_init zf_new adl0) L0 zf_new L0.
    unfold oinv_at, ostate, fresh_mem. simpl (0 =? 0). cbv iota.
    entailer!. apply (af_init_swf _ _ AF); auto. }
  { unfold oinv. Intros ph za La zb Lb. unfold oinv_at. Intros.
    forward_if.
    { (* phase < 2: the body, by obody_stmt *)
      unfold abbreviate in POSTCONDITION, MORE_COMMANDS. subst POSTCONDITION MORE_COMMANDS.
      eapply semax_pre; [ | apply (OB Espec J0 J1 gv v_used v_fresh w ph za La zb Lb AF WB Hw Pa Pb ltac:(lia)) ].
      unfold oinv_at. entailer!. }
    { (* phase = 2: break *)
      forward. unfold obrk. Exists za La zb Lb.
      assert (ph = 2) by lia. subst ph. unfold oinv_at. entailer!. } }
  { (* the increment *)
    unfold ocont. Intros ph za La zb Lb. unfold oinv_at. Intros.
    forward. unfold oinv. Exists (ph + 1) za La zb Lb. unfold oinv_at. entailer!. }
  (* after the loop: return 0 *)
  unfold obrk. Intros za La zb Lb. unfold oinv_at. Intros.
  forward. Exists (Int.repr 0).
  sep_apply (a_frame gv v_used). sep_apply (fresh_mem2_frame gv v_fresh). entailer!.
Qed.
