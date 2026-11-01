(* Law rj_bad_block, main: statements 24-28 (new_stream, inflateInit2_ and its check, next_in, next_out, flush)
   (BBWSetKit.bbs_set3_stmt): inflateInit2_ on main's raw stream (any failure returns 0; it can only be Z_MEM_ERROR),
   the stores of next_in and next_out into the struct, then the loop's invariant (BBWKit.bbw_inv) at pos = 0,
   ob = [] with the theory's invariant from BBWDefs.bbw_init. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5 Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.bit_writer.BWSpec.
Require Import Zlib.proof.harness.bit_writer.BBWDefs.
Require Import Zlib.proof.harness.bit_writer.BWLawCS Zlib.proof.harness.bit_writer.BWGlobals.
Require Import Zlib.proof.harness.bit_writer.BBWKit.
Require Import Zlib.proof.harness.bit_writer.BBWHelp.
Require Import Zlib.proof.harness.bit_writer.BBWSetKit.

Lemma bbs_set3 : bbs_set3_stmt.
Proof.
  intros Espec J gv vs vbt vbit w kind which lits S0 room stream out HJ K.
  unfold bbs_A2, bbw_seg24, POST_B, bbw_POST. abbreviate_semax.
  Intros.
  unfold R_bb, bw_R. Intros.
  make_func_ptr Zlib.inflate.code._zcalloc. make_func_ptr Zlib.inflate.code._zcfree.
  gather_SEP (func_ptr' _ (gv Zlib.inflate.code._zcalloc)) (func_ptr' _ (gv Zlib.inflate.code._zcfree)).
  fold (zfuncs gv).
  (* new_stream(&strm) *)
  rewrite bb_strm_undef.
  forward_call (vs, Tsh, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef, Vundef).
  (* if (inflateInit2(&strm, window_bits) != Z_OK) return 0; *)
  unfold bw_hversion_at. rewrite <- bb_chars_i.
  assert_PROP (isptr (gv BBC.___stringlit_rj_bad_block_1)) as Pver by entailer!.
  assert_PROP (isptr vs) as Pstrm by entailer!.
  forward_call (gv, Tsh, vs,
                RF nullval (Vint (Int.repr 0)) Vundef nullval (Vint (Int.repr 0)) Vundef Vundef Vundef Vundef,
                Vundef, Vundef, nullval, w, gv BBC.___stringlit_rj_bad_block_1, Ers,
                map (fun c : Z => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0], 49, 112).
  { rewrite if_false by (destruct vs; try contradiction; discriminate). rewrite bb_raw_zs. cancel. }
  { repeat split; auto; change (Zlength _) with 6; rep_lia. }
  Intros vret. destruct vret as [aok sp]. simpl fst in *; simpl snd in *.
  rewrite bb_init_ret by auto.
  destruct aok.
  2: { forward_if False.
       { sep_apply (bb_init_fail_mem gv vs
           (RF nullval (Vint (Int.repr 0)) Vundef nullval (Vint (Int.repr 0)) Vundef Vundef Vundef Vundef)
           Vundef Vundef nullval Z_MEM_ERROR sp w Pstrm ltac:(discriminate)).
         forward. Exists (Int.repr 0). entailer!. }
       { bb_infeas. } }
  forward_if True; [bb_infeas | forward; entailer! | ].
  rewrite bb_init_ok by auto.
  destruct (bb_init_facts sp w H) as [_ [Hwr [Hmd Hhd]]].
  set (L := init_live sp w) in *.
  unfold istream_raw. Intros.
  assert (HL: live_ok L) by (repeat match goal with H: _ /\ _ |- _ => destruct H end; assumption).
  rewrite bb_raw_zs. unfold raw_after_init. rewrite Hwr.
  cbn [rf_ni rf_ai rf_tin rf_no rf_ao rf_tout rf_dt rf_adler rf_res Z.eqb].
  rewrite bb_zs_c.
  (* strm.next_in = stream; strm.next_out = out; *)
  forward. forward.
  unfold zs_val. cbn [fst snd].
  (* flush = (int) nondet_u32() *)
  forward_call tt. Intros u.
  set (flush := Int.signed (Int.repr u)).
  assert (Hfl: Int.min_signed <= flush <= Int.max_signed) by apply Int.signed_range.
  assert (Eu: Int.repr u = Int.repr flush) by (unfold flush; rewrite Int.repr_signed; auto).
  rewrite Eu. clearbody flush. clear Eu.
  (* the loop from its invariant at pos = 0, ob = [] *)
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply (K flush); unfold bbw_args; tauto].
  unfold bbw_inv.
  change (data_at_ Ews (tarray tuchar room) out) with (data_at Ews (tarray tuchar room) (Zrepeat Vundef room) out).
  Exists 0 (@nil Z) (bb_z stream 0 out 0) L (Zrepeat Vundef room).
  match goal with |- context [data_at Tsh (Tstruct BBC._z_stream_s noattr) ?v vs] =>
    change v with (zs_val stream (Vint (Int.repr 0)) (Vlong (Int64.repr 0)) out (Vint (Int.repr 0))
                     (Vlong (Int64.repr 0)) nullval (l_sp L) (gv Zlib.inflate.code._zcalloc)
                     (gv Zlib.inflate.code._zcfree) nullval (Vint (Int.repr 0)) Vundef Vundef) end.
  rewrite <- bb_zs_c.
  sep_apply (bb_offer_istream gv vs L stream 0 out 0 HL Hwr ltac:(rep_lia) ltac:(rep_lia)).
  assert (HJ0: J S0 kind which lits 0 [] (l_s L)) by (apply (bbw_init J HJ); auto).
  assert (Hsw: swfW (l_s L)) by (unfold swfW; rewrite Hmd; split; intros E; compute in E; discriminate).
  pose proof (Zlength_nonneg lits).
  entailer!.
  rewrite Zlength_nil. lia.
Qed.
