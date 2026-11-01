(* Law api_counters, main: harness/api_counters.c proved against MainLib.main_core_spec R_cnt (Globals.v) for ANY invariant P
   with the facts of Facts.v (pieces_facts P), on the kit MainKit.v; the checks of
   api_counters.c: after each inflate() call, avail_in/avail_out never grow, next_in/next_out moved on by exactly the bytes consumed/produced, total_in/total_out are the sums (read, written). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5 Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.inflate_pieces.LawCS.
Require Import Zlib.proof.harness.inflate_pieces.Globals.
Require Import Zlib.proof.harness.inflate_pieces.Facts.
Require Import Zlib.proof.harness.inflate_pieces.MainKit.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.harness.api_counters.code.
Require Import Zlib.proof.harness.inflate_pieces.MainCntLoop.

#[local] Existing Instance Cnt.CS.
#[local] Existing Instances Cnt.CC_inflate Cnt.CC_adler32 Cnt.CC_crc32 Cnt.CC_zutil Cnt.CC_inffast Cnt.CC_inftrees
  Cnt.CC_compress.
Import CntK.

Definition Gk_cnt := @Gk_of Cnt.CS [].

Lemma body_cnt P : pieces_facts P ->
  @semax_body (QPvarspecs Cnt.p) Gk_cnt Cnt.CS f_main (_main, main_core_spec R_cnt).
Proof.
  intros PF.
  start_function.
  unfold R_cnt, R_of. Intros.
  make_func_ptr Zlib.inflate.code._zcalloc. make_func_ptr Zlib.inflate.code._zcfree.
  gather_SEP (func_ptr' _ (gv inflate.code._zcalloc)) (func_ptr' _ (gv inflate.code._zcfree)).
  fold (zfuncs gv).
  forward_call tt. Intros wb.
  forward_call (9223372036854775807). Intros len.
  apply -> seq_assoc. apply -> seq_assoc.
  forward_call (len, gv).
  Intros vret. destruct vret as [inp src]. simpl fst in *; simpl snd in *.
  match goal with H: Zlength src = len |- _ => subst len end.
  rewrite !bytes_a, !tok_a.
  forward.
  rewrite strm_undef.
  forward_call (v_strm, Tsh, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef, Vundef).
  rewrite (ns_raw_eq gv v_strm).
  assert_PROP (isptr v_strm) as Pvs by entailer!.
  destruct (eq_dec inp nullval) as [PN|PN].
  { subst inp.
    match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx [] (LOCALx (temp _t'4 (Vint (Int.repr 1)) :: Q) (SEPx R))) end.
    { forward. entailer!. }
    { contradiction. }
    forward_if. { forward. Exists (Int.repr 0). sep_apply raw_frame. entailer!. } { infeas. } }
  aptr inp Pinp.
  assert (Ew: Int.repr wb = Int.repr (Int.signed (Int.repr wb))) by (rewrite Int.repr_signed; auto).
  rewrite Ew. clear Ew. set (w := Int.signed (Int.repr wb)).
  assert (Hw: Int.min_signed <= w <= Int.max_signed) by apply Int.signed_range. clearbody w.
  rewrite hversion.
  aptr (gv ___stringlit_api_counters_1) Pver.
  forward_if (EX alloc_ok: bool, EX sp: val,
    PROP (alloc_ok = true -> isptr sp)
    LOCAL (temp _t'4 (bool2val (negb (Int.eq (Int.repr (init_ret v_strm 49 112 w alloc_ok)) (Int.repr 0))));
           temp _input inp; temp _input_len (Vlong (Int64.repr (Zlength src)));
           lvar _strm (Tstruct _z_stream_s noattr) v_strm; gvars gv)
    SEP (init_mem gv Tsh v_strm ns_raw Vundef Vundef nullval (init_ret v_strm 49 112 w alloc_ok) sp w;
         @data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength hv_list)) hv_list (gv ___stringlit_api_counters_1);
         version_lit gv; mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv;
         malloc_token Ews (tarray tuchar (Zlength src)) inp;
         data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) inp)).
  { infeas. }
  { forward_call (gv, Tsh, v_strm, ns_raw, Vundef, Vundef, nullval, w, gv ___stringlit_api_counters_1, Ers,
                  hv_list, 49, 112).
    { rewrite if_false by (intro; subst; contradiction). cancel. }
    { change (Zlength hv_list) with 6; repeat split; auto; rep_lia. }
    Intros vret. destruct vret as [alloc_ok sp].
    forward. Exists alloc_ok sp. entailer!. apply derives_refl. }
  Intros alloc_ok sp.
  rewrite init_ret_ok by auto.
  destruct alloc_ok; [destruct (wbits_ok w) eqn:WB | ];
    unfold init_mem; rewrite if_false by (intro; subst; contradiction); simpl Z.eqb; cbv iota.
  2,3: forward_if; [forward; Exists (Int.repr 0); sep_apply raw_frame; entailer! | infeas].
  forward_if. { infeas. }
  Intros. set (L0 := init_live sp w) in *.
  assert_PROP (live_ok L0) as HL0 by (unfold istream_raw; entailer!).
  sep_apply init_istreamA.
  assert (HP0: P (z_init L0 Vundef) L0).
  { apply (pf_init P PF w); auto. apply z_init_ok. }
  forward. forward.
  set (Fr := (@data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength hv_list)) hv_list
               (gv ___stringlit_api_counters_1) * version_lit gv)%logic).
  forward_loop (pk_inv_c P gv v_strm inp src Fr)
    continue: (pk_inv_c P gv v_strm inp src Fr)
    break: (pk_inv_c P gv v_strm inp src Fr).
  { unfold pk_inv_c. Exists (z_init L0 Vundef) L0. entailer!. split; [apply z_init_ok | simpl; pose proof (Zlength_nonneg src); lia]. unfold Fr; cancel. }
  2: { unfold pk_inv_c. Intros z L. forward_call tt. Intros c.
       forward_if; [forward; Exists z L; entailer! | forward; Exists z L; entailer!]. }
  2: { unfold pk_inv_c. Intros z L. forward. Exists (Int.repr 0). sep_apply a_frame. entailer!. }
  unfold pk_inv_c. Intros z L.
  unfold abbreviate in POSTCONDITION, MORE_COMMANDS. subst POSTCONDITION MORE_COMMANDS.
  eapply semax_pre; [ | apply (body_cnt_loop P gv v_strm inp src Fr z L); auto; lia ].
  entailer!.
Qed.
