(* Law api_split_invariant, main: statements 23-28, the split stream: new_stream(&split), code_split =
   inflateInit2_(&split, window, "1.3.2", sizeof(z_stream)) (`return 0` on Z_MEM_ERROR, then
   gp_assert(code_split == Z_OK)), split.next_in = input_split (the copy of the input),
   split.next_out = out_split:
   the loop invariant holds with P = 0, O = [] (SIFacts.sf_init) (sm_B -> sm_inv). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_split_invariant.SILawCS.
Require Import Zlib.proof.harness.api_split_invariant.SIGlobals.
Require Import Zlib.proof.harness.api_split_invariant.SIFacts.
Require Import Zlib.proof.harness.api_split_invariant.SIMainKit.
Require Import Zlib.harness.api_split_invariant.code.
Local Open Scope logic.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers (here at `code_split = inflateInit2_(...)`, with _input, _input_len, _input_split in the context); each
   identifier comparison is decided by vm_compute instead. *)
Ltac sm_rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in sm_rlt_fix u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := sm_rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

Lemma seg_init_ok {Espec: OracleKind} Inv Max gv vwb vone vsplit w src room flush inp ins o1 o2 r1 z1 L1 ow1:
  si_facts Inv Max -> sm_A_facts w src room flush inp ins o1 o2 -> sm_B_facts Max w src room r1 z1 ow1 ->
  semax Delta_m
    (sm_inv Inv gv vwb vone vsplit w src room ins o1 o2 r1 (sm_fr gv vwb vone inp src o1 room z1 L1 ow1))
    sm_seg29 POST_B ->
  semax Delta_m (sm_B gv vwb vone vsplit w src room inp ins o1 o2 r1 z1 L1 ow1) sm_seg23 POST_B.
Proof.
  intros SF HA HB K.
  destruct HA as (Hw & Bs & Hsrc & Hroom & Hfl & Hb & Ht & Pinp & Pins & Po1 & Po2).
  unfold sm_seg23, sm_B, Delta_m, Gmain_k, POST_B. simplify_func_tycontext. abbreviate_semax.
  assert_PROP (isptr vsplit) as Pvs by entailer!.
  rewrite sm_strm_undef.
  forward_call (vsplit, Tsh, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef, Vundef).
  rewrite (sm_ns_raw_eq gv vsplit).
  rewrite (sm_hversion gv).
  assert_PROP (isptr (gv ___stringlit_api_split_invariant_1)) as Pver
    by (sep_apply (data_at_local_facts Ers (tarray tschar (Zlength sm_hv)) sm_hv
                     (gv ___stringlit_api_split_invariant_1)); Intros; apply prop_right; auto).
  forward_call (gv, Tsh, vsplit, sm_ns_raw, Vundef, Vundef, nullval, w, gv ___stringlit_api_split_invariant_1, Ers,
                sm_hv, 49, 112).
  { rewrite if_false by (intro; subst; contradiction). cancel. }
  { change (Zlength sm_hv) with 6. pose proof (sm_window_wbits w Hw). destruct Hw as [E|[E|[E|E]]]; subst w; repeat split; auto; try rep_lia; intro; apply writable_share_top. }
  Intros vret. destruct vret as [alloc_ok sp].
  simpl fst in *; simpl snd in *.
  rewrite sm_init_ret by auto. rewrite (sm_window_wbits w Hw).
  destruct alloc_ok; unfold init_mem; rewrite if_false by (intro; subst; contradiction); simpl Z.eqb; cbv iota.
  (* code_split = Z_MEM_ERROR returns; otherwise gp_assert(code_split == Z_OK) holds *)
  2: { forward_if; [ | sm_infeas]. forward. Exists (Int.repr 0). sep_apply sm_raw_frame. unfold sm_one.
       sep_apply sm_a_frame. entailer!. }
  forward_if. { sm_infeas. }
  forward_call Int.one.
  set (L0 := init_live sp w) in *.
  assert_PROP (live_ok L0) as HL0 by (unfold istream_raw; entailer!).
  sep_apply sm_init_istreamA.
  rewrite sm_istreamA_unfold. Intros.
  unfold sm_tup. simpl zf_ni. simpl zf_no.
  forward. forward.
  (* the split stream with next_in = input_split and next_out = out_split *)
  set (z0 := sm_next (sm_z_init L0) ins o2).
  match goal with |- context [data_at Tsh t_zsl ?t vsplit] =>
    replace t with (sm_tup gv z0 (adler_v (raw_live (Some L0)) z0 Vundef) (l_sp L0)) by reflexivity end.
  assert (Hz0: zf_ok z0) by exact H1.
  sep_apply (sm_istreamA_fold gv Tsh vsplit z0 Vundef L0); auto.
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | exact K].
  (* the loop invariant at P = 0, O = [] *)
  assert (HI: Inv w src room 0 [] L0) by (apply (sf_init _ _ SF); auto).
  assert (HS: swfW (l_s L0)) by (apply sm_swfW_init; auto).
  assert (HH: head_opt (Some L0) = emp) by apply sm_head_init.
  unfold sm_inv. Exists 0 (@nil Z) z0 L0.
  match goal with |- context [@data_at ?cs Ers (tarray tschar ?k) ?v (gv ___stringlit_api_split_invariant_1)] =>
    change (@data_at cs Ers (tarray tschar k) v (gv ___stringlit_api_split_invariant_1)) with (si_hversion gv) end.
  rewrite HH, sm_out_nil by lia. unfold sm_fr, sm_one.
  assert (E0: forall p, isptr p -> offset_val 0 p = p)
    by (intros [] ?; try contradiction; simpl; rewrite Ptrofs.add_zero; auto).
  rewrite !E0 by auto.
  entailer!.
  rewrite Zlength_nil. lia.
Qed.
