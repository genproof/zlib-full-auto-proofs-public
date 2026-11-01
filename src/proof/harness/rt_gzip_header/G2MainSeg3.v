(* Law rt_gzip_header on the round-2 harness, main's body, segment 3 (G2MainKit.seg3_stmt): statements 36-39,
   deflateSetHeader(&compressor, &head) and its test, capacity = deflateBound_z(&compressor, 0),
   compressed = malloc(capacity) and its NULL test.  The header is accepted (G2DFacts.gd_head), the bound is
   defined and the deflate loop's invariant J starts from it (gd_bound, gd_range); the memory lemmas are in
   G2MS3Kit.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.rt_gzip_header.CS.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainDefs.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.rt_gzip_header.G2DFacts.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainKit.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS3Kit.
Require Import Zlib.harness.rt_gzip_header.code.
#[local] Existing Instance Zlib.proof.harness.rt_gzip_header.CS.CS.
Local Open Scope logic.

(* the kernel must not unfold the model's loops when it compares their instances *)
Local Strategy opaque [loop loop2].

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers; each identifier comparison is decided by vm_compute instead. *)
Ltac rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in rlt_fix u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

Lemma g2seg3_ok : seg3_stmt.
Proof.
  intros Espec J0 J gv vh vg vc vd vr g st DF.
  destruct st as [s tin tout adler msg msgv].
  unfold A28, seg3, POST_m, Delta_m, gp_locals, gs_locals, lv_locals. simplify_func_tycontext.
  cbn [st_s st_tin st_tout st_adler st_msg st_msgv app].
  Intros.
  pose proof (gh_of_ok2 g H) as Gok.
  pose proof (gd_head _ _ DF _ _ _ _ _ (gh_of g) dz0 H0 Gok) as Hc.
  destruct (gd_bound _ _ DF _ _ _ _ _ (gh_of g) H0 Gok) as (b & Hb & Hbr & HJ).
  destruct (gd_range _ _ DF _ _ _ _ _ _ _ _ HJ) as (_ & _ & _ & _ & _ & _ & Htin & Htout & Had).
  set (s1 := set_d_gzhead s (Some (gh_of g))) in *.
  sep_apply (head_open g vh H).
  sep_apply (raw_fields vc (mkDside s tin tout adler msg msgv) Htin Htout Had).
  unfold st_fields. rewrite af_split. cbn [st_s st_tin st_tout st_adler st_msg st_msgv].
  forward_call (Some s, vc, nullval, nullval, vh, gh_of g, selp g 1 (g_xp g), selp g 2 (g_np g),
    selp g 4 (g_cp g), (Some s1, dz0, Z_OK), dz0, gv).
  { cancel. }
  { unfold on_state, c_on_state. rewrite Hc. reflexivity. }
  cbn [fst snd]. simpl (Z_OK =? Z_OK). cbv iota.
  forward_if.
  { discriminate. }
  change (gzh_at Ews (gh_of g) vh (selp g 1 (g_xp g)) (selp g 2 (g_np g)) (selp g 4 (g_cp g)))
    with (hdr_at (Some s1) vh (hx_of g)).
  rewrite ni_cs.
  forward_call (Some s1, vc, nullval, vh, hx_of g, 0, b, gv).
  { unfold u64_ok. rep_lia. }
  forward_call (tarray tuchar b, gv).
  { simpl. rewrite Z.max_r by lia. unfold max_u64 in *. rep_lia. }
  Intros cbp.
  rewrite ?ni_cs.
  assert (Ehc : hclose vh g s1 (hx_of g) (Hr_of g vh)) by (apply head_close; [ exact H | apply gz_set ]).
  destruct (eq_dec cbp nullval) as [Ecp | Ecp].
  - (* compressed == NULL: return 0, main's locals back *)
    subst cbp. forward_if.
    + forward. Exists (Int.repr 0). entailer!.
      sep_apply (af_join vc nullval 0 tin nullval 0 tout msgv adler).
      sep_apply (comp_back vc gv (Some s1) vh nullval 0 tin nullval 0 tout msgv adler).
      sep_apply (Ehc s1 eq_refl). unfold gside.
      sep_apply (data_at_data_at_ Tsh t_g (hvals g) vh).
      sep_apply (data_at_data_at_ Tsh t_g (gval g) vg).
      cancel.
    + contradiction.
  - Intros. forward_if.
    + contradiction.
    + forward.
      Exists (mkDside s1 tin tout adler msg msgv) (hx_of g) (Hr_of g vh) b cbp.
      unfold A32, st_fields, cnew, gp_locals, gs_locals, lv_locals.
      cbn [st_s st_tin st_tout st_adler st_msg st_msgv app].
      sep_apply (af_join vc nullval 0 tin nullval 0 tout msgv adler).
      entailer!.
Qed.
