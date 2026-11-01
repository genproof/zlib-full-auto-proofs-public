(* Law inflate_header, main: positions 53 .. 74 of b0 (IHMainKit.v): stream_defaults(&s), inflateInit2
   (`if (r != Z_OK) return 0;`), the three head_buf()s and their null check, the maxima, the seven pick()s of
   h's other fields, inflateGetHeader(&s, &h) and its checks (Z_STREAM_ERROR exactly for wbits < 16: inflateEnd
   and return), gp_assert(h.done == 0), pos = 0; establishes the loop invariant ih_inv (ihf_init, ihf_wrap of
   IHFacts.v) for the gz_header h0 given to inflateGetHeader and its buffers H; then seg_75 (given). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.crc32.HarnessRef.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_header.IHLawCS Zlib.proof.harness.inflate_header.IHGlobals
               Zlib.proof.harness.inflate_header.IHHelpers Zlib.proof.harness.inflate_header.IHFacts
               Zlib.proof.harness.inflate_header.IHMainStmt.
Require Import Zlib.harness.x_inflate_header.code.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.inflate_header.IHMainKit.
Require Import Zlib.proof.harness.inflate_header.IHMainInitKit Zlib.proof.harness.inflate_header.IHMainInitB
               Zlib.proof.harness.inflate_header.IHMainInitC.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* Helpers of inflateInit2_ (as inflate_check/IKMain.v)                                          *)

Lemma ihi_tschar_cs sh n (v: list val) q:
  @data_at Zlib.units.Inflate.CS sh (tarray tschar n) v q = @data_at CS sh (tarray tschar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.

Definition ihi_hver : list val := map (fun c => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0].

Lemma ihi_hver_lit gv:
  ih_hversion_lit gv =
  @data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength ihi_hver)) ihi_hver
    (gv Zlib.harness.x_inflate_header.code.___stringlit_x_inflate_header_1).
Proof. unfold ih_hversion_lit. rewrite (ihi_tschar_cs Ers (Zlength ihi_hver)). reflexivity. Qed.

Lemma ihi_hver_to gv:
  ih_hversion_lit gv |--
  @data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength ihi_hver)) ihi_hver
    (gv Zlib.harness.x_inflate_header.code.___stringlit_x_inflate_header_1).
Proof. rewrite ihi_hver_lit. apply derives_refl. Qed.

Lemma ihi_hver_from gv:
  @data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength ihi_hver)) ihi_hver
    (gv Zlib.harness.x_inflate_header.code.___stringlit_x_inflate_header_1) |-- ih_hversion_lit gv.
Proof. rewrite ihi_hver_lit. apply derives_refl. Qed.

(* a stream left by a failed inflateInit2_ is the local variable's memory *)
Lemma ihi_init_fail_mem gv vs r msgv stv opq ret sp w:
  isptr vs -> ret <> Z_OK ->
  init_mem gv Tsh vs r msgv stv opq ret sp w |-- @data_at_ CS Tsh (Tstruct _z_stream_s noattr) vs.
Proof.
  intros P Hr. unfold init_mem.
  destruct (eq_dec vs nullval); [subst; contradiction | ].
  destruct (ret =? Z_VERSION_ERROR); [unfold raw_strm; apply ih_strm_to_undef | ].
  destruct (ret =? Z_MEM_ERROR); [unfold raw_strm; apply ih_strm_to_undef | ].
  destruct (Z.eqb_spec ret Z_OK); [contradiction | ].
  unfold raw_strm; apply ih_strm_to_undef.
Qed.

Lemma ihi_init_istream gv vs tin tout adl dt rs L:
  0 <= adl <= Int64.max_unsigned ->
  istream_raw gv Tsh vs
    (raw_after_init (RF nullval (Vint (Int.repr 0)) (Vlong (Int64.repr tin)) nullval (Vint (Int.repr 0))
       (Vlong (Int64.repr tout)) (Vint (Int.repr dt)) (Vlong (Int64.repr adl)) (Vlong (Int64.repr rs))) (l_s L)) L
  = istream gv Tsh vs (ihi_z_init adl rs L) (Some L).
Proof.
  intros A. rewrite <- istream_raw_istream.
  - unfold raw_after_init, ihi_z_init; simpl. f_equal. f_equal. destruct (i_wrap (l_s L) =? 0); reflexivity.
  - unfold zf_ok, ihi_z_init; simpl. split; [rep_lia | ]. split; [rep_lia | ]. split; [rep_lia | ].
    split; [rep_lia | ]. split; [rep_lia | ].
    destruct (i_wrap (l_s L) =? 0); [auto | ].
    assert (M: Z.land (i_wrap (l_s L)) 1 = i_wrap (l_s L) mod 2) by (apply (Z.land_ones _ 1); lia).
    rewrite M. pose proof (Z.mod_pos_bound (i_wrap (l_s L)) 2 ltac:(lia)). rep_lia.
  - reflexivity.
Qed.

Lemma ihi_init_ret (vs: val) w a: isptr vs ->
  init_ret vs 49 112 w a = if a then (if wbits_ok w then Z_OK else Z_STREAM_ERROR) else Z_MEM_ERROR.
Proof.
  intros P. unfold init_ret, sizeof_z_stream. simpl.
  rewrite if_false by (destruct vs; try contradiction; discriminate). destruct a; reflexivity.
Qed.

Lemma ihi_b2z_false b: Int.repr (b2z b) = Int.zero -> b = false.
Proof. destruct b; simpl; auto. intros E. exfalso. apply Int.one_not_zero. exact E. Qed.

Lemma ihi_nul_iff (nul: Z) (p: val):
  (nul = 0 -> p = nullval) -> (negb (nul =? 0) && ihi_isnull p)%bool = false -> (nul = 0 <-> p = nullval).
Proof.
  intros A B. split; auto. intros E. subst p. unfold ihi_isnull in B. rewrite if_true in B by auto.
  rewrite andb_true_r in B. destruct (Z.eqb_spec nul 0); auto; discriminate.
Qed.

Ltac show := match goal with |- semax _ ?P _ _ => fail 100 "PRE" P | |- ?G => fail 100 "GOAL" G end.

Ltac ihi_bool := unfold ihi_isnull, b2z in *;
  repeat match goal with
  | |- context [eq_dec ?p nullval] => destruct (eq_dec p nullval); [subst p | ]
  | H: context [eq_dec ?p nullval] |- _ => destruct (eq_dec p nullval); [subst p | ]
  | |- context [?a =? 0] => destruct (Z.eqb_spec a 0)
  | H: context [?a =? 0] |- _ => destruct (Z.eqb_spec a 0)
  end; simpl in *; try contradiction; try lia;
  try match goal with |- context [sem_cmp_pp Ceq ?p _] => destruct p; try contradiction end;
  try reflexivity;
  try (exfalso; match goal with H: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact H
                              | H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity
                              | H: Int.zero <> Int.zero |- _ => apply H; reflexivity
                              | H: Int.one = Int.zero |- _ => apply Int.one_not_zero; exact H end).

Ltac ihi_infeas := exfalso; first [ match goal with H: ?a <> ?b |- _ => solve [apply H; reflexivity] end
                              | match goal with H: _ |- _ => solve [discriminate H] end
                              | contradiction
                              | match goal with H: Int.repr _ = Int.repr _ |- _ =>
                                  apply repr_inj_signed in H; [lia | rep_lia | rep_lia] end
                              | lia ].

Lemma init_ok {Espec: OracleKind} I gv V g b P:
  ih_facts I -> ih_f53 g b P ->
  (forall h0 H, ih_glob I g b P h0 H ->
     semax Delta_m (ih_inv I gv V g b P h0 H (version_lit gv * ih_hversion_lit gv)) seg_75 POST_b) ->
  semax Delta_m (ih_s53 gv V g b P) seg_53 POST_b.
Proof.
  intros CF F53 K.
  destruct V as [vs vh vxs vns vcs vosn]; destruct b as [w xmax nmax cmax xnul nnul cnul];
  destruct P as [srcp xfp nfp cfp].
  unfold ih_s53, seg_53, Delta_m, Gmain, POST_b, POST_m.
  cbn [v_s_ v_h_ v_xs_ v_ns_ v_cs_ v_osn_ b_w b_xmax b_nmax b_cmax b_xnul b_nnul b_cnul p_src p_xf p_nf p_cf].
  simplify_func_tycontext. abbreviate_semax.
  unfold ih_f53 in F53. cbn [b_w b_xmax b_nmax b_cmax b_xnul b_nnul b_cnul p_src p_xf p_nf p_cf] in F53.
  destruct F53 as (Hg & Hw & Hxm & Hnm & Hcm & Hxn & Hnn & Hcn & Psrc & Pxf & Pnf & Pcf).
  assert_PROP (isptr vs) as Pvs by entailer!.
  replace_SEP 6 (@data_at Zlib.units.Inflate.CS Tsh Rep.t_strm ih_strm_undef vs).
  { entailer!. }
  forward_call (vs, Tsh, Vundef, Vundef).
  Intros vv. destruct vv as [[[[tin tout] adl] dt] rs]. simpl fst in *. simpl snd in *.
  set (rr := RF nullval (Vint (Int.repr 0)) (Vlong (Int64.repr tin)) nullval (Vint (Int.repr 0))
               (Vlong (Int64.repr tout)) (Vint (Int.repr dt)) (Vlong (Int64.repr adl)) (Vlong (Int64.repr rs))).
  replace_SEP 0 (if eq_dec vs nullval then emp else raw_strm gv Tsh vs rr Vundef Vundef nullval nullval nullval).
  { rewrite if_false by (destruct vs; try contradiction; discriminate). entailer!. }
  replace_SEP 6 (@data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength ihi_hver)) ihi_hver
                   (gv Zlib.harness.x_inflate_header.code.___stringlit_x_inflate_header_1)).
  { entailer!. apply ihi_hver_to. }
  assert_PROP (isptr (gv Zlib.harness.x_inflate_header.code.___stringlit_x_inflate_header_1)) as Pver by entailer!.
  forward_call (gv, Tsh, vs, rr, Vundef, Vundef, nullval, w,
                gv Zlib.harness.x_inflate_header.code.___stringlit_x_inflate_header_1, Ers, ihi_hver, 49, 112).
  { repeat match goal with |- _ /\ _ => split end; try exact Pver; change (Zlength ihi_hver) with 6; rep_lia. }
  Intros vret. destruct vret as [alloc_ok sp]. simpl fst in *. simpl snd in *.
  rewrite (ihi_init_ret vs w alloc_ok Pvs).
  destruct alloc_ok; [destruct (wbits_ok w) eqn:WOK | ].
  2: { forward_if; [ | ihi_infeas ].
       sep_apply (ihi_init_fail_mem gv vs rr Vundef Vundef nullval Z_STREAM_ERROR sp w Pvs ltac:(discriminate)).
       forward. Exists (Int.repr 0). entailer!. }
  2: { forward_if; [ | ihi_infeas ].
       sep_apply (ihi_init_fail_mem gv vs rr Vundef Vundef nullval Z_MEM_ERROR sp w Pvs ltac:(discriminate)).
       forward. Exists (Int.repr 0). entailer!. }
  forward_if.
  { ihi_infeas. }
  unfold init_mem.
  rewrite if_false by (destruct vs; try contradiction; discriminate).
  change (Z_OK =? Z_VERSION_ERROR) with false; change (Z_OK =? Z_MEM_ERROR) with false;
    change (Z_OK =? Z_OK) with true.
  cbv beta iota zeta.
  remember (init_live sp w) as L0 eqn:HL0.
  subst rr.
  rewrite ihi_init_istream by auto.
  assert_PROP (live_ok L0 /\ zf_ok (ihi_z_init adl rs L0)) as LZ by (unfold istream; entailer!).
  destruct LZ as [LOK ZOK].
  assert (Psp: isptr sp) by auto.
  rewrite <- ihi_hver_lit.
  freeze [1;2;5;6;12;13;14;15;16;17;18;19] FR.
  forward_call (xmax, xnul, vxs, Tsh, gv).
  Intros vr. destruct vr as [[xb xq] xbs]. cbn [fst snd] in *.
  forward.
  forward_call (nmax, nnul, vns, Tsh, gv).
  Intros vr. destruct vr as [[nb nq] nbs]. cbn [fst snd] in *.
  forward.
  forward_call (cmax, cnul, vcs, Tsh, gv).
  Intros vr. destruct vr as [[cb cq] cbs]. cbn [fst snd] in *.
  forward.
  ifpost _t'37 (Int.repr (b2z (negb (xnul =? 0) && ihi_isnull xb))).
  { forward. destruct (eq_dec xb nullval) as [Nx|Nx].
    - subst xb. forward. entailer!; ihi_bool.
    - Intros. forward. entailer!; ihi_bool. }
  { forward. entailer!; ihi_bool. }
  ifpost _t'38 (Int.repr (b2z ((negb (xnul =? 0) && ihi_isnull xb) || (negb (nnul =? 0) && ihi_isnull nb)))).
  { forward. entailer!; ihi_bool. }
  { forward_if.
    - forward. destruct (eq_dec nb nullval) as [Nn|Nn].
      + subst nb. forward. forward. entailer!; ihi_bool.
      + Intros. forward. forward. entailer!; ihi_bool.
    - forward. entailer!; ihi_bool. }
  ifpost _t'39 (Int.repr (b2z ((negb (xnul =? 0) && ihi_isnull xb) || (negb (nnul =? 0) && ihi_isnull nb) ||
                               (negb (cnul =? 0) && ihi_isnull cb)))).
  { forward. entailer!; ihi_bool. }
  { forward_if.
    - forward. destruct (eq_dec cb nullval) as [Nc|Nc].
      + subst cb. forward. forward. entailer!; ihi_bool.
      + Intros. forward. forward. entailer!; ihi_bool.
    - forward. entailer!; ihi_bool. }
  forward_if.
  { forward. Exists (Int.repr 0). apply andp_right; [apply prop_right; reflexivity |].
    sep_apply (ih_istream_to_undef gv vs (ihi_z_init adl rs (init_live sp w)) (Some (init_live sp w))).
    sep_apply (data_at_data_at_ Tsh (Tstruct _gz_header_s noattr)).
    sep_apply (data_at_data_at_ Tsh (tptr tuchar) xq vxs).
    sep_apply (data_at_data_at_ Tsh (tptr tuchar) nq vns).
    sep_apply (data_at_data_at_ Tsh (tptr tuchar) cq vcs).
    cancel. }
  match goal with Hz: (_ || _)%bool = false |- _ => rewrite !orb_false_iff in Hz; destruct Hz as [[Bx Bn] Bc] end.
  assert (F60: ihi_f60 I g (IHB w xmax nmax cmax xnul nnul cnul) (IHP srcp xfp nfp cfp) sp adl rs
                 (IHH xb nb cb xq nq cq) xbs nbs cbs).
  { unfold ihi_f60, ih_f53. cbn [b_w b_xmax b_nmax b_cmax b_xnul b_nnul b_cnul p_src p_xf p_nf p_cf
                                 h_xb h_nb h_cb h_xq h_nq h_cq].
    repeat match goal with |- _ /\ _ => split end; first [ apply ihi_nul_iff; assumption | lia | auto ]. }
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  thaw FR.
  eapply semax_pre; [ | apply (picks_ok I gv (IHV vs vh vxs vns vcs vosn) g (IHB w xmax nmax cmax xnul nnul cnul)
                                (IHP srcp xfp nfp cfp) sp adl rs (IHH xb nb cb xq nq cq) xbs nbs cbs F60);
                        intros; apply (hdr_ok I); auto ].
  unfold ihi_s60, ihi_buf, ihi_h60.
  cbn [v_s_ v_h_ v_xs_ v_ns_ v_cs_ v_osn_ b_w b_xmax b_nmax b_cmax b_xnul b_nnul b_cnul p_src p_xf p_nf p_cf
       h_xb h_nb h_cb h_xq h_nq h_cq].
  subst L0. entailer!.
Qed.
