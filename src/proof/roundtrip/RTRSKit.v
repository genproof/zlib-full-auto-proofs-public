(* Law deflate_roundtrip, gzip header: main with inflate()'s and inflateGetHeader's header-relaxed
   specifications (RTHSpec.inflate_spec6 / inflateGetHeader_spec6), the kit.

   - The law's G gives inflate and inflateGetHeader THE binary intersection of their Spec5 specification and their
     v6 specification (inflate_specI, inflateGetHeader_specI): its body is the pair of bodies (LibStmt5 for Spec5,
     RTHSpec.rt_head6_stmt for v6), and it is a subspecification of each.  So main's segments proved against
     Spec5 (RTRMKit.Delta_m, Gm5) and the gzip-header segment proved against v6 (Delta_m6, Gm6) both move to
     main's context with the intersections (Delta_mI, GmI) by tycontext_sub (rs_tsub).
   - The gzip run with a header (R.head_set = 1) from A6 to main's end, in Delta_m6, in parts:
     seg6 (the inflateGetHeader block; position 7 is skipped: wrap = 2) -> AH8 (the stream with the header
     attached: head_mem6, the buffers' remaining malloc tokens rm_htoks) -> seg8 (exact_copy, malloc, the stores,
     inflate(&t, Z_FINISH) by inflate_spec6, hd6_ok from gz_first_ok) -> AH16 -> seg16 (position 16 skipped
     (wrap = 2), Z_MEM_ERROR return, the asserts, bytes_same(ob, data)) -> AH21 -> seg21 (the header checks and
     inflateEnd). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.HarnessRef.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.roundtrip.RTXFacts.
Require Import Zlib.proof.roundtrip.RTRCS Zlib.proof.roundtrip.RTRRunSpec Zlib.proof.roundtrip.RTRRunKit Zlib.proof.roundtrip.RTRApiConv Zlib.proof.roundtrip.RTRMainSpec.
Require Zlib.proof.inflate_api.Spec5 Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.roundtrip.RTIIface.
Require Import Zlib.proof.roundtrip.RTHSpec Zlib.proof.roundtrip.RTHIfDefs.
Require Import Zlib.harness.x_deflate_roundtrip.code.
Require Import Zlib.proof.roundtrip.RTRMKit.
Require Zlib.proof.uncompr.URunFrame.
#[local] Existing Instance RTRCS.CS.
Local Open Scope logic.

Module S5 := Zlib.proof.inflate_api.Spec5.

(** ** The contexts *)

(* main's context with the v6 specifications (the gzip-header segment) *)
Definition Gm6 (I : api_inv) (Iend : dstate -> Prop) : funspecs :=
  [deflate_run_spec I Iend; deflateEnd_spec; stream_defaults_spec; exact_copy_spec;
   S5.inflateInit2__spec; inflateGetHeader_spec6;
   S5.inflateSetDictionary_spec; inflate_spec6;
   S5.inflateEnd_spec;
   ref_adler32_spec; bytes_same_spec;
   Zlib.proof.inflate_api.Bodies5.zcalloc_i; Zlib.proof.inflate_api.Bodies5.zcfree_i;
   (_quickproof_malloc, malloc_spec'); gp_assert_spec].

Definition Delta_m6 (I : api_inv) (Iend : dstate -> Prop) : tycontext :=
  func_tycontext f_main (QPvarspecs p) (Gm6 I Iend) nil.

(* the intersections *)
Definition inflate_fI : funspec :=
  binary_intersection' (snd S5.inflate_spec) (snd inflate_spec6) eq_refl eq_refl.
Definition inflateGetHeader_fI : funspec :=
  binary_intersection' (snd S5.inflateGetHeader_spec) (snd inflateGetHeader_spec6) eq_refl eq_refl.
Definition inflate_specI : ident * funspec := (fst S5.inflate_spec, inflate_fI).
Definition inflateGetHeader_specI : ident * funspec := (fst S5.inflateGetHeader_spec, inflateGetHeader_fI).

Lemma inflate_fI_sub : funspec_sub inflate_fI (snd S5.inflate_spec) /\ funspec_sub inflate_fI (snd inflate_spec6).
Proof. apply binary_intersection'_sub. Qed.
Lemma inflateGetHeader_fI_sub :
  funspec_sub inflateGetHeader_fI (snd S5.inflateGetHeader_spec) /\
  funspec_sub inflateGetHeader_fI (snd inflateGetHeader_spec6).
Proof. apply binary_intersection'_sub. Qed.

(* main's context in the law *)
Definition GmI (I : api_inv) (Iend : dstate -> Prop) : funspecs :=
  [deflate_run_spec I Iend; deflateEnd_spec; stream_defaults_spec; exact_copy_spec;
   S5.inflateInit2__spec; inflateGetHeader_specI;
   S5.inflateSetDictionary_spec; inflate_specI;
   S5.inflateEnd_spec;
   ref_adler32_spec; bytes_same_spec;
   Zlib.proof.inflate_api.Bodies5.zcalloc_i; Zlib.proof.inflate_api.Bodies5.zcfree_i;
   (_quickproof_malloc, malloc_spec'); gp_assert_spec].

Definition Delta_mI (I : api_inv) (Iend : dstate -> Prop) : tycontext :=
  func_tycontext f_main (QPvarspecs p) (GmI I Iend) nil.

(* a context whose functions have subspecifications *)
Lemma rs_tsub (G1 G2 : funspecs) V f :
  Forall2 (fun a b => fst a = fst b /\ funspec_sub (snd b) (snd a)) G1 G2 ->
  tycontext_sub (func_tycontext f V G1 nil) (func_tycontext f V G2 nil).
Proof.
  intros H. apply tycontext_sub_i99. split.
  - assert (E : make_tycontext_g V G1 = make_tycontext_g V G2).
    { unfold make_tycontext_g. induction H as [ | a b G1 G2 [Ei Es] H IH]; [reflexivity | ].
      simpl. rewrite IH, Ei. f_equal.
      destruct a as [ia fa], b as [ib fb]; simpl in *. destruct fa, fb; simpl in Es.
      destruct Es as [[-> ->] _]. reflexivity. }
    intros id. rewrite E. destruct (Maps.PTree.get id (make_tycontext_g V G2)); simpl; auto.
  - intros id. rewrite !semax_prog.find_id_maketycontext_s.
    induction H as [ | a b G1 G2 [Ei Es] H IH]; [exact I | ].
    destruct a as [ia fa], b as [ib fb]; simpl in *. subst ib.
    if_tac; [ | exact IH].
    exists fb. split; [reflexivity | ]. apply funspec_sub_sub_si; exact Es.
Qed.

Lemma Delta_m_subI I Iend : tycontext_sub (Delta_m I Iend) (Delta_mI I Iend).
Proof.
  unfold Delta_m, Delta_mI. apply rs_tsub. unfold Gm5, GmI.
  do 5 (apply Forall2_cons; [split; [reflexivity | apply funspec_sub_refl] | ]).
  apply Forall2_cons; [split; [reflexivity | exact (proj1 inflateGetHeader_fI_sub)] | ].
  apply Forall2_cons; [split; [reflexivity | apply funspec_sub_refl] | ].
  apply Forall2_cons; [split; [reflexivity | exact (proj1 inflate_fI_sub)] | ].
  do 7 (apply Forall2_cons; [split; [reflexivity | apply funspec_sub_refl] | ]).
  apply Forall2_nil.
Qed.

Lemma Delta_m6_subI I Iend : tycontext_sub (Delta_m6 I Iend) (Delta_mI I Iend).
Proof.
  unfold Delta_m6, Delta_mI. apply rs_tsub. unfold Gm6, GmI.
  do 5 (apply Forall2_cons; [split; [reflexivity | apply funspec_sub_refl] | ]).
  apply Forall2_cons; [split; [reflexivity | exact (proj2 inflateGetHeader_fI_sub)] | ].
  apply Forall2_cons; [split; [reflexivity | apply funspec_sub_refl] | ].
  apply Forall2_cons; [split; [reflexivity | exact (proj2 inflate_fI_sub)] | ].
  do 7 (apply Forall2_cons; [split; [reflexivity | apply funspec_sub_refl] | ]).
  apply Forall2_nil.
Qed.

(** ** The gzip run with a header: the values *)

(* the header's fields as deflateSetHeader got them (hdr_of): the extra field, the name and the comment with their
   zero bytes; main's buffers have exactly these sizes (R.xlen, R.nl + 1, R.cl + 1) *)
Definition rm_x (rf : rfinal) : list Z := rs_xf (rf_rs rf).
Definition rm_nm (rf : rfinal) : list Z := rs_nm (rf_rs rf) ++ [0].
Definition rm_cm (rf : rfinal) : list Z := rs_cm (rf_rs rf) ++ [0].

(* the gz_header main gives to inflateGetHeader (the scalar fields and the buffer bytes are anything: hraw6) *)
Definition rm_h0 (rf : rfinal) : hstate :=
  HS 0 0 0 0 true 0 (Zlength (rm_x rf)) (Zrepeat 0 (Zlength (rm_x rf)))
     true (Zlength (rm_nm rf)) (Zrepeat 0 (Zlength (rm_nm rf)))
     true (Zlength (rm_cm rf)) (Zrepeat 0 (Zlength (rm_cm rf))) 0 0.

(* the live part after inflateInit2(&t, 32) and inflateGetHeader(&t, &ih) *)
Definition rm_hL (rf : rfinal) (sp vih xb nb cb : val) : live :=
  head_live (init_live sp 32) (rm_h0 rf) vih Tsh xb nb cb.

(* the malloc tokens of the header buffers of non-zero size (those of size 0 are in head_mem6's btok) *)
Definition nbtok (b : val) (n : Z) : mpred := if zeq n 0 then emp else malloc_token Ews (tarray tuchar n) b.
Definition rm_htoks (rf : rfinal) (xb nb cb : val) : mpred :=
  nbtok xb (Zlength (rm_x rf)) * nbtok nb (Zlength (rm_nm rf)) * nbtok cb (Zlength (rm_cm rf)).

(** ** The pure facts of the inflate() call with the header *)

(* the header inflate reported, at Z_STREAM_END *)
Definition gz_end (rf : rfinal) (h : hstate) : Prop :=
  let gh := hdr_of (rf_rs rf) in
  h_done h = 1 /\ h_text h = DS.gz_text gh /\ h_time h = DS.gz_time gh /\ h_os h = DS.gz_os gh /\
  h_hcrc h = DS.gz_hcrc gh /\ h_extra_len h = DS.gz_extra_len gh /\
  h_xbuf h = rm_x rf /\ h_nbuf h = rm_nm rf /\ h_cbuf h = rm_cm rf /\
  h_xp h = true /\ h_np h = true /\ h_cp h = true.

(* the model's result of the call *)
Definition gz_res_ok (rf : rfinal) (res : result) : Prop :=
  rdone (rf_O rf) (rm_D rf) res /\
  (r_ret res = Z_STREAM_END -> gz_end rf (m_h (r_m res)) /\ hdr_mode (m_mode (r_m res)) = false).

(* the call from the live part L offered all of O and |D| bytes of space: it passes the header (hd6_ok) and its
   result *)
Definition gz_first_ok (rf : rfinal) (L : live) : Prop :=
  forall z, live_ok L -> zcall_ok z (rf_O rf) (rm_D rf) ->
    (exists n, hpass 4 n (m_init z L (rf_O rf))) /\
    (forall res, Zlib.proof.inflate.Model2.run2 4 lenfix_list distfix_list (m_init z L (rf_O rf)) res ->
                 gz_res_ok rf res).

(* after the call, in main's terms *)
Definition gz_call_ok (rf : rfinal) (r : Z) (z1 : zfields) (L1 : live) (ow : list Z) : Prop :=
  fin_ok rf r z1 ow /\ (r = Z_STREAM_END -> gz_end rf (l_h L1) /\ hdr_mode (i_mode (l_s L1)) = false).

(** ** The segments and assertions of the header path *)

Definition seg21 : statement := ltac:(rm_seg (rm_drop 21 (rm_first (fn_body f_main)))).

(* before exact_copy: the header attached (L: rm_hL rf sp vih xb nb cb) *)
Definition AH8 (Iend : dstate -> Prop) (rf : rfinal) (vR vs vt vih : val) (gv : globals) (z : zfields)
    (L : live) : environ -> mpred :=
  PROP (rf_ok Iend vR rf; rf_hset rf = 1; rm_zinit z; gz_first_ok rf L;
        i_head (l_s L) = true; l_headp L = vih; l_hsh L = Tsh)
  LOCAL (lvar _R t_drun vR; lvar _s t_strmL vs; lvar _t t_strmL vt; lvar _ih t_gzhL vih; gvars gv)
  SEP (istream gv Tsh vt z (Some L); head_mem6 L; rm_htoks rf (l_xb L) (l_nb L) (l_cb L);
       rm_dside rf vR; data_at_ Tsh t_strmL vs; mem_mgr gv; Rm gv; zfuncs gv; TT).

(* after the inflate() call *)
Definition AH16 (Iend : dstate -> Prop) (rf : rfinal) (vR vs vt vih : val) (gv : globals) (ibp obp : val)
    (r : Z) (z1 : zfields) (L1 : live) (ow : list Z) (cont : list val) : environ -> mpred :=
  PROP (rf_ok Iend vR rf; rf_hset rf = 1; gz_call_ok rf r z1 L1 ow; Zlength cont = rf_nf rf;
        i_head (l_s L1) = true; l_headp L1 = vih; l_hsh L1 = Tsh)
  LOCAL (temp _r (vi r); temp _ib ibp; temp _ob obp;
         lvar _R t_drun vR; lvar _s t_strmL vs; lvar _t t_strmL vt; lvar _ih t_gzhL vih; gvars gv)
  SEP (istream gv Tsh vt z1 (Some L1); head_mem6 L1; rm_htoks rf (l_xb L1) (l_nb L1) (l_cb L1);
       in_rep (rm_ib rf ibp); in_tok true (rm_ib rf ibp);
       out_rep (rm_ob rf obp cont) ow; out_tok true (Some (rm_ob rf obp cont));
       rm_dside rf vR; data_at_ Tsh t_strmL vs; mem_mgr gv; Rm gv; zfuncs gv; TT).

(* before the header checks: Z_STREAM_END, the data checked *)
Definition AH21 (Iend : dstate -> Prop) (rf : rfinal) (vR vs vt vih : val) (gv : globals) (z1 : zfields)
    (L1 : live) : environ -> mpred :=
  PROP (rf_ok Iend vR rf; rf_hset rf = 1; gz_end rf (l_h L1); hdr_mode (i_mode (l_s L1)) = false;
        i_head (l_s L1) = true; l_headp L1 = vih; l_hsh L1 = Tsh)
  LOCAL (lvar _R t_drun vR; lvar _s t_strmL vs; lvar _t t_strmL vt; lvar _ih t_gzhL vih; gvars gv)
  SEP (istream gv Tsh vt z1 (Some L1); head_mem6 L1; rm_htoks rf (l_xb L1) (l_nb L1) (l_cb L1);
       rm_dside rf vR; data_at_ Tsh t_strmL vs; mem_mgr gv; Rm gv; zfuncs gv; TT).

(** ** Memory lemmas *)

Definition rm_head_tuple : Type :=
  (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * val))))))))))))%type.

Lemma rm_head_cs sh (v : rm_head_tuple) q :
  @data_at Zlib.units.Inflate.CS sh Zlib.proof.inflate.Rep.t_head v q = @data_at CS sh t_gzhL v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.

Lemma rm_head_to_undef sh (v : rm_head_tuple) q :
  @data_at Zlib.units.Inflate.CS sh Zlib.proof.inflate.Rep.t_head v q |-- @data_at_ CS sh t_gzhL q.
Proof. rewrite rm_head_cs. apply data_at_data_at_. Qed.

(* the gz_header ih while the stream holds it: the local's memory at a return *)
Lemma rm_head6_ret L vih :
  i_head (l_s L) = true -> l_headp L = vih -> l_hsh L = Tsh -> head_mem6 L |-- data_at_ Tsh t_gzhL vih * TT.
Proof.
  intros Hh Hp Hs. unfold head_mem6. rewrite Hh, Hp, Hs.
  rewrite !sepcon_assoc. rewrite distrib_orp_sepcon. apply orp_left.
  - unfold head_rep. sep_apply rm_head_to_undef. cancel.
  - unfold head_rep6, head_rep6p. Intros. Intros vt vtm vxf vos vxl vhc lx ln lc.
    sep_apply rm_head_to_undef. cancel.
Qed.

(** ** inflate()'s model keeps i_head (as inflate_header/IHMainCall.v) *)
Definition rmh_om (o : Zlib.proof.inflate.Model.iout) : mst :=
  match o with Zlib.proof.inflate.Model.IBrk m => m | Zlib.proof.inflate.Model.IRet _ m => m end.

Lemma rmh_step_head flush fx dx m :
  i_head (m_s (rmh_om (Zlib.proof.inflate.Model2.stepf2 flush fx dx m))) = i_head (m_s m).
Proof.
  destruct (Z_le_gt_dec Zlib.proof.inflate.Model.HEAD (i_mode (m_s m)));
  [destruct (Z_le_gt_dec (i_mode (m_s m)) Zlib.proof.inflate.Model.BAD) |].
  - pose proof (Zlib.proof.uncompr.URunFrame.step2_ok flush fx dx _ (Zlib.proof.uncompr.URunFrame.fast_fr fx dx) m
                  ltac:(unfold Zlib.proof.uncompr.URunFrame.vmode; lia)) as S.
    unfold Zlib.proof.inflate.Model2.stepf2.
    destruct (Zlib.proof.inflate.Model2.step2 _ _ _ _ m); simpl in *;
      unfold Zlib.proof.uncompr.URunFrame.fr in S; tauto.
  - unfold Zlib.proof.inflate.Model2.stepf2, Zlib.proof.inflate.Model2.step2, Zlib.proof.inflate.Model.m_mode.
    repeat match goal with |- context [if Z.eqb ?a ?b then _ else _] =>
      let E := fresh "E" in destruct (Z.eqb a b) eqn:E;
      [apply Z.eqb_eq in E; rewrite E in *; exfalso; compute in l, g; first [congruence | tauto] | ] end;
    try match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
  - unfold Zlib.proof.inflate.Model2.stepf2, Zlib.proof.inflate.Model2.step2, Zlib.proof.inflate.Model.m_mode.
    repeat match goal with |- context [if Z.eqb ?a ?b then _ else _] =>
      let E := fresh "E" in destruct (Z.eqb a b) eqn:E;
      [apply Z.eqb_eq in E; rewrite E in *; exfalso; compute in g; first [congruence | tauto] | ] end;
    try match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.

Lemma rmh_loop_head flush fx dx m o :
  Zlib.proof.inflate.Model2.loop2 flush fx dx m o -> i_head (m_s (rmh_om o)) = i_head (m_s m).
Proof.
  induction 1 as [m r m' E|m m' E Lv|m m' o E Lv L IH].
  - pose proof (rmh_step_head flush fx dx m) as S. rewrite E in S. exact S.
  - pose proof (rmh_step_head flush fx dx m) as S. rewrite E in S. exact S.
  - pose proof (rmh_step_head flush fx dx m) as S. rewrite E in S. simpl in S. rewrite IH, S. reflexivity.
Qed.

Lemma rmh_run_head flush z L inp res :
  Zlib.proof.inflate.Model2.run2 flush lenfix_list distfix_list (m_init z L inp) res ->
  i_head (m_s (r_m res)) = i_head (l_s L).
Proof.
  intros Hrun. destruct Hrun as (o2 & Lp & R).
  pose proof (rmh_loop_head _ _ _ _ _ Lp) as Hh.
  replace (i_head (m_s (m_init z L inp))) with (i_head (l_s L)) in Hh
    by (unfold m_init; simpl; destruct (_ =? _); reflexivity).
  destruct o2 as [m | r0 m]; simpl in Hh.
  - destruct R.
    + simpl. exact Hh.
    + destruct (Zlib.proof.uncompr.URunFrame.leave_fin_fr flush m) as (_ & _ & _ & D & _). rewrite D. exact Hh.
  - subst res. simpl. exact Hh.
Qed.
