(* Law inflate_header, main: the loop body up to the null check of ib / ob (IHMainKit.v seg_loop, positions
   L0 .. L9): the draws of nlim, aout, flush, stop, the two gp_assume, ain = nlim - pos,
   ib = exact_copy(src + pos, ain), ob = exact_space(aout, &osnap), `if (ib == NULL || ob == NULL) return 0;`;
   then segL10 (given).  As inflate_check/IKMainPre.v. *)
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
Local Open Scope logic.

Ltac pre_infeas := exfalso; first [ match goal with H: ?a <> ?b |- _ => solve [apply H; reflexivity] end
                              | match goal with H: _ |- _ => solve [discriminate H] end
                              | contradiction
                              | lia ].

Lemma ih_src_len_bound g: ih_ok g -> 0 <= Zlength (ih_src g) <= 2 ^ 20.
Proof.
  intros (_ & _ & _ & _ & Hx & _ & Hn & _ & Hc & _).
  pose proof (Zlength_nonneg (g_xf g)). pose proof (Zlength_nonneg (g_nf g)). pose proof (Zlength_nonneg (g_cf g)).
  unfold ih_src, ih_hdr.
  destruct (fl g 2), (fl g 4), (fl g 8), (fl g 16); autorewrite with sublist; simpl; lia.
Qed.

Lemma ih_src_bytes g: ih_ok g -> is_bytes (ih_src g).
Proof.
  intros (Hf & Hm & Hx & Ho & Hxl & Hxb & Hnl & Hnb & Hcl & Hcb & _).
  assert (Hst: 0 <= ih_stored g <= 65535).
  { unfold ih_stored. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
    change (Z.ones 16) with 65535.
    match goal with |- context [?a mod ?m] => pose proof (Z.mod_pos_bound a m ltac:(lia)) end. lia. }
  pose proof (Zlength_nonneg (g_xf g)).
  assert (Hnz: forall l, Forall (fun b => 0 < b <= 255) l -> is_bytes l).
  { intros l Hl. unfold is_bytes. eapply Forall_impl; [ | exact Hl]. intros a Ha. simpl in Ha. rep_lia. }
  unfold ih_src, ih_hdr, is_bytes.
  repeat rewrite Forall_app.
  repeat split.
  - repeat constructor; try rep_lia;
      match goal with |- context [?a mod 256] => pose proof (Z.mod_pos_bound a 256 ltac:(lia)); rep_lia end.
  - destruct (fl g 4); [ | constructor]. apply Forall_app. split; [ | exact Hxb].
    repeat constructor; try (pose proof (Z.mod_pos_bound (Zlength (g_xf g)) 256); rep_lia);
      try (apply Z.div_pos; lia);
      match goal with |- ?a / 256 <= _ => cut (a / 256 < 256); [rep_lia | apply Z.div_lt_upper_bound; lia] end.
  - destruct (fl g 8); [ | constructor]. apply Forall_app. split; [apply Hnz; exact Hnb | repeat constructor; rep_lia].
  - destruct (fl g 16); [ | constructor]. apply Forall_app. split; [apply Hnz; exact Hcb | repeat constructor; rep_lia].
  - destruct (fl g 2); [ | constructor].
    repeat constructor; try (pose proof (Z.mod_pos_bound (ih_stored g) 256); rep_lia);
      try (apply Z.div_pos; lia);
      match goal with |- ?a / 256 <= _ => cut (a / 256 < 256); [rep_lia | apply Z.div_lt_upper_bound; lia] end.
  - repeat constructor; rep_lia.
  - unfold Zrepeat. simpl. repeat constructor; rep_lia.
Qed.

Lemma pre_ok {Espec: OracleKind} I gv V g b P h0 H Fr (Inv: environ -> mpred) pos z L:
  ih_glob I g b P h0 H -> I g (b_w b) h0 pos z L -> 0 <= pos <= Zlength (ih_src g) -> ih_Lok V H L ->
  (forall ain aout flush stop ibp obp q bs,
     ih_buf_facts I V g b P h0 H pos z L ain aout flush stop ibp obp q bs ->
     semax Delta_m (ih_buf gv V g b P h0 H Fr pos z L ain aout flush stop ibp obp q bs) segL10 (ih_PL Inv)) ->
  semax Delta_m (ih_at gv V g b P h0 H Fr pos z L) seg_loop (ih_PL Inv).
Proof.
  intros G HI Hpos HL K.
  pose proof G as G'. destruct G' as (CF & F53 & _).
  assert (Hlive: i_head (l_s L) = true) by (apply (proj1 (ihf_live I CF g (b_w b) h0 pos z L HI))).
  pose proof HL as HL'. destruct HL' as (Hhp & Hhs & _).
  pose proof (ih_src_len_bound g (proj1 F53)) as Hsl.
  pose proof F53 as F53'. destruct F53' as (_ & _ & _ & _ & _ & _ & _ & _ & Psrc & _).
  destruct V as [vs vh vxs vns vcs vosn]; simpl in *.
  unfold ih_at, seg_loop, Delta_m, Gmain, ih_PL, POST_b, POST_m. simplify_func_tycontext. abbreviate_semax.
  cbn [v_s_ v_h_ v_xs_ v_ns_ v_cs_ v_osn_].
  forward_call tt. Intros nlim.
  forward_call tt. Intros aout.
  forward_call tt. Intros flu.
  forward_call tt. Intros stop.
  assert (Ef: Int.repr flu = Int.repr (Int.signed (Int.repr flu))) by (rewrite Int.repr_signed; auto).
  rewrite Ef. clear Ef. set (flush := Int.signed (Int.repr flu)).
  assert (Hfl: Int.min_signed <= flush <= Int.max_signed) by apply Int.signed_range. clearbody flush.
  ifpost _t'45 (Int.repr (if andb (pos <=? nlim) (nlim <=? Zlength (ih_src g)) then 1 else 0)).
  { forward. entailer!. arg_cmp. }
  { forward. entailer!. arg_cmp. }
  forward_call (Int.repr (if andb (pos <=? nlim) (nlim <=? Zlength (ih_src g)) then 1 else 0)).
  assumed. apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
  forward_call (Int.repr (if aout <=? 2 ^ 20 then 1 else 0)).
  { entailer!. arg_cmp. }
  assumed. apply Z.leb_le in E.
  forward.
  rewrite sub_repr. set (ain := nlim - pos).
  assert (Hain: 0 <= ain /\ pos + ain <= Zlength (ih_src g)) by (subst ain; lia). clearbody ain.
  forward_call (offset_val pos (p_src P), Ews, p_src P, pos, Zlength (ih_src g), bytes_rep (ih_src g), ain,
                sublist pos (pos + ain) (ih_src g), gv).
  { rewrite ih_bytes_adler_cs. cancel. }
  { apply Zlib.proof.adler32.Ptr.cbuf_ok_slice; auto; try lia; apply ih_src_bytes, (proj1 F53). }
  Intros ibp.
  forward_call (aout, vosn, Tsh, gv).
  { rewrite ih_ptr_adler_cs_. cancel. }
  Intros vret. destruct vret as [[obp q] bs]. simpl fst in *. simpl snd in *.
  rewrite ih_ptr_adler_cs.
  match goal with Hb: Zlength bs = aout |- _ => rename Hb into Hbs end. subst aout.
  destruct (eq_dec ibp nullval) as [IN|IN].
  { subst ibp.
    ifpost _t'48 (Int.repr 1). { forward. entailer!. } { pre_infeas. }
    forward_if. { forward. Exists (Int.repr 0). sep_apply ih_istream_to_undef.
                  sep_apply (ih_head_mem_undef L (l_headp L)); auto. entailer!. }
    { pre_infeas. } }
  Intros.
  rewrite (ih_bytes_adler_cs Ews ain _ ibp), (ih_tok_adler_cs Ews ain ibp).
  destruct (eq_dec obp nullval) as [ON|ON].
  { subst obp.
    ifpost _t'48 (Int.repr 1).
    { pre_infeas. }
    { forward. entailer!. }
    forward_if. { forward. Exists (Int.repr 0). sep_apply ih_istream_to_undef.
                  sep_apply (ih_head_mem_undef L (l_headp L)); auto. entailer!. }
    { pre_infeas. } }
  Intros.
  rewrite (ih_bytes_adler_cs Ews (Zlength bs) _ obp),
    (ih_tok_adler_cs Ews (Zlength bs) obp), (ih_bytes_adler_cs Ews (Zlength bs) _ q), (ih_tok_adler_cs Ews (Zlength bs) q).
  assert_PROP (isptr obp /\ isptr ibp /\ isptr q) as Pob by entailer!. destruct Pob as (Pob & Pib & Pq).
  ifpost _t'48 (Int.repr 0).
  { pre_infeas. }
  { forward. entailer!. destruct obp; try contradiction; reflexivity. }
  forward_if.
  { pre_infeas. }
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply (K ain (Zlength bs) flush stop ibp obp q bs)].
  2: { unfold ih_buf_facts. split; [exact G | ]. split; [exact HI | ]. split; [exact HL | ].
       repeat split; auto; rep_lia. }
  unfold ih_buf. cbn [v_s_ v_h_ v_xs_ v_ns_ v_cs_ v_osn_]. entailer!.
Qed.
