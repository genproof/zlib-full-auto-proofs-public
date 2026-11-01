(* Law deflate_bound_split, main: the four stores into s and r = deflate(&s, finishing ? Z_FINISH : Z_NO_FLUSH) (statements 11..15 of lbody) (SplitKit.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.harness.x_deflate_bound_split.code.
Require Import Zlib.proof.harness.deflate_bound_split_v9.SplitMain Zlib.proof.harness.deflate_bound_split_v9.SplitKit.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

(* the call's witness that next_out is weakly valid: the 0-byte object's token *)
Definition wtok (n : Z) : wvw := if n =? 0 then WVtok (tarray tuchar 0) else WVnone.
Definition tok_rest (n : Z) (p : val) : mpred :=
  if n =? 0 then emp else malloc_token Ews (tarray tuchar n) p.

Lemma tok_split n p :
  malloc_token Ews (tarray tuchar n) p = tok_rest n p * wv_at (wtok n) p.
Proof.
  unfold tok_rest, wtok, wv_at. destruct (n =? 0) eqn:E.
  - apply Z.eqb_eq in E. subst n. rewrite emp_sepcon. reflexivity.
  - rewrite sepcon_emp. reflexivity.
Qed.

Lemma wtok_ok' n : n = 0 -> wv_ok (wtok n).
Proof. intros ->. simpl. reflexivity. Qed.

Lemma obj_unf (q : val) (l : list Z) :
  obj q l = malloc_token Ews (tarray tuchar (Zlength l)) q * data_at Ews (tarray tuchar (Zlength l)) (map vi l) q.
Proof. reflexivity. Qed.

Lemma obj_out (q : val) (l : list Z) :
  obj q l = tok_rest (Zlength l) q * wv_at (wtok (Zlength l)) q *
            data_at Ews (tarray tuchar (Zlength (map vi l))) (map vi l) q.
Proof. unfold obj. rewrite tok_split, Zlength_map. reflexivity. Qed.

Lemma l2_af_fold (sp ib : val) (inb : list Z) (ob : val) (obs : list Z) (lim pos aout ti to : Z) (m : val) (ad : Z) :
  isptr ib -> Zlength inb = lim - pos -> Zlength obs = aout ->
  u32_ok (lim - pos) -> u64_ok ti -> u32_ok aout -> u64_ok to -> u64_ok ad ->
  field_at Ews t_strm (DOT deflate.code._next_in) ib sp *
  field_at Ews t_strm (DOT deflate.code._avail_in) (Vint (Int.repr (lim - pos))) sp *
  field_at Ews t_strm (DOT deflate.code._total_in) (vl ti) sp *
  field_at Ews t_strm (DOT deflate.code._next_out) ob sp *
  field_at Ews t_strm (DOT deflate.code._avail_out) (Vint (Int.repr aout)) sp *
  field_at Ews t_strm (DOT deflate.code._total_out) (vl to) sp *
  field_at Ews t_strm (DOT deflate.code._msg) m sp *
  field_at Ews t_strm (DOT deflate.code._adler) (vl ad) sp
  |-- api_fields sp (offset_val 0 ib) (Zlength inb) ti ob (Zlength (map vi obs)) to m ad.
Proof.
  intros Pib Hl Ho. intros. rewrite isptr_offset_val_zero by auto. rewrite Zlength_map, Hl, Ho.
  unfold api_fields. entailer!.
Qed.

Lemma dstream_sp_fold lvl os strmp ghp sp gv :
  dstream_sp lvl os strmp ghp sp gv |-- dstream lvl os strmp ghp gv.
Proof. rewrite dstream_sp_eq. Exists sp. cancel. Qed.

Lemma hdr_at_gz s s' ghp hx :
  d_gzhead s' = d_gzhead s -> hdr_at (Some s) ghp hx = hdr_at (Some s') ghp hx.
Proof. intros E. unfold hdr_at. rewrite E. reflexivity. Qed.

Lemma part_l2 {Espec : OracleKind} Bpre Brun sp hp vosn gv bs b pos fin s f ci :
  (forall s' z' code msgv',
     semax Delta_m (B2 Bpre Brun sp hp vosn gv bs b pos fin s f ci s' z' code msgv') lsuf16
       (Rbody Bpre Brun sp hp vosn gv bs b)) ->
  semax Delta_m (B1 Bpre Brun sp hp vosn gv bs b pos fin s f ci) lsuf11 (Rbody Bpre Brun sp hp vosn gv bs b).
Proof.
  intros HK. unfold lsuf11, B1.
  Intros.
  unfold live, sf_at, api_fields. Intros.
  unfold B_locals, loop_locals; simpl app.
  pose proof H as Hci.
  destruct Hci as [HJ [Hlim [Hfin [Hfl [Haout [HOl [HOb [Pib [Pob Pq]]]]]]]]].
  pose proof HJ as HJ'.
  destruct HJ' as [BS [BF [HOB [HR [Hgz [Hmsg [Hpos Hb]]]]]]].
  pose proof BS as BS'.
  destruct BS' as [BD [Hdl [_ [_ [_ [_ [Hdb _]]]]]]].
  assert (Hn : 0 <= bd_n (bs_d bs) <= 1048576) by (destruct BD as (_ & _ & _ & _ & _ & Hn & _); exact Hn).
  assert (Hinb : Zlength (ci_inb bs pos ci) = ci_lim ci - pos)
    by (unfold ci_inb; rewrite Zlength_sublist; lia).
  assert (Hinbb : bytes (ci_inb bs pos ci)) by (unfold ci_inb; apply Forall_sublist; auto).
  destruct (bf_split _ _ BF (bd_n (bs_d bs)) b pos fin s (sf_tin f) (sf_tout f) (sf_adler f)
              (ci_inb bs pos ci) (ci_aout ci) (ci_flush ci) (sf_msg f))
    as (s' & z' & code & Hrun & Hgz' & Hcode & Hain & Hto & HR');
    auto; try lia.
  { unfold ci_flush. destruct (ci_fin ci); auto. }
  { intros ->. unfold ci_flush. rewrite Hfin; auto. }
  { unfold ci_flush. intros E. destruct (ci_fin ci) eqn:Ef; [rewrite Hinb; rewrite Hfl by auto; lia|].
    unfold Z_NO_FLUSH, Z_FINISH in E. lia. }
  forward. forward. forward. forward.
  forward_if (temp _t'48 (vi (ci_flush ci))).
  { forward. unfold ci_flush. match goal with E : ci_fin ci = _ |- _ => rewrite E end.
    destruct (Rbody Bpre Brun sp hp vosn gv bs b) as [Rn Rb Rc Rr]. cbn [RA_normal]. entailer!. }
  { forward. unfold ci_flush. match goal with E : ci_fin ci = _ |- _ => rewrite E end.
    destruct (Rbody Bpre Brun sp hp vosn gv bs b) as [Rn Rb Rc Rr]. cbn [RA_normal]. entailer!. }
  rewrite dstream_sp_eq. Intros spp.
  assert (U : u32_ok (ci_lim ci - pos)) by (unfold u32_ok; rep_lia).
  assert (U2 : u32_ok (ci_aout ci)) by (unfold u32_ok; rep_lia).
  unfold iobjs. rewrite (obj_unf (ci_ib ci)), (obj_out (ci_ob ci)).
  sep_apply (l2_af_fold sp (ci_ib ci) (ci_inb bs pos ci) (ci_ob ci) (ci_obs ci) (ci_lim ci) pos (ci_aout ci)
               (sf_tin f) (sf_tout f) (sf_msgv f) (sf_adler f) Pib Hinb HOl U H1 U2 H3 H4).
  repeat flatten_sepcon_in_SEP.
  forward_call (Some s, sp, ghp_of hp bs true, spp, hx_of bs, ci_ib ci, Ews, ci_inb bs pos ci, 0,
                Zlength (ci_inb bs pos ci), sf_tin f, ci_ob ci, map vi (ci_obs ci),
                wtok (Zlength (ci_obs ci)), sf_tout f, sf_msgv f, sf_msg f, sf_adler f,
                ci_flush ci, (Some s', z', code), gv).
  { split; [| split; [| split]].
    - intros E; apply wtok_ok'. rewrite Zlength_map in E. auto.
    - unfold s32_ok, ci_flush, Z_FINISH, Z_NO_FLUSH. destruct (ci_fin ci); rep_lia.
    - unfold strm_ranges, zmk; simpl. rewrite Zlength_map, HOl, Hinb.
      unfold bytes in Hinbb. rewrite Zlength_nil. unfold u32_ok, u64_ok in *.
      repeat split; auto; try rep_lia.
    - exists (fun x => x). split; [ apply ef_ok_id | ].
      unfold on_state, c_on_state. rewrite c_deflate_g_id. rewrite Zlength_map, HOl.
      change (zmk ?a ?b ?c ?d ?e ?f ?g ?h) with (zcall a b c d e f g h). rewrite Hrun. reflexivity. }
  simpl fst; simpl snd.
  Intros msgv'.
  forward.
  eapply semax_pre; [| apply (HK s' z' code msgv')].
  unfold B2, live, sf_at, sf_after, iobjs. cbn [sf_nin sf_ain sf_tin sf_nout sf_aout sf_tout sf_msg sf_msgv sf_adler].
  rewrite (hdr_at_gz s s' _ _ Hgz').
  sep_apply (dstream_sp_fold 2 (Some s') sp (ghp_of hp bs true) spp gv).
  rewrite (obj_unf (ci_ib ci)), (tok_split (ci_aout ci)).
  rewrite Zlength_map, HOl.
  assert (Hst : step_ok Brun bs b pos s f ci s' z' code) by (unfold step_ok; auto 10).
  unfold B_locals, loop_locals; simpl app.
  entailer!.
Qed.
