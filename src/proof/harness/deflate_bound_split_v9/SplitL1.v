(* Law deflate_bound_split, main: the loop body up to the NULL check of ib / ob (statements 0..10 of lbody: the draws, the assumes, lim, ain, exact_copy, exact_space, if (ib == NULL || ob == NULL) return 0) (SplitKit.v). *)
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

(* after if (!finishing) ..: lim and finishing chosen *)
Definition L1P (sp hp vosn : val) (gv : globals) (bs : bsetup) (b pos : Z) (fin : bool) (s : dstate)
    (f : sfields) (nlim aout fsel lim : Z) (fin' : bool) : environ -> mpred :=
  PROP (pos <= lim <= bd_n (bs_d bs); fin = true -> fin' = true; fin' = true -> lim = bd_n (bs_d bs))
  LOCAL (temp _lim (vi lim); temp _fsel (Vint (Int.repr fsel));
   temp _aout (Vint (Int.repr aout)); temp _nlim (Vint (Int.repr nlim));
   temp _data (bd_datap (bs_d bs)); temp _n (vi (bd_n (bs_d bs)));
   temp _bound (vl b); temp _pos (vi pos);
   temp _finishing (vi (fin_flag fin')); lvar _osnap (tptr tuchar) vosn;
   lvar _h t_gzh hp; lvar _s t_strm sp; gvars gv)
  SEP (live sp hp gv bs true s f; obj (bd_datap (bs_d bs)) (bs_data bs);
   data_at_ Tsh (tptr tuchar) vosn; mem_mgr gv; deflate_globals gv; TT).

Lemma l1_vp n (v : list val) p Q :
  malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) v p * Q |-- valid_pointer p.
Proof.
  destruct (zlt 0 n).
  - apply sepcon_valid_pointer1. apply sepcon_valid_pointer2.
    apply data_at_valid_ptr; auto. simpl. rep_lia.
  - apply sepcon_valid_pointer1. apply sepcon_valid_pointer1.
    apply malloc_token_valid_pointer. simpl. rep_lia.
Qed.

Ltac l1_tc_null :=
  apply denote_tc_test_eq_split; [ | apply valid_pointer_zero64; auto ];
  eapply derives_trans; [ | eapply (l1_vp _ _ _ TT) ]; solve [cancel].

Ltac l1_ret HM HOB HGZ :=
  forward; Exists (Int.repr 0); entailer!;
  match goal with |- context [live ?sp ?hp ?gv ?bs true ?s ?f] =>
    sep_apply (HM sp hp gv bs true s f HOB HGZ) end;
  repeat (sep_apply data_at_data_at_); cancel.

Lemma part_l1 {Espec : OracleKind} Bpre Brun sp hp vosn gv bs b pos fin s f :
  split_mem_ok ->
  (forall ci, semax Delta_m (B1 Bpre Brun sp hp vosn gv bs b pos fin s f ci) lsuf11
                (Rbody Bpre Brun sp hp vosn gv bs b)) ->
  semax Delta_m (J Bpre Brun sp hp vosn gv bs b pos fin s f) lbody (Rbody Bpre Brun sp hp vosn gv bs b).
Proof.
  intros HM HB.
  unfold J, lbody, Rbody, Rm_ret, POST_m, loop_locals. Intros.
  assert (HJ : J_ok Bpre Brun bs b pos fin s f) by assumption.
  unfold J_ok in H. destruct H as [HBS [HBF [HOB [HBR [HGZ [HMS [HPOS HBD]]]]]]].
  assert (HDn : bd_n (bs_d bs) <= 1048576) by (unfold bs_ok, bd_ok in HBS; tauto).
  assert (HDl : Zlength (bs_data bs) = bd_n (bs_d bs)) by (unfold bs_ok in HBS; tauto).
  assert (HDb : bytes (bs_data bs)) by (unfold bs_ok in HBS; tauto).
  assert (HDp : isptr (bd_datap (bs_d bs))) by (unfold bs_ok, bd_ok in HBS; tauto).
  abbreviate_semax.
  forward.
  forward_call tt. Intros nlim.
  forward_call tt. Intros aout. forward_call tt. Intros fsel.
  forward_call (Int.repr (if aout <=? 1048576 then 1 else 0)).
  { entailer!. arg_cmp. }
  Intros. assumed. apply Z.leb_le in E. rename E into HAo.
  forward.
  forward_if (EX lim : Z, EX fin' : bool, L1P sp hp vosn gv bs b pos fin s f nlim aout fsel lim fin').
  { (* not finishing *)
    assert (Hf : fin = false) by (destruct fin; [ discriminate | reflexivity ]). subst fin.
    forward_if (temp _t'44 (vi (if ((pos <=? nlim) && (nlim <=? bd_n (bs_d bs)))%bool then 1 else 0))).
    { forward. entailer!. arg_cmp. }
    { forward. entailer!. arg_cmp. }
    forward_call (Int.repr (if ((pos <=? nlim) && (nlim <=? bd_n (bs_d bs)))%bool then 1 else 0)).
    Intros. assumed. apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1, E2.
    forward.
    forward_if.
    { forward. forward. Exists (bd_n (bs_d bs)) true. unfold L1P. entailer!. }
    { forward. Exists nlim false. unfold L1P. entailer!. } }
  { (* finishing *)
    assert (Hf : fin = true) by (destruct fin; [ reflexivity | contradiction ]). subst fin.
    forward. Exists (bd_n (bs_d bs)) true. unfold L1P. entailer!. }
  Intros lim fin'. unfold L1P. Intros.
  forward.
  unfold obj. Intros.
  forward_call (offset_val pos (bd_datap (bs_d bs)), Ews, bd_datap (bs_d bs), pos, Zlength (bs_data bs),
                map vi (bs_data bs), lim - pos, sublist pos lim (bs_data bs), gv).
  { entailer!. simpl.
    destruct (bd_datap (bs_d bs)); try contradiction. unfold vi; simpl. f_equal. f_equal. f_equal.
    rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_intu, Ptrofs.of_int.
    rewrite Int.unsigned_repr by rep_lia. reflexivity. }
  { unfold cbuf_ok. split; [reflexivity | ]. split; [auto | ]. split; [lia | ]. split; [lia | ].
    split; [rewrite Zlength_sublist by lia; lia | ]. split.
    - unfold is_bytes. apply Forall_sublist. eapply Forall_impl; [ | exact HDb ]. simpl; intros; rep_lia.
    - replace (pos + (lim - pos)) with lim by lia. unfold bytes_rep. rewrite sublist_map. reflexivity. }
  Intros ib.
  forward_call (aout, vosn, Tsh, gv).
  Intros vret. destruct vret as [[vob q] obs]. cbn [fst snd].
  Intros.
  destruct (eq_dec ib nullval) as [Hib | Hib].
  { (* ib = NULL: return 0 *)
    forward_if (temp _t'47 (vi 1)).
    { forward. entailer!. }
    { forward. entailer!. }
    forward_if.
    { l1_ret HM HOB HGZ. }
    { match goal with H : Int.repr 1 = Int.zero |- _ => discriminate H end. } }
  Intros.
  destruct (eq_dec vob nullval) as [Hob | Hob].
  { (* ob = NULL: return 0 *)
    forward_if (temp _t'47 (vi 1)).
    { contradiction. }
    { forward. entailer!. }
    forward_if.
    { l1_ret HM HOB HGZ. }
    { match goal with H : Int.repr 1 = Int.zero |- _ => discriminate H end. } }
  Intros.
  forward_if (temp _t'47 (vi 0)).
  { contradiction. }
  { forward. entailer!. destruct vob; try contradiction; reflexivity. }
  forward_if.
  { match goal with H : Int.repr 0 <> Int.zero |- _ => contradiction H; reflexivity end. }
  cbn [fst snd] in *.
  eapply semax_pre; [ | apply (HB (mkCI lim aout fin' ib vob q obs)) ].
  unfold B1, B_locals, loop_locals, iobjs, obj, ci_inb.
  cbn [ci_lim ci_aout ci_fin ci_ib ci_ob ci_q ci_obs app].
  rewrite Zlength_sublist by lia. subst aout.
  unfold bytes_rep. rewrite sub_repr.
  entailer!.
  unfold ci_ok; cbn [ci_lim ci_aout ci_fin ci_ib ci_ob ci_q ci_obs].
  split; [ exact HJ | ]. split; [ lia | ]. split; [ exact H3 | ]. split; [ exact H4 | ].
  split; [ rep_lia | ]. split; [ reflexivity | ].
  split; [ unfold bytes; eapply Forall_impl; [ | exact H6 ]; simpl; intros; rep_lia | ].
  split; [ match goal with H : malloc_compatible _ ib |- _ => clear - H; destruct ib; simpl in *; tauto end | ].
  split; [ match goal with H : malloc_compatible _ vob |- _ => clear - H; destruct vob; simpl in *; tauto end | ].
  match goal with H : malloc_compatible _ q |- _ => clear - H; destruct q; simpl in *; tauto end.
Qed.
