(* Law inflate_dict, main encoder half: a back-reference of a fixed block (with the hist loop) (statement in ITEncKit.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessRef Zlib.proof.adler32.HarnessBytes
               Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_common.DRefSpec.
Require Import Zlib.proof.harness.inflate_dict.ITLawCS Zlib.proof.harness.inflate_dict.ITGlobals
               Zlib.proof.harness.inflate_dict.ITFacts Zlib.proof.harness.inflate_dict.ITMainKit
               Zlib.proof.harness.inflate_dict.ITEncKit.
Require Import Zlib.harness.x_inflate_dict.code.
Require Import Zlib.proof.crc32.Spec.

(* ---------------------------------------------------------------------------------------------- *)
(* Pure facts                                                                                     *)

Lemma lz_copy_S n d out :
  lz_copy (S n) d out = lz_copy n d out ++ [Znth (Zlength (lz_copy n d out) - d) (lz_copy n d out)].
Proof.
  revert out; induction n; intros out.
  - reflexivity.
  - change (lz_copy (S (S n)) d out) with (lz_copy (S n) d (out ++ [Znth (Zlength out - d) out])).
    rewrite IHn. reflexivity.
Qed.

Lemma Zlength_lz_copy n d out : Zlength (lz_copy n d out) = Zlength out + Z.of_nat n.
Proof.
  induction n.
  - simpl. lia.
  - rewrite lz_copy_S, Zlength_app, IHn, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma is_bytes_lz_copy n d out :
  is_bytes out -> 1 <= d <= Zlength out -> is_bytes (lz_copy n d out).
Proof.
  intros Hb Hd. induction n.
  - auto.
  - rewrite lz_copy_S. unfold is_bytes in *. apply Forall_app. split; auto.
    constructor; [ | constructor].
    rewrite Zlength_lz_copy in *. apply Forall_Znth; auto. rewrite Zlength_lz_copy. lia.
Qed.

Lemma len_code_range len : 0 <= len_code len <= 28.
Proof.
  unfold len_code. destruct (len =? 258); [lia|].
  pose proof (Zlength_nonneg (filter (fun b => b <=? len) (sublist 1 28 len_base))).
  assert (Zlength (filter (fun b => b <=? len) (sublist 1 28 len_base)) <= Zlength (sublist 1 28 len_base)).
  { rewrite !Zlength_correct. apply Nat2Z.inj_le. apply filter_length_le. }
  change (Zlength (sublist 1 28 len_base)) with 27 in H0. lia.
Qed.

Lemma dist_code_range dist : 0 <= dist_code dist <= 29.
Proof.
  unfold dist_code.
  pose proof (Zlength_nonneg (filter (fun b => b <=? dist) (sublist 1 30 dist_base))).
  assert (Zlength (filter (fun b => b <=? dist) (sublist 1 30 dist_base)) <= Zlength (sublist 1 30 dist_base)).
  { rewrite !Zlength_correct. apply Nat2Z.inj_le. apply filter_length_le. }
  change (Zlength (sublist 1 30 dist_base)) with 29 in H0. lia.
Qed.

Lemma fixed_ll_nz i : 0 <= i < 288 -> Znth i fixed_ll <> 0.
Proof.
  intros Hb.
  assert (Hc: forallb (fun i => negb (Znth i fixed_ll =? 0)) (map Z.of_nat (seq 0 288)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hc. specialize (Hc i).
  assert (Hin: In i (map Z.of_nat (seq 0 288))).
  { apply in_map_iff. exists (Z.to_nat i). split; [lia | apply in_seq; lia]. }
  specialize (Hc Hin). apply negb_true_iff, Z.eqb_neq in Hc. auto.
Qed.

Lemma fixed_dl_nz i : 0 <= i < 32 -> Znth i fixed_dl <> 0.
Proof. intros Hi. unfold fixed_dl. rewrite Znth_repeat' by (simpl; lia). lia. Qed.

Lemma Zlength_fixed_ll : Zlength fixed_ll = 288.
Proof. reflexivity. Qed.
Lemma Zlength_fixed_dl : Zlength fixed_dl = 32.
Proof. reflexivity. Qed.

(* the history-and-data after i bytes of the copy: dict, then the data so far *)
Definition hcopy (h D: list Z) (dist i: Z) : list Z :=
  sublist (Zlength h) (Zlength h + Zlength D + i) (lz_copy (Z.to_nat i) dist (h ++ D)).

Lemma hcopy_eq h D dist i : 0 <= i -> h ++ hcopy h D dist i = lz_copy (Z.to_nat i) dist (h ++ D).
Proof.
  intros Hi. unfold hcopy.
  destruct (lz_copy_prefix (Z.to_nat i) dist (h ++ D)) as [l El].
  assert (Hl: Zlength (lz_copy (Z.to_nat i) dist (h ++ D)) = Zlength h + Zlength D + i)
    by (rewrite Zlength_lz_copy, Zlength_app; lia).
  rewrite El in *. rewrite <- app_assoc in *. rewrite Zlength_app in Hl.
  pose proof (Zlength_nonneg h).
  rewrite sublist_app2 by lia. rewrite Z.sub_diag.
  rewrite sublist_same by lia. auto.
Qed.

Lemma Zlength_hcopy h D dist i : 0 <= i -> Zlength (hcopy h D dist i) = Zlength D + i.
Proof.
  intros Hi. pose proof (hcopy_eq h D dist i Hi) as E.
  apply (f_equal (@Zlength Z)) in E. rewrite Zlength_app, Zlength_lz_copy, Zlength_app in E. lia.
Qed.

Lemma hcopy_0 h D dist : hcopy h D dist 0 = D.
Proof.
  pose proof (hcopy_eq h D dist 0 ltac:(lia)) as E. simpl in E. apply app_inv_head in E. auto.
Qed.

Lemma hcopy_S h D dist i : 0 <= i ->
  hcopy h D dist (i + 1) = hcopy h D dist i ++ [Znth (Zlength h + Zlength D + i - dist) (h ++ hcopy h D dist i)].
Proof.
  intros Hi. pose proof (hcopy_eq h D dist (i + 1) ltac:(lia)) as E.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) in E by lia.
  rewrite lz_copy_S, <- (hcopy_eq h D dist i Hi), Zlength_app, Zlength_hcopy, <- app_assoc in E by lia.
  apply app_inv_head in E. rewrite E. f_equal. f_equal. f_equal. lia.
Qed.

Lemma is_bytes_hcopy h D dist i : 0 <= i -> is_bytes h -> is_bytes D -> 1 <= dist <= Zlength h + Zlength D ->
  is_bytes (hcopy h D dist i).
Proof.
  intros Hi Hh HD Hd. assert (Hb: is_bytes (h ++ hcopy h D dist i)).
  { rewrite hcopy_eq by auto. apply is_bytes_lz_copy; [apply Forall_app; auto | rewrite Zlength_app; lia]. }
  apply Forall_app in Hb. tauto.
Qed.

Lemma upd_data_sub (dcont: list val) (P: list Z) b :
  Zlength P < Zlength dcont -> sublist 0 (Zlength P) dcont = bytes_rep P ->
  sublist 0 (Zlength (P ++ [b])) (upd_Znth (Zlength P) dcont (Vint (Int.repr b))) = bytes_rep (P ++ [b]).
Proof.
  intros Hl Hs. pose proof (Zlength_nonneg P).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  rewrite (sublist_split 0 (Zlength P) (Zlength P + 1)) by (rewrite ?Zlength_upd_Znth; lia).
  rewrite sublist_upd_Znth_l by lia. rewrite Hs.
  rewrite sublist_len_1 by (rewrite Zlength_upd_Znth; lia). rewrite upd_Znth_same by lia.
  unfold bytes_rep. rewrite map_app. reflexivity.
Qed.

Lemma sym_bits_ref E bs last syms len dist :
  sym_bits E bs last (syms ++ [Ref len dist]) = sym_bits E bs last syms ++ send_one fixed_ll fixed_dl (Ref len dist).
Proof.
  unfold sym_bits. rewrite <- flat_map_app. simpl. rewrite app_nil_r, <- !app_assoc. reflexivity.
Qed.

(* the data after the reference *)
Lemma edata_ref E bs syms len dist : 0 <= len ->
  edata E (bs ++ [Fixed (syms ++ [Ref len dist])]) = hcopy (e_dict E) (edata E (bs ++ [Fixed syms])) dist len.
Proof.
  intros Hl. unfold edata.
  pose proof (expand_data (e_dict E) (bs ++ [Fixed (syms ++ [Ref len dist])])) as E1.
  rewrite expand_fixed_ref, expand_data, <- hcopy_eq in E1 by auto.
  apply app_inv_head in E1. auto.
Qed.

Ltac or_then := match goal with H: (if ?c then 1 else 0) <> 0 |- _ =>
  destruct c; [reflexivity | contradiction H; reflexivity] end.
Ltac or_else := match goal with H: Int.repr (if ?c then 1 else 0) = Int.zero |- _ =>
  destruct c; [exfalso; exact (Int.one_not_zero H) | simpl; arg_cmp] end.

Lemma seg_ref_ok {Espec: OracleKind} : seg_ref_stmt.
Proof.
  intros E bs last syms dcont Post. destruct Post as [Pn Pb Pc Pr]. unfold sym_room. cbv [seg_ref]. Intros.
  forward_call tt. Intros len.
  forward_call tt. Intros dist.
  set (D := edata E (bs ++ [Fixed syms])) in *.
  destruct H3 as (Hdc & HD & HDb & HDs).
  pose proof H as (Hwb & Hfl & Hisel & Hwsel & Hdl & Hdb & Hp1 & Hp2 & Hp3 & Hp4).
  assert (Hmaxd: 2 ^ 8 <= 2 ^ e_wb E <= 2 ^ 15) by (split; apply Z.pow_le_mono_r; lia).
  pose proof (Zlength_nonneg (e_dict E)). pose proof (Zlength_nonneg D).
  ifpost _t'25 (Int.repr (if orb (len <? 3) (258 <? len) then 1 else 0)).
  { forward. entailer!. destruct (Z.ltb_spec len 3); [reflexivity | lia]. }
  { forward. entailer!. destruct (Z.ltb_spec len 3); [lia|]. simpl. arg_cmp. }
  ifpost _t'26 (Int.repr (if orb (orb (len <? 3) (258 <? len)) (dist <? 1) then 1 else 0)).
  { forward. entailer!. or_then. }
  { forward. entailer!. or_else. }
  ifpost _t'27 (Int.repr (if orb (orb (orb (len <? 3) (258 <? len)) (dist <? 1))
                               (Zlength (e_dict E) + Zlength D <? dist) then 1 else 0)).
  { forward. entailer!. or_then. }
  { forward. entailer!. or_else. }
  ifpost _t'28 (Int.repr (if orb (orb (orb (orb (len <? 3) (258 <? len)) (dist <? 1))
                               (Zlength (e_dict E) + Zlength D <? dist)) (2 ^ e_wb E <? dist) then 1 else 0)).
  { forward. entailer!. or_then. }
  { forward. entailer!. or_else. }
  forward_if.
  { forward. unfold sym_inv, sym_at. Exists syms dcont. entailer!. unfold data_ok; auto. }
  match goal with H: Int.repr (if ?c then 1 else 0) = Int.zero |- _ =>
    destruct c eqn:Hc; [exfalso; exact (Int.one_not_zero H) | clear H] end.
  repeat rewrite Bool.orb_false_iff in Hc.
  destruct Hc as ((((Hc1 & Hc2) & Hc3) & Hc4) & Hc5).
  apply Z.ltb_ge in Hc1, Hc2, Hc3, Hc4, Hc5.
  forward_call (Int.repr (if Zlength D + len <=? 2^18 then 1 else 0)).
  { entailer!. change (Int.shl (Int.repr 1) (Int.repr 18)) with (Int.repr (2 ^ 18)). arg_cmp. }
  assumed. apply Z.leb_le in E0.
  remember (2^18) as N eqn:HN.
  match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx (?A :: _ :: ?R)))) _ _ =>
    forward_for_simple_bound len (EX i:Z, EX dc: list val,
       PROPx [Zlength dc = N; sublist 0 (Zlength D + i) dc = bytes_rep (hcopy (e_dict E) D dist i)]
       (LOCALx Q (SEPx (A :: data_at Ews (tarray tuchar N) dc (e_datap E) :: R)))) end.
  { Exists dcont. entailer!. rewrite hcopy_0, ?Z.add_0_r. auto. }
  { Intros. rename H9 into Hdci, H10 into Hdsi.
    assert (Hli: Zlength (hcopy (e_dict E) D dist i) = Zlength D + i) by (apply Zlength_hcopy; lia).
    assert (Hbi: is_bytes (hcopy (e_dict E) D dist i)) by (apply is_bytes_hcopy; auto; lia).
    forward_call (Ews, e_dictp E, e_dict E, Ews, e_datap E, N, dc, hcopy (e_dict E) D dist i,
                  Zlength (e_dict E) + Zlength D + i - dist).
    { entailer!. }
    set (bt := Znth (Zlength (e_dict E) + Zlength D + i - dist) (e_dict E ++ hcopy (e_dict E) D dist i)).
    forward.
    assert (Hbt: 0 <= bt <= Byte.max_unsigned).
    { assert (Hb2: is_bytes (e_dict E ++ hcopy (e_dict E) D dist i)) by (apply Forall_app; auto).
      unfold is_bytes in Hb2. rewrite Forall_Znth in Hb2. apply Hb2. rewrite Zlength_app, Hli. lia. }
    rewrite zero_ext_inrange by (rewrite Int.unsigned_repr by rep_lia; simpl; rep_lia).
    Exists (upd_Znth (Zlength D + i) dc (Vint (Int.repr bt))).
    clear HN. entailer!.
    rewrite hcopy_S by lia. fold bt.
    replace (Zlength D + (i + 1)) with (Zlength (hcopy (e_dict E) D dist i ++ [bt]))
      by (rewrite Zlength_app, Hli, Zlength_cons, Zlength_nil; lia).
    rewrite <- Hli. apply upd_data_sub; [lia | rewrite Hli; auto]. }
  Intros dc. rename H8 into Hdci, H9 into Hdsi.
  assert (Hli: Zlength (hcopy (e_dict E) D dist len) = Zlength D + len) by (apply Zlength_hcopy; lia).
  assert (Hbi: is_bytes (hcopy (e_dict E) D dist len)) by (apply is_bytes_hcopy; auto; lia).
  forward.
  forward_call (e_gv E, Ers, Tsh, Ews, sym_bits E bs last syms, 2^19, e_srcp E, e_vw E, len, dist).
  { unfold bw_room. split; [lia | split; [ | rep_lia]].
    set (b := Zlength (sym_bits E bs last syms)) in *. pose proof (Zlength_nonneg (sym_bits E bs last syms)).
    pose proof (Z.div_mod b 8 ltac:(lia)). pose proof (Z.mod_pos_bound b 8 ltac:(lia)).
    pose proof (Z.div_mod (b + 31 + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (b + 31 + 7) 8 ltac:(lia)).
    lia. }
  rewrite <- sym_bits_ref.
  unfold sym_inv. Exists (syms ++ [Ref len dist]) dc. unfold sym_at.
  rewrite edata_ref by lia. rewrite <- HN.
  entailer!.
  fold D. split3.
  - apply syms_ok_snoc. split; auto.
    assert (Hz: Zlength (syms_data (expand (e_dict E) bs) syms) = Zlength (e_dict E) + Zlength D).
    { rewrite <- expand_fixed, expand_data, Zlength_app. reflexivity. }
    pose proof (len_code_range len). pose proof (dist_code_range dist).
    unfold sym_ok. rewrite Hz, Zlength_fixed_ll, Zlength_fixed_dl.
    split3; [lia | lia | split3; [lia | lia | split3; [ | lia | ]]].
    + apply fixed_ll_nz. lia.
    + apply fixed_dl_nz. lia.
  - unfold data_ok. rewrite Hli. split3; [auto | lia | split; auto].
  - rewrite Hli. auto.
Qed.
