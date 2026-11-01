(* Law inflate_decode, main: a back-reference in the symbol loop (the branch kind >= 128). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.HarnessRef
               Zlib.proof.adler32.MainLib.
Require Zlib.proof.crc32.HarnessRef.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_common.DRefSpec.
Require Import Zlib.proof.rfc1951.Decode.
Require Import Zlib.proof.harness.inflate_decode.IDLawCS Zlib.proof.harness.inflate_decode.IDGlobals.
Require Import Zlib.harness.x_inflate_decode.code.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.inflate_decode.IDMainKit.



(* ---------------------------------------------------------------------------------------------- *)
(* Pure facts (Format.v)                                                                          *)

Fixpoint idref_chk_from (f: Z -> bool) (fuel: nat) (z: Z) : bool :=
  match fuel with O => true | S k => f z && idref_chk_from f k (z + 1) end.

Lemma idref_chk_from_ok f fuel z : idref_chk_from f fuel z = true -> forall d, z <= d < z + Z.of_nat fuel -> f d = true.
Proof.
  revert z. induction fuel as [|k IH]; intros z H d Hd; simpl in *; [lia | ].
  apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec d z); [subst; auto | apply (IH (z + 1)); auto; lia].
Qed.

Definition idref_dchk (dist: Z) : bool :=
  (0 <=? dist_code dist) && (dist_code dist <=? 29) && (Znth (dist_code dist) dist_base <=? dist) &&
  (0 <=? Znth (dist_code dist) dist_extra) && (Znth (dist_code dist) dist_extra <=? 13).

Lemma idref_dchk_all : idref_chk_from idref_dchk 32768 1 = true.
Proof. vm_compute. reflexivity. Qed.

Definition idref_lchk (len: Z) : bool :=
  (0 <=? len_code len) && (len_code len <=? 28) && (Znth (len_code len) len_base <=? len) &&
  (0 <=? Znth (len_code len) len_extra) && (Znth (len_code len) len_extra <=? 5).

Lemma idref_lchk_all : idref_chk_from idref_lchk 256 3 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma idref_len_code len : 3 <= len <= 258 ->
  0 <= len_code len <= 28 /\ Znth (len_code len) len_base <= len /\ 0 <= Znth (len_code len) len_extra <= 5.
Proof.
  intros Hl. pose proof (idref_chk_from_ok _ _ _ idref_lchk_all len ltac:(assert (E: Z.of_nat 256 = 256) by (vm_compute; reflexivity); rewrite E; lia)) as H.
  unfold idref_lchk in H. rewrite !andb_true_iff, !Z.leb_le in H. lia.
Qed.

Lemma idref_dist_code dist : 1 <= dist <= 32768 ->
  0 <= dist_code dist <= 29 /\ Znth (dist_code dist) dist_base <= dist /\
  0 <= Znth (dist_code dist) dist_extra <= 13.
Proof.
  intros Hl. pose proof (idref_chk_from_ok _ _ _ idref_dchk_all dist ltac:(assert (E: Z.of_nat 32768 = 32768) by (vm_compute; reflexivity); rewrite E; lia)) as H.
  unfold idref_dchk in H. rewrite !andb_true_iff, !Z.leb_le in H. lia.
Qed.

Lemma idref_lz_copy_S n d out :
  lz_copy (S n) d out = lz_copy n d out ++ [Znth (Zlength (lz_copy n d out) - d) (lz_copy n d out)].
Proof.
  revert out. induction n as [|n IH]; intros out; [reflexivity | ].
  change (lz_copy (S (S n)) d out) with (lz_copy (S n) d (out ++ [Znth (Zlength out - d) out])).
  rewrite IH. reflexivity.
Qed.

Lemma idref_lz_copy_len n d out : Zlength (lz_copy n d out) = Zlength out + Z.of_nat n.
Proof.
  induction n as [|n IH]; [simpl; lia | ].
  rewrite idref_lz_copy_S, Zlength_app, IH, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma idref_lz_copy_bytes n d out : is_bytes out -> is_bytes (lz_copy n d out).
Proof.
  intros H. induction n as [|n IH]; [exact H | ].
  rewrite idref_lz_copy_S. unfold is_bytes in *. apply Forall_app; split; auto.
  constructor; [ | constructor].
  set (l := lz_copy n d out) in *. set (i := Zlength l - d).
  destruct (zlt i 0); [rewrite Znth_underflow by lia; cbv [default Inhabitant_Z]; rep_lia | ].
  destruct (zlt i (Zlength l)); [ | rewrite Znth_overflow by lia; cbv [default Inhabitant_Z]; rep_lia].
  rewrite Forall_forall in IH. apply IH. apply Znth_In. lia.
Qed.

Lemma idref_syms_data_app out syms s : syms_data out (syms ++ [s]) = sym_data (syms_data out syms) s.
Proof. unfold syms_data. rewrite fold_left_app. reflexivity. Qed.

Lemma idref_syms_ok_app wmax ll dl out syms s :
  syms_ok wmax ll dl out syms -> sym_ok wmax ll dl (syms_data out syms) s -> syms_ok wmax ll dl out (syms ++ [s]).
Proof.
  unfold syms_data. revert out. induction syms as [|t r IH]; intros out H1 H2; simpl in *.
  - tauto.
  - destruct H1 as [Ht Hr]. split; auto.
Qed.

Lemma idref_bits_msb_mod c n : 0 <= n <= 16 -> bits_msb (c mod 65536) n = bits_msb c n.
Proof.
  intros Hn. unfold bits_msb, bits_le. f_equal. apply map_ext_in. intros i Hi.
  apply in_seq in Hi. change 65536 with (2 ^ 16). apply Z.mod_pow2_bits_low. lia.
Qed.

Lemma idref_bits_le_len v n : 0 <= n -> Zlength (bits_le v n) = n.
Proof. intros. unfold bits_le. rewrite Zlength_map, Zlength_correct, seq_length. lia. Qed.

Lemma idref_bits_msb_len c n : 0 <= n -> Zlength (bits_msb c n) = n.
Proof. intros. unfold bits_msb. rewrite Zlength_rev. apply idref_bits_le_len; auto. Qed.

Lemma idref_fixed :
  Zlength fixed_ll = 288 /\ Zlength fixed_dl = 32 /\ (forall i, 0 <= i < 288 -> 0 < Znth i fixed_ll <= 9) /\
  (forall i, 0 <= i < 32 -> Znth i fixed_dl = 5).
Proof.
  assert (Hl: Zlength fixed_ll = 288) by reflexivity.
  split; [exact Hl | split; [reflexivity | split]].
  - intros i Hi. assert (Forall (fun x => 0 < x <= 9) fixed_ll) as F.
    { unfold fixed_ll. rewrite !Forall_app. repeat split; apply Forall_forall; intros x Hx;
        apply repeat_spec in Hx; lia. }
    rewrite Forall_forall in F. apply F. apply Znth_In. lia.
  - intros i Hi. unfold fixed_dl. change 32%nat with (Z.to_nat 32). rewrite Znth_repeat_inrange; lia.
Qed.

(* room for the bits of a back-reference (at most 48) after the 8 bytes of kind_at *)
Lemma idref_room B x cap k :
  Zlength B / 8 + 8 <= cap -> cap <= Int.max_unsigned -> 0 <= k -> Zlength x + k <= 57 -> bw_room (B ++ x) cap k.
Proof.
  intros Hr Hc Hk Hx. unfold bw_room. rewrite Zlength_app.
  pose proof (Zlength_nonneg B). pose proof (Zlength_nonneg x).
  split; [lia | split; [ | lia]].
  pose proof (Z.div_mod (Zlength B) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Zlength B) 8 ltac:(lia)).
  set (q := Zlength B / 8) in *. set (r := Zlength B mod 8) in *.
  assert ((Zlength B + Zlength x + k + 7) / 8 < q + 9); [ | lia].
  apply Z.div_lt_upper_bound; lia.
Qed.

Lemma idref_znth_vals (l: list val) L m i : 0 <= i < m -> m <= Zlength l -> sublist 0 m l = zvals L ->
  Znth i l = Vint (Int.repr (Znth i L)) /\ Zlength L = m.
Proof.
  intros Hi Hm E.
  assert (HL: Zlength L = m).
  { unfold zvals in E. rewrite <- (Zlength_map _ _ (fun x => Vint (Int.repr x)) L), <- E, Zlength_sublist; lia. }
  split; auto.
  assert (E2: Znth i (sublist 0 m l) = Znth i l) by (rewrite Znth_sublist by lia; f_equal; lia).
  rewrite <- E2, E. unfold zvals. rewrite Znth_map by lia. reflexivity.
Qed.

(* the tables' arrays at the law's compspecs *)
Lemma idref_uchar_cs sh n (v: list val) q :
  @data_at Zlib.contracts.x_inflate_decode.Harness.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_harness); [apply JMeq_refl | reflexivity]. Qed.

Lemma idref_ushort_cs sh n (v: list val) q :
  @data_at Zlib.contracts.x_inflate_decode.Harness.CS sh (tarray tushort n) v q = @data_at CS sh (tarray tushort n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_harness); [apply JMeq_refl | reflexivity]. Qed.

Lemma idref_byte_znth (l: list Z) k : is_bytes l -> 0 <= Znth k l <= Byte.max_unsigned.
Proof.
  intros H. destruct (zlt k 0); [rewrite Znth_underflow by lia; cbv [default Inhabitant_Z]; rep_lia | ].
  destruct (zlt k (Zlength l)); [ | rewrite Znth_overflow by lia; cbv [default Inhabitant_Z]; rep_lia].
  unfold is_bytes in H. rewrite Forall_forall in H. apply H. apply Znth_In. lia.
Qed.

Lemma idref_room0 B cap k :
  Zlength B / 8 + 8 <= cap -> cap <= Int.max_unsigned -> 0 <= k <= 57 -> bw_room B cap k.
Proof. intros. rewrite <- (app_nil_r B). apply idref_room; auto; [lia | rewrite Zlength_nil; lia]. Qed.

Lemma idref_tabs_law gv sh : dref_tabs gv sh id_tabs =
  (@data_at CS sh (tarray tushort 29) (zvals len_base) (gv _x_inflate_decode__ref_lbase) *
   @data_at CS sh (tarray tuchar 29) (zvals len_extra) (gv _x_inflate_decode__ref_lext) *
   @data_at CS sh (tarray tushort 30) (zvals dist_base) (gv _x_inflate_decode__ref_dbase) *
   @data_at CS sh (tarray tuchar 30) (zvals dist_extra) (gv _x_inflate_decode__ref_dext))%logic.
Proof. unfold dref_tabs, id_tabs. rewrite !idref_uchar_cs, !idref_ushort_cs. reflexivity. Qed.

Lemma idref_znth_zvals l i : 0 <= i < Zlength l -> Znth i (zvals l) = Vint (Int.repr (Znth i l)).
Proof. intros. unfold zvals. rewrite Znth_map by lia. reflexivity. Qed.

Lemma idref_canon_znth l k : 0 <= k < Zlength l -> Znth k (canon_vals l) = canon_val l k.
Proof.
  intros Hk. unfold canon_vals.
  assert (Hl: Zlength (seq 0 (length l)) = Zlength l) by (rewrite !Zlength_correct, seq_length; lia).
  rewrite Znth_map by lia. f_equal.
  rewrite <- nth_Znth by lia. rewrite seq_nth by (rewrite Zlength_correct in Hk; lia). lia.
Qed.

Lemma idref_canon_send l k : 0 < Znth k l <= 15 ->
  send_sym l k = bits_msb (canon_val l k) (Znth k l) /\ 0 <= canon_val l k < 65536.
Proof.
  intros Hk. unfold canon_val, send_sym.
  destruct (Z.eqb_spec (Znth k l) 0); [lia | ].
  rewrite idref_bits_msb_mod by lia. split; [reflexivity | apply Z.mod_pos_bound; lia].
Qed.

(* the object data[0 .. N) during the copy loop: the data after i bytes of the copy, then the old contents *)
Definition idref_cont (N: Z) (dcont: list val) (D: list Z) (d i: Z) : list val :=
  bytes_rep (lz_copy (Z.to_nat i) d D) ++ sublist (Zlength D + i) N dcont.

Lemma idref_cont_0 dcont D d : data_ok dcont D -> idref_cont 262144 dcont D d 0 = dcont.
Proof.
  intros (H1 & H2 & H3 & H4). unfold idref_cont. simpl lz_copy. rewrite Z.add_0_r, <- H4.
  rewrite sublist_rejoin by (pose proof (Zlength_nonneg D); lia). rewrite <- H1. apply sublist_same; lia.
Qed.

Lemma idref_cont_len N dcont D d i : Zlength dcont = N -> 0 <= i -> Zlength D + i <= N ->
  Zlength (idref_cont N dcont D d i) = N.
Proof.
  intros H1 Hi H2. unfold idref_cont, bytes_rep.
  rewrite Zlength_app, Zlength_map, idref_lz_copy_len, Zlength_sublist by (pose proof (Zlength_nonneg D); lia).
  rewrite Z2Nat.id by lia. lia.
Qed.

Lemma idref_cont_get N dcont D d i : 1 <= d <= Zlength D -> 0 <= i ->
  Znth (Zlength D + i - d) (idref_cont N dcont D d i) =
  Vint (Int.repr (Znth (Zlength D + i - d) (lz_copy (Z.to_nat i) d D))).
Proof.
  intros Hd Hi. unfold idref_cont, bytes_rep.
  assert (HL: Zlength (lz_copy (Z.to_nat i) d D) = Zlength D + i) by (rewrite idref_lz_copy_len; lia).
  rewrite Znth_app1 by (rewrite Zlength_map; lia). rewrite Znth_map by lia. reflexivity.
Qed.

Lemma idref_cont_step N dcont D d i : Zlength dcont = N -> 0 <= i -> Zlength D + i < N ->
  upd_Znth (Zlength D + i) (idref_cont N dcont D d i)
    (Vint (Int.repr (Znth (Zlength D + i - d) (lz_copy (Z.to_nat i) d D)))) =
  idref_cont N dcont D d (i + 1).
Proof.
  intros H1 Hi H2. unfold idref_cont, bytes_rep. pose proof (Zlength_nonneg D).
  assert (HL: Zlength (lz_copy (Z.to_nat i) d D) = Zlength D + i) by (rewrite idref_lz_copy_len; lia).
  rewrite Z2Nat.inj_add by lia. change (Z.to_nat 1) with 1%nat. rewrite Nat.add_1_r.
  rewrite idref_lz_copy_S, map_app, <- app_assoc, HL.
  assert (HS: Zlength (sublist (Zlength D + i) N dcont) = N - (Zlength D + i)) by (rewrite Zlength_sublist; lia).
  rewrite upd_Znth_app2 by (rewrite Zlength_map, HL, HS; lia).
  rewrite Zlength_map, HL, Z.sub_diag. f_equal.
  rewrite (sublist_split (Zlength D + i) (Zlength D + i + 1) N) by lia.
  rewrite (sublist_one (Zlength D + i)) by lia.
  rewrite upd_Znth_app1 by (rewrite Zlength_cons, Zlength_nil; lia).
  rewrite upd_Znth0. simpl. f_equal. f_equal. lia.
Qed.

Lemma idref_cont_end dcont D d n : data_ok dcont D -> 0 <= n -> Zlength D + n <= 262144 ->
  data_ok (idref_cont 262144 dcont D d n) (lz_copy (Z.to_nat n) d D).
Proof.
  intros Hok Hn Hle. pose proof Hok as (H1 & H2 & H3 & H4).
  assert (HL: Zlength (lz_copy (Z.to_nat n) d D) = Zlength D + n) by (rewrite idref_lz_copy_len; lia).
  split; [apply idref_cont_len; lia | ].
  split; [lia | ].
  split; [apply idref_lz_copy_bytes; auto | ].
  pose proof (Zlength_nonneg D).
  unfold idref_cont. rewrite HL, sublist_app1 by (unfold bytes_rep; rewrite ?Zlength_map, ?HL; lia).
  apply sublist_same; unfold bytes_rep; rewrite ?Zlength_map, ?HL; lia.
Qed.

(* the dynamic block's checks of main (`continue` unless they pass) *)
Definition idref_okb (hk: hkind) (len dist: Z) : bool :=
  match hk with
  | HFix => true
  | HDyn nlen ndist _ toks =>
      (257 + len_code len <? nlen) && negb (Znth (257 + len_code len) (dyn_lens toks) =? 0) &&
      (dist_code dist <? ndist) && negb (Znth (nlen + dist_code dist) (dyn_lens toks) =? 0)
  end.

Lemma idref_okb_sym hk wmax out len dist : hk_ok hk -> idref_okb hk len dist = true ->
  3 <= len <= 258 -> 1 <= dist <= Zlength out -> dist <= wmax -> dist <= 32768 ->
  sym_ok wmax (hk_ll hk) (hk_dl hk) out (Ref len dist).
Proof.
  intros Hk Hb Hl Hd Hw Hd'.
  destruct (idref_len_code len Hl) as (Hlc & _). destruct (idref_dist_code dist ltac:(lia)) as (Hdc & _).
  unfold sym_ok. do 3 (split; [auto | ]).
  destruct hk as [|nlen ndist cl toks]; cbn [hk_ll hk_dl].
  - destruct idref_fixed as (H1 & H2 & H3 & H4).
    rewrite H1, H2. split; [lia | split; [specialize (H3 (257 + len_code len)); lia | ]].
    split; [lia | rewrite H4; lia].
  - destruct Hk as (Hnl & Hnd & Hhdr).
    assert (HL: Zlength (dyn_lens toks) = nlen + ndist) by (destruct Hhdr as (_&_&_&_&?&_); auto).
    unfold idref_okb in Hb. rewrite !andb_true_iff, !negb_true_iff, Z.ltb_lt, Z.ltb_lt, !Z.eqb_neq in Hb.
    destruct Hb as (((Hb1 & Hb2) & Hb3) & Hb4).
    unfold dyn_ll, dyn_dl.
    rewrite !Zlength_sublist by lia.
    rewrite !Znth_sublist by lia.
    rewrite Z.add_0_r, (Z.add_comm (dist_code dist) nlen).
    repeat split; auto; lia.
Qed.


Lemma idref_dyn_range nlen ndist cl toks : hk_ok (HDyn nlen ndist cl toks) ->
  Zlength (dyn_lens toks) = nlen + ndist /\ 257 <= nlen <= 286 /\ 1 <= ndist <= 30 /\
  forall i, 0 <= i < nlen + ndist -> 0 <= Znth i (dyn_lens toks) <= 15.
Proof.
  intros (Hnl & Hnd & (_ & _ & _ & _ & HL & (Hll & _) & (Hdl & _))).
  split; [auto | split; [auto | split; [auto | ]]].
  intros i Hi. unfold lens_ok, dyn_ll, dyn_dl, MAXLEN in *. destruct (zlt i nlen).
  - pose proof (proj1 (Forall_Znth _ _) Hll i ltac:(rewrite Zlength_sublist; lia)) as F.
    cbv beta in F. rewrite Znth_sublist, Z.add_0_r in F by lia. exact F.
  - pose proof (proj1 (Forall_Znth _ _) Hdl (i - nlen) ltac:(rewrite Zlength_sublist; lia)) as F.
    cbv beta in F. rewrite Znth_sublist in F by lia. rewrite Z.sub_add in F. exact F.
Qed.


(* abstract the big objects' sizes (array loads/stores overflow the stack on the literals), and restore them
   (IDMainBlk's abs_sizes / rest_sizes) *)
Ltac idref_abs :=
  set (N0 := 262144) in *; set (N1 := 262145) in *; set (N2 := 524288) in *;
  assert (HN0: 262144 <= N0 <= 262144) by (unfold N0; lia);
  assert (HN1: 262145 <= N1 <= 262145) by (unfold N1; lia);
  assert (HN2: 524288 <= N2 <= 524288) by (unfold N2; lia);
  clearbody N0 N1 N2.
Ltac idref_rest :=
  match goal with N0: Z, N1: Z, N2: Z, HN0: 262144 <= ?N0 <= 262144, HN1: 262145 <= ?N1 <= 262145,
                  HN2: 524288 <= ?N2 <= 524288 |- _ =>
    assert (N0 = 262144) by lia; assert (N1 = 262145) by lia; assert (N2 = 524288) by lia; subst N0 N1 N2
  end.

(* the value of a C condition chain `t = 1` / `t = (tbool) (cond)` *)
Ltac bsolve :=
  unfold bool2val, Int.eq, Int.ltu in *;
  rewrite ?Int.unsigned_repr by rep_lia;
  repeat match goal with
   | |- context [?a <? ?b] => destruct (Z.ltb_spec a b)
   | |- context [?a <=? ?b] => destruct (Z.leb_spec a b)
   | |- context [?a =? ?b] => destruct (Z.eqb_spec a b)
   | H: context [?a <? ?b] |- _ => destruct (Z.ltb_spec a b)
   | H: context [?a <=? ?b] |- _ => destruct (Z.leb_spec a b)
   | H: context [?a =? ?b] |- _ => destruct (Z.eqb_spec a b)
   | |- context [zlt ?a ?b] => destruct (zlt a b)
   | |- context [zeq ?a ?b] => destruct (zeq a b)
   end; simpl in *;
  first [reflexivity | lia | exfalso; lia | contradiction | discriminate
        | match goal with H: ?x <> ?y |- _ => exfalso; apply H; reflexivity end].

(* replace the loaded value Znth i l by its value v (E: Znth i l = v; any Inhabitant instance) *)
Ltac zrw E :=
  match type of E with Znth ?i ?l = ?v =>
    match goal with |- context [@Znth ?A ?d i l] => replace (@Znth A d i l) with v by (rewrite <- E; reflexivity) end
  end.

(* forward_if with the post: the precondition and `temp t (b as 0/1)`, branches left open *)
Ltac fif0 t b :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp t (Vint (Int.repr (Z.b2z b))) :: Q) (SEPx R)))
  end.

(* forward_if with the post: the precondition and `temp t (b as 0/1)` *)
Ltac fif t b :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp t (Vint (Int.repr (Z.b2z b))) :: Q) (SEPx R)))
  end; [forward; entailer!; bsolve | forward; entailer!; bsolve | ].

Lemma id_ref_ok {Espec: OracleKind} gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr
    bs ls isbz last hk llc lcc dcc syms dcont kind (R: ret_assert) :
  blk_hyps wrap wb flevel isel datap srcp isbp bs ls isbz last -> hk_ok hk -> hk_arrays_ok hk llc lcc dcc ->
  128 <= kind ->
  semax Delta_id
    (kind_at gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr bs ls isbz last hk llc lcc dcc
       syms dcont kind)
    seg_ref
    (loop1_ret_assert (sym_inv gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr bs ls isbz last
                         hk llc lcc dcc) R).
Proof.
  intros HB HK HA Hk.
  destruct R as [Rn Rb Rc Rr]. unfold loop1_ret_assert.
  unfold seg_ref, Delta_id, Gmain_k. simplify_func_tycontext. abbreviate_semax.
  unfold kind_at. Intros.
  destruct HB as (Hpar & Pd & Ps & Pi & Hbok & Hexp & Hisb & Hlast & Hls).
  assert (Hwb: 8 <= wb <= 15) by (unfold par_ok in Hpar; lia).
  assert (Hmaxd: 256 <= 2 ^ wb <= 32768).
  { split; [change 256 with (2 ^ 8) | change 32768 with (2 ^ 15)]; apply Z.pow_le_mono_r; lia. }
  set (D := syms_data (expand [] bs) syms) in *.
  assert (HD: Zlength D <= 262144) by (destruct H0 as (_ & ? & _); auto).
  pose proof (Zlength_nonneg D).
  forward_call. Intros len. forward_call. Intros dist.
  fif _t'24 ((len <? 3) || (258 <? len))%bool.
  fif _t'25 ((len <? 3) || (258 <? len) || (dist <? 1))%bool.
  fif _t'26 ((len <? 3) || (258 <? len) || (dist <? 1) || (Zlength D <? dist))%bool.
  fif _t'27 ((len <? 3) || (258 <? len) || (dist <? 1) || (Zlength D <? dist) || (2 ^ wb <? dist))%bool.
  forward_if.
  { forward. unfold sym_inv, sym_at. Exists syms dcont. entailer!. }
  match goal with Hc: ((_ || _)%bool = false) |- _ =>
    rewrite !orb_false_iff, !Z.ltb_ge in Hc; destruct Hc as ((((Hl1 & Hl2) & Hd1) & Hd2) & Hd3) end.
  drop_LOCALs [_t'24; _t'25; _t'26; _t'27].
  forward_call (gv, Ers, len).
  forward_call (gv, Ers, dist).
  destruct (idref_len_code len ltac:(lia)) as (Hlc1 & Hlc2 & Hlc3).
  destruct (idref_dist_code dist ltac:(lia)) as (Hdc1 & Hdc2 & Hdc3).
  fif0 _t'30 (negb (idref_okb hk len dist)).
  { destruct hk as [|nlen ndist cl toks]; cbn [hk_dyn hk_nlen hk_ndist] in *.
    { exfalso; lia. }
    destruct (idref_dyn_range _ _ _ _ HK) as (HL & Hnl & Hnd & Hrg).
    destruct HA as ((Hc1 & Hc2 & Hc3) & Hllv & Hlcv & Hdcv).
    fif0 _t'31 ((nlen <=? 257 + len_code len) || (Znth (257 + len_code len) (dyn_lens toks) =? 0))%bool.
    { forward. entailer!. bsolve. }
    { destruct (idref_znth_vals llc (dyn_lens toks) (nlen + ndist) (257 + len_code len)) as [E _];
        [lia | lia | auto | ].
      pose proof (Hrg (257 + len_code len) ltac:(lia)).
      forward. all: zrw E. { entailer!; rep_lia. }
      forward. entailer!. bsolve. }
    fif _t'32 ((nlen <=? 257 + len_code len) || (Znth (257 + len_code len) (dyn_lens toks) =? 0) ||
               (ndist <=? dist_code dist))%bool.
    forward_if.
    { forward. entailer!. unfold idref_okb. bsolve. }
    { destruct (idref_znth_vals llc (dyn_lens toks) (nlen + ndist) (nlen + dist_code dist)) as [E _];
        [bsolve | lia | auto | ].
      pose proof (Hrg (nlen + dist_code dist) ltac:(bsolve)).
      forward. all: zrw E. { entailer!; rep_lia. }
      forward. forward. entailer!. unfold idref_okb. bsolve. }
  }
  { destruct hk as [|nlen ndist cl toks]; cbn [hk_dyn hk_nlen hk_ndist] in *.
    { forward. entailer!. }
    discriminate. }
  forward_if.
  { forward. unfold sym_inv, sym_at. Exists syms dcont. entailer!. }
  assert (Hok: idref_okb hk len dist = true) by assumption.
  assert (Hsym: sym_ok (2 ^ wb) (hk_ll hk) (hk_dl hk) D (Ref len dist)) by (apply idref_okb_sym; auto; lia).
  forward_call (Int.repr (if Zlength D + len <=? 262144 then 1 else 0)).
  { entailer!. change (Int.shl (Int.repr 1) (Int.repr 18)) with (Int.repr 262144).
    unfold Int.ltu. rewrite !Int.unsigned_repr by rep_lia.
    destruct (zlt 262144 (Zlength D + len)); destruct (Z.leb_spec (Zlength D + len) 262144); try lia; reflexivity. }
  assumed. apply Z.leb_le in E.
  drop_LOCALs [_t'30].
  rewrite <- (idref_cont_0 dcont D dist H0).
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    match R with context C [idref_cont 262144 dcont D dist 0] =>
      forward_for_simple_bound len (@exp (environ -> mpred) _ Z (fun i: Z => PROPx P (LOCALx Q (SEPx
        ltac:(let r := context C [idref_cont 262144 dcont D dist i] in exact r)))))
    end
  end.
  { entailer!. }
  { idref_abs.
    assert (EV: Znth (Zlength D + i - dist) (idref_cont N0 dcont D dist i) =
                Vint (Int.repr (Znth (Zlength D + i - dist) (lz_copy (Z.to_nat i) dist D))))
      by (apply idref_cont_get; lia).
    assert (HB: 0 <= Znth (Zlength D + i - dist) (lz_copy (Z.to_nat i) dist D) <= Byte.max_unsigned)
      by (apply idref_byte_znth, idref_lz_copy_bytes; destruct H0 as (_ & _ & ? & _); auto).
    assert (HCL: Zlength (idref_cont N0 dcont D dist i) = N0)
      by (apply idref_cont_len; destruct H0; lia).
    forward. all: zrw EV. { entailer!; lia. }
    forward.
    rewrite zext8, Z.mod_small by rep_lia.
    rewrite (idref_cont_step N0 dcont D dist i) by (destruct H0; lia).
    entailer!. }
  forward.
  forward_if.
  { destruct hk as [|nlen ndist cl toks]; cbn [hk_dyn hk_nlen hk_ndist] in *.
    { exfalso; lia. }
    destruct (idref_dyn_range _ _ _ _ HK) as (HL & Hnl & Hnd & Hrg).
    destruct HA as ((Hc1 & Hc2 & Hc3) & Hllv & Hlcv & Hdcv).
    assert (Hok' := Hok). unfold idref_okb in Hok'.
    rewrite !andb_true_iff, !negb_true_iff, Z.ltb_lt, Z.ltb_lt, !Z.eqb_neq in Hok'.
    destruct Hok' as (((Ho1 & Ho2) & Ho3) & Ho4).
    set (L := dyn_lens toks) in *.
    set (lc := len_code len) in *. set (dc := dist_code dist) in *.
    assert (HLl: Zlength (dyn_ll nlen toks) = nlen) by (unfold dyn_ll; fold L; rewrite Zlength_sublist; lia).
    assert (HLd: Zlength (dyn_dl nlen ndist toks) = ndist)
      by (unfold dyn_dl; fold L; rewrite Zlength_sublist; lia).
    assert (Zll: Znth (257 + lc) (dyn_ll nlen toks) = Znth (257 + lc) L)
      by (unfold dyn_ll; fold L; rewrite Znth_sublist by lia; f_equal; lia).
    assert (Zdl: Znth dc (dyn_dl nlen ndist toks) = Znth (nlen + dc) L)
      by (unfold dyn_dl; fold L; rewrite Znth_sublist by lia; f_equal; lia).
    pose proof (Hrg (257 + lc) ltac:(lia)) as R1. pose proof (Hrg (nlen + dc) ltac:(lia)) as R2.
    destruct (idref_canon_send (dyn_ll nlen toks) (257 + lc) ltac:(rewrite Zll; lia)) as [S1 C1].
    destruct (idref_canon_send (dyn_dl nlen ndist toks) dc ltac:(rewrite Zdl; lia)) as [S2 C2].
    destruct (idref_znth_vals lcc (canon_vals (dyn_ll nlen toks)) nlen (257 + lc)) as [E1 _]; [lia | lia | auto | ].
    rewrite idref_canon_znth in E1 by lia.
    destruct (idref_znth_vals llc L (nlen + ndist) (257 + lc)) as [E2 _]; [lia | lia | auto | ].
    destruct (idref_znth_vals dcc (canon_vals (dyn_dl nlen ndist toks)) ndist dc) as [E3 _]; [lia | lia | auto | ].
    rewrite idref_canon_znth in E3 by lia.
    destruct (idref_znth_vals llc L (nlen + ndist) (nlen + dc)) as [E4 _]; [lia | lia | auto | ].
    unfold sym_bits in H2.
    set (B0 := enc_bits (id_wrapper wrap wb flevel) bs ++ bits_le last 1 ++ hk_bits (HDyn nlen ndist cl toks) ++
               flat_map (send_one (hk_ll (HDyn nlen ndist cl toks)) (hk_dl (HDyn nlen ndist cl toks))) syms) in *.
    forward. all: zrw E1. { entailer!; rep_lia. }
    forward. all: zrw E2. { entailer!; rep_lia. }
    forward_call (Tsh, Ews, B0, 524288, srcp, vw, canon_val (dyn_ll nlen toks) (257 + lc), Znth (257 + lc) L).
    { apply idref_room0; [exact H2 | rep_lia | lia]. }
    assert (T1: Znth lc (zvals len_base) = Vint (Int.repr (Znth lc len_base)))
      by (apply idref_znth_zvals; change (Zlength len_base) with 29; lia).
    assert (T2: Znth lc (zvals len_extra) = Vint (Int.repr (Znth lc len_extra)))
      by (apply idref_znth_zvals; change (Zlength len_extra) with 29; lia).
    assert (T3: Znth dc (zvals dist_base) = Vint (Int.repr (Znth dc dist_base)))
      by (apply idref_znth_zvals; change (Zlength dist_base) with 30; lia).
    assert (T4: Znth dc (zvals dist_extra) = Vint (Int.repr (Znth dc dist_extra)))
      by (apply idref_znth_zvals; change (Zlength dist_extra) with 30; lia).
    assert (B1: 0 <= Znth lc len_base).
    { apply (proj1 (Forall_Znth len_base (fun x => 0 <= x))); [unfold len_base; repeat constructor; lia | ].
      change (Zlength len_base) with 29; lia. }
    assert (B3: 0 <= Znth dc dist_base).
    { apply (proj1 (Forall_Znth dist_base (fun x => 0 <= x))); [unfold dist_base; repeat constructor; lia | ].
      change (Zlength dist_base) with 30; lia. }
    rewrite idref_tabs_law. Intros.
    forward. all: zrw T1. { entailer!; rep_lia. }
    forward. all: zrw T2. { entailer!; rep_lia. }
    forward_call (Tsh, Ews, B0 ++ bits_msb (canon_val (dyn_ll nlen toks) (257 + lc)) (Znth (257 + lc) L),
                  524288, srcp, vw, len - Znth lc len_base, Znth lc len_extra).
    { apply idref_room; [exact H2 | rep_lia | lia | rewrite idref_bits_msb_len by lia; lia]. }
    forward. all: zrw E3. { entailer!; rep_lia. }
    forward. all: zrw E4. { entailer!; rep_lia. }
    forward_call (Tsh, Ews, (B0 ++ bits_msb (canon_val (dyn_ll nlen toks) (257 + lc)) (Znth (257 + lc) L)) ++
                              bits_le (len - Znth lc len_base) (Znth lc len_extra),
                  524288, srcp, vw, canon_val (dyn_dl nlen ndist toks) dc, Znth (nlen + dc) L).
    { rewrite <- app_assoc. apply idref_room; [exact H2 | rep_lia | lia | ].
      rewrite Zlength_app, idref_bits_msb_len, idref_bits_le_len by lia; lia. }
    forward. all: zrw T3. { entailer!; rep_lia. }
    forward. all: zrw T4. { entailer!; rep_lia. }
    forward_call (Tsh, Ews, ((B0 ++ bits_msb (canon_val (dyn_ll nlen toks) (257 + lc)) (Znth (257 + lc) L)) ++
                              bits_le (len - Znth lc len_base) (Znth lc len_extra)) ++
                              bits_msb (canon_val (dyn_dl nlen ndist toks) dc) (Znth (nlen + dc) L),
                  524288, srcp, vw, dist - Znth dc dist_base, Znth dc dist_extra).
    { rewrite <- !app_assoc. apply idref_room; [exact H2 | rep_lia | lia | ].
      rewrite !Zlength_app, !idref_bits_msb_len, !idref_bits_le_len by lia; lia. }
    assert (SO: send_one (dyn_ll nlen toks) (dyn_dl nlen ndist toks) (Ref len dist) =
                bits_msb (canon_val (dyn_ll nlen toks) (257 + lc)) (Znth (257 + lc) L) ++
                bits_le (len - Znth lc len_base) (Znth lc len_extra) ++
                bits_msb (canon_val (dyn_dl nlen ndist toks) dc) (Znth (nlen + dc) L) ++
                bits_le (dist - Znth dc dist_base) (Znth dc dist_extra)).
    { unfold send_one. cbv zeta. change (len_code len) with lc. change (dist_code dist) with dc.
      rewrite S1, S2, Zll, Zdl. reflexivity. }
    assert (HS2: syms_ok (2 ^ wb) (hk_ll (HDyn nlen ndist cl toks)) (hk_dl (HDyn nlen ndist cl toks))
                   (expand [] bs) (syms ++ [Ref len dist]))
      by (apply idref_syms_ok_app; auto).
    assert (HD2: syms_data (expand [] bs) (syms ++ [Ref len dist]) = lz_copy (Z.to_nat len) dist D)
      by (rewrite idref_syms_data_app; reflexivity).
    assert (HDok: data_ok (idref_cont 262144 dcont D dist len) (lz_copy (Z.to_nat len) dist D))
      by (apply idref_cont_end; auto; lia).
    assert (HL2: Zlength (lz_copy (Z.to_nat len) dist D) = Zlength D + len) by (rewrite idref_lz_copy_len; lia).
    unfold sym_inv, sym_at. Exists (syms ++ [Ref len dist]) (idref_cont 262144 dcont D dist len).
    subst B0.
    rewrite HD2, HL2, <- flat_map_app, idref_tabs_law. cbn [hk_ll hk_dl hk_dyn hk_nlen hk_ndist flat_map] in *.
    rewrite app_nil_r, SO, <- !app_assoc. rewrite add_repr.
    entailer!. }
  { destruct hk as [|nlen ndist cl toks]; cbn [hk_dyn hk_nlen hk_ndist] in *; [ | discriminate].
    match goal with |- context [bw_at Tsh Ews ?B 524288 srcp vw] =>
      forward_call (gv, Ers, Tsh, Ews, B, 524288, srcp, vw, len, dist) end.
    { unfold sym_bits in H2. apply idref_room0; [exact H2 | rep_lia | lia]. }
    assert (HS2: syms_ok (2 ^ wb) (hk_ll HFix) (hk_dl HFix) (expand [] bs) (syms ++ [Ref len dist]))
      by (apply idref_syms_ok_app; auto).
    assert (HD2: syms_data (expand [] bs) (syms ++ [Ref len dist]) = lz_copy (Z.to_nat len) dist D)
      by (rewrite idref_syms_data_app; reflexivity).
    assert (HDok: data_ok (idref_cont 262144 dcont D dist len) (lz_copy (Z.to_nat len) dist D))
      by (apply idref_cont_end; auto; lia).
    assert (HL2: Zlength (lz_copy (Z.to_nat len) dist D) = Zlength D + len) by (rewrite idref_lz_copy_len; lia).
    unfold sym_inv, sym_at. Exists (syms ++ [Ref len dist]) (idref_cont 262144 dcont D dist len).
    rewrite HD2, HL2, <- flat_map_app. cbn [hk_ll hk_dl hk_dyn hk_nlen hk_ndist flat_map] in *.
    rewrite app_nil_r, <- !app_assoc. rewrite add_repr.
    entailer!. }
Qed.
