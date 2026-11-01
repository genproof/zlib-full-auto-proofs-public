(* Law inflate_decode, main: a literal in the symbol loop (the branch kind < 128). *)
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
(* The bit writer's struct at the law's compspecs                                                 *)

Lemma bw_struct_cs sh (v: val * (val * val)) q :
  @data_at Zlib.contracts.x_inflate_decode.Harness.CS sh t_bw v q = @data_at CS sh (Tstruct _bw noattr) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_harness); [apply JMeq_refl | reflexivity]. Qed.

Lemma bw_at_law sh bsh B cap buf w :
  bw_at sh bsh B cap buf w =
  EX c: list val, !! bw_bytes_ok B cap c &&
    (@data_at CS sh (Tstruct _bw noattr)
       (buf, (Vint (Int.repr (Zlength B / 8)), Vint (Int.repr (Zlength B mod 8)))) w *
     @data_at Zlib.contracts.x_inflate_decode.Harness.CS bsh (tarray tuchar cap) c buf)%logic.
Proof. unfold bw_at, bw_rep. f_equal. extensionality c. rewrite bw_struct_cs. reflexivity. Qed.

Lemma bw_fold sh bsh B cap buf w c : bw_bytes_ok B cap c ->
  (@data_at CS sh (Tstruct _bw noattr)
     (buf, (Vint (Int.repr (Zlength B / 8)), Vint (Int.repr (Zlength B mod 8)))) w *
   @data_at Zlib.contracts.x_inflate_decode.Harness.CS bsh (tarray tuchar cap) c buf)%logic
  |-- bw_at sh bsh B cap buf w.
Proof. intros. rewrite bw_at_law. Exists c. entailer!. Qed.

(* 8 bytes of room (the harness's gp_assume) give room for 57 bits *)
Lemma room8 B cap k : 0 <= k <= 57 -> Zlength B / 8 + 8 <= cap -> cap <= Int.max_unsigned -> bw_room B cap k.
Proof.
  intros Hk Hr Hc. unfold bw_room. split; [lia | split; [ | lia]].
  pose proof (Zlength_nonneg B). pose proof (Z.div_mod (Zlength B) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (Zlength B) 8 ltac:(lia)).
  set (q := Zlength B / 8) in *. set (r := Zlength B mod 8) in *.
  assert ((Zlength B + k + 7) / 8 < q + 9); [ | lia].
  apply Z.div_lt_upper_bound; lia.
Qed.

Lemma pack_len B : Zlength (pack B) = (Zlength B + 7) / 8.
Proof.
  unfold pack. rewrite Zlength_map, Zlength_correct, seq_length.
  apply Z2Nat.id. apply Z.div_pos; [pose proof (Zlength_nonneg B) | ]; lia.
Qed.

Lemma bw_len_bound B cap c :
  bw_bytes_ok B cap c -> 0 <= Zlength B / 8 <= cap /\ (Zlength B + 7) / 8 <= cap.
Proof.
  intros (_ & H & _). rewrite pack_len in H. pose proof (Zlength_nonneg B).
  assert (Zlength B / 8 <= (Zlength B + 7) / 8) by (apply Z.div_le_mono; lia).
  split; [split; [apply Z.div_pos | ] | ]; lia.
Qed.

(* the argument of gp_assume(x + k <= 1 << 19) *)
Ltac room_arg x k m :=
  try change (let (q, _) := Z.div_eucl (Zlength ?B) 8 in q) with (Zlength B / 8);
  try change (Int.shl (Int.repr 1) (Int.repr 19)) with (Int.repr 524288);
  unfold Int.ltu; rewrite ?Int.add_signed, ?Int.unsigned_repr by rep_lia;
  destruct (zlt m (x + k)); destruct (Z.leb_spec (x + k) m); try lia; reflexivity.

(* abstract the big objects' sizes (array loads/stores overflow the stack on the literals), and restore them *)
Ltac abs_sizes :=
  set (N0 := 262144) in *; set (N1 := 262145) in *; set (N2 := 524288) in *;
  assert (HN0: 262144 <= N0 <= 262144) by (unfold N0; lia);
  assert (HN1: 262145 <= N1 <= 262145) by (unfold N1; lia);
  assert (HN2: 524288 <= N2 <= 524288) by (unfold N2; lia);
  clearbody N0 N1 N2.
Ltac rest_sizes :=
  match goal with N0: Z, N1: Z, N2: Z, HN0: 262144 <= ?N0 <= 262144, HN1: 262145 <= ?N1 <= 262145,
                  HN2: 524288 <= ?N2 <= 524288 |- _ =>
    assert (N0 = 262144) by lia; assert (N1 = 262145) by lia; assert (N2 = 524288) by lia; subst N0 N1 N2;
    clear HN0 HN1 HN2
  end.

Ltac show := match goal with |- semax _ ?P _ _ => fail 100 "PRE" P | |- ?G => fail 100 "GOAL" G end.
Ltac gpa := forward_call (Int.repr 1); [ solve [entailer!; try reflexivity] .. | ].

Ltac lt_arg x m k :=
  simpl; try change (Int.shl (Int.repr 1) (Int.repr k)) with (Int.repr m);
  unfold Int.ltu; rewrite ?Int.unsigned_repr by rep_lia;
  destruct (zlt x m); destruct (Z.ltb_spec x m); try lia; reflexivity.

Lemma zext8 x : 0 <= x <= 255 -> Int.zero_ext 8 (Int.repr x) = Int.repr x.
Proof.
  intros. apply zero_ext_inrange. rewrite Int.unsigned_repr by rep_lia. simpl. lia.
Qed.

Lemma flat_map_snoc {A B} (f: A -> list B) l x : flat_map f (l ++ [x]) = flat_map f l ++ f x.
Proof. induction l as [ | a r IH]; simpl; [rewrite app_nil_r; auto | rewrite IH, app_assoc; auto]. Qed.

Lemma syms_data_snoc out syms s : syms_data out (syms ++ [s]) = sym_data (syms_data out syms) s.
Proof. unfold syms_data. rewrite fold_left_app. reflexivity. Qed.

Lemma syms_ok_snoc w ll dl out syms s :
  syms_ok w ll dl out syms -> sym_ok w ll dl (syms_data out syms) s -> syms_ok w ll dl out (syms ++ [s]).
Proof.
  revert out. induction syms as [ | a r IH]; intros out H1 H2; simpl in *.
  - auto.
  - destruct H1. split; auto.
Qed.

Lemma data_ok_snoc dcont D b :
  data_ok dcont D -> Zlength D < 262144 -> 0 <= b <= 255 ->
  data_ok (upd_Znth (Zlength D) dcont (Vint (Int.repr b))) (D ++ [b]).
Proof.
  intros (HL & HDl & HDb & HDs) H1 H2.
  pose proof (Zlength_nonneg D).
  unfold data_ok. rewrite Zlength_upd_Znth, Zlength_app, Zlength_cons, Zlength_nil.
  refine (conj _ (conj _ (conj _ _))); [lia | lia | | ].
  - apply Forall_app. split; [exact HDb | constructor; [simpl; rep_lia | constructor]].
  - rewrite (sublist_split 0 (Zlength D) (Zlength D + 1)) by (rewrite ?Zlength_upd_Znth; lia).
    rewrite sublist_upd_Znth_l by lia. rewrite HDs.
    rewrite sublist_len_1 by (rewrite Zlength_upd_Znth; lia). rewrite upd_Znth_same by lia.
    unfold bytes_rep. rewrite map_app. reflexivity.
Qed.

Lemma fixed_ll_nz b : 0 <= b < 288 -> Znth b fixed_ll <> 0.
Proof.
  intros Hb.
  assert (HF: Forall (fun x => 7 <= x <= 9) fixed_ll).
  { assert (Hb': forallb (fun x => andb (7 <=? x) (x <=? 9)) fixed_ll = true) by (vm_compute; reflexivity).
    apply Forall_forall. intros x Hx. rewrite forallb_forall in Hb'. specialize (Hb' x Hx).
    apply andb_prop in Hb'. destruct Hb' as [X1 X2]. apply Z.leb_le in X1, X2. lia. }
  assert (Zlength fixed_ll = 288) by reflexivity.
  rewrite Forall_Znth in HF. specialize (HF b ltac:(lia)). lia.
Qed.

Lemma znth_sub_zvals (l: list val) m zs i :
  sublist 0 m l = zvals zs -> 0 <= i < m -> m <= Zlength l -> Znth i l = Vint (Int.repr (Znth i zs)).
Proof.
  intros H Hi Hm.
  assert (Zlength zs = m).
  { assert (Zlength (sublist 0 m l) = m) by (rewrite Zlength_sublist; lia).
    rewrite H in H0. unfold zvals in H0. rewrite Zlength_map in H0. exact H0. }
  replace (Znth i l) with (Znth i (sublist 0 m l)) by (rewrite Znth_sublist by lia; f_equal; lia).
  rewrite H. unfold zvals. rewrite Znth_map by lia. reflexivity.
Qed.

Lemma canon_vals_Znth lens i : 0 <= i < Zlength lens -> Znth i (canon_vals lens) = canon_val lens i.
Proof.
  intros Hi. unfold canon_vals.
  rewrite Znth_map by (rewrite Zlength_correct, seq_length, <- Zlength_correct; lia).
  f_equal. rewrite <- nth_Znth by (rewrite Zlength_correct, seq_length, <- Zlength_correct; lia).
  rewrite seq_nth by (rewrite Zlength_correct in Hi; lia). simpl. lia.
Qed.

Lemma bits_msb_mod16 c l : 0 <= l <= 16 -> bits_msb (c mod 65536) l = bits_msb c l.
Proof.
  intros Hl. unfold bits_msb, bits_le. f_equal. apply map_ext_in. intros i Hi.
  apply in_seq in Hi. change 65536 with (2 ^ 16). rewrite Z.mod_pow2_bits_low; [reflexivity | lia].
Qed.

(* rewrite with H: Znth i l = v, up to the Inhabitant instance *)
Ltac zrw H :=
  match type of H with @Znth ?A _ ?i ?l = ?v =>
    match goal with |- context [@Znth A ?d i l] =>
      replace (@Znth A d i l) with v by (rewrite <- H; reflexivity) end end.

Ltac xcontra := exfalso; first [match goal with H: ?x <> ?x |- _ => exact (H eq_refl) end
  | match goal with H: Int.repr ?a = Int.zero |- _ =>
      apply (f_equal Int.unsigned) in H; rewrite Int.unsigned_repr, Int.unsigned_zero in H by rep_lia; lia end
  | lia].

Lemma id_lit_ok {Espec: OracleKind} gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr
    bs ls isbz last hk llc lcc dcc syms dcont kind (R: ret_assert) :
  blk_hyps wrap wb flevel isel datap srcp isbp bs ls isbz last -> hk_ok hk -> hk_arrays_ok hk llc lcc dcc ->
  kind < 128 ->
  semax Delta_id
    (kind_at gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr bs ls isbz last hk llc lcc dcc
       syms dcont kind)
    seg_lit
    (loop1_ret_assert (sym_inv gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr bs ls isbz last
                         hk llc lcc dcc) R).
Proof.
  intros HH Hk Ha Hkind. destruct R as [Rn Rb Rc Rr].
  unfold kind_at. Intros.
  unfold seg_lit, Delta_id, Gmain_k. simplify_func_tycontext. abbreviate_semax.
  rename H into Hsyms. rename H0 into Hdata. rename H1 into Hkr. rename H2 into Hroom.
  forward_call tt. Intros lit.
  destruct hk as [ | nlen ndist cl toks]; cbv [hk_dyn hk_nlen hk_ndist hk_ll hk_dl hk_bits] in *.
  - match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _t'21 (Vint Int.zero) :: Q) (SEPx R))) end.
    { xcontra. }
    { forward. entailer!. }
    forward_if.
    { xcontra. }
    set (D := syms_data (expand [] bs) syms) in *.
    pose proof Hdata as (HdL & HDl & HDb & HDs).
    forward_call (Int.repr (if Zlength D <? 262144 then 1 else 0)).
    { entailer!. lt_arg (Zlength D) 262144 18. }
    assumed. apply Z.ltb_lt in E.
    pose proof (Zlength_nonneg D). clear HdL.
    abs_sizes.
    forward.
    rest_sizes.
    forward.
    rewrite zext8 by rep_lia.
    set (B := enc_bits (id_wrapper wrap wb flevel) bs ++ bits_le last 1 ++ [true; false] ++
              flat_map (send_one fixed_ll fixed_dl) syms) in *.
    forward_if.
    { xcontra. }
    forward_call (Tsh, Ews, B, 524288, srcp, vw, lit).
    { apply room8; [lia | exact Hroom | rep_lia]. }
    unfold sym_inv, sym_at. Exists (syms ++ [Lit lit]) (upd_Znth (Zlength D) dcont (Vint (Int.repr lit))).
    rewrite (flat_map_snoc (send_one fixed_ll fixed_dl)). simpl send_one.
    rewrite syms_data_snoc. simpl sym_data. fold D.
    assert (syms_ok (2 ^ wb) fixed_ll fixed_dl (expand [] bs) (syms ++ [Lit lit])).
    { apply syms_ok_snoc; auto. simpl. split; [unfold byte_ok; rep_lia | apply fixed_ll_nz; rep_lia]. }
    assert (data_ok (upd_Znth (Zlength D) dcont (Vint (Int.repr lit))) (D ++ [lit]))
      by (apply data_ok_snoc; auto; rep_lia).
    subst B. rewrite <- !app_assoc.
    entailer!.
    rewrite Zlength_app, Zlength_cons, Zlength_nil. reflexivity.
  - destruct Hk as (Hnlen & Hndist & Hhdr).
    pose proof Hhdr as (_ & _ & _ & _ & Hdlen & Hllok & _).
    destruct Ha as (Hcodes & Hll & Hlc & _).
    pose proof Hcodes as (Hllc & Hlcc & _).
    assert (Hlit: 0 <= lit < nlen) by rep_lia.
    set (L := Znth lit (dyn_ll nlen toks)).
    assert (HLr: 0 <= L <= 15).
    { destruct Hllok as (Hlo & _). unfold lens_ok in Hlo. rewrite Forall_Znth in Hlo. apply Hlo.
      unfold dyn_ll. rewrite Zlength_sublist by lia. lia. }
    assert (HL: Znth lit llc = Vint (Int.repr L)).
    { rewrite (znth_sub_zvals llc (nlen + ndist) (dyn_lens toks) lit) by first [exact Hll | lia].
      unfold L, dyn_ll. rewrite Znth_sublist by lia. rewrite Z.add_0_r. reflexivity. }
    assert (HC: Znth lit lcc = Vint (Int.repr (canon_val (dyn_ll nlen toks) lit))).
    { rewrite (znth_sub_zvals lcc nlen (canon_vals (dyn_ll nlen toks)) lit) by first [exact Hlc | lia].
      rewrite canon_vals_Znth; auto. unfold dyn_ll. rewrite Zlength_sublist by lia. lia. }
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _t'21 (Vint (Int.repr (if L =? 0 then 1 else 0))) :: Q) (SEPx R))) end.
    { abs_sizes. forward.
      { zrw HL. entailer!. rep_lia. }
      zrw HL. forward. rest_sizes. entailer!. destruct (zeq L 0), (Z.eqb_spec L 0); try lia; reflexivity. }
    { xcontra. }
    forward_if.
    { forward. unfold sym_inv, sym_at. Exists syms dcont. entailer!. }
    assert (HL0: L <> 0).
    { intro E. match goal with H: Int.repr (if L =? 0 then 1 else 0) = Int.zero |- _ =>
        rewrite E in H; simpl in H; xcontra end. }
    set (D := syms_data (expand [] bs) syms) in *.
    pose proof Hdata as (HdL & HDl & HDb & HDs).
    forward_call (Int.repr (if Zlength D <? 262144 then 1 else 0)).
    { entailer!. lt_arg (Zlength D) 262144 18. }
    assumed. apply Z.ltb_lt in E.
    pose proof (Zlength_nonneg D). clear HdL.
    abs_sizes.
    forward.
    rest_sizes.
    forward.
    rewrite zext8 by rep_lia.
    set (B := enc_bits (id_wrapper wrap wb flevel) bs ++ bits_le last 1 ++
              ([false; true] ++ dyn_hdr_bits nlen ndist cl toks) ++
              flat_map (send_one (dyn_ll nlen toks) (dyn_dl nlen ndist toks)) syms) in *.
    set (C := canon_val (dyn_ll nlen toks) lit) in *.
    assert (HCr: 0 <= C < 65536).
    { unfold C, canon_val. destruct (Znth lit (dyn_ll nlen toks) =? 0); [lia | apply Z.mod_pos_bound; lia]. }
    assert (ES: bits_msb C L = send_sym (dyn_ll nlen toks) lit).
    { unfold C, canon_val, send_sym. fold L. destruct (Z.eqb_spec L 0); [contradiction | ].
      apply bits_msb_mod16. lia. }
    forward_if.
    2: { xcontra. }
    abs_sizes.
    forward.
    { zrw HC. entailer!. lia. }
    zrw HC.
    forward.
    { zrw HL. entailer!. rep_lia. }
    zrw HL.
    rest_sizes.
    forward_call (Tsh, Ews, B, 524288, srcp, vw, C, L).
    { split; [lia | split; [apply room8; [lia | exact Hroom | rep_lia] | rep_lia]]. }
    rewrite ES.
    unfold sym_inv, sym_at. Exists (syms ++ [Lit lit]) (upd_Znth (Zlength D) dcont (Vint (Int.repr lit))).
    rewrite (flat_map_snoc (send_one (dyn_ll nlen toks) (dyn_dl nlen ndist toks))). simpl send_one.
    rewrite syms_data_snoc. simpl sym_data. fold D.
    assert (syms_ok (2 ^ wb) (dyn_ll nlen toks) (dyn_dl nlen ndist toks) (expand [] bs) (syms ++ [Lit lit])).
    { apply syms_ok_snoc; auto. simpl. split; [unfold byte_ok; rep_lia | exact HL0]. }
    assert (data_ok (upd_Znth (Zlength D) dcont (Vint (Int.repr lit))) (D ++ [lit]))
      by (apply data_ok_snoc; auto; rep_lia).
    subst B. cbv [hk_bits]. rewrite <- !app_assoc.
    entailer!.
    rewrite Zlength_app, Zlength_cons, Zlength_nil. reflexivity.
Qed.
