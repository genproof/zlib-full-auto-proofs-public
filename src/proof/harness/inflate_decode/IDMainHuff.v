(* Law inflate_decode, main: a Huffman block up to its symbol loop (the branch bt != 0 of the block loop's body:
   dyn, nlen, ndist, the dynamic header by dyn_header or BTYPE 01). *)
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
(* Helpers                                                                                        *)

Lemma huff_uchar_cs sh n (v: list val) q :
  @data_at Zlib.contracts.x_inflate_decode.Harness.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_harness); [apply JMeq_refl | reflexivity]. Qed.

Lemma huff_ushort_cs sh n (v: list val) q :
  @data_at Zlib.contracts.x_inflate_decode.Harness.CS sh (tarray tushort n) v q = @data_at CS sh (tarray tushort n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_harness); [apply JMeq_refl | reflexivity]. Qed.

Lemma huff_bits22 : bits_le 2 2 = [false; true].
Proof. reflexivity. Qed.
Lemma huff_bits12 : bits_le 1 2 = [true; false].
Proof. reflexivity. Qed.

(* 8 bytes of room (the harness's gp_assume) give room for 57 bits (IDMainBlk.room8) *)
Lemma huff_room8 B cap k : 0 <= k <= 57 -> Zlength B / 8 + 8 <= cap -> cap <= Int.max_unsigned -> bw_room B cap k.
Proof.
  intros Hk Hr Hc. unfold bw_room. split; [lia | split; [ | lia]].
  pose proof (Zlength_nonneg B). pose proof (Z.div_mod (Zlength B) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (Zlength B) 8 ltac:(lia)).
  set (q := Zlength B / 8) in *. set (r := Zlength B mod 8) in *.
  assert ((Zlength B + k + 7) / 8 < q + 9); [ | lia].
  apply Z.div_lt_upper_bound; lia.
Qed.

Lemma huff_pack_len B : Zlength (pack B) = (Zlength B + 7) / 8.
Proof.
  unfold pack. rewrite Zlength_map, Zlength_correct, seq_length.
  apply Z2Nat.id. apply Z.div_pos; [pose proof (Zlength_nonneg B) | ]; lia.
Qed.

Lemma huff_len_bound B cap c :
  bw_bytes_ok B cap c -> 0 <= Zlength B / 8 <= cap /\ (Zlength B + 7) / 8 <= cap.
Proof.
  intros (_ & H & _). rewrite huff_pack_len in H. pose proof (Zlength_nonneg B).
  assert (Zlength B / 8 <= (Zlength B + 7) / 8) by (apply Z.div_le_mono; lia).
  split; [split; [apply Z.div_pos | ] | ]; lia.
Qed.

Lemma huff_bw_at_law sh bsh B cap buf w :
  bw_at sh bsh B cap buf w =
  EX c: list val, !! bw_bytes_ok B cap c &&
    (@data_at CS sh (Tstruct _bw noattr)
       (buf, (Vint (Int.repr (Zlength B / 8)), Vint (Int.repr (Zlength B mod 8)))) w *
     @data_at Zlib.contracts.x_inflate_decode.Harness.CS bsh (tarray tuchar cap) c buf)%logic.
Proof.
  unfold bw_at, bw_rep. f_equal. extensionality c. f_equal. f_equal.
  apply equal_f; apply (@data_at_change_composite _ _ CC_harness); [apply JMeq_refl | reflexivity].
Qed.

Lemma huff_bw_fold sh bsh B cap buf w c : bw_bytes_ok B cap c ->
  (@data_at CS sh (Tstruct _bw noattr)
     (buf, (Vint (Int.repr (Zlength B / 8)), Vint (Int.repr (Zlength B mod 8)))) w *
   @data_at Zlib.contracts.x_inflate_decode.Harness.CS bsh (tarray tuchar cap) c buf)%logic
  |-- bw_at sh bsh B cap buf w.
Proof. intros. rewrite huff_bw_at_law. Exists c. entailer!. Qed.

Lemma huff_room_bfinal E l cap k :
  0 <= k <= 49 -> Zlength E / 8 + 8 <= cap -> cap <= Int.max_unsigned -> bw_room (E ++ bits_le l 1) cap k.
Proof.
  intros Hk Hr Hc. unfold bw_room. split; [lia | split; [ | lia]].
  rewrite Zlength_app. change (Zlength (bits_le l 1)) with 1.
  pose proof (Zlength_nonneg E). pose proof (Z.div_mod (Zlength E) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (Zlength E) 8 ltac:(lia)).
  set (q := Zlength E / 8) in *. set (r := Zlength E mod 8) in *.
  assert ((Zlength E + 1 + k + 7) / 8 < q + 9); [ | lia].
  apply Z.div_lt_upper_bound; lia.
Qed.

(* the room of dyn_header from the harness's gp_assume *)
Lemma huff_dyn_room B nlen ndist :
  Zlength B / 8 + 16 + 2 * (nlen + ndist) <= 524288 ->
  Zlength (B ++ bits_le 2 2) / 8 + 15 + 2 * (nlen + ndist) <= 524288.
Proof.
  intros H. rewrite huff_bits22, Zlength_app. change (Zlength [false; true]) with 2.
  pose proof (Zlength_nonneg B).
  assert ((Zlength B + 2) / 8 < Zlength B / 8 + 2); [ | lia].
  pose proof (Z.div_mod (Zlength B) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Zlength B) 8 ltac:(lia)).
  apply Z.div_lt_upper_bound; lia.
Qed.

Lemma huff_canon_len lens : Zlength (canon_vals lens) = Zlength lens.
Proof. unfold canon_vals. rewrite Zlength_map, !Zlength_correct, seq_length. reflexivity. Qed.

Lemma huff_arrays nlen ndist clsent toks llc lcc dcc :
  257 <= nlen <= 286 -> 1 <= ndist <= 30 -> dyn_hdr_ok nlen ndist clsent toks -> codes_ok llc lcc dcc ->
  hk_arrays_ok (HDyn nlen ndist clsent toks)
    (zvals (dyn_lens toks) ++ sublist (nlen + ndist) 316 llc)
    (zvals (canon_vals (dyn_ll nlen toks)) ++ sublist nlen 286 lcc)
    (zvals (canon_vals (dyn_dl nlen ndist toks)) ++ sublist ndist 30 dcc).
Proof.
  intros Hn Hd (_ & _ & _ & _ & Hl & _ & _) (H1 & H2 & H3).
  assert (Hll: Zlength (dyn_ll nlen toks) = nlen) by (unfold dyn_ll; rewrite Zlength_sublist; lia).
  assert (Hdl: Zlength (dyn_dl nlen ndist toks) = ndist) by (unfold dyn_dl; rewrite Zlength_sublist; lia).
  unfold zvals.
  split; [unfold codes_ok | ]; rewrite ?Zlength_app, ?Zlength_map, ?huff_canon_len, ?Zlength_sublist by lia.
  - lia.
  - split; [ | split]; rewrite sublist0_app1 by (rewrite ?Zlength_map, ?huff_canon_len; lia);
      rewrite sublist_same by (rewrite ?Zlength_map, ?huff_canon_len; lia); reflexivity.
Qed.

Ltac hcmp :=
  repeat match goal with H: context [Z.leb ?a ?b] |- _ => destruct (Z.leb_spec a b) end;
  cbn [andb] in *; try lia;
  try match goal with H: Int.repr 1 = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact H end;
  arg_cmp.

Ltac huff_room_arg x k m :=
  try change (let (q, _) := Z.div_eucl (Zlength ?B) 8 in q) with (Zlength B / 8);
  try change (Int.shl (Int.repr 1) (Int.repr 19)) with (Int.repr 524288);
  unfold Int.ltu; rewrite ?Int.add_signed, ?Int.mul_signed, ?Int.unsigned_repr, ?Int.signed_repr by rep_lia;
  destruct (zlt m (x + k)); destruct (Z.leb_spec (x + k) m); try lia; reflexivity.

Lemma id_huff_ok {Espec: OracleKind} gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr
    bs ls dcont isbz llc lcc dcc last bt (R: ret_assert) :
  blk_hyps wrap wb flevel isel datap srcp isbp bs ls isbz last -> 1 <= bt <= 3 ->
  (forall hk llc' lcc' dcc', hk_ok hk -> (hk_dyn hk = 1 <-> bt = 2) -> hk_arrays_ok hk llc' lcc' dcc' ->
     semax Delta_id (sym_inv gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr bs ls isbz last
                       hk llc' lcc' dcc') S_sym R) ->
  semax Delta_id
    (blk_mid gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr bs ls dcont isbz llc lcc dcc last bt)
    S_huff R.
Proof.
  intros HH Hbt Hk. destruct R as [Rn Rb Rc Rr].
  unfold S_huff. apply <- seq_assoc. apply <- seq_assoc. apply <- seq_assoc.
  apply semax_seq with (Q := EX hk: hkind, EX llc': list val, EX lcc': list val, EX dcc': list val,
    !! (hk_ok hk /\ (hk_dyn hk = 1 <-> bt = 2) /\ hk_arrays_ok hk llc' lcc' dcc') &&
    sym_inv gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr bs ls isbz last hk llc' lcc' dcc').
  2: { apply extract_exists_pre; intro hk. apply extract_exists_pre; intro llc'.
       apply extract_exists_pre; intro lcc'. apply extract_exists_pre; intro dcc'.
       apply semax_extract_prop; intros (H1 & H2 & H3). apply Hk; auto. }
  unfold blk_mid. Intros.
  unfold Delta_id, Gmain_k. simplify_func_tycontext. abbreviate_semax.
  forward. forward. forward.
  set (B := enc_bits (id_wrapper wrap wb flevel) bs ++ bits_le last 1) in *.
  forward_if.
  { (* dynamic *)
    forward_call tt. Intros nlen.
    forward_call tt. Intros ndist.
    forward_if (temp _t'16 (Vint (Int.repr (if andb (257 <=? nlen) (nlen <=? 286) then 1 else 0)))).
    { forward. entailer!. hcmp. }
    { forward. entailer!. hcmp. }
    forward_if (temp _t'17 (Vint (Int.repr (if andb (andb (257 <=? nlen) (nlen <=? 286)) (1 <=? ndist) then 1 else 0)))).
    { forward. entailer!. hcmp. }
    { forward. entailer!. hcmp. }
    forward_if (temp _t'18 (Vint (Int.repr (if andb (andb (andb (257 <=? nlen) (nlen <=? 286)) (1 <=? ndist)) (ndist <=? 30) then 1 else 0)))).
    { forward. entailer!. hcmp. }
    { forward. entailer!. hcmp. }
    forward_call (Int.repr (if andb (andb (andb (257 <=? nlen) (nlen <=? 286)) (1 <=? ndist)) (ndist <=? 30) then 1 else 0)).
    assumed. rewrite !andb_true_iff, !Z.leb_le in E.
    rewrite huff_bw_at_law. Intros c.
    forward.
    destruct (huff_len_bound _ _ _ H6) as [HB0 HB1].
    forward_call (Int.repr (if Zlength B / 8 + 16 + 2 * (nlen + ndist) <=? 524288 then 1 else 0)).
    { clearbody B. entailer!. huff_room_arg (Zlength B / 8 + 16) (2 * (nlen + ndist)) 524288. }
    assumed. apply Z.leb_le in E0.
    sep_apply (huff_bw_fold Tsh Ews B 524288 srcp vw c H6).
    forward_call (Tsh, Ews, B, 524288, srcp, vw, 2, 2).
    { apply huff_room8; rep_lia. }
    rewrite <- (huff_uchar_cs Tsh 316 llc vll), <- (huff_ushort_cs Tsh 286 lcc vlc),
      <- (huff_ushort_cs Tsh 30 dcc vdc), <- (huff_uchar_cs Ers 19 (zvals clorder) (gv _cl_order)).
    forward_call (gv, Tsh, Ews, B ++ bits_le 2 2, 524288, srcp, vw, nlen, ndist, Tsh, vll, llc, vlc, lcc, vdc, dcc).
    { destruct H0 as (? & ? & ?). repeat split; auto; try lia; try rep_lia. apply huff_dyn_room; lia. }
    Intros vret. destruct vret as [clsent toks]. cbn [fst snd] in *.
    rewrite !huff_uchar_cs, !huff_ushort_cs.
    destruct E as ((En & Ed1) & Ed2).
    Exists (HDyn nlen ndist clsent toks)
      (zvals (dyn_lens toks) ++ sublist (nlen + ndist) 316 llc)
      (zvals (canon_vals (dyn_ll nlen toks)) ++ sublist nlen 286 lcc)
      (zvals (canon_vals (dyn_dl nlen ndist toks)) ++ sublist ndist 30 dcc).
    unfold sym_inv, sym_at. Exists (@nil sym) dcont.
    cbn [hk_bits hk_dyn hk_nlen hk_ndist hk_ll hk_dl flat_map syms_ok syms_data fold_left].
    unfold syms_data; cbn [fold_left].
    rewrite H3. subst B. rewrite <- !app_assoc, huff_bits22, app_nil_r.
    pose proof (huff_arrays nlen ndist clsent toks llc lcc dcc ltac:(lia) ltac:(lia) H7 H0).
    entailer!.
    split; [simpl; split; [lia | split; [lia | auto]] | ].
    destruct (zeq bt 2); [tauto | discriminate]. }
  { (* fixed *)
    forward_call (Tsh, Ews, B, 524288, srcp, vw, 1, 2).
    { subst B. apply huff_room_bfinal; rep_lia. }
    Exists HFix llc lcc dcc.
    unfold sym_inv, sym_at. Exists (@nil sym) dcont.
    cbn [hk_bits hk_dyn hk_nlen hk_ndist hk_ll hk_dl flat_map syms_ok syms_data fold_left].
    unfold syms_data; cbn [fold_left].
    rewrite H3. subst B. rewrite <- !app_assoc, huff_bits12, app_nil_r.
    entailer!.
    split.
    + split; [intro X; discriminate | intro X; subst bt; destruct (zeq 2 2); simpl in H3; congruence].
    + split; [exact H0 | exact I]. }
Qed.