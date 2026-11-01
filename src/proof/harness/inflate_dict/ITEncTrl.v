(* Law inflate_dict, main encoder half: the trailer, up to slen = w.len, then the inflate half (statement in ITEncKit.v). *)
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
(* Pure facts over bits and pack (as ITEncStored.v)                                               *)

Lemma itt_Zlength_bits_le v n : 0 <= n -> Zlength (bits_le v n) = n.
Proof. intros. unfold bits_le. rewrite Zlength_map, Zlength_correct, seq_length. lia. Qed.

Lemma itt_Zlength_zeros n : 0 <= n -> Zlength (zeros n) = n.
Proof. intros. unfold zeros. rewrite Zlength_correct, repeat_length. lia. Qed.

Lemma itt_Zlength_bytes_bits l : Zlength (bytes_bits l) = 8 * Zlength l.
Proof.
  induction l as [|x r IH]; [reflexivity|].
  change (bytes_bits (x :: r)) with (bits_le x 8 ++ bytes_bits r).
  rewrite Zlength_app, IH, itt_Zlength_bits_le, Zlength_cons by lia. lia.
Qed.

Lemma itt_bits_le_ext a b n : 0 <= n -> (forall i, 0 <= i < n -> Z.testbit a i = Z.testbit b i) ->
  bits_le a n = bits_le b n.
Proof.
  intros Hn H. unfold bits_le. apply map_ext_in. intros i Hi. apply in_seq in Hi. apply H. lia.
Qed.

Lemma itt_bits_le_mod v n : 0 <= n -> bits_le (v mod 2 ^ n) n = bits_le v n.
Proof. intros. apply itt_bits_le_ext; auto. intros. apply Z.mod_pow2_bits_low. lia. Qed.

Lemma itt_map_seq_shift {A} (f: nat -> A) s len : map f (seq s len) = map (fun i => f (s + i)%nat) (seq 0 len).
Proof.
  revert s; induction len as [|len IH]; intros s; [reflexivity|].
  simpl. rewrite IH. rewrite Nat.add_0_r. f_equal. rewrite <- seq_shift, map_map.
  apply map_ext. intros i. f_equal. lia.
Qed.

Lemma itt_bits_le_split v a b : 0 <= a -> 0 <= b -> bits_le v (a + b) = bits_le v a ++ bits_le (v / 2 ^ a) b.
Proof.
  intros Ha Hb. unfold bits_le. rewrite Z2Nat.inj_add by lia. rewrite seq_app, map_app. f_equal.
  rewrite itt_map_seq_shift. apply map_ext_in. intros i Hi. apply in_seq in Hi.
  rewrite Z.div_pow2_bits by lia. f_equal. lia.
Qed.

Lemma itt_skipn_app_ge {A} n (l1 l2: list A) : (length l1 <= n)%nat -> skipn n (l1 ++ l2) = skipn (n - length l1) l2.
Proof. intros. rewrite skipn_app. rewrite skipn_all2 by lia. reflexivity. Qed.

Lemma itt_sublist_app_ge {A} (B C: list A) lo hi : Zlength B <= lo <= hi ->
  sublist lo hi (B ++ C) = sublist (lo - Zlength B) (hi - Zlength B) C.
Proof.
  intros H. unfold sublist. rewrite Zlength_correct in *. rewrite List.firstn_app.
  rewrite firstn_all2 by lia. rewrite itt_skipn_app_ge by lia.
  f_equal; [lia | f_equal; lia].
Qed.

Lemma itt_Zlength_pack B : Zlength (pack B) = (Zlength B + 7) / 8.
Proof.
  unfold pack. rewrite Zlength_map, Zlength_correct, seq_length.
  pose proof (Zlength_nonneg B). rewrite Z2Nat.id; auto. apply Z.div_pos; lia.
Qed.

Lemma itt_pack_app B C : Zlength B mod 8 = 0 -> pack (B ++ C) = pack B ++ pack C.
Proof.
  intros HB. pose proof (Zlength_nonneg B) as HB0. pose proof (Zlength_nonneg C) as HC0.
  assert (EB: Zlength B = 8 * (Zlength B / 8)) by (pose proof (Z.div_mod (Zlength B) 8); lia).
  set (k := Zlength B / 8) in *. assert (Hk: 0 <= k) by (apply Z.div_pos; lia).
  unfold pack. rewrite Zlength_app.
  assert (E1: (Zlength B + Zlength C + 7) / 8 = k + (Zlength C + 7) / 8).
  { rewrite EB. replace (8 * k + Zlength C + 7) with ((Zlength C + 7) + k * 8) by lia.
    rewrite Z.div_add by lia. lia. }
  assert (E2: (Zlength B + 7) / 8 = k).
  { rewrite EB. replace (8 * k + 7) with (7 + k * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
  rewrite E1, E2. assert (HCk: 0 <= (Zlength C + 7) / 8) by (apply Z.div_pos; lia).
  rewrite Z2Nat.inj_add by lia. rewrite seq_app, map_app. f_equal.
  - apply map_ext_in. intros i Hi. apply in_seq in Hi. f_equal.
    rewrite sublist_app1; auto; try lia.
  - rewrite itt_map_seq_shift. apply map_ext_in. intros i Hi. f_equal.
    rewrite itt_sublist_app_ge by lia. f_equal; lia.
Qed.

Lemma itt_bval_byte_all :
  forallb (fun x => bval (bits_le x 8) =? x) (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma itt_bval_byte x : 0 <= x < 256 -> bval (bits_le x 8) = x.
Proof.
  intros Hx. pose proof itt_bval_byte_all as H. rewrite forallb_forall in H.
  apply Z.eqb_eq. apply H. apply in_map_iff. exists (Z.to_nat x). split; [lia|]. apply in_seq. lia.
Qed.

Lemma itt_pack_byte x : 0 <= x < 256 -> pack (bits_le x 8) = [x].
Proof.
  intros Hx. unfold pack. rewrite itt_Zlength_bits_le by lia. change (Z.to_nat ((8 + 7) / 8)) with 1%nat.
  cbn [seq map]. change (8 * Z.of_nat 0) with 0. change (0 + 8) with 8.
  rewrite sublist_same by (rewrite ?itt_Zlength_bits_le; lia). rewrite itt_bval_byte; auto.
Qed.

Lemma itt_pack_bytes_bits l : is_bytes l -> pack (bytes_bits l) = l.
Proof.
  induction l as [|x r IH]; intros Hl; [reflexivity|].
  inversion Hl; subst. change (bytes_bits (x :: r)) with (bits_le x 8 ++ bytes_bits r). rewrite itt_pack_app.
  - rewrite itt_pack_byte by rep_lia. rewrite IH; auto.
  - rewrite itt_Zlength_bits_le by lia. reflexivity.
Qed.

Lemma itt_pack_app_bytes B l : Zlength B mod 8 = 0 -> is_bytes l -> pack (B ++ bytes_bits l) = pack B ++ l.
Proof. intros. rewrite itt_pack_app, itt_pack_bytes_bits; auto. Qed.

Lemma itt_zext8 x : Int.zero_ext 8 x = Int.repr (Int.unsigned x mod 256).
Proof. rewrite <- (Int.repr_unsigned (Int.zero_ext 8 x)). rewrite Int.zero_ext_mod by (cbn; lia). reflexivity. Qed.

Lemma itt_shru8 v : 0 <= v <= Int.max_unsigned -> Int.shru (Int.repr v) (Int.repr 8) = Int.repr (v / 256).
Proof.
  intros. rewrite Int.shru_div_two_p. rewrite !Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma itt_not v : 0 <= v <= Int.max_unsigned -> Int.not (Int.repr v) = Int.repr (Int.max_unsigned - v).
Proof.
  intros. rewrite Int.not_neg. unfold Int.neg. rewrite Int.unsigned_repr by rep_lia.
  unfold Int.mone. rewrite add_repr. apply Int.eqm_samerepr. exists (-1).
  change Int.max_unsigned with (Int.modulus - 1). lia.
Qed.

Lemma itt_pad8_shift h q : pad8 (8 * h + q) = pad8 q.
Proof. unfold pad8. f_equal. f_equal. replace (8 * h + q) with (q + h * 8) by lia. apply Z_mod_plus_full. Qed.

Lemma itt_pad8_props p : (p + pad8 p) mod 8 = 0 /\ 0 <= pad8 p < 8.
Proof. unfold pad8. split; Z.div_mod_to_equations; lia. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The stream                                                                                     *)

Lemma itt_be_bytes4 a :
  be_bytes a 4 = [Z.shiftr a 24 mod 256; Z.shiftr a 16 mod 256; Z.shiftr a 8 mod 256; Z.shiftr a 0 mod 256].
Proof. reflexivity. Qed.

Lemma itt_be_bytes_ok a : is_bytes (be_bytes a 4).
Proof.
  rewrite itt_be_bytes4. unfold is_bytes.
  repeat constructor; match goal with |- context [?x mod 256] => pose proof (Z.mod_pos_bound x 256) end; rep_lia.
Qed.

Lemma itt_land3 f : 0 <= f -> 0 <= Z.land f 3 <= 3.
Proof.
  intros Hf. assert (E: Z.land f 3 = f mod 4) by (apply (Z.land_ones f 2); lia).
  rewrite E. pose proof (Z.mod_pos_bound f 4 ltac:(lia)). lia.
Qed.

Lemma itt_hdr_ok E : ectx_ok E -> is_bytes (hdr_bytes E).
Proof.
  intros (Hwb & Hfl & _). unfold hdr_bytes. destruct (e_zlib E); [ | constructor].
  unfold is_bytes. apply Forall_app. split; [ | apply itt_be_bytes_ok].
  unfold zlib_hdr. pose proof (itt_land3 (e_flevel E) ltac:(lia)) as Hl.
  set (l := Z.land (e_flevel E) 3) in *.
  set (c := (e_wb E - 8) * 16 + 8). set (f0 := l * 64 + 32).
  pose proof (Z.mod_pos_bound (31 - (c * 256 + f0) mod 31) 31 ltac:(lia)).
  repeat constructor; unfold c, f0 in *; simpl; rep_lia.
Qed.

(* the bits of the stream: header, blocks, padding, trailer *)
Definition itt_trl (E: ectx) (bs: list block) : list bool :=
  if e_zlib E then bytes_bits (be_bytes (ref_adler32 1 (edata E bs)) 4) else [].

Lemma itt_src E bs : ectx_ok E ->
  let B0 := bytes_bits (hdr_bytes E) ++ enc_blocks 0 bs in
  pack ((B0 ++ zeros (pad8 (Zlength B0))) ++ itt_trl E bs) = it_src (eg E bs).
Proof.
  intros HE B0. unfold B0.
  rewrite Zlength_app, itt_Zlength_bytes_bits, itt_pad8_shift.
  rewrite <- !app_assoc. rewrite itt_pack_app by (rewrite itt_Zlength_bytes_bits, Z.mul_comm, Z_mod_mult; auto).
  rewrite itt_pack_bytes_bits by (apply itt_hdr_ok; auto).
  rewrite app_assoc. fold (deflate_bits bs).
  pose proof (itt_pad8_props (Zlength (enc_blocks 0 bs))) as [Hp Hp8].
  assert (Hd: Zlength (deflate_bits bs) mod 8 = 0).
  { unfold deflate_bits. rewrite Zlength_app, itt_Zlength_zeros by lia. auto. }
  unfold it_src, it_wrapper, eg, itt_trl, hdr_bytes; cbn [g_zlib g_wb g_flevel g_dict g_bs].
  destruct (e_zlib E).
  - rewrite itt_pack_app_bytes by (auto; apply itt_be_bytes_ok).
    unfold stream_bytes. rewrite <- !app_assoc. reflexivity.
  - rewrite app_nil_r. reflexivity.
Qed.

Lemma itt_it_ok E bs : ectx_ok E -> bs <> [] -> enc_ok E bs -> Zlength (edata E bs) <= 2 ^ 18 ->
  Zlength (it_src (eg E bs)) <= 2 ^ 19 -> it_ok (eg E bs).
Proof.
  intros (Hwb & Hfl & Hi & Hw & Hdl & Hdb & _) Hne (Hnd & Hok) Hd Hs.
  unfold it_ok. cbn [g_wb g_flevel g_dict g_bs g_zlib g_iw eg].
  split; [lia | ]. split; [lia | ]. split; [auto | ]. split; [exact Hd | ]. split; [exact Hs | ].
  split; [exact Hnd | ]. split.
  - unfold stream_ok, it_wrapper, wrapper_ok, wf. cbn [g_wb g_flevel g_dict g_bs g_zlib eg].
    assert (Hb: Forall byte_ok (e_dict E)) by (eapply Forall_impl; [ | exact Hdb]; intros x Hx; unfold byte_ok; rep_lia).
    destruct (e_zlib E).
    + split; [lia | ]. split; [split; [lia | split; [apply itt_land3; lia | reflexivity]] | ].
      split; [reflexivity | ]. split; auto.
    + split; [lia | ]. split; [exact I | ]. split; [exact I | ]. split; auto.
  - unfold iw_of. destruct (e_zlib E); [ | reflexivity].
    destruct (e_isel E <? 85); [left; reflexivity | ]. destruct (e_isel E <? 170); [right; left; reflexivity | ].
    right; right; reflexivity.
Qed.

Lemma itt_trl_len E bs : Zlength (itt_trl E bs) = if e_zlib E then 32 else 0.
Proof. unfold itt_trl. destruct (e_zlib E); [rewrite itt_Zlength_bytes_bits; reflexivity | reflexivity]. Qed.

(* hides an equation from entailer!'s subst *)
Definition itt_hide (P: Prop) : Prop := P.

Lemma itt_arg a k : 0 <= a < 2 ^ 32 -> 0 <= k < 32 ->
  Int.zero_ext 8 (Int.repr (Int64.unsigned (Int64.shru (Int64.repr a) (Int64.repr k)))) = Int.repr (Z.shiftr a k mod 256).
Proof.
  intros Ha Hk. unfold Int64.shru. rewrite (Int64.unsigned_repr a) by rep_lia. rewrite (Int64.unsigned_repr k) by rep_lia.
  assert (0 <= Z.shiftr a k <= a).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | ].
    apply Z.div_le_upper_bound; [lia | ]. pose proof (Z.pow_pos_nonneg 2 k). assert (1 <= 2 ^ k) by (change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia). nia. }
  rewrite Int64.unsigned_repr by rep_lia.
  rewrite <- (Int.repr_unsigned (Int.zero_ext 8 _)). rewrite Int.zero_ext_mod by (cbn; lia).
  rewrite Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma itt_eval a k : 0 <= a < 2 ^ 32 -> 0 <= k < 32 ->
  eval_cast tuchar tuchar (eval_cast tulong tuchar (eval_binop Oshr tulong tint (Vlong (Int64.repr a)) (Vint (Int.repr k)))) =
  Vint (Int.repr (Z.shiftr a k mod 256)).
Proof.
  intros Ha Hk. unfold eval_binop, eval_cast. cbn - [Int64.repr Int64.shru Int.repr Int64.unsigned Int.zero_ext Int64.ltu Int.unsigned Int64.iwordsize].
  rewrite (Int.unsigned_repr k) by rep_lia. rewrite itt_arg by auto. f_equal.
  pose proof (Z.mod_pos_bound (Z.shiftr a k) 256 ltac:(lia)).
  rewrite itt_zext8, Int.unsigned_repr by rep_lia. rewrite Zmod_mod. reflexivity.
Qed.

Lemma itt_eval0 a : 0 <= a < 2 ^ 32 ->
  eval_cast tuchar tuchar (eval_cast tulong tuchar (Vlong (Int64.repr a))) = Vint (Int.repr (Z.shiftr a 0 mod 256)).
Proof.
  intros Ha. unfold eval_cast. cbn - [Int64.repr Int.repr Int64.unsigned Int.zero_ext Int.unsigned].
  rewrite ?Z.shiftr_0_r, Int64.unsigned_repr by rep_lia. f_equal.
  pose proof (Z.mod_pos_bound a 256 ltac:(lia)).
  rewrite !itt_zext8, (Int.unsigned_repr a), Int.unsigned_repr by rep_lia. rewrite Zmod_mod. reflexivity.
Qed.

(* the argument (unsigned char) (a >> k) of bw_byte, after forward_call (va: a's value, hidden) *)
Ltac itt_argt Hva Ha ev :=
  entailer!; unfold itt_hide in Hva; subst; cbn [typeof firstn length];
  match goal with |- [?p; ?x] = [?q; ?y] =>
    assert (Ep: p = q) by (destruct q; try contradiction; reflexivity);
    assert (Ex: x = y) by (exact ev); rewrite Ep, Ex; reflexivity end.

Ltac itt_room Ht :=
  unfold bw_room; rewrite ?Zlength_app, ?itt_Zlength_bits_le, ?Ht by lia;
  repeat match goal with |- context [?x mod 256] =>
    lazymatch goal with H: 0 <= x mod 256 < 256 |- _ => fail | _ => pose proof (Z.mod_pos_bound x 256 ltac:(lia)) end end;
  repeat split; try rep_lia; Z.div_mod_to_equations; lia.

Lemma itt_post_ent (Delta: tycontext) (P Q: environ -> mpred) (R: ret_assert) :
  ENTAIL Delta, P |-- Q -> ENTAIL Delta, P |-- RA_normal (overridePost Q R).
Proof. intros H. destruct R. exact H. Qed.

Local Arguments Z.div : simpl never.
Local Arguments Z.modulo : simpl never.

Lemma seg_trl_ok {Espec: OracleKind} : seg_trl_stmt.
Proof.
  intros K E bs dcont. unfold blk_end, S_trl. Intros.
  set (B0 := bytes_bits (hdr_bytes E) ++ enc_blocks 0 bs).
  rewrite bw_at_law. Intros c0.
  assert (Hr0: (Zlength B0 + 7) / 8 <= 2 ^ 19)
    by (destruct H3 as (_ & Hp & _); rewrite itt_Zlength_pack in Hp; auto).
  gather_SEP (data_at Tsh (Tstruct _bw noattr) _ (e_vw E)) (data_at Ews (tarray tuchar (2 ^ 19)) c0 (e_srcp E)).
  replace_SEP 0 (bw_at Tsh Ews B0 (2 ^ 19) (e_srcp E) (e_vw E)).
  { entailer!. rewrite bw_at_law. Exists c0. entailer!. }
  forward_call (Tsh, Ews, B0, 2 ^ 19, e_srcp E, e_vw E).
  { unfold bw_room. rewrite Z.add_0_r. rep_lia. }
  pose proof (Zlength_nonneg B0) as HB00.
  set (p0 := pad8 (Zlength B0)). pose proof (itt_pad8_props (Zlength B0)) as Hp0. fold p0 in Hp0.
  set (B1 := B0 ++ zeros p0).
  assert (HB1: Zlength B1 = Zlength B0 + p0) by (unfold B1; rewrite Zlength_app, itt_Zlength_zeros by lia; lia).
  set (t := Zlength B1 / 8).
  assert (Ht: Zlength B1 = 8 * t) by (unfold t; rewrite HB1 in *; Z.div_mod_to_equations; lia).
  assert (Ht1: t <= 2 ^ 19) by (rewrite HB1 in Ht; Z.div_mod_to_equations; lia).
  assert (Hmod1: Zlength B1 mod 8 = 0) by (rewrite Ht, Z.mul_comm, Z_mod_mult; auto).
  clearbody t.
  assert (Hdiv1: Zlength B1 / 8 = t) by (rewrite Ht, Z.mul_comm, Z_div_mult; lia).
  rewrite bw_at_law. Intros c1. rewrite Hdiv1, Hmod1.
  forward.
  forward_call (Int.repr (if t + 4 <=? 2 ^ 19 then 1 else 0)).
  { entailer!. change (Int.shl (Int.repr 1) (Int.repr 19)) with (Int.repr (2 ^ 19)). arg_cmp. }
  assumed. apply Z.leb_le in E0.
  gather_SEP (data_at Tsh (Tstruct _bw noattr) _ (e_vw E)) (data_at Ews (tarray tuchar (2 ^ 19)) c1 (e_srcp E)).
  replace_SEP 0 (bw_at Tsh Ews B1 (2 ^ 19) (e_srcp E) (e_vw E)).
  { entailer!. rewrite bw_at_law. Exists c1. rewrite Hmod1. entailer!. }
  set (B2 := B1 ++ itt_trl E bs).
  match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx (_ :: ?R)))) _ _ =>
    forward_if (PROPx [] (LOCALx Q (SEPx (bw_at Tsh Ews B2 (2 ^ 19) (e_srcp E) (e_vw E) :: R)))) end.
  { destruct (e_zlib E) eqn:Hz; [ | contradiction].
    destruct H2 as (Hdc & HDl & HDb & HDs).
    destruct H as (Hwb & Hfl & Hi & Hw & Hdl & Hdb & Pd & Pb & Pa & Ps).
    forward_call (1, e_datap E, Ews, e_datap E, 0, 2 ^ 18, dcont, Zlength (edata E bs), edata E bs).
    { rewrite bytes_adler_cs. cancel. }
    { repeat (split; [rep_lia|]). unfold cbuf_ok. rewrite isptr_offset_val_zero by auto.
      pose proof (Zlength_nonneg (edata E bs)). repeat split; auto; lia. }
    rewrite ?bytes_adler_cs.
    set (a := ref_adler32 1 (edata E bs)).
    assert (Ha: 0 <= a < 2 ^ 32).
    { apply ref_adler32_valid. unfold adler_valid, adler_lo, adler_hi, ADLER_BASE. cbn. split; [lia | split; reflexivity]. }
    assert (Haq: itt_hide (ref_adler32 1 (edata E bs) = a)) by reflexivity.
    clearbody a.
    remember (Vlong (Int64.repr a)) as va eqn:Hva'.
    assert (Hva: itt_hide (va = Vlong (Int64.repr a))) by exact Hva'. clear Hva'.
    forward_call (Tsh, Ews, B1, 2 ^ 19, e_srcp E, e_vw E, Z.shiftr a 24 mod 256).
    { itt_argt Hva Ha (itt_eval a 24 Ha ltac:(lia)). }
    { itt_room Ht. }
    forward_call (Tsh, Ews, B1 ++ bits_le (Z.shiftr a 24 mod 256) 8, 2 ^ 19, e_srcp E, e_vw E, Z.shiftr a 16 mod 256).
    { itt_argt Hva Ha (itt_eval a 16 Ha ltac:(lia)). }
    { itt_room Ht. }
    forward_call (Tsh, Ews, (B1 ++ bits_le (Z.shiftr a 24 mod 256) 8) ++ bits_le (Z.shiftr a 16 mod 256) 8, 2 ^ 19,
                  e_srcp E, e_vw E, Z.shiftr a 8 mod 256).
    { itt_argt Hva Ha (itt_eval a 8 Ha ltac:(lia)). }
    { itt_room Ht. }
    forward_call (Tsh, Ews, ((B1 ++ bits_le (Z.shiftr a 24 mod 256) 8) ++ bits_le (Z.shiftr a 16 mod 256) 8) ++
                  bits_le (Z.shiftr a 8 mod 256) 8, 2 ^ 19, e_srcp E, e_vw E, Z.shiftr a 0 mod 256).
    { itt_argt Hva Ha (itt_eval0 a Ha). }
    { itt_room Ht. }
    assert (EB: (((B1 ++ bits_le (Z.shiftr a 24 mod 256) 8) ++ bits_le (Z.shiftr a 16 mod 256) 8) ++
                 bits_le (Z.shiftr a 8 mod 256) 8) ++ bits_le (Z.shiftr a 0 mod 256) 8 = B2).
    { unfold B2, itt_trl. rewrite Hz. unfold itt_hide in Haq. rewrite Haq, itt_be_bytes4.
      cbn [bytes_bits flat_map]. rewrite app_nil_r, <- !app_assoc. reflexivity. }
    rewrite EB. apply itt_post_ent. entailer!. }
  { destruct (e_zlib E) eqn:Hz; [exfalso; apply Int.one_not_zero; exact H5 | ].
    assert (EB: B1 = B2) by (unfold B2, itt_trl; rewrite Hz, app_nil_r; reflexivity).
    rewrite EB. forward. apply itt_post_ent. entailer!. }
  assert (HB2: Zlength B2 = 8 * (t + if e_zlib E then 4 else 0)).
  { unfold B2. rewrite Zlength_app, itt_trl_len, Ht. destruct (e_zlib E); lia. }
  assert (Hm2: Zlength B2 mod 8 = 0) by (rewrite HB2, Z.mul_comm, Z_mod_mult; auto).
  assert (Hd2: Zlength B2 / 8 = t + if e_zlib E then 4 else 0) by (rewrite HB2, Z.mul_comm, Z_div_mult; lia).
  assert (Hsrc: it_src (eg E bs) = pack B2) by (symmetry; apply itt_src; auto).
  assert (Hsl: Zlength (it_src (eg E bs)) = t + if e_zlib E then 4 else 0).
  { rewrite Hsrc, itt_Zlength_pack, <- Hd2. Z.div_mod_to_equations; lia. }
  rewrite bw_at_law. Intros c2. rewrite Hm2, Hd2.
  forward.
  eapply semax_pre; [ | apply (K (e_gv E) (e_vw E) (e_vs E) (e_vosn E) (e_vdl E) (e_dictp E) (e_badp E) (e_datap E)
                                (e_srcp E) (eg E bs) (e_isel E) (e_wsel E) dcont c2 I) ].
  destruct H5 as (Hc2 & Hp2 & Hs2). rewrite <- Hsrc in Hp2, Hs2.
  pose proof H2 as (Hdc & HDl & HDb & HDs).
  assert (Hok: it_ok (eg E bs)) by (apply itt_it_ok; auto).
  pose proof H as (_ & _ & Hi & Hw & _ & Hdb & Pd & Pb & Pa & Ps).
  unfold enc_done. rewrite Hsl. rewrite Hsl in Hs2. unfold enc_fr.
  rewrite eg_data, eg_bad, eg_dictid. cbn [g_zlib g_wb g_dict g_iw eg].
  sep_apply (data_at_data_at_ Tsh (Tstruct _bw noattr)
    (e_srcp E, (Vint (Int.repr (t + (if e_zlib E then 4 else 0))), Vint (Int.repr 0))) (e_vw E)).
  set (N18 := 2 ^ 18) in *. set (N19 := 2 ^ 19) in *.
  assert (HN: itt_hide (N18 = 2 ^ 18 /\ N19 = 2 ^ 19)) by (split; reflexivity).
  clearbody N18 N19.
  entailer!.
Qed.
