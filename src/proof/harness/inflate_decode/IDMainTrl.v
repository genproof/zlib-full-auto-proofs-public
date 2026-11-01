(* Law inflate_decode, main: after the block loop, the trailer (bw_align, the Adler-32 / CRC-32 and length
   bytes), slen, the garbage, total. *)
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

Require Zlib.proof.crc32.Combine.

(* ---------------------------------------------------------------------------------------------- *)
(* Pure facts: packing bits into bytes                                                            *)

Lemma trl_bits_le_len v n : 0 <= n -> Zlength (bits_le v n) = n.
Proof. intros. unfold bits_le. rewrite Zlength_map, Zlength_correct, seq_length. apply Z2Nat.id; lia. Qed.

Lemma trl_bytes_bits_len l : Zlength (bytes_bits l) = 8 * Zlength l.
Proof.
  induction l as [|b r IH]; [reflexivity | ].
  unfold bytes_bits in *. cbn [flat_map]. rewrite Zlength_app, IH, trl_bits_le_len, Zlength_cons by lia. lia.
Qed.

Lemma trl_zeros_len n : 0 <= n -> Zlength (zeros n) = n.
Proof. intros. unfold zeros. rewrite Zlength_correct, repeat_length. apply Z2Nat.id; lia. Qed.

Lemma trl_map_seq_shift {A} (f: nat -> A) a m :
  map f (seq a m) = map (fun k => f (a + k)%nat) (seq 0 m).
Proof.
  revert a f. induction m as [|m IH]; intros a f; [reflexivity | ].
  simpl. rewrite Nat.add_0_r. f_equal. rewrite IH, (IH 1%nat (fun k => f (a + k)%nat)).
  apply map_ext. intros k. f_equal. lia.
Qed.

Lemma trl_pack_app X Y : Zlength X mod 8 = 0 -> pack (X ++ Y) = pack X ++ pack Y.
Proof.
  intros HX. unfold pack.
  pose proof (Zlength_nonneg X). pose proof (Zlength_nonneg Y).
  set (q := Zlength X / 8).
  assert (EXl: Zlength X = 8 * q) by (pose proof (Z.div_mod (Zlength X) 8); subst q; lia).
  assert (Hq: 0 <= q) by lia.
  assert (Eq: (Zlength (X ++ Y) + 7) / 8 = q + (Zlength Y + 7) / 8).
  { rewrite Zlength_app, EXl.
    replace (8 * q + Zlength Y + 7) with ((Zlength Y + 7) + q * 8) by lia.
    rewrite Z.div_add by lia. lia. }
  assert (Eq2: (Zlength X + 7) / 8 = q).
  { rewrite EXl. replace (8 * q + 7) with (7 + q * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
  assert (HY: 0 <= (Zlength Y + 7) / 8) by (apply Z.div_pos; lia).
  rewrite Eq, Eq2, Z2Nat.inj_add, seq_app, map_app by lia.
  f_equal.
  - apply map_ext_in. intros k Hk. apply in_seq in Hk.
    rewrite sublist_app1; auto; rewrite ?EXl; lia.
  - rewrite trl_map_seq_shift. apply map_ext. intros k.
    rewrite sublist_app2 by (rewrite EXl; lia). rewrite EXl, !Nat2Z.inj_add, Z2Nat.id by lia.
    f_equal; f_equal; lia.
Qed.

Lemma trl_bval_byte_all :
  forallb (fun k => let b := Z.of_nat k in
                    if list_eq_dec Z.eq_dec (pack (bits_le b 8)) [b] then true else false) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma trl_pack_byte b : 0 <= b < 256 -> pack (bits_le b 8) = [b].
Proof.
  intros Hb. pose proof trl_bval_byte_all as H. rewrite forallb_forall in H.
  specialize (H (Z.to_nat b)). rewrite in_seq, Z2Nat.id in H by lia.
  cbv zeta in H. destruct (list_eq_dec Z.eq_dec (pack (bits_le b 8)) [b]); auto.
  exfalso. assert (false = true) by (apply H; lia). discriminate.
Qed.

Lemma trl_pack_nil : pack [] = [].
Proof. reflexivity. Qed.

Lemma trl_pack_bytes_bits l : is_bytes l -> pack (bytes_bits l) = l.
Proof.
  induction l as [|b r IH]; intros Hl; [reflexivity | ].
  inversion Hl; subst. unfold bytes_bits in *. cbn [flat_map].
  rewrite trl_pack_app by (rewrite trl_bits_le_len by lia; reflexivity).
  rewrite trl_pack_byte by rep_lia. rewrite IH by auto. reflexivity.
Qed.

Lemma trl_bval_range l : 0 <= bval l < 2 ^ Zlength l.
Proof.
  induction l as [|b r IH]; [simpl; lia | ].
  cbn [bval]. rewrite Zlength_cons, Z.pow_succ_r by apply Zlength_nonneg.
  destruct b; simpl Z.b2z; lia.
Qed.

Lemma trl_pack_ok bs : is_bytes (pack bs).
Proof.
  unfold is_bytes, pack. rewrite Forall_map. apply Forall_forall. intros k _. hnf.
  set (l := sublist _ _ bs). pose proof (trl_bval_range l).
  assert (Zlength l <= 8).
  { unfold l, sublist. rewrite Zlength_correct, length_skipn, length_firstn.
    pose proof (Nat.le_min_l (Z.to_nat (8 * Z.of_nat k + 8)) (length bs)). lia. }
  assert (2 ^ Zlength l <= 2 ^ 8) by (apply Z.pow_le_mono_r; [lia | auto]).
  change (2 ^ 8) with 256 in *. rep_lia.
Qed.

Lemma trl_pad8_mod p : 0 <= p -> (p + pad8 p) mod 8 = 0.
Proof.
  intros. unfold pad8. pose proof (Z.mod_pos_bound p 8 ltac:(lia)).
  rewrite Z.add_mod, Z.mod_mod by lia.
  destruct (zeq (p mod 8) 0) as [E | E].
  - rewrite E. reflexivity.
  - rewrite (Z.mod_small (8 - p mod 8)) by lia. replace (p mod 8 + (8 - p mod 8)) with 8 by lia. reflexivity.
Qed.

Lemma trl_pad8_shift h e : pad8 (8 * h + e) = pad8 e.
Proof. unfold pad8. f_equal. f_equal. rewrite Z.add_comm, Z.mul_comm, Z_mod_plus_full. reflexivity. Qed.

(* the final bits: header bytes, the blocks, the padding, the trailer bytes *)
Lemma trl_pack_final hdr E T : is_bytes hdr -> is_bytes T ->
  pack (((bytes_bits hdr ++ E) ++ zeros (pad8 (Zlength (bytes_bits hdr ++ E)))) ++ bytes_bits T) =
  hdr ++ pack (E ++ zeros (pad8 (Zlength E))) ++ T.
Proof.
  intros Hh HT.
  rewrite Zlength_app, trl_bytes_bits_len, trl_pad8_shift.
  rewrite <- !app_assoc. rewrite trl_pack_app by (rewrite trl_bytes_bits_len; rewrite Z.mul_comm, Z_mod_mult; reflexivity).
  rewrite trl_pack_bytes_bits by auto. f_equal.
  rewrite app_assoc, trl_pack_app.
  - rewrite trl_pack_bytes_bits by auto. reflexivity.
  - rewrite Zlength_app, trl_zeros_len by (unfold pad8; apply Z.mod_pos_bound; lia).
    apply trl_pad8_mod. apply Zlength_nonneg.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The stream                                                                                     *)

Definition trl_bytes (W: wrapper) (D: list Z) : list Z :=
  match W with
  | WRaw => []
  | WZlib _ _ _ => be_bytes (Zlib.proof.adler32.Model.ref_adler32 1 D) 4
  | WGzip _ => le_bytes (Zlib.proof.crc32.Model.ref_crc32 0 D) 4 ++ le_bytes (Zlength D mod 2 ^ 32) 4
  end.

Lemma trl_data_nil bs : data [] bs = expand [] bs.
Proof. unfold data. rewrite Zlength_nil. apply sublist_same; auto. Qed.

Lemma trl_stream_id wrap wb flevel al :
  stream_bytes (id_wrapper wrap wb flevel) [] al =
  hdr_bytes (id_wrapper wrap wb flevel) ++ deflate_bytes al ++ trl_bytes (id_wrapper wrap wb flevel) (expand [] al).
Proof.
  unfold stream_bytes, id_wrapper. rewrite trl_data_nil.
  destruct (wrap =? 1); [ | destruct (wrap =? 2)]; simpl; rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The bit writer at the law's compspecs (as IDMainBlk.v)                                         *)

Lemma trl_bw_struct_cs sh (v: val * (val * val)) q :
  @data_at Zlib.contracts.x_inflate_decode.Harness.CS sh t_bw v q = @data_at CS sh (Tstruct _bw noattr) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_harness); [apply JMeq_refl | reflexivity]. Qed.

Lemma trl_bytes_cs sh n (v: list val) q :
  @data_at Zlib.contracts.x_inflate_decode.Harness.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_harness); [apply JMeq_refl | reflexivity]. Qed.

Lemma trl_bw_at_law sh bsh B cap buf w :
  bw_at sh bsh B cap buf w =
  EX c: list val, !! bw_bytes_ok B cap c &&
    (@data_at CS sh (Tstruct _bw noattr)
       (buf, (Vint (Int.repr (Zlength B / 8)), Vint (Int.repr (Zlength B mod 8)))) w *
     @data_at CS bsh (tarray tuchar cap) c buf)%logic.
Proof. unfold bw_at, bw_rep. f_equal. extensionality c. rewrite trl_bw_struct_cs, trl_bytes_cs. reflexivity. Qed.

Lemma trl_bw_fold sh bsh B cap buf w c : bw_bytes_ok B cap c ->
  (@data_at CS sh (Tstruct _bw noattr)
     (buf, (Vint (Int.repr (Zlength B / 8)), Vint (Int.repr (Zlength B mod 8)))) w *
   @data_at CS bsh (tarray tuchar cap) c buf)%logic
  |-- bw_at sh bsh B cap buf w.
Proof. intros. rewrite trl_bw_at_law. Exists c. entailer!. Qed.

Lemma trl_room8 B cap k : 0 <= k <= 57 -> Zlength B / 8 + 8 <= cap -> cap <= Int.max_unsigned -> bw_room B cap k.
Proof.
  intros Hk Hr Hc. unfold bw_room. split; [lia | split; [ | lia]].
  pose proof (Zlength_nonneg B). pose proof (Z.div_mod (Zlength B) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (Zlength B) 8 ltac:(lia)).
  set (q := Zlength B / 8) in *. set (r := Zlength B mod 8) in *.
  assert ((Zlength B + k + 7) / 8 < q + 9); [ | lia].
  apply Z.div_lt_upper_bound; lia.
Qed.

Lemma trl_pack_len B : Zlength (pack B) = (Zlength B + 7) / 8.
Proof.
  unfold pack. rewrite Zlength_map, Zlength_correct, seq_length.
  apply Z2Nat.id. apply Z.div_pos; [pose proof (Zlength_nonneg B) | ]; lia.
Qed.

Lemma trl_bw_len_bound B cap c :
  bw_bytes_ok B cap c -> 0 <= Zlength B / 8 <= cap /\ (Zlength B + 7) / 8 <= cap.
Proof.
  intros (_ & H & _). rewrite trl_pack_len in H. pose proof (Zlength_nonneg B).
  assert (Zlength B / 8 <= (Zlength B + 7) / 8) by (apply Z.div_le_mono; lia).
  split; [split; [apply Z.div_pos | ] | ]; lia.
Qed.

Ltac trl_room_arg x k m :=
  try change (let (q, _) := Z.div_eucl (Zlength ?B) 8 in q) with (Zlength B / 8);
  try change (Int.shl (Int.repr 1) (Int.repr 19)) with (Int.repr 524288);
  unfold Int.ltu; rewrite ?Int.add_signed, ?Int.unsigned_repr by rep_lia;
  destruct (zlt m (x + k)); destruct (Z.leb_spec (x + k) m); try lia; reflexivity.

Lemma trl_bytes_adler_cs sh n (v: list val) q :
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.

Lemma trl_bytes_crc_cs sh n (v: list val) q :
  @data_at Zlib.units.Crc32.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_crc32); [apply JMeq_refl | reflexivity]. Qed.

(* after the trailer: the bits B *)
Definition trl_aft (gv: globals) (vw vll vlc vdc vs vosn: val) (wrap wb flevel isel: Z) (datap srcp isbp: val)
    (Fr: mpred) (al: list block) (ls: Z) (dcont: list val) (isbz: list Z) (llc lcc dcc: list val) (B: list bool)
    : environ -> mpred :=
  PROP ()
  LOCAL (temp _wrap (Vint (Int.repr wrap)); temp _wb (Vint (Int.repr wb)); temp _flevel (Vint (Int.repr flevel));
         temp _isel (Vint (Int.repr isel)); temp _data datap; temp _src srcp; temp _isb isbp;
         temp _maxd (Vint (Int.repr (2 ^ wb))); temp _n (Vint (Int.repr (Zlength (expand [] al))));
         temp _last_start (Vint (Int.repr ls));
         lvar _osnap (tptr tuchar) vosn; lvar _s (Tstruct _z_stream_s noattr) vs;
         lvar _dcodes (tarray tushort 30) vdc; lvar _lcodes (tarray tushort 286) vlc;
         lvar _ll (tarray tuchar 316) vll; lvar _w (Tstruct _bw noattr) vw; gvars gv)
  SEP (bw_at Tsh Ews B 524288 srcp vw;
       data_at Ews (tarray tuchar 262144) dcont datap;
       data_at Ews (tarray tuchar 262145) (bytes_rep isbz) isbp;
       malloc_token Ews (tarray tuchar 262144) datap; malloc_token Ews (tarray tuchar 524288) srcp;
       malloc_token Ews (tarray tuchar 262145) isbp;
       data_at Tsh (tarray tuchar 316) llc vll; data_at Tsh (tarray tushort 286) lcc vlc;
       data_at Tsh (tarray tushort 30) dcc vdc;
       dref_tabs gv Ers id_tabs; data_at Ers (tarray tuchar 19) (zvals clorder) (gv _cl_order);
       data_at_ Tsh (Tstruct _z_stream_s noattr) vs; data_at_ Tsh (tptr tuchar) vosn;
       mem_mgr gv; dres gv; Fr).

Lemma trl_cast_shr_l v s : 0 <= v < 2 ^ 32 -> 0 <= s < 32 ->
  eval_cast tuchar tuchar (eval_cast tulong tuchar (eval_binop Oshr tulong tint (Vlong (Int64.repr v)) (Vint (Int.repr s))))
  = Vint (Int.repr (Z.shiftr v s mod 256)).
Proof.
  intros Hv Hs.
  unfold eval_binop, force_val2, sem_binary_operation', sem_shr, sem_shift. simpl.
  rewrite Int.unsigned_repr by rep_lia.
  change Int64.modulus with (2 ^ 64) in *.
  rewrite !Int64.Z_mod_modulus_eq. change Int64.modulus with (2 ^ 64).
  rewrite (Z.mod_small s), (Z.mod_small v) by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  assert (Hy: 0 <= v / 2 ^ s <= v).
  { split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; [lia | ]].
    assert (0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia). nia. }
  rewrite (Z.mod_small (v / 2 ^ s)) by lia.
  f_equal. rewrite Int.zero_ext_idem by lia.
  rewrite <- (Int.repr_unsigned (Int.zero_ext 8 _)), Int.zero_ext_mod by (cbn; lia).
  rewrite Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma trl_cast_l v : 0 <= v < 2 ^ 32 ->
  eval_cast tuchar tuchar (eval_cast tulong tuchar (Vlong (Int64.repr v))) = Vint (Int.repr (v mod 256)).
Proof.
  intros Hv. simpl.
  rewrite Int64.Z_mod_modulus_eq. change Int64.modulus with (2 ^ 64). rewrite Z.mod_small by lia.
  f_equal. rewrite Int.zero_ext_idem by lia.
  rewrite <- (Int.repr_unsigned (Int.zero_ext 8 _)), Int.zero_ext_mod by (cbn; lia).
  rewrite Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma trl_cast_shr_i v s : 0 <= v <= Int.max_unsigned -> 0 <= s < 32 ->
  eval_cast tuchar tuchar (eval_cast tuint tuchar (eval_binop Oshr tuint tint (Vint (Int.repr v)) (Vint (Int.repr s))))
  = Vint (Int.repr (Z.shiftr v s mod 256)).
Proof.
  intros Hv Hs. simpl.
  f_equal. rewrite Int.zero_ext_idem by lia.
  unfold Int.shru. rewrite !Int.unsigned_repr by rep_lia.
  rewrite Z.shiftr_div_pow2 by lia.
  assert (Hy: 0 <= v / 2 ^ s <= v).
  { split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia] | apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia | ]].
    assert (0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia). nia. }
  rewrite <- (Int.repr_unsigned (Int.zero_ext 8 _)), Int.zero_ext_mod by (cbn; lia).
  rewrite Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma trl_cast_i v : 0 <= v <= Int.max_unsigned ->
  eval_cast tuchar tuchar (eval_cast tuint tuchar (Vint (Int.repr v))) = Vint (Int.repr (v mod 256)).
Proof.
  intros Hv. simpl.
  f_equal. rewrite Int.zero_ext_idem by lia.
  rewrite <- (Int.repr_unsigned (Int.zero_ext 8 _)), Int.zero_ext_mod by (cbn; lia).
  rewrite Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma trl_len_byte B b : Zlength (B ++ bits_le b 8) = Zlength B + 8.
Proof. rewrite Zlength_app, trl_bits_le_len by lia. reflexivity. Qed.

Lemma trl_be4 v : bytes_bits (be_bytes v 4) =
  bits_le (Z.shiftr v 24 mod 256) 8 ++ bits_le (Z.shiftr v 16 mod 256) 8 ++ bits_le (Z.shiftr v 8 mod 256) 8 ++
  bits_le (v mod 256) 8.
Proof. reflexivity. Qed.

Lemma trl_le4 v : bytes_bits (le_bytes v 4) =
  bits_le (v mod 256) 8 ++ bits_le (Z.shiftr v 8 mod 256) 8 ++ bits_le (Z.shiftr v 16 mod 256) 8 ++
  bits_le (Z.shiftr v 24 mod 256) 8.
Proof. reflexivity. Qed.

Lemma trl_bytes_bits_app l1 l2 : bytes_bits (l1 ++ l2) = bytes_bits l1 ++ bytes_bits l2.
Proof. unfold bytes_bits. symmetry. apply flat_map_app. Qed.

Lemma trl_le_bytes_ok v n : is_bytes (le_bytes v n).
Proof.
  unfold is_bytes, le_bytes. rewrite Forall_map. apply Forall_forall. intros i _.
  pose proof (Z.mod_pos_bound (Z.shiftr v (8 * Z.of_nat i)) 256 ltac:(lia)). hnf; rep_lia.
Qed.

Lemma trl_be_bytes_ok v n : is_bytes (be_bytes v n).
Proof. unfold be_bytes, is_bytes. apply Forall_rev. apply trl_le_bytes_ok. Qed.

Lemma trl_T_ok W D : is_bytes (trl_bytes W D) /\ Zlength (trl_bytes W D) <= 8.
Proof.
  destruct W; cbn [trl_bytes].
  - split; [constructor | rewrite Zlength_nil; lia].
  - split; [apply trl_be_bytes_ok | ]. unfold be_bytes. rewrite Zlength_rev.
    unfold le_bytes. rewrite Zlength_map, Zlength_correct, seq_length. simpl. lia.
  - split.
    + apply Forall_app. split; apply trl_le_bytes_ok.
    + rewrite Zlength_app. unfold le_bytes. rewrite !Zlength_map, !Zlength_correct, !seq_length. simpl. lia.
Qed.

Lemma trl_hdr_ok wrap wb flevel isel : par_ok wrap wb flevel isel -> is_bytes (hdr_bytes (id_wrapper wrap wb flevel)).
Proof.
  intros (Hw & Hb & Hf & _). unfold id_wrapper.
  destruct (wrap =? 1).
  - cbn [hdr_bytes]. rewrite app_nil_r. unfold zlib_hdr.
    assert (Ex: Z.land flevel 3 = flevel mod 4) by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; reflexivity).
    rewrite Ex. pose proof (Z.mod_pos_bound flevel 4 ltac:(lia)).
    set (x := flevel mod 4) in *.
    set (y := (31 - (((wb - 8) * 16 + 8) * 256 + (x * 64 + 0)) mod 31) mod 31).
    assert (0 <= y < 31) by (apply Z.mod_pos_bound; lia).
    repeat constructor; rep_lia.
  - destruct (wrap =? 2).
    + vm_compute. repeat constructor; discriminate.
    + constructor.
Qed.

Ltac trl_arg := cbn [firstn length typeof];
  first [rewrite trl_cast_shr_l by (rep_lia || lia) | rewrite trl_cast_l by (rep_lia || lia)
        | rewrite trl_cast_shr_i by (rep_lia || lia) | rewrite trl_cast_i by (rep_lia || lia)];
  entailer!.

Ltac trl_side :=
  rewrite ?trl_len_byte;
  repeat match goal with |- _ /\ _ => split end;
  try match goal with |- bw_room _ _ _ => apply trl_room8; [lia | rewrite ?trl_len_byte | rep_lia] end;
  try match goal with |- 0 <= ?x mod 256 => pose proof (Z.mod_pos_bound x 256 ltac:(lia)); lia end;
  try match goal with |- ?x mod 256 <= 255 => pose proof (Z.mod_pos_bound x 256 ltac:(lia)); lia end;
  try lia; try (Z.to_euclidean_division_equations; lia).

Lemma trl_join3 {cs: compspecs} sh n1 n2 (a b c: list val) p :
  field_compatible (tarray tuchar 524288) [] p -> 0 <= n1 -> 0 <= n2 -> n1 + n2 <= 524288 ->
  Zlength a = n1 -> Zlength b = n2 -> Zlength c = 524288 - (n1 + n2) ->
  (data_at sh (Tarray tuchar n1 noattr) a p * data_at sh (tarray tuchar n2) b (offset_val n1 p) *
   data_at sh (Tarray tuchar (524288 - (n1 + n2)) noattr) c (offset_val (n1 + n2) p))%logic
  |-- data_at sh (tarray tuchar 524288) (a ++ b ++ c) p.
Proof.
  intros FC H1 H2 H3 La Lb Lc.
  rewrite (split3_data_at_Tarray_tuchar sh 524288 n1 (n1 + n2) (a ++ b ++ c) p)
    by (rewrite ?Zlength_app; lia).
  change (Tarray tuchar 524288 noattr) with (tarray tuchar 524288).
  rewrite !arr_field_address0 by (auto; lia).
  change (sizeof tuchar) with 1. rewrite !Z.mul_1_l.
  replace (n1 + n2 - n1) with n2 by lia.
  rewrite sublist_app1 by (rewrite ?Zlength_app; lia). rewrite sublist_same by lia.
  rewrite sublist_app2 by lia. rewrite La, Z.sub_diag, Z.add_simpl_l.
  rewrite sublist_app1 by lia. rewrite sublist_same by lia.
  rewrite sublist_app2 by (rewrite ?Zlength_app; lia).
  rewrite sublist_app2 by (rewrite ?Zlength_app; lia).
  rewrite sublist_same by (rewrite ?Zlength_app; lia).
  cancel.
Qed.

Ltac trl_byte b :=
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?S))) _ _ =>
    match S with context [bw_at _ _ ?B _ ?buf ?w] =>
      with_strategy opaque [Int64.shru] forward_call (Tsh, Ews, B, 524288, buf, w, b); [trl_arg | trl_side | ]
    end
  end.


Lemma id_trl_ok {Espec: OracleKind} gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr
    (Post: ret_assert) :
  par_ok wrap wb flevel isel -> isptr datap -> isptr srcp -> isptr isbp ->
  (forall al ls dcont isbz srcl scont,
     trl_facts wrap wb flevel isel datap srcp isbp al ls dcont isbz srcl scont ->
     semax Delta_id (trl_mid gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr al ls dcont isbz
                       srcl scont) S_mid Post) ->
  semax Delta_id (enc_post gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr) S_trl Post.
Proof.
  intros Hpar Pd Ps Pi Hk. destruct Post as [Pn Pb Pc Pr].
  unfold enc_post. Intros al ls dcont isbz llc lcc dcc.
  unfold S_trl, Delta_id, Gmain_k. simplify_func_tycontext. abbreviate_semax.
  set (W := id_wrapper wrap wb flevel) in *.
  set (E := enc_blocks 0 al) in *.
  set (B := bytes_bits (hdr_bytes W) ++ E) in *.
  rewrite trl_bw_at_law. Intros c. rename H5 into Hbw.
  destruct (trl_bw_len_bound _ _ _ Hbw) as [HB0 HB1].
  sep_apply (trl_bw_fold Tsh Ews B 524288 srcp vw c Hbw).
  forward_call (Tsh, Ews, B, 524288, srcp, vw).
  { unfold bw_room. rewrite Z.add_0_r. split; [lia | split; [lia | rep_lia]]. }
  set (B1 := B ++ zeros (pad8 (Zlength B))) in *.
  rewrite trl_bw_at_law. Intros c1. rename H5 into Hbw1.
  destruct (trl_bw_len_bound _ _ _ Hbw1) as [HB2 HB3].
  forward.
  forward_call (Int.repr (if Zlength B1 / 8 + 24 <=? 524288 then 1 else 0)).
  { entailer!.
    change (let (q, _) := Z.div_eucl (Zlength B1) 8 in q) with (Zlength B1 / 8).
    replace (Zlength B1 / 8 + 8 + 16) with (Zlength B1 / 8 + 24) by lia.
    trl_room_arg (Zlength B1 / 8) 24 524288. }
  assumed. apply Z.leb_le in E0.
  sep_apply (trl_bw_fold Tsh Ews B1 524288 srcp vw c1 Hbw1).
  assert (HB1m: Zlength B1 mod 8 = 0).
  { subst B1. rewrite Zlength_app, trl_zeros_len by (unfold pad8; apply Z.mod_pos_bound; lia).
    apply trl_pad8_mod. apply Zlength_nonneg. }
  set (D := expand [] al) in *.
  pose proof H1 as (HDc & HDl & HDb & HDs).
  set (T := trl_bytes W D).
  forward_if (trl_aft gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr al ls dcont isbz llc lcc dcc
                (B1 ++ bytes_bits T)).
  { (* zlib *)
    rewrite <- trl_bytes_adler_cs.
    forward_call (1, datap, Ews, datap, 0, 262144, dcont, Zlength D, D).
    { unfold cbuf_ok. destruct datap; try contradiction. simpl. rewrite ptrofs_add_repr_0_r.
      repeat split; auto; try lia. }
    rewrite trl_bytes_adler_cs.
    assert (Hv1: Zlib.proof.adler32.Model.adler_valid 1) by (cbv; repeat split; congruence).
    pose proof (Zlib.proof.adler32.Model.ref_adler32_valid 1 D Hv1) as [Hra _].
    set (ra := Zlib.proof.adler32.Model.ref_adler32 1 D) in *.
    assert (Era: ra = Zlib.proof.adler32.Model.ref_adler32 1 D) by reflexivity.
    clearbody ra.
    with_strategy opaque [Int64.shru] forward_call (Tsh, Ews, B1, 524288, srcp, vw, Z.shiftr ra 24 mod 256).
    { trl_arg. }
    { trl_side. }
    with_strategy opaque [Int64.shru] forward_call
      (Tsh, Ews, B1 ++ bits_le (Z.shiftr ra 24 mod 256) 8, 524288, srcp, vw, Z.shiftr ra 16 mod 256).
    { trl_arg. }
    { trl_side. }
    with_strategy opaque [Int64.shru] forward_call
      (Tsh, Ews, (B1 ++ bits_le (Z.shiftr ra 24 mod 256) 8) ++ bits_le (Z.shiftr ra 16 mod 256) 8, 524288, srcp, vw,
       Z.shiftr ra 8 mod 256).
    { trl_arg. }
    { trl_side. }
    with_strategy opaque [Int64.shru] forward_call
      (Tsh, Ews, ((B1 ++ bits_le (Z.shiftr ra 24 mod 256) 8) ++ bits_le (Z.shiftr ra 16 mod 256) 8) ++
                 bits_le (Z.shiftr ra 8 mod 256) 8, 524288, srcp, vw, ra mod 256).
    { trl_arg. }
    { trl_side. }
    assert (Ew: wrap = 1).
    { destruct Hpar as (Hw & _). apply repr_inj_unsigned in H5; rep_lia. }
    assert (ET: T = be_bytes ra 4).
    { unfold T, trl_bytes, W, id_wrapper. rewrite Ew, Era. reflexivity. }
    unfold trl_aft. rewrite ET, trl_be4, !app_assoc.
    cbn [RA_normal]. entailer!. }
  forward_if (trl_aft gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr al ls dcont isbz llc lcc dcc
                (B1 ++ bytes_bits T)).
  { (* gzip *)
    rewrite <- trl_bytes_crc_cs.
    forward_call (0, datap, Ews, datap, 0, 262144, dcont, Zlength D, D).
    { unfold cbuf_ok. destruct datap; try contradiction. simpl. rewrite ptrofs_add_repr_0_r.
      repeat split; auto; try lia. }
    rewrite trl_bytes_crc_cs.
    pose proof (Zlib.proof.crc32.Combine.ref_crc32_range 0 D HDb) as Hrc. unfold Zlib.proof.crc32.GF2.is32 in Hrc.
    set (rc := Zlib.proof.crc32.Model.ref_crc32 0 D) in *.
    assert (Erc: rc = Zlib.proof.crc32.Model.ref_crc32 0 D) by reflexivity.
    clearbody rc.
    trl_byte (rc mod 256).
    trl_byte (Z.shiftr rc 8 mod 256).
    trl_byte (Z.shiftr rc 16 mod 256).
    trl_byte (Z.shiftr rc 24 mod 256).
    trl_byte (Zlength D mod 256).
    trl_byte (Z.shiftr (Zlength D) 8 mod 256).
    trl_byte (Z.shiftr (Zlength D) 16 mod 256).
    trl_byte (Z.shiftr (Zlength D) 24 mod 256).
    assert (Ew: wrap = 2).
    { destruct Hpar as (Hw & _). apply repr_inj_unsigned in H6; rep_lia. }
    assert (ET: T = le_bytes rc 4 ++ le_bytes (Zlength D) 4).
    { unfold T, trl_bytes, W, id_wrapper. rewrite Ew, Erc, (Z.mod_small (Zlength D)) by rep_lia. reflexivity. }
    unfold trl_aft. rewrite ET, trl_bytes_bits_app, !trl_le4, !app_assoc.
    cbn [RA_normal]. entailer!. }
  { forward.
    assert (ET: T = []).
    { unfold T, trl_bytes, W, id_wrapper.
      destruct (Z.eqb_spec wrap 1); [subst; contradiction | ].
      destruct (Z.eqb_spec wrap 2); [subst; contradiction | ]. reflexivity. }
    unfold trl_aft. rewrite ET. cbn [bytes_bits flat_map]. rewrite app_nil_r. entailer!. }
  (* slen = w.len *)
  destruct (trl_T_ok W D) as [HTb HTl]. change (trl_bytes W D) with T in HTb, HTl.
  pose proof (Zlength_nonneg T).
  set (B2 := B1 ++ bytes_bits T).
  assert (HB2m: Zlength B2 mod 8 = 0).
  { unfold B2. rewrite Zlength_app, trl_bytes_bits_len. Z.to_euclidean_division_equations; lia. }
  set (S := stream_bytes W [] al).
  assert (ES: pack B2 = S).
  { unfold B2, B1, B, S. rewrite trl_pack_final by (auto; apply (trl_hdr_ok wrap wb flevel isel Hpar)).
    unfold W. rewrite trl_stream_id. reflexivity. }
  assert (ESl: Zlength B2 / 8 = Zlength S).
  { rewrite <- ES, trl_pack_len. Z.to_euclidean_division_equations; lia. }
  assert (HSl: Zlength S <= Zlength B1 / 8 + 8).
  { rewrite <- ESl. unfold B2. rewrite Zlength_app, trl_bytes_bits_len. Z.to_euclidean_division_equations; lia. }
  unfold trl_aft. rewrite trl_bw_at_law. Intros c2. fold B2.
  match goal with Hx: bw_bytes_ok B2 _ _ |- _ => rename Hx into Hbw2 end.
  rewrite ESl.
  forward.
  forward_call tt. Intros glen.
  forward_call (Int.repr (if glen <=? 16 then 1 else 0)).
  { entailer!. unfold Int.ltu. rewrite !Int.unsigned_repr by rep_lia.
    destruct (zlt 16 glen); destruct (Z.leb_spec glen 16); try lia; reflexivity. }
  assumed. match goal with Ex: (glen <=? 16) = true |- _ => apply Z.leb_le in Ex; rename Ex into Hglen end.
  destruct Hbw2 as (Hc2l & Hc2p & Hc2s). rewrite ES in Hc2p, Hc2s.
  pose proof (Zlength_nonneg S).
  assert (Hroom: Zlength S + glen <= 524288) by lia.
  assert_PROP (field_compatible (tarray tuchar 524288) [] srcp) as FCs by entailer!.
  rewrite (split3_data_at_Tarray_tuchar Ews 524288 (Zlength S) (Zlength S + glen) c2 srcp) by lia.
  change (Tarray tuchar 524288 noattr) with (tarray tuchar 524288).
  rewrite !arr_field_address0 by (auto; lia).
  change (sizeof tuchar) with 1. rewrite !Z.mul_1_l.
  replace (Zlength S + glen - Zlength S) with glen by lia.
  flatten_sepcon_in_SEP.
  sep_apply (data_at_data_at_ Ews (Tarray tuchar glen noattr) (sublist (Zlength S) (Zlength S + glen) c2)
               (offset_val (Zlength S) srcp)).
  assert (Pnn: offset_val (Zlength S) srcp <> nullval) by (destruct srcp; try contradiction; discriminate).
  forward_call (offset_val (Zlength S) srcp, glen, Ews).
  { rewrite if_false by auto. cancel. }
  Intros gb. rewrite if_false by auto. fold (bytes_rep gb).
  match goal with Hx: Zlength gb = glen |- _ => rename Hx into Hgbl end.
  match goal with Hx: Forall _ gb |- _ => rename Hx into Hgbb end.
  forward.
  set (srcl := S ++ gb).
  set (scont := bytes_rep S ++ bytes_rep gb ++ sublist (Zlength S + glen) 524288 c2).
  assert (HF: trl_facts wrap wb flevel isel datap srcp isbp al ls dcont isbz srcl scont).
  { assert (HSb: is_bytes S) by (rewrite <- ES; apply trl_pack_ok).
    assert (Hgbb': is_bytes gb) by exact Hgbb.
    unfold trl_facts. change (stream_bytes (id_wrapper wrap wb flevel) [] al) with S.
    change (expand [] al) with D.
    assert (Hsl: Zlength srcl = Zlength S + glen) by (unfold srcl; rewrite Zlength_app; lia).
    split; [exact Hpar | ]. split; [exact Pd | ]. split; [exact Ps | ]. split; [exact Pi | ].
    split; [exact H | ]. split; [exact H0 | ]. split; [exact H1 | ]. split; [exact H2 | ].
    split; [exact H4 | ]. split; [lia | ]. split; [lia | ].
    split; [unfold srcl, is_bytes; apply Forall_app; split; auto | ].
    split; [unfold srcl; rewrite sublist_app1 by lia; apply sublist_same; lia | ].
    split; [unfold scont; rewrite !Zlength_app, !Zlength_bytes_rep, Zlength_sublist by lia; lia | ].
    split; [lia | ].
    unfold scont, srcl. rewrite app_assoc. unfold bytes_rep at 1 2. rewrite <- map_app. fold (bytes_rep (S ++ gb)).
    rewrite sublist_app1 by (rewrite ?Zlength_bytes_rep, ?Zlength_app; lia).
    apply sublist_same; [lia | rewrite Zlength_bytes_rep; reflexivity]. }
  unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
  eapply semax_pre; [ | apply (Hk al ls dcont isbz srcl scont HF) ].
  unfold trl_mid. rewrite Hc2s.
  assert (L1: Zlength (bytes_rep S) = Zlength S) by apply Zlength_bytes_rep.
  assert (L2: Zlength (bytes_rep gb) = glen) by (rewrite Zlength_bytes_rep; auto).
  assert (L3: Zlength (sublist (Zlength S + glen) 524288 c2) = 524288 - (Zlength S + glen))
    by (rewrite Zlength_sublist by lia; lia).
  sep_apply (trl_join3 Ews (Zlength S) glen (bytes_rep S) (bytes_rep gb) (sublist (Zlength S + glen) 524288 c2) srcp
               FCs ltac:(lia) ltac:(lia) ltac:(lia) L1 L2 L3).
  change (stream_bytes (id_wrapper wrap wb flevel) [] al) with S.
  assert (Hsl: Zlength srcl = Zlength S + glen) by (unfold srcl; rewrite Zlength_app; lia).
  rewrite Hsl.
  change (bytes_rep S ++ bytes_rep gb ++ sublist (Zlength S + glen) 524288 c2) with scont. clearbody scont.
  sep_apply (data_at_data_at_ Tsh (Tstruct _bw noattr)).
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 316)).
  sep_apply (data_at_data_at_ Tsh (tarray tushort 286)).
  sep_apply (data_at_data_at_ Tsh (tarray tushort 30)).
  (* the big objects' sizes: abstract them (entailer! overflows the stack on the literals) *)
  set (N0 := 262144) in *. set (N1 := 262145) in *. set (N2 := 524288) in *. clearbody N0 N1 N2.
  entailer!.
Qed.
