(* Law rfc_level0_blocks, main: statements 1-17 (l0_A0 -> l0_A18): data_len = upto(PTRDIFF_MAX), window_bits,
   mem_level and strategy from nondet_u32, blocks / head_len / trailer_len / size (Level0Defs' l0_blocks,
   l0_hlen, l0_tlen, l0_size: L0Kit2's l0_blocks_eq, l0_hlen_*; no wrap for data_len <= PTRDIFF_MAX,
   L0Kit2.l0_size_range), room = size + upto(SIZE_MAX - size), data = alloc_any_bytes(data_len), `return 0` if
   it is NULL, expected = copy_of(data, data_len), compressed = malloc(room), `return 0` if either is NULL. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.deflate.Level0Calls.
Require Import Zlib.proof.harness.rfc_level0_blocks.L0B2MainStmt.
Require Import Zlib.proof.harness.rfc_level0_size.L0Kit2.
Require Import Zlib.proof.harness.rfc_level0_blocks.L0B2Kit.
Require Import Zlib.harness.rfc_level0_blocks.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

Ltac simplify_remove_localdef_temp ::= l0_rlt.

(* [Q] without the binding of the temporary [t] *)
Ltac rm_temp t Q :=
  lazymatch Q with
  | temp t _ :: ?Q' => Q'
  | ?a :: ?Q' => let r := rm_temp t Q' in constr:(a :: r)
  | nil => constr:(@nil localdef)
  end.

(* forward over an [if] after which the temporary [t] is [v] (one or two temporaries) *)
Ltac fif1 t v :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    let Q' := rm_temp t Q in forward_if (PROPx P (LOCALx (temp t v :: Q') (SEPx R))) end.
Ltac fif2 t v t' v' :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    let Q1 := rm_temp t Q in let Q' := rm_temp t' Q1 in
    forward_if (PROPx P (LOCALx (temp t v :: temp t' v' :: Q') (SEPx R))) end.

(* a goal on comparisons of Z values, by cases on them *)
Ltac zcase :=
  unfold Int.lt, l0_hlen, l0_tlen in *; rewrite ?Int.signed_repr in * by rep_lia;
  repeat match goal with
  | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b)
  | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b)
  | |- context [Z.gtb ?a ?b] => destruct (Z.gtb_spec a b)
  | |- context [zlt ?a ?b] => destruct (zlt a b)
  | H : context [zlt ?a ?b] |- _ => destruct (zlt a b)
  end; cbn [andb orb negb] in *; try lia;
  try match goal with H : typed_true _ _ |- _ => inversion H; fail end;
  try match goal with H : typed_false _ _ |- _ => inversion H; fail end;
  try (repeat split; reflexivity).

(* `return 0` *)
Ltac ret0 := forward; Exists (Int.repr 0); entailer!.

(* SIZE_MAX - size as main computes it, (unsigned long) -1 - size *)
Lemma l0_room_arg (size : Z) : Int64.repr (-1 - size) = Int64.repr (Int64.max_unsigned - size).
Proof.
  apply Int64.eqm_samerepr. exists (-1). unfold Int64.max_unsigned. rewrite Int64.modulus_power. simpl. lia.
Qed.

Lemma seg_inputs_ok : seg_inputs_stmt.
Proof.
  intros Espec gv vs K.
  unfold l0_seg1, l0_A0, POST_B, POST_l0. abbreviate_semax.
  forward_call 9223372036854775807.
  Intros n.
  forward_call tt. Intros u1. forward_call tt. Intros u2. forward_call tt. Intros u3. forward.
  rewrite <- (Int.repr_signed (Int.repr u1)), <- (Int.repr_signed (Int.repr u2)),
    <- (Int.repr_signed (Int.repr u3)).
  pose proof (Int.signed_range (Int.repr u1)). pose proof (Int.signed_range (Int.repr u2)).
  pose proof (Int.signed_range (Int.repr u3)).
  forget (Int.signed (Int.repr u1)) as wbits. forget (Int.signed (Int.repr u2)) as mem.
  forget (Int.signed (Int.repr u3)) as strategy. clear dependent u1. clear dependent u2. clear dependent u3.
  fif1 _blocks (Vlong (Int64.repr (l0_blocks n))).
  { forward. entailer!. rewrite !Int64.unsigned_repr in * by rep_lia.
    rewrite l0_blocks_eq by lia. destruct (Z.ltb_spec 0 n); [reflexivity | lia]. }
  { forward. entailer!. rewrite !Int64.unsigned_repr in * by rep_lia.
    rewrite l0_blocks_eq by lia. destruct (Z.ltb_spec 0 n); [lia | reflexivity]. }
  forward. forward.
  fif1 _t'5 (Val.of_bool ((0 <=? wbits) && (wbits <=? 15))%bool).
  { forward. entailer!. zcase. }
  { forward. entailer!. zcase. }
  fif2 _head_len (Vlong (Int64.repr (if ((0 <=? wbits) && (wbits <=? 15))%bool then 2 else 0)))
       _trailer_len (Vlong (Int64.repr (if ((0 <=? wbits) && (wbits <=? 15))%bool then 4 else 0))).
  { forward. forward. entailer!. zcase. }
  { forward. entailer!. zcase. }
  fif2 _head_len (Vlong (Int64.repr (l0_hlen wbits))) _trailer_len (Vlong (Int64.repr (l0_tlen wbits))).
  { forward. forward. entailer!. zcase. }
  { forward. entailer!. zcase. }
  forward.
  assert (Hn : 0 <= n <= 9223372036854775807) by lia.
  pose proof (l0_blocks_range n Hn) as HB. pose proof (l0_size_range wbits n Hn) as HS.
  rewrite Int.signed_repr by rep_lia. rewrite mul64_repr, !add64_repr.
  change (l0_hlen wbits + 5 * l0_blocks n + n + l0_tlen wbits) with (l0_size wbits n).
  (* room = size + upto(SIZE_MAX - size) *)
  forward_call (Int64.max_unsigned - l0_size wbits n).
  { entailer!. simpl. rewrite l0_room_arg. reflexivity. }
  Intros x. forward. rewrite add64_repr.
  set (room := l0_size wbits n + x).
  assert (HR : l0_size wbits n <= room <= Int64.max_unsigned) by (subst room; lia).
  clearbody room.
  (* data = alloc_any_bytes(data_len); if (data == NULL) return 0; *)
  forward_call (n, gv).
  Intros vret. destruct vret as [datap bs].
  cbn [fst snd] in *. rewrite l0_token_cs, l0_bytes_cs.
  destruct (eq_dec datap nullval) as [Pd | Pd].
  { subst datap. forward_if.
    { ret0. }
    { contradiction. } }
  destruct (eq_dec datap nullval); [contradiction|]. Intros.
  forward_if.
  { contradiction. }
  assert_PROP (isptr datap) as Pdp by entailer!.
  (* expected = copy_of(data, data_len), the copy of the data the blocks are compared with *)
  rewrite <- l0_bytes_cs.
  forward_call (datap, Ews, datap, 0, n, bytes_rep bs, n, bs, gv).
  { unfold cbuf_ok. rewrite isptr_offset_val_zero by auto.
    repeat split; auto; try lia. rewrite sublist_same by (unfold bytes_rep; rewrite ?Zlength_map; lia).
    reflexivity. }
  Intros ep.
  rewrite l0_bytes_cs.
  (* compressed = malloc(room) *)
  forward_call (tarray tuchar room, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros compp.
  (* if (expected == NULL || compressed == NULL) return 0; *)
  destruct (eq_dec ep nullval) as [Pe | Pe].
  { subst ep. fif1 _t'10 (vi 1).
    { forward. entailer!. }
    { contradiction. }
    forward_if.
    { ret0. }
    { discriminate. } }
  rewrite l0_token_cs, l0_bytes_cs.
  Intros.
  destruct (eq_dec compp nullval) as [Pc | Pc].
  { subst compp. fif1 _t'10 (vi 1).
    { contradiction. }
    { forward. entailer!. }
    forward_if.
    { ret0. }
    { discriminate. } }
  destruct (eq_dec compp nullval); [contradiction|]. Intros.
  fif1 _t'10 (vi 0).
  { contradiction. }
  { forward. entailer!. destruct compp; try contradiction; reflexivity. }
  forward_if.
  { l0_bad. }
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  assert_PROP (isptr ep /\ isptr compp) as Pp by entailer!.
  destruct Pp as [Pep Pcp].
  assert (Hcf : l0_cf n bs datap compp wbits mem strategy room).
  { unfold l0_cf, l0_max_size, l0_max_u64, s32_ok.
    repeat split; try rep_lia; auto; try (apply l0_is_bytes; auto). }
  eapply semax_pre; [ | apply (K n bs datap ep compp wbits mem strategy room)].
  unfold l0_A18, l0_data. rewrite !l0_bytes_rep. entailer!.
Qed.
