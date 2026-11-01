(* The main of harness/ck_adler32.c, proved against main_core_spec (memory manager only: adler32.c has
   no globals).  The harness's own loop computes the RFC 1950 sums from the start value s2 << 16 | s1;
   its invariant is that (s1, s2) are the two halves of ref_adler32 over the bytes read so far, so the
   final check is adler32_z_val = ref_adler32 for a valid start value (Model.adler32_z_val_ref). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Zlib.contracts.ck_adler32.
Require Import Zlib.harness.ck_adler32.code.
Require Import Zlib.proof.adler32.Spec Zlib.proof.adler32.Facts2 Zlib.proof.adler32.HarnessRef.
Require Import Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.Facts Zlib.proof.adler32.Ptr.
Require Import Zlib.proof.harness.laws_common.Spec.

Definition p := Zlib.contracts.ck_adler32.whole_prog.
Definition comps := ltac:(let x := eval vm_compute in (prog_composites p) in exact x).
Definition cprog : Clight.program := Clightdefs.mkprogram comps nil nil 1%positive Logic.I.
#[export] Instance CS : compspecs. make_compspecs cprog. Defined.
#[export] Instance CC2 : change_composite_env Zlib.units.Adler32.CS CS. make_cs_preserve Zlib.units.Adler32.CS CS. Defined.

Ltac tok_cs :=
  match goal with |- context [@malloc_token Zlib.units.Adler32.CS ?sh ?t] =>
    rewrite (@malloc_token_change_composite Zlib.units.Adler32.CS CS CC2 sh t) by reflexivity end;
  cancel.

Ltac tok_norm :=
  repeat match goal with |- context [@malloc_token Zlib.units.Adler32.CS ?sh ?t] =>
    rewrite (@malloc_token_change_composite Zlib.units.Adler32.CS CS CC2 sh t) by reflexivity end.

Ltac side := try (solve [cancel | tok_cs | entailer!; arg_cmp]).

Definition R (gv: globals) : mpred := emp.

Definition Gmain : funspecs := [upto_spec; any_bytes_spec; adler32_z_spec; gp_assert_spec].

(* The reference state after the bytes l, from the halves (s1, s2) of the start value. *)
Definition ref_state (s1 s2: Z) (l: list Z) : Z * Z := fold_left adler_ref_step l (s1, s2).

Lemma ref_state_succ s1 s2 data i: 0 <= i < Zlength data ->
  ref_state s1 s2 (sublist 0 (i + 1) data) = adler_ref_step (ref_state s1 s2 (sublist 0 i data)) (Znth i data).
Proof.
  intros. unfold ref_state. rewrite (sublist_split 0 i (i + 1)) by lia.
  rewrite fold_left_app, sublist_len_1 by lia. reflexivity.
Qed.

Lemma ref_state_range s1 s2 l: 0 <= s1 < ADLER_BASE -> 0 <= s2 < ADLER_BASE ->
  0 <= fst (ref_state s1 s2 l) < ADLER_BASE /\ 0 <= snd (ref_state s1 s2 l) < ADLER_BASE.
Proof. intros. apply adler_ref_fold_range; auto. Qed.

(* The packed start value has the halves s1 and s2, and the checksum is the packed final state. *)
Lemma ref_state_adler s1 s2 data: 0 <= s1 < ADLER_BASE -> 0 <= s2 < ADLER_BASE ->
  ref_adler32 (s2 * 65536 + s1) data =
  snd (ref_state s1 s2 data) * 65536 + fst (ref_state s1 s2 data).
Proof.
  intros. unfold ref_adler32, adler_pack, ref_state, ADLER_BASE in *.
  rewrite adler_lo_pack, adler_hi_pack by lia. reflexivity.
Qed.

Lemma body_main: semax_body (QPvarspecs p) Gmain f_main (_main, main_core_spec R).
Proof.
  start_function.
  unfold R. Intros.
  forward_call (Int64.max_signed).
  Intros len.
  forward_call (len, gv).
  Intros vret. destruct vret as [buf data]. simpl fst in *; simpl snd in *.
  match goal with H: Zlength data = len |- _ => rename H into Hdn end.
  match goal with H: is_bytes data |- _ => rename H into Hby end.
  destruct (eq_dec buf nullval) as [PB|PB].
  { subst buf. forward_if False. { ret0. } { first [contradiction | discriminate]. } }
  Intros.
  forward_if True.
  { contradiction. }
  { forward. entailer!. }
  Intros.
  forward_call 65520. Intros s1.
  forward_call 65520. Intros s2.
  forward.
  forward_for_simple_bound len
    (EX i: Z,
     PROP ()
     LOCAL (temp _s1 (Vlong (Int64.repr (fst (ref_state s1 s2 (sublist 0 i data)))));
            temp _s2 (Vlong (Int64.repr (snd (ref_state s1 s2 (sublist 0 i data)))));
            temp _start (Vlong (Int64.repr (s2 * 65536 + s1)));
            temp _buf buf; temp _len (Vlong (Int64.repr len)); gvars gv)
     SEP (mem_mgr gv; malloc_token Ews (tarray tuchar len) buf;
          data_at Ews (tarray tuchar len) (bytes_rep data) buf)).
  { entailer!. rewrite or_pack_int by lia. reflexivity. }
  { pose proof (ref_state_range s1 s2 (sublist 0 i data)) as [Ra Rb]; try (unfold ADLER_BASE; lia).
    sep_apply (@change_compspecs_data_at_cancel Zlib.units.Adler32.CS CS CC2 Ews (tarray tuchar len)
                 (tarray tuchar len) (bytes_rep data) (bytes_rep data) buf eq_refl eq_refl (JMeq_refl _)).
    assert_PROP (field_compatible (tarray tuchar len) [] buf) as FC by entailer!.
    pose proof (add_ptr_long buf len 0 i FC ltac:(lia) ltac:(rep_lia)) as E.
    rewrite isptr_offset_val_zero in E by auto. rewrite Z.add_0_l in E.
    assert (Hb2: 0 <= Znth i data <= Byte.max_unsigned) by (apply is_bytes_Znth; auto; lia).
    forward.
    { entailer!. rewrite Znth_bytes_rep by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite Znth_bytes_rep by lia.
    forward. forward.
    entailer!.
    rewrite ref_state_succ by lia. unfold adler_ref_step. simpl fst; simpl snd.
    rewrite (modu65521 (fst (ref_state s1 s2 (sublist 0 i data)) + Znth i data)) by (unfold ADLER_BASE in *; rep_lia).
    assert (0 <= (fst (ref_state s1 s2 (sublist 0 i data)) + Znth i data) mod ADLER_BASE < ADLER_BASE)
      by (apply Z.mod_pos_bound; unfold ADLER_BASE; lia).
    rewrite add64_repr. rewrite modu65521 by (unfold ADLER_BASE in *; rep_lia).
    split; auto. }
  (* adler32_z(start, buf, len) == s2 * 65536 + s1 *)
  rewrite sublist_same by lia.
  assert (Hv: adler_valid (s2 * 65536 + s1)) by (apply adler_valid_pack; unfold ADLER_BASE; lia).
  pose proof (ref_state_range s1 s2 data) as [Ra Rb]; try (unfold ADLER_BASE; lia).
  assert_PROP (isptr buf) as Pbuf by entailer!.
  assert (CB: cbuf_ok false buf Ews buf 0 len len (bytes_rep data) data) by (subst len; apply cbuf_ok_whole; auto).
  forward_call (s2 * 65536 + s1, buf, len, false, Ews, buf, 0, len, bytes_rep data, data, true, Ews).
  all: side.
  tok_norm. rewrite adler32_z_val_ref by auto. rewrite ref_state_adler by (unfold ADLER_BASE in *; lia).
  forward_call (Int.repr 1).
  { entailer!. rewrite Int64.eq_true. reflexivity. }
  ret0.
Qed.
