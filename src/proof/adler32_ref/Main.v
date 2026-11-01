(* The main of harness/adler32_ref.c, proved against main_core_spec (memory manager only: adler32.c has
   no globals). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Zlib.contracts.x_adler32_ref.
Require Import Zlib.harness.x_adler32_ref.code.
Require Import Zlib.proof.adler32.Spec Zlib.proof.adler32.Facts2 Zlib.proof.adler32.HarnessRef.
Require Import Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib Zlib.proof.adler32.Ptr.

Definition p := Zlib.contracts.x_adler32_ref.whole_prog.
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

Lemma land_lo a: 0 <= a -> Z.land a 65535 = adler_lo a.
Proof. intros. unfold adler_lo. change 65535 with (Z.ones 16). apply Z.land_ones. lia. Qed.

Lemma land_hi a: 0 <= a -> Z.land (Z.shiftr a 16) 65535 = adler_hi a.
Proof.
  intros. unfold adler_hi. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(* The second assert of adler32_z(any, ..): the high halves agree mod 65521. *)
Lemma hi_check r rf: 0 <= r <= Int64.max_unsigned -> 0 <= rf <= Int64.max_unsigned ->
  adler_hi r mod ADLER_BASE = adler_hi rf ->
  Int64.eq (Int64.modu (Int64.and (Int64.shru (Int64.repr r) (Int64.repr 16)) (Int64.repr 65535)) (Int64.repr 65521))
    (Int64.and (Int64.shru (Int64.repr rf) (Int64.repr 16)) (Int64.repr 65535)) = true.
Proof.
  intros. rewrite !adler_hi_int2 by auto.
  rewrite modu65521 by (pose proof (adler_hi_range r); rep_lia).
  rewrite H1. apply Int64.eq_true.
Qed.

(* Comparisons of the halves of a 64-bit value. *)
Ltac adl_cmp a :=
  pose proof (adler_lo_range a); pose proof (adler_hi_range a);
  rewrite ?adler_lo_int2, ?adler_hi_int2 in * by auto;
  rewrite ?land_hi, ?land_lo in * by lia;
  simpl; unfold Int64.cmpu, Int64.ltu in *;
  rewrite ?Int64.unsigned_repr in * by rep_lia;
  try change (Int.unsigned (Int.repr (-1))) with 4294967295 in *;
  rewrite ?Int64.unsigned_repr in * by rep_lia;
  repeat match goal with |- context [zlt ?a ?b] => destruct (zlt a b) end;
  repeat match goal with H: context [zlt ?a ?b] |- _ => destruct (zlt a b) end;
  repeat match goal with |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b) end;
  repeat match goal with |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b) end;
  repeat match goal with H: context [Z.ltb ?a ?b] |- _ => destruct (Z.ltb_spec a b) end;
  repeat match goal with H: context [Z.leb ?a ?b] |- _ => destruct (Z.leb_spec a b) end;
  simpl in *;
  try (match goal with H: ?x <> ?y |- _ => assert (x = y) by reflexivity; contradiction end);
  try lia; try reflexivity; try discriminate.

Definition Gmain : funspecs := [adler32_z_spec; adler32_spec; ref_adler32_spec;
  bytes_copy_spec; bytes_same_spec; (_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
  nondet_u32_spec; nondet_bytes_spec; gp_assert_spec; gp_assume_spec].

(* pick(x) of an unsigned long local variable. *)
Ltac pick_ulong v :=
  let FC := fresh "FC" in let P := fresh "P" in let N := fresh "N" in
  assert_PROP (field_compatible tulong [] v) as FC by entailer!;
  sep_apply (data_at_ulong_bytes Tsh v);
  assert_PROP (isptr v) as P by entailer!;
  assert (N: v <> nullval) by (destruct v; try contradiction; discriminate);
  forward_call (v, 8, Tsh);
  [ rewrite if_false by auto; cancel | ];
  let bs := fresh "bs" in
  Intros bs; rewrite if_false by auto;
  match goal with H1: Zlength bs = 8, H2: Forall _ bs |- _ => sep_apply (pick_tulong Tsh bs v H1 H2 FC) end.

Lemma body_main: semax_body (QPvarspecs p) Gmain f_main (_main, main_core_spec R).
Proof.
  start_function.
  unfold R. Intros.
  pick_ulong v_adler. Intros vadler.
  pick_ulong v_any. Intros vany.
  assert (E1: Vlong vadler = Vlong (Int64.repr (Int64.unsigned vadler))) by (rewrite Int64.repr_unsigned; auto).
  assert (E2: Vlong vany = Vlong (Int64.repr (Int64.unsigned vany))) by (rewrite Int64.repr_unsigned; auto).
  rewrite E1, E2. clear E1 E2.
  assert (Ha: 0 <= Int64.unsigned vadler <= Int64.max_unsigned) by rep_lia.
  assert (Hy: 0 <= Int64.unsigned vany <= Int64.max_unsigned) by rep_lia.
  remember (Int64.unsigned vadler) as adler eqn:Ea. clear Ea.
  remember (Int64.unsigned vany) as any eqn:Eb. clear Eb.
  forward_call tt. Intros n.
  forward_call tt. Intros k.
  forward_call tt. Intros len.
  (* gp_assume(valid adler) *)
  forward.
  ifpost _t'4 (Int.repr (if andb (adler_lo adler <? 65521) (adler_hi adler <? 65521) then 1 else 0)).
  { forward. forward. entailer!. adl_cmp adler. }
  { forward. entailer!. adl_cmp adler. }
  ifpost _t'5 (Int.repr (if andb (andb (adler_lo adler <? 65521) (adler_hi adler <? 65521)) (adler <=? 4294967295) then 1 else 0)).
  { forward. forward. entailer!. adl_cmp adler. }
  { forward. entailer!. adl_cmp adler. }
  forward_call (Int.repr (if andb (andb (adler_lo adler <? 65521) (adler_hi adler <? 65521)) (adler <=? 4294967295) then 1 else 0)).
  assumed.
  apply andb_prop in E. destruct E as [E E3]. apply andb_prop in E. destruct E as [E1 E2].
  apply Z.ltb_lt in E1. apply Z.ltb_lt in E2. apply Z.leb_le in E3.
  assert (Hval: adler_valid adler) by (split; [lia | split; auto]).
  forward_call (Int.repr (if n <=? 2 ^ 20 then 1 else 0)).
  all: side.
  assumed. apply Z.leb_le in E.
  forward_call (Int.repr (if k <=? n then 1 else 0)).
  all: side.
  assumed. apply Z.leb_le in E0.
  forward_call (tarray tuchar n, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros buf.
  forward_call (tarray tuchar n, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros snap.
  destruct (eq_dec buf nullval) as [PB|PB].
  { subst buf.
    ifpost _t'8 Int.one.
    { forward. entailer!. }
    { contradiction. }
    forward_if False. { ret0. } { first [contradiction | discriminate]. } }
  Intros.
  destruct (eq_dec snap nullval) as [PS|PS].
  { subst snap.
    ifpost _t'8 Int.one.
    { contradiction. }
    { forward. entailer!. }
    forward_if False. { ret0. } { first [contradiction | discriminate]. } }
  Intros.
  ifpost _t'8 Int.zero.
  { contradiction. }
  { forward. entailer!. destruct snap; try contradiction; reflexivity. }
  ifsame. { first [contradiction | discriminate]. } { forward. entailer!. }
  (* the buffer: n arbitrary bytes, and its snapshot *)
  forward_call (buf, n, Ews).
  { rewrite if_false by auto. cancel. }
  Intros data. rewrite if_false by auto.
  match goal with H: Zlength data = n |- _ => rename H into Hdn end.
  match goal with H: Forall _ data |- _ => rename H into Hdb end.
  assert (Hby: is_bytes data) by exact Hdb.
  subst n.
  assert_PROP (isptr buf) as Pbuf by entailer!.
  assert_PROP (isptr snap) as Psnap by entailer!.
  fold (bytes_rep data).
  assert (CB: cbuf_ok false buf Ews buf 0 (Zlength data) (Zlength data) (bytes_rep data) data)
    by (apply cbuf_ok_whole; auto).
  forward_call (snap, Ews, buf, Ews, buf, 0, Zlength data, bytes_rep data, Zlength data, data).
  (* want = ref_adler32(adler, buf, n) *)
  forward.
  forward_call (adler, buf, Ews, buf, 0, Zlength data, bytes_rep data, Zlength data, data).
  forward.
  (* adler32_z(adler, buf, n) == want *)
  forward.
  forward_call (adler, buf, Zlength data, false, Ews, buf, 0, Zlength data, bytes_rep data, data, true, Ews).
  all: side.
  tok_norm. rewrite adler32_z_val_ref by auto.
  forward_call (Int.repr 1).
  all: side.
  (* adler32(adler, buf, n) == want *)
  forward.
  forward_call (adler, buf, Zlength data, false, Ews, buf, 0, Zlength data, bytes_rep data, data, true, Ews).
  all: side.
  tok_norm. rewrite adler32_z_val_ref by auto.
  forward_call (Int.repr 1).
  all: side.
  (* adler32_z(adler32_z(adler, buf, k), buf + k, n - k) == want *)
  forward.
  assert (CBk: cbuf_ok false buf Ews buf 0 (Zlength data) k (bytes_rep data) (sublist 0 k data))
    by (apply cbuf_ok_prefix; auto; lia).
  forward_call (adler, buf, k, false, Ews, buf, 0, Zlength data, bytes_rep data, sublist 0 k data, true, Ews).
  all: side.
  tok_norm. rewrite adler32_z_val_ref by auto.
  pose proof (ref_adler32_valid adler (sublist 0 k data) Hval) as Hvk.
  assert (Rk: 0 <= ref_adler32 adler (sublist 0 k data) <= Int64.max_unsigned) by (destruct Hvk; rep_lia).
  assert (CBk2: cbuf_ok false (offset_val k buf) Ews buf k (Zlength data) (Zlength data - k) (bytes_rep data)
                  (sublist k (Zlength data) data)).
  { replace (sublist k (Zlength data) data) with (sublist k (k + (Zlength data - k)) data) by (f_equal; lia).
    apply cbuf_ok_slice; auto; lia. }
  forward_call (ref_adler32 adler (sublist 0 k data), offset_val k buf, Zlength data - k, false, Ews, buf, k,
                Zlength data, bytes_rep data, sublist k (Zlength data) data, true, Ews).
  all: side.
  tok_norm. rewrite adler32_z_val_ref by auto.
  rewrite ref_adler32_app by auto.
  rewrite <- sublist_split by lia. rewrite sublist_same by lia.
  forward_call (Int.repr 1).
  all: side.
  (* r = adler32_z(any, buf, n) *)
  forward.
  forward_call (any, buf, Zlength data, false, Ews, buf, 0, Zlength data, bytes_rep data, data, true, Ews).
  all: side.
  tok_norm.
  forward.
  (* ref = ref_adler32(reduced any, buf, n) *)
  forward. forward.
  pose proof (adler_reduce_valid any) as Hred. destruct Hred as [Hred1 _].
  forward_call (adler_reduce any, buf, Ews, buf, 0, Zlength data, bytes_rep data, Zlength data, data).
  { entailer!. simpl.
    pose proof (adler_lo_range any). pose proof (adler_hi_range any).
    rewrite adler_hi_int2 by auto. rewrite land_lo by lia.
    rewrite (modu65521 (adler_hi any)), (modu65521 (adler_lo any)) by rep_lia.
    change (Int64.repr 16) with (Int64.repr (Int.unsigned (Int.repr 16))).
    assert (0 <= adler_hi any mod ADLER_BASE < ADLER_BASE) by (apply Z.mod_pos_bound; unfold ADLER_BASE; lia).
    assert (0 <= adler_lo any mod ADLER_BASE < ADLER_BASE) by (apply Z.mod_pos_bound; unfold ADLER_BASE; lia).
    rewrite or_pack_int by (unfold ADLER_BASE in *; lia).
    rewrite Int.unsigned_repr by rep_lia. reflexivity. }
  forward.
  pose proof (adler32_z_val_mod any data) as [M1 M2].
  pose proof (adler32_z_val_range any data Hby) as (Rr & Rl & Rh).
  pose proof (ref_adler32_valid (adler_reduce any) data (adler_reduce_valid any)) as (Vr & Vl & Vh).
  set (r := adler32_z_val any data) in *. set (rf := ref_adler32 (adler_reduce any) data) in *.
  clearbody r rf.
  set (w := ref_adler32 adler data) in *. set (w0 := ref_adler32 adler (sublist 0 k data)) in *.
  clearbody w w0.
  forward_call (Int.repr 1).
  { entailer!. simpl.
    rewrite land_lo by lia. rewrite land_lo by lia.
    rewrite modu65521 by (pose proof (adler_lo_range (r)); rep_lia).
    rewrite M1. rewrite Int64.eq_true. reflexivity. }
  (* floyd's automation unfolds the 64-bit operations of this argument for minutes: keep them opaque *)
  Opaque Int64.shru' Int64.and Int64.modu Int64.eq Int64.shru.
  forward_call (Int.repr 1).
  { entailer!. rewrite hi_check by rep_lia. reflexivity. }
  Transparent Int64.shru' Int64.and Int64.modu Int64.eq Int64.shru.
  forward_call (Int.repr 1).
  { entailer!. simpl. unfold Int64.cmpu, Int64.ltu. change (Int.unsigned (Int.repr (-1))) with 4294967295.
    rewrite !Int64.unsigned_repr by rep_lia. destruct (zlt 4294967295 (r)); [lia | reflexivity]. }
  (* adler32(any, Z_NULL, len) == 1 and adler32_z(any, Z_NULL, len) == 1 *)
  forward.
  forward_call (any, nullval, len, true, Ews, nullval, 0, 0, @nil val, @nil Z, false, Ews).
  all: side.
  forward_call (Int.repr 1).
  all: side.
  forward.
  forward_call (any, nullval, len, true, Ews, nullval, 0, 0, @nil val, @nil Z, false, Ews).
  all: side.
  forward_call (Int.repr 1).
  all: side.
  (* bytes_same(buf, snap, n) *)
  assert (CBs: cbuf_ok false snap Ews snap 0 (Zlength data) (Zlength data) (bytes_rep data) data)
    by (apply cbuf_ok_whole; auto).
  forward_call (buf, Ews, buf, 0, Zlength data, bytes_rep data, data, snap, Ews, snap, 0, Zlength data,
                bytes_rep data, data, Zlength data).
  all: side.
  destruct (list_eq_dec Z.eq_dec data data) as [_|NE]; [ | contradiction].
  forward_call (Int.repr 1).
  all: side.
  forward_call (tarray tuchar (Zlength data), buf, gv).
  { rewrite if_false by auto. sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength data)) (bytes_rep data) buf).
    cancel. }
  forward_call (tarray tuchar (Zlength data), snap, gv).
  { rewrite if_false by auto. sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength data)) (bytes_rep data) snap).
    cancel. }
  ret0.
Qed.
