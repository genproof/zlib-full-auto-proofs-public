(* Law rt_session (harness/rt_session.c): main's statements 0-23 (SMKit.segA1_stmt), from PRE0 to A24: the draws
   (level .. strategy; gp_assume(deflate_params_ok(..)) makes them parameters deflateInit2 accepts, rparams_ok;
   choice, with_dict, with_head; the lengths; text, time, os, hcrc), the objects dict, extra (alloc_any_bytes), name,
   comment (any_string) and data (alloc_any_bytes), and their NULL test, main returning 0 if one is NULL.  Statements
   0-22 are proved here up to SMA1Kit.Q23; statement 23 by the cases of the pointers (SMA1C1.v .. SMA1C6.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SDFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.proof.harness.rt_session.SMA1Kit.
Require Import Zlib.proof.harness.rt_session.SMA1C1.
Require Import Zlib.proof.harness.rt_session.SMA1C2.
Require Import Zlib.proof.harness.rt_session.SMA1C3.
Require Import Zlib.proof.harness.rt_session.SMA1C4.
Require Import Zlib.proof.harness.rt_session.SMA1C5.
Require Import Zlib.proof.harness.rt_session.SMA1C6.
Require Zlib.proof.harness.laws_session.Spec.
Require Zlib.proof.harness.laws_session.Facts.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers; each identifier comparison is decided by vm_compute instead. *)
Ltac sa1_rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in sa1_rlt_fix u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := sa1_rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

(* the drawn int parameters as the signed values main passes on *)
Lemma sa1_vi_signed x : Vint (Int.repr x) = vi (Int.signed (Int.repr x)).
Proof. unfold vi; rewrite Int.repr_signed; reflexivity. Qed.

(* (tbool) (choice & 1) for a byte choice *)
Lemma sa1_odd ch : 0 <= ch <= 255 ->
  (if Int.eq (Int.and (Int.repr ch) (Int.repr 1)) Int.zero then Int.zero else Int.one) = Int.repr (Z.b2z (Z.odd ch)).
Proof.
  intros Hc. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia.
  change (Z.land ch 1) with (Z.land ch (Z.ones 1)). rewrite Z.land_ones by lia.
  change (2 ^ 1) with 2. rewrite Zmod_odd. destruct (Z.odd ch); reflexivity.
Qed.

(* dict_len = 1 + upto(UINT_MAX - 1) *)
Lemma sa1_add1 d : 0 <= d <= 4294967294 ->
  Int64.add (Int64.repr (Int.signed (Int.repr 1))) (Int64.repr d) = Int64.repr (1 + d).
Proof.
  intros Hd. change (Int.signed (Int.repr 1)) with 1.
  rewrite Int64.add_unsigned, !Int64.unsigned_repr by rep_lia. reflexivity.
Qed.

(* statement 23 by the cases of the five pointers (SMA1C1.v .. SMA1C6.v) *)
Lemma sa1_test {Espec : OracleKind} gv vh vg vc va vd lvl wb mem str ch dl cap text utm os hcrc
    dict xf nm cm data dp xp np cmp datp :
  a1_facts lvl wb mem str ch dl cap text utm os hcrc dict xf nm cm data ->
  a1_triple gv vh vg vc va vd lvl wb mem str ch dl cap text utm os hcrc dict xf nm cm data dp xp np cmp datp.
Proof.
  intros HF.
  destruct (eq_dec dp nullval) as [Hd | Hd]; [now apply sa1_c1 |].
  destruct (eq_dec xp nullval) as [Hx | Hx]; [now apply sa1_c2 |].
  destruct (eq_dec np nullval) as [Hn | Hn]; [now apply sa1_c3 |].
  destruct (eq_dec cmp nullval) as [Hc | Hc]; [now apply sa1_c4 |].
  destruct (eq_dec datp nullval) as [Ht | Ht]; [now apply sa1_c5 | now apply sa1_c6].
Qed.

Lemma sm_segA1 : segA1_stmt.
Proof.
  intros Espec gv vh vg vc va vd. unfold PRE0, segA1, POST_s, lvs, lv_locals.
  unfold Delta_s; simplify_func_tycontext. abbreviate_semax.
  forward_call. Intros lv.
  forward_call. Intros wv.
  forward_call. Intros mv.
  forward_call. Intros sv.
  rewrite !sa1_vi_signed.
  forward_call (Int.signed (Int.repr lv), Int.signed (Int.repr wv), Int.signed (Int.repr mv),
                Int.signed (Int.repr sv)).
  destruct (Zlib.proof.harness.laws_session.Spec.deflate_params_valid (Int.signed (Int.repr lv))
              (Int.signed (Int.repr wv)) (Int.signed (Int.repr mv)) (Int.signed (Int.repr sv))) eqn:Hpv.
  2:{ forward_call (Int.zero). contradiction. }
  forward_call (Int.one).
  rewrite Zlib.proof.harness.laws_session.Facts.deflate_params_valid_rt in Hpv.
  pose proof (Int.signed_range (Int.repr lv)). pose proof (Int.signed_range (Int.repr wv)).
  pose proof (Int.signed_range (Int.repr mv)). pose proof (Int.signed_range (Int.repr sv)).
  set (lvl := Int.signed (Int.repr lv)) in *. set (wb := Int.signed (Int.repr wv)) in *.
  set (mem := Int.signed (Int.repr mv)) in *. set (str := Int.signed (Int.repr sv)) in *.
  clearbody lvl wb mem str.
  forward_call. Intros ch.
  (* with_dict = window_bits <= 15 && (choice & 1) *)
  sa1_ifpost _t'7 (vi (Z.b2z ((wb <=? 15) && Z.odd ch))).
  { forward. rewrite (sa1_odd ch) by rep_lia. rewrite (proj2 (Z.leb_le wb 15)) by lia. entailer!. }
  { forward. rewrite (proj2 (Z.leb_gt wb 15)) by lia. entailer!. }
  forward.
  (* with_head = window_bits > 15 && (choice & 1) *)
  sa1_ifpost _t'8 (vi (Z.b2z ((15 <? wb) && Z.odd ch))).
  { forward. rewrite (sa1_odd ch) by rep_lia. rewrite (proj2 (Z.ltb_lt 15 wb)) by lia. entailer!. }
  { forward. rewrite (proj2 (Z.ltb_ge 15 wb)) by lia. entailer!. }
  forward.
  (* dict_len = 1 + upto(UINT_MAX - 1), extra_len, name_len, comment_len, data_len, out_size *)
  forward_call 4294967294. Intros dl. forward.
  rewrite (sa1_add1 dl) by lia.
  forward_call 65535. Intros xl.
  forward_call 4294967294. Intros nl.
  forward_call 4294967294. Intros cl.
  forward_call max_size. Intros n.
  forward_call max_size. Intros cap.
  (* text, time, os, hcrc *)
  forward_call. Intros ut.
  rewrite <- !seq_assoc. forward_call. Intros utm. forward.
  forward_call. Intros uo.
  forward_call. Intros uh.
  rewrite Int.unsigned_repr by rep_lia.
  rewrite (sa1_vi_signed ut), (sa1_vi_signed uo), (sa1_vi_signed uh).
  pose proof (Int.signed_range (Int.repr ut)). pose proof (Int.signed_range (Int.repr uo)).
  pose proof (Int.signed_range (Int.repr uh)).
  set (text := Int.signed (Int.repr ut)) in *. set (os := Int.signed (Int.repr uo)) in *.
  set (hcrc := Int.signed (Int.repr uh)) in *. clearbody text os hcrc.
  (* the five objects *)
  forward_call (1 + dl, gv). Intros vret. destruct vret as [dp dict]. cbn [fst snd] in *.
  forward_call (xl, gv). Intros vret. destruct vret as [xp xf]. cbn [fst snd] in *.
  forward_call (nl, gv). Intros vret. destruct vret as [np nm]. cbn [fst snd] in *.
  forward_call (cl, gv). Intros vret. destruct vret as [cmp cm]. cbn [fst snd] in *.
  forward_call (n, gv). { unfold max_size in *; rep_lia. } Intros vret. destruct vret as [datp data].
  cbn [fst snd] in *.
  subst xl nl cl n.
  rewrite <- H22.
  assert (HF : a1_facts lvl wb mem str ch dl cap text utm os hcrc dict xf nm cm data).
  { unfold a1_facts, rs32, rbytes, nzbytes. repeat split; try exact Hpv;
      try (eapply Forall_impl; [ | eassumption]; cbv beta; intros; rep_lia); rep_lia. }
  (* statement 23 *)
  exact (sa1_test gv vh vg vc va vd lvl wb mem str ch dl cap text utm os hcrc dict xf nm cm data dp xp np cmp datp
           HF).
Qed.
