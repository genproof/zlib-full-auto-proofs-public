(* Law rfc_trailing_bytes, main: statements 21-26 of TBKit.v (room, after = upto(room), input =
   any_bytes(compressed_len + after) and its NULL check, the loop copying the compressed bytes to input), from
   TBKit.tb_DH to TBKit.tb_TH. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.harness.clip_streams.CS Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.DFacts Zlib.proof.harness.clip_streams.IFacts.
Require Import Zlib.proof.harness.clip_streams.TBFacts Zlib.proof.harness.clip_streams.MainDefs.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.zutil.Libc.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.TBKit.
Require Import Zlib.harness.rfc_trailing_bytes.code.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

(* remove_localdef_temp by rewriting (Floyd's default simplification is slow on main's many temporaries) *)
Lemma tbi_rlt_nil i: remove_localdef_temp i [] = [].
Proof. reflexivity. Qed.
Lemma tbi_rlt_gvars i g l: remove_localdef_temp i (gvars g :: l) = gvars g :: remove_localdef_temp i l.
Proof. reflexivity. Qed.
Lemma tbi_rlt_lvar i j t v l: remove_localdef_temp i (lvar j t v :: l) = lvar j t v :: remove_localdef_temp i l.
Proof. reflexivity. Qed.
Lemma tbi_rlt_same i v l: remove_localdef_temp i (temp i v :: l) = remove_localdef_temp i l.
Proof. simpl. unfold rlt_ident_eq. rewrite if_true by auto. reflexivity. Qed.
Lemma tbi_rlt_cons i j v l: i <> j -> remove_localdef_temp i (temp j v :: l) = temp j v :: remove_localdef_temp i l.
Proof. intros. simpl. unfold rlt_ident_eq. rewrite if_false by auto. reflexivity. Qed.

Ltac tbi_rlt :=
  repeat first [ rewrite tbi_rlt_nil | rewrite tbi_rlt_gvars | rewrite tbi_rlt_lvar | rewrite tbi_rlt_same
               | rewrite tbi_rlt_cons by (let X := fresh in intro X; discriminate X) ].
Ltac simplify_remove_localdef_temp ::= tbi_rlt.

(* byte arrays and malloc tokens of any_bytes (at the compspecs of the laws_common.h helpers) at main's *)
Lemma tbi_bytes_adler sh n (v: list val) q:
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at CS.CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.
Lemma tbi_tok_adler sh n q:
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) q = @malloc_token CS.CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_adler32). reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The input object during the copy loop                                                          *)

(* the input object after i iterations: the first i bytes of O, then the bytes bs any_bytes gave from i on *)
Definition tbi_mix (i : Z) (O bs : list Z) : list Z := sublist 0 i O ++ sublist i (Zlength bs) bs.

Lemma tbi_mix_0 O bs : tbi_mix 0 O bs = bs.
Proof. unfold tbi_mix. rewrite sublist_nil, sublist_same by lia. reflexivity. Qed.

Lemma tbi_mix_length i O bs : 0 <= i <= Zlength O -> Zlength O <= Zlength bs -> Zlength (tbi_mix i O bs) = Zlength bs.
Proof. intros. unfold tbi_mix. rewrite Zlength_app, !Zlength_sublist by lia. lia. Qed.

(* the store of iteration i: input[i] = compressed[i] *)
Lemma tbi_mix_store i O bs : 0 <= i < Zlength O -> Zlength O <= Zlength bs -> rbytes O ->
  upd_Znth i (bytes_rep (tbi_mix i O bs)) (Vint (Int.zero_ext 8 (Int.repr (Znth i O)))) =
  bytes_rep (tbi_mix (i + 1) O bs).
Proof.
  intros Hi Hl HO.
  assert (B : 0 <= Znth i O < 256) by (exact (proj1 (Forall_Znth O _) HO i Hi)).
  assert (E : Int.zero_ext 8 (Int.repr (Znth i O)) = Int.repr (Znth i O)).
  { rewrite <- (Int.repr_unsigned (Int.zero_ext 8 _)). rewrite Int.zero_ext_mod by (cbn; lia).
    rewrite Int.unsigned_repr by rep_lia. change (two_p 8) with 256. rewrite Z.mod_small by lia. reflexivity. }
  rewrite E. unfold bytes_rep.
  change (Vint (Int.repr (Znth i O))) with ((fun b => Vint (Int.repr b)) (Znth i O)).
  rewrite upd_Znth_map. f_equal. unfold tbi_mix.
  rewrite (sublist_split 0 i (i + 1) O) by lia. rewrite (sublist_split i (i + 1) (Zlength bs) bs) by lia.
  rewrite !sublist_len_1 by lia. rewrite <- app_assoc.
  rewrite upd_Znth_app2 by (rewrite Zlength_sublist by lia; list_solve).
  rewrite Zlength_sublist by lia. replace (i - (i - 0)) with 0 by lia.
  simpl app. rewrite upd_Znth0. reflexivity.
Qed.

(* the byte i of the compressed object (i < |O|): O's *)
Lemma tbi_O_at i O (R : list val) : 0 <= i < Zlength O ->
  Znth i (bytes_rep O ++ R) = Vint (Int.repr (Znth i O)).
Proof.
  intros Hi. unfold bytes_rep. rewrite app_Znth1 by (rewrite Zlength_map; lia).
  rewrite Znth_map by lia. reflexivity.
Qed.

Lemma tb_input : tb_input_stmt.
Proof.
  intros Espec wbits n b D O dp op cp vc vd gv K.
  unfold tb_seg21, tb_DH, POST_B, POST_tb. abbreviate_semax.
  Intros.
  forward.
  set (r := if Zlength O <? max_size then max_size - Zlength O else 0).
  match goal with |- semax _ (PROPx _ (LOCALx (_ :: ?Q) (SEPx ?R))) _ _ =>
    forward_if (PROPx [] (LOCALx (temp _room (Vlong (Int64.repr r)) :: Q) (SEPx R))) end.
  { forward. entailer!. unfold r, max_size. destruct (Z.ltb_spec (Zlength O) 9223372036854775807); [reflexivity | lia]. }
  { forward. entailer!. unfold r, max_size. destruct (Z.ltb_spec (Zlength O) 9223372036854775807); [lia | reflexivity]. }
  assert (Hr : 0 <= r /\ (Zlength O < max_size -> Zlength O + r = max_size) /\ (max_size <= Zlength O -> r = 0)).
  { unfold r. destruct (Z.ltb_spec (Zlength O) max_size); unfold max_size in *; lia. }
  clearbody r.
  forward_call r.
  { unfold max_size in *. rep_lia. }
  Intros after.
  assert (Ha : Zlength O + after <= Ptrofs.max_unsigned).
  { destruct (Z.lt_ge_cases (Zlength O) max_size); unfold max_size in *; rep_lia. }
  forward_call (Zlength O + after, gv).
  Intros vret. destruct vret as [ip bs]. simpl fst in *; simpl snd in *.
  destruct (eq_dec ip nullval) as [Pip|Pip].
  { subst ip. forward_if. { ret0. } { exfalso; auto. } }
  Intros. rewrite tbi_bytes_adler, tbi_tok_adler.
  forward_if.
  { contradiction. }
  assert (HOl : Zlength O <= Zlength bs) by lia.
  freeze [0;1;3;4;5;6;7;9;10;11;12] FR.
  forward_for_simple_bound (Zlength O) (EX i : Z,
    PROP ()
    LOCAL (temp _input ip; temp _after (Vlong (Int64.repr after));
           temp _room (Vlong (Int64.repr r)); temp _data_len (Vlong (Int64.repr n));
           temp _data dp; temp _out op; temp _window_bits (Vint (Int.repr wbits));
           temp _compressed cp; temp _compressed_len (Vlong (Int64.repr (Zlength O)));
           lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
    SEP (FRZL FR; data_at Ews (tarray tuchar (Zlength O + after)) (bytes_rep (tbi_mix i O bs)) ip;
         data_at Ews (tarray tuchar b) (bytes_rep O ++ Zrepeat Vundef (b - Zlength O)) cp)).
  { entailer!. rewrite tbi_mix_0. auto. }
  { assert (Bo : 0 <= Znth i O < 256) by (exact (proj1 (Forall_Znth O _) H7 i ltac:(lia))).
    forward.
    { rewrite tbi_O_at by lia. entailer!. simpl; rep_lia. }
    rewrite tbi_O_at by lia.
    forward.
    rewrite tbi_mix_store by (auto; lia).
    entailer!. }
  assert_PROP (isptr ip) as Pip2 by entailer!.
  assert (Hsl : Zlength (tbi_mix (Zlength O) O bs) = Zlength O + after) by (rewrite tbi_mix_length; lia).
  assert (Hf : tb_facts wbits n D O (tbi_mix (Zlength O) O bs) dp op ip).
  { unfold tb_facts. rewrite Hsl. split; [exact H | ]. split; [exact H0 | ]. split; [exact H1 | ].
    split; [lia | ]. split; [ | split; [ | repeat split; auto; lia]].
    - unfold tbi_mix. rewrite sublist0_app1 by (rewrite Zlength_sublist; lia).
      rewrite (sublist_same 0 (Zlength O) O) by lia. rewrite sublist_same by lia. reflexivity.
    - unfold bytes_ok, tbi_mix. apply Forall_app; split.
      + apply Forall_sublist. eapply Forall_impl; [ | exact H7]. simpl. intros; rep_lia.
      + apply Forall_sublist. exact H10. }
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  thaw FR.
  eapply semax_pre; [ | apply (K _ _ Hf)].
  unfold tb_TH. rewrite Hsl. replace (Zlength O + after - Zlength O) with after by lia.
  entailer!.
Qed.
