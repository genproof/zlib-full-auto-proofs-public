(* Law rt_gzip_header on the round-2 harness: the bodies of the harness's own functions any_string and same_field
   (G2MainDefs.rtg2_helpers_stmt; the two functions are unchanged since round 1, whose proof this is). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.Bytes.
Require Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.harness.rt_gzip_header.code.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainDefs.

#[local] Existing Instance Zlib.units.Adler32.CS.

(* same_field: the absent case compares got with NULL; the present case calls bytes_eq only on a non-NULL got,
   whose object (possibly of size 0) is valid by its malloc token *)
Lemma body_same_field : semax_body [] Gprog_same_field f_same_field same_field_spec.
Proof.
  start_function.
  forward_if.
  { assert (present = 0).
    { rewrite <- (Int.signed_repr present) by rep_lia. rewrite H6. reflexivity. }
    subst present. specialize (H1 eq_refl). subst got. forward. }
  assert (Hp : present <> 0). { intro; subst; contradiction. }
  assert (Hq : (present =? 0) = false) by lia.
  rewrite Hq.
  destruct (eq_dec got nullval) as [Eg|Ng].
  { subst got. Intros.
    forward_if (temp _t'1 (Vint Int.zero)).
    { discriminate. }
    { forward. entailer!. }
    forward. rewrite Hq. entailer!. }
  Intros.
  assert_PROP (isptr got /\ isptr given) by entailer!.
  forward_if (temp _t'1 (Vint (Int.repr (if list_eq_dec Z.eq_dec dg dv then 1 else 0)))).
  { forward_call (got, shg, got, 0, len, bytes_rep dg, dg, given, shv, given, 0, len, bytes_rep dv, dv, len).
    { unfold cbuf_ok, bytes_rep in *.
      rewrite !isptr_offset_val_zero by tauto.
      rewrite !sublist_same by (rewrite ?Zlength_map; lia).
      repeat split; auto; lia. }
    forward. entailer!. destruct (list_eq_dec Z.eq_dec dg dv); reflexivity. }
  { contradiction. }
  forward. rewrite Hq. destruct (eq_dec got nullval); [contradiction|]. entailer!.
Qed.

(* any_string: any_bytes(len + 1); the loop keeps the invariant that the first i bytes are nonzero (each
   gp_assume adds one); the final store makes the last byte 0 *)
Lemma body_any_string : semax_body [] Gprog_any_string f_any_string any_string_spec.
Proof.
  start_function.
  forward_call (len + 1, gv).
  Intros vret. destruct vret as [q bs]. simpl fst in *; simpl snd in *.
  destruct (eq_dec q nullval) as [Eq|Nq].
  { subst q. forward_if. 2: contradiction. forward.
    Exists nullval (repeat 1 (Z.to_nat len)). entailer!.
    split. { rewrite Zlength_repeat; lia. }
    apply Forall_forall; intros x Hx; apply repeat_spec in Hx; subst; rep_lia. }
  Intros.
  forward_if. { subst q. contradiction. }
  assert (Hb : Forall (fun b => 0 <= b <= Byte.max_unsigned) bs) by exact H1.
  forward_for_simple_bound len (EX i : Z,
    PROP (Forall (fun b => 0 < b) (sublist 0 i bs))
    LOCAL (temp _string q; gvars gv; temp _len (Vlong (Int64.repr len)))
    SEP (mem_mgr gv; malloc_token Ews (tarray tuchar (len + 1)) q;
         data_at Ews (tarray tuchar (len + 1)) (bytes_rep bs) q)).
  { rewrite sublist_nil. entailer!. }
  { pose proof (proj1 (Forall_forall _ _) Hb (Znth i bs) ltac:(apply Znth_In; lia)) as Hi. simpl in Hi.
    forward.
    { entailer!. unfold bytes_rep. rewrite Znth_map by lia. simpl. rewrite Int.unsigned_repr by rep_lia. lia. }
    match goal with |- context [temp _t'2 ?v] => replace v with (Vint (Int.repr (Znth i bs))) end.
    2: { unfold bytes_rep; rewrite Znth_map by lia; reflexivity. }
    forward_call (Int.repr (if Z.eq_dec (Znth i bs) 0 then 0 else 1)).
    { entailer!.
      destruct (Z.eq_dec (Znth i bs) 0) as [E|E]; [rewrite E; reflexivity|].
      simpl. rewrite Int.eq_false; [reflexivity|].
      intro X. apply repr_inj_unsigned in X; rep_lia. }
    destruct (Z.eq_dec (Znth i bs) 0) as [E|E]; [contradiction|].
    entailer!.
    rewrite (sublist_split 0 i (i + 1)) by lia. rewrite sublist_len_1 by lia.
    apply Forall_app; split; auto. constructor; [lia|constructor]. }
  Intros.
  forward.
  forward.
  Exists q (sublist 0 len bs).
  rewrite if_false by auto.
  assert (Eb : upd_Znth len (bytes_rep bs) (Vint (Int.zero_ext 8 (Int.repr 0))) =
               bytes_rep (sublist 0 len bs ++ [0])).
  { unfold bytes_rep. rewrite upd_Znth_unfold by (rewrite Zlength_map; lia).
    rewrite map_app, <- sublist_map, Zlength_map, H0, sublist_nil. reflexivity. }
  rewrite Eb. entailer!.
  split. { rewrite Zlength_sublist; lia. }
  apply Forall_forall. intros x Hx.
  split. { eapply Forall_forall in H3; eauto. }
  apply (sublist_In 0 len bs) in Hx. eapply Forall_forall in Hb; eauto. lia.
Qed.

Lemma rtg2_helpers : rtg2_helpers_stmt.
Proof. split; [exact body_any_string | exact body_same_field]. Qed.
