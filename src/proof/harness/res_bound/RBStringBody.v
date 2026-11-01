(* Law res_bound: the body of the harness's any_string against RBString.any_string_spec. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.res_bound.RBString.
Require Import Zlib.harness.res_bound.code.
Require Zlib.units.Adler32.
#[local] Existing Instance Zlib.units.Adler32.CS.

(* any_string(len) allocates len + 1 arbitrary bytes, assumes the first len of them non-zero and stores a zero at
   [len].  The loop invariant: the first i bytes are non-zero (each gp_assume adds one).  When malloc fails, the
   returned byte list is only a witness of the right length (here len ones); no memory is described. *)
Lemma body_any_string : any_string_body_stmt.
Proof.
  unfold any_string_body_stmt.
  start_function.
  forward_call (len + 1, gv).
  Intros vret. destruct vret as [q bs]; simpl fst in *; simpl snd in *.
  destruct (eq_dec q nullval) as [Hq | Hq].
  { subst q. forward_if.
    2: { exfalso; auto. }
    forward. Exists nullval (Zrepeat 1 len).
    rewrite if_true by auto. entailer!.
    split; [rewrite Zlength_Zrepeat; lia |].
    apply Forall_forall; intros b Hb. unfold Zrepeat in Hb; apply repeat_spec in Hb; subst b; rep_lia. }
  Intros.
  forward_if.
  { contradiction. }
  forward_for_simple_bound len
    (EX i : Z,
     PROP (Forall (fun b => b <> 0) (sublist 0 i bs))
     LOCAL (temp _string q; gvars gv; temp _len (Vlong (Int64.repr len)))
     SEP (mem_mgr gv; malloc_token Ews (tarray tuchar (len + 1)) q;
          data_at Ews (tarray tuchar (len + 1)) (bytes_rep bs) q)).
  { entailer!. }
  { assert (Hb : 0 <= Znth i bs <= Byte.max_unsigned) by (apply is_bytes_Znth; auto; lia).
    forward.
    { entailer!. rewrite Znth_bytes_rep by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite Znth_bytes_rep by lia.
    forward_call (Int.repr (if Z.eq_dec (Znth i bs) 0 then 0 else 1)).
    { entailer!. simpl. unfold Int.eq. destruct (Z.eq_dec (Znth i bs) 0) as [E|E].
      - rewrite E. reflexivity.
      - rewrite zeq_false; [reflexivity|]. rewrite !Int.unsigned_repr by rep_lia. auto. }
    destruct (Z.eq_dec (Znth i bs) 0) as [E|E]; [contradiction|].
    entailer!.
    rewrite (sublist_split 0 i (i+1)) by lia. rewrite sublist_len_1 by lia.
    apply Forall_app; split; auto. }
  Intros. forward. forward.
  Exists q (sublist 0 len bs). rewrite if_false by auto.
  entailer!.
  { split; [rewrite Zlength_sublist; lia |].
    apply Forall_forall; intros b Hb.
    pose proof (is_bytes_sublist bs 0 len H1) as Hs. unfold is_bytes in Hs.
    rewrite Forall_forall in Hs, H3. specialize (Hs b Hb). specialize (H3 b Hb). rep_lia. }
  apply derives_refl'. f_equal.
  rewrite bytes_rep_app. unfold bytes_rep at 2. simpl.
  rewrite <- sublist_bytes_rep.
  rewrite upd_Znth_unfold by (rewrite Zlength_bytes_rep; lia).
  rewrite Zlength_bytes_rep, H0.
  replace (len + 1 + 1 - 1 - (len + 1)) with 0 by lia. simpl. f_equal.
  rewrite sublist_nil. reflexivity.
Qed.
