(* What the memory laws need of the counting allocator (Spec.v) besides the bodies.

   - The block layout: a block of 8 + n bytes from malloc is the size_t header and, 8 bytes further, the n
     bytes handed out ([block_bytes], [block_split], [block_merge]).
   - The transfer to zlib's interface: count_alloc_spec and count_free_spec are stated at the harness unit's
     compspecs CS_count, which know struct z_stream_s and struct count only; deflate.c and inflate.c allocate
     at their own compspecs (struct internal_state, struct inflate_state, arrays).  The counting allocator
     never looks inside a block, so its specifications meet [zalloc_spec] / [zfree_spec] of [counted cp za zf]
     at ANY compspecs, with no side condition: a block of type t is used at CS_count as the byte array of
     sizeof t bytes ([counted_zalloc_sub], [counted_zfree_sub], [counted_za_funcs]).
   - The counters: while the bytes held stay a size_t value after every event, the size_t counters of the
     struct count are exactly the bytes held and the most held ([cnt_za]). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.harness.counted.Spec.

(* ---------------------------------------------------------------------- *)
(* The block layout                                                       *)
(* ---------------------------------------------------------------------- *)

Lemma malloc_compatible_after_header: forall n b, 0 <= n -> malloc_compatible (8 + n) b ->
  malloc_compatible 8 b /\ malloc_compatible n (offset_val 8 b).
Proof.
  intros n b N M. destruct b; try contradiction. simpl in M |- *. destruct M as [A S].
  unfold natural_alignment in *.
  rewrite <- (Ptrofs.repr_unsigned i), ptrofs_add_repr, !Ptrofs.unsigned_repr by rep_lia.
  split; split; try lia; auto. apply Z.divide_add_r; auto. apply Z.divide_refl.
Qed.

Section Layout.
Context {cs: compspecs}.

Lemma block_bytes: forall sh n b, 0 <= n -> malloc_compatible (8 + n) b ->
  data_at_ sh (tarray tuchar (8 + n)) b = (memory_block sh 8 b * memory_block sh n (offset_val 8 b))%logic.
Proof.
  intros sh n b N M.
  rewrite <- memory_block_data_at_.
  2: { apply malloc_compatible_field_compatible; auto. simpl. rewrite Z.max_r by lia. now rewrite Z.mul_1_l. }
  simpl sizeof. rewrite Z.max_r, Z.mul_1_l by lia.
  destruct b; try contradiction. simpl in M. destruct M as [_ M].
  rewrite <- (Ptrofs.repr_unsigned i) at 1 2. rewrite memory_block_split by rep_lia.
  simpl offset_val. replace (Ptrofs.add i (Ptrofs.repr 8)) with (Ptrofs.repr (Ptrofs.unsigned i + 8)); [reflexivity |].
  rewrite <- ptrofs_add_repr, Ptrofs.repr_unsigned; reflexivity.
Qed.

(* count_alloc's view of a new block: the header, then an object of type t *)
Lemma block_split: forall sh t b,
  complete_legal_cosu_type t = true -> natural_aligned natural_alignment t = true ->
  malloc_compatible (8 + sizeof t) b ->
  data_at_ sh (tarray tuchar (8 + sizeof t)) b = (data_at_ sh tulong b * data_at_ sh t (offset_val 8 b))%logic.
Proof.
  intros sh t b C NA M. pose proof (sizeof_pos t) as P.
  destruct (malloc_compatible_after_header (sizeof t) b) as [M8 Mt]; [lia | exact M |].
  rewrite <- (memory_block_data_at_ sh t) by (apply malloc_compatible_field_compatible; auto).
  rewrite <- (memory_block_data_at_ sh tulong) by (apply malloc_compatible_field_compatible; auto).
  apply block_bytes; auto; lia.
Qed.

(* count_free's view: the header and any object after it make the whole block again *)
Lemma block_merge: forall sh t b, malloc_compatible (8 + sizeof t) b ->
  (data_at_ sh tulong b * data_at_ sh t (offset_val 8 b))%logic |-- data_at_ sh (tarray tuchar (8 + sizeof t)) b.
Proof.
  intros sh t b M. pose proof (sizeof_pos t) as P.
  rewrite block_bytes by (auto; lia). rewrite !data_at__memory_block. Intros. simpl sizeof. cancel.
Qed.

End Layout.

(* ---------------------------------------------------------------------- *)
(* The token at two compspecs                                             *)
(* ---------------------------------------------------------------------- *)

(* the token depends on the size of the type only *)
Lemma count_tok_size: forall (cs1 cs2: compspecs) t1 t2 p, @sizeof cs1 t1 = @sizeof cs2 t2 ->
  @count_tok cs1 t1 p = @count_tok cs2 t2 p.
Proof.
  intros cs1 cs2 t1 t2 p E. unfold count_tok. rewrite E.
  rewrite (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2) Ews tulong _ _ (JMeq_refl _)) by reflexivity.
  rewrite (@malloc_token_change_composite cs1 cs2 (CCE_any cs1 cs2) Ews (tarray tuchar (8 + @sizeof cs2 t2)))
    by reflexivity.
  reflexivity.
Qed.

(* the block handed out is aligned and fits, as one from malloc *)
Lemma count_tok_compatible: forall {cs: compspecs} t p,
  @count_tok cs t p |-- !! (malloc_compatible (sizeof t) p /\ p = offset_val 8 (offset_val (-8) p)).
Proof.
  intros cs t p. unfold count_tok.
  sep_apply (malloc_token_local_facts Ews (tarray tuchar (8 + sizeof t)) (offset_val (-8) p)).
  Intros. apply prop_right. pose proof (sizeof_pos t).
  simpl sizeof in H. rewrite Z.max_r, Z.mul_1_l in H by lia.
  destruct (malloc_compatible_after_header (sizeof t) (offset_val (-8) p)) as [_ M]; [lia | exact H |].
  assert (isptr p) by (destruct p; try contradiction; exact I).
  rewrite offset_offset_val in M |- *. change (-8 + 8) with 0 in M |- *.
  rewrite isptr_offset_val_zero in M |- * by auto. auto.
Qed.

(* a block of type t at cs is the byte array of its size at any other compspecs *)
Lemma count_block_cs: forall (cs1 cs2: compspecs) t1 t2 p,
  @sizeof cs1 t1 = @sizeof cs2 t2 ->
  @complete_legal_cosu_type (@cenv_cs cs2) t2 = true ->
  @natural_aligned cs2 natural_alignment t2 = true ->
  (@count_tok cs1 t1 p * @data_at_ cs1 Ews t1 p)%logic |-- (@count_tok cs2 t2 p * @data_at_ cs2 Ews t2 p)%logic.
Proof.
  intros cs1 cs2 t1 t2 p E C N.
  rewrite (count_tok_size cs1 cs2 t1 t2 p E).
  sep_apply (@count_tok_compatible cs2 t2 p). Intros.
  rewrite (@data_at__memory_block cs1). Intros. rewrite E.
  rewrite <- (@memory_block_data_at_ cs2 Ews t2 p) by (apply malloc_compatible_field_compatible; tauto).
  cancel.
Qed.

(* ---------------------------------------------------------------------- *)
(* count_alloc and count_free as zlib's zalloc and zfree, at any compspecs  *)
(* ---------------------------------------------------------------------- *)

Section Transfer.
Context {cs: compspecs}.
Variables cp za zf: val.

Lemma counted_zalloc_sub: funspec_sub (snd count_alloc_spec) (@zalloc_spec cs (counted cp za zf)).
Proof.
  do_funspec_sub. destruct w as [[[[t items] size] gv] tr].
  Exists (cp, za, zf, tarray tuchar (items * size), items, size, gv, tr) emp. simpl. Intros.
  assert (S: @sizeof CS_count (tarray tuchar (items * size)) = items * size)
    by (simpl; rewrite Z.max_r by lia; lia).
  apply andp_right; [apply prop_right | cancel]. split.
  - intros rho'. apply andp_left2. rewrite emp_sepcon.
    Intros p. Exists p. entailer!. if_tac; [cancel |].
    sep_apply (count_block_cs CS_count cs (tarray tuchar (items * size)) t (eval_id ret_temp rho')); auto;
      [lia | cancel].
  - repeat split; auto; lia.
Qed.

Lemma counted_zfree_sub: funspec_sub (snd count_free_spec) (@zfree_spec cs (counted cp za zf)).
Proof.
  do_funspec_sub. destruct w as [[[t p] gv] tr].
  Exists (cp, za, zf, tarray tuchar (@sizeof cs t), p, gv, tr) emp. simpl. Intros.
  pose proof (@sizeof_pos cs t) as P.
  assert (S: @sizeof CS_count (tarray tuchar (@sizeof cs t)) = @sizeof cs t)
    by (simpl; rewrite Z.max_r by lia; lia).
  sep_apply (count_block_cs cs CS_count t (tarray tuchar (@sizeof cs t)) p); auto.
  apply andp_right; [apply prop_right | cancel]. split.
  - intros rho'. apply andp_left2. rewrite emp_sepcon. rewrite Z.max_r, Z.mul_1_l by lia. entailer!.
  - repeat split; auto.
Qed.

(* the two function pointers main stores in the z_stream are zlib's allocator [counted cp za zf] *)
Lemma counted_za_funcs:
  (func_ptr' (snd count_alloc_spec) za * func_ptr' (snd count_free_spec) zf)%logic
  |-- @za_funcs cs (counted cp za zf).
Proof.
  unfold za_funcs. simpl za_alloc. simpl za_free.
  apply sepcon_derives; apply func_ptr'_mono; [apply counted_zalloc_sub | apply counted_zfree_sub].
Qed.

End Transfer.

(* ---------------------------------------------------------------------- *)
(* The counters                                                            *)
(* ---------------------------------------------------------------------- *)

(* the size_t counters are the bytes held and the most held, while the bytes held after each event stay
   within size_t *)
Lemma cnt_za: forall tr,
  (forall l1 l2, tr = l1 ++ l2 -> 0 <= za_now l1 <= Int64.max_unsigned) ->
  cnt tr = (za_now tr, za_peak tr).
Proof.
  assert (G: forall tr,
    (forall l1 l2, tr = l1 ++ l2 -> 0 <= za_now l1 <= Int64.max_unsigned) ->
    cnt tr = (za_now tr, za_peak tr) /\ 0 <= za_peak tr <= Int64.max_unsigned).
  { intros tr. rewrite <- (rev_involutive tr). induction (rev tr) as [| e l IH]; intros H.
    - simpl rev. split; [reflexivity | rewrite za_peak_nil; rep_lia].
    - simpl rev in *. destruct IH as [IH1 IH2].
      { intros l1 l2 E. apply (H l1 (l2 ++ [e])). rewrite E, app_assoc. reflexivity. }
      pose proof (H (rev l ++ [e]) [] (eq_sym (app_nil_r _))) as Hn.
      unfold cnt in *. rewrite fold_left_app. rewrite IH1. simpl fold_left.
      destruct e as [n | n | ]; simpl cnt_step.
      + rewrite za_now_alloc in Hn |- *. rewrite za_peak_alloc.
        rewrite Z.mod_small by rep_lia.
        destruct (Z.ltb_spec (za_peak (rev l)) (za_now (rev l) + n)).
        * rewrite Z.max_r by lia. split; [reflexivity | lia].
        * rewrite Z.max_l by lia. split; [reflexivity | lia].
      + rewrite za_now_free in Hn |- *. rewrite za_peak_free.
        rewrite Z.mod_small by rep_lia. split; [reflexivity | lia].
      + rewrite za_now_fail, za_peak_fail. split; [reflexivity | lia]. }
  intros tr H. apply (G tr H).
Qed.
