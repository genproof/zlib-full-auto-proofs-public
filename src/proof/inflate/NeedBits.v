(* NEEDBITS(n) for a constant n <= 32:  while (bits < n) { PULLBYTE(); }  from loop_state F m to
   loop_state F (needbits n m).  Used by every case that starts with (or reaches, in the loop state)
   a constant NEEDBITS. *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CaseCommon.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.
Set Ltac Backtrace.

(* the body of NEEDBITS's while loop (PULLBYTE), with clightgen's temporaries t1 (next) and t2 (byte) *)
Definition pullbyte_body (t1 t2: ident) : statement :=
  Ssequence
    (Sifthenelse (Ebinop Oeq (Etempvar _have tuint) (Econst_int (Int.repr 0) tint) tint)
      (Ssequence (Sset _leave (Econst_int (Int.repr 1) tint)) Sbreak) Sskip)
    (Ssequence
      (Sset _have (Ebinop Osub (Etempvar _have tuint) (Econst_int (Int.repr 1) tint) tuint))
      (Ssequence
        (Ssequence
          (Ssequence (Sset t1 (Etempvar _next (tptr tuchar)))
            (Sset _next (Ebinop Oadd (Etempvar t1 (tptr tuchar)) (Econst_int (Int.repr 1) tint) (tptr tuchar))))
          (Ssequence (Sset t2 (Ederef (Etempvar t1 (tptr tuchar)) tuchar))
            (Sset _hold (Ebinop Oadd (Etempvar _hold tulong)
                           (Ebinop Oshl (Ecast (Etempvar t2 tuchar) tulong) (Etempvar _bits tuint) tulong)
                           tulong))))
        (Sset _bits (Ebinop Oadd (Etempvar _bits tuint) (Econst_int (Int.repr 8) tint) tuint)))).

Definition needbits_stmt (n: Z) (t1 t2: ident) : statement :=
  Swhile (Ebinop Olt (Etempvar _bits tuint) (Ecast (Econst_int (Int.repr n) tint) tuint) tint)
    (pullbyte_body t1 t2).

(* the temporaries of the loop state *)
Definition loop_temps : list ident :=
  [_strm; _flush; _state; _next; _put; _have; _left; _hold; _bits; _in; _out; _ret; _leave].

(* ---------------------------------------------------------------------------------------------- *)
(* the model: k pulls                                                                             *)

Fixpoint pullk (k: nat) (m: mst) : mst := match k with O => m | S k' => pullk k' (pull m) end.

Lemma pullk_S: forall k m, pullk (S k) m = pull (pullk k m).
Proof. induction k; intros; simpl; auto. rewrite <- IHk. reflexivity. Qed.

(* pulls change only next, hold and bits *)
Lemma mem_rep_pull: forall F m, mem_rep F (pull m) = mem_rep F m.
Proof. intros. reflexivity. Qed.
Lemma mem_rep_pullk: forall F k m, mem_rep F (pullk k m) = mem_rep F m.
Proof. induction k; intros; simpl; auto. rewrite IHk. reflexivity. Qed.

Lemma pullk_fields: forall k m,
  m_s (pullk k m) = m_s m /\ m_h (pullk k m) = m_h m /\ m_inp (pullk k m) = m_inp m /\
  m_aout (pullk k m) = m_aout m /\ m_ow (pullk k m) = m_ow m /\ m_in (pullk k m) = m_in m /\
  m_out (pullk k m) = m_out m /\ m_ret (pullk k m) = m_ret m /\ m_leave (pullk k m) = m_leave m /\
  m_nx (pullk k m) = m_nx m + Z.of_nat k.
Proof.
  induction k; intros; simpl. { repeat split; lia. }
  destruct (IHk (pull m)) as (A1&A2&A3&A4&A5&A6&A7&A8&A9&A10).
  rewrite A1, A2, A3, A4, A5, A6, A7, A8, A9, A10. unfold pull. mnorm_goal. repeat split; lia.
Qed.

Lemma needbits_f_S: forall k n m,
  needbits_f (S k) n m =
  if m_bits m <? n then if m_have m =? 0 then set_leave m else needbits_f k n (pull m) else m.
Proof. reflexivity. Qed.

Lemma needbits_f_ge: forall k n m, n <= m_bits m -> needbits_f k n m = m.
Proof. destruct k; intros; simpl; auto. destruct (m_bits m <? n) eqn:E; auto. lia. Qed.

(* the LOCAL part of loop_state *)
Definition loop_locals (F: frame) (m: mst) : list localdef :=
  [temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
   temp _next (in_ptr (f_ib F) (m_nx m)); temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
   temp _have (zv (m_have m)); temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
   temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
   temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
   lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
   lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F)].

Lemma loop_state_eq: forall F m,
  loop_state F m = PROPx [in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m)]
                     (LOCALx (loop_locals F m) (SEPx [mem_rep F m; locals_rep F])).
Proof. reflexivity. Qed.

Lemma in_ok_have0: forall m, in_ok InNull (m_inp m) -> mwf m -> m_have m = 0.
Proof. intros m H W. unfold in_ok in H. pose proof (mw_nx _ W). unfold m_have. rewrite H in *. simpl in *. list_solve. Qed.

Lemma in_byte: forall sh p lo n c inp j,
  in_ok (InBuf sh p lo n c) inp -> 0 <= j < Zlength inp ->
  @Znth val Vundef (lo + j) c = Vint (Int.repr (Znth j inp)).
Proof.
  intros sh p lo n c inp j H Hj. unfold in_ok in H. destruct H as (_&_&Hlo&Hn&Hc&_&Hsub&_).
  rewrite <- Znth_byte_vals by lia. rewrite <- Hsub. rewrite Znth_sublist by lia. f_equal. lia.
Qed.

Lemma hold_add_eq: forall h b bt, 0 <= b -> 0 <= bt < 64 ->
  Int64.repr (u64 (h + b * 2 ^ bt)) = Int64.add (Int64.repr h) (Int64.shl (Int64.repr b) (Int64.repr bt)).
Proof.
  intros h b bt Hb Hbt. unfold u64.
  rewrite Int64.shl_mul_two_p. rewrite (Int64.unsigned_repr bt) by rep_lia.
  rewrite two_p_equiv. unfold Int64.mul.
  assert (P: 0 <= 2 ^ bt <= Int64.max_unsigned).
  { split. apply Z.pow_nonneg; lia.
    assert (2 ^ bt <= 2 ^ 63) by (apply Z.pow_le_mono_r; lia). rep_lia. }
  rewrite (Int64.unsigned_repr (2 ^ bt)) by exact P.
  rewrite Int64.add_unsigned.
  apply Int64.eqm_samerepr.
  apply Int64.eqm_trans with (h + b * 2 ^ bt)%Z.
  - change (2 ^ 64) with Int64.modulus. apply Int64.eqm_sym. apply Zbits.eqmod_mod. reflexivity.
  - apply Int64.eqm_add.
    + apply Int64.eqm_unsigned_repr.
    + apply Int64.eqm_trans with (Int64.unsigned (Int64.repr b) * 2 ^ bt)%Z.
      * apply Int64.eqm_mult. apply Int64.eqm_unsigned_repr. apply Int64.eqm_refl.
      * apply Int64.eqm_unsigned_repr.
Qed.

Lemma bytes_ok_Znth: forall l j, bytes_ok l -> 0 <= j < Zlength l -> 0 <= Znth j l <= 255.
Proof.
  intros l j H Hj. unfold bytes_ok in H. rewrite Forall_forall in H. apply H. apply Znth_In. auto.
Qed.

Lemma semax_needbits_FLAGS {Espec: OracleKind} (F: frame) (m: mst) (n: Z):
  mwf m -> m_leave m = 0 -> 0 <= n <= 32 ->
  semax Delta_inflate (loop_state F m) (needbits_stmt n _t'13 _t'432)
    (normal_ret_assert (loop_state F (needbits n m))).
Proof.
  intros W HL Hn.
  pose proof (mw_bits _ W) as WB. pose proof (mw_nx _ W) as WNX. pose proof (mw_inp _ W) as WINP.
  destruct F as [gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush].
  unfold needbits_stmt, pullbyte_body, loop_state. frame_simpl.
  abbreviate_semax.
  forward_loop (EX k: nat,
     PROP ((k <= 4)%nat; needbits_f (4 - k) n (pullk k m) = needbits n m;
           m_bits (pullk k m) = (m_bits m + 8 * Z.of_nat k)%Z;
           (0 < k)%nat -> (m_bits m + 8 * (Z.of_nat k - 1) < n)%Z;
           (m_nx m + Z.of_nat k <= Zlength (m_inp m))%Z;
           in_ok ib (m_inp m); out_ok ob (m_aout m))
     LOCAL (temp _strm strmp; temp _flush (zv flush); temp _state sp;
            temp _next (in_ptr ib (m_nx (pullk k m)));
            temp _put (out_ptr ob (Zlength (m_ow m)));
            temp _have (zv (m_have (pullk k m))); temp _left (zv (m_left m));
            temp _hold (lv (m_hold (pullk k m))); temp _bits (zv (m_bits (pullk k m)));
            temp _in (zv (m_in m)); temp _out (zv (m_out m));
            temp _ret (zv (m_ret m)); temp _leave (zv 0);
            lvar _here t_code vhere; lvar _last t_code vlast;
            lvar _hbuf (tarray tuchar 4) vhbuf; gvars gv)
     SEP (mem_rep (Fr gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush) m; locals_rep (Fr gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush)))
    break: (loop_state (Fr gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush) (needbits n m)).
  - Exists 0%nat. simpl pullk. entailer!.
  - Intros k.
    destruct (pullk_fields k m) as (P1&P2&P3&P4&P5&P6&P7&P8&P9&P10).
    assert (HB: 0 <= m_bits (pullk k m) <= 71) by lia.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx ((m_bits (pullk k m) < n)%Z :: P) (LOCALx Q (SEPx R))) end.
    + (* bits < n: go on *)
      forward. entailer!.
    + (* bits >= n: the loop ends *)
      forward.
      assert (E: needbits n m = pullk k m).
      { match goal with H: needbits_f _ _ _ = needbits n m |- _ => rewrite <- H end.
        apply needbits_f_ge. lia. }
      rewrite E. unfold loop_state. rewrite mem_rep_pullk.
      entailer!.
      unfold m_left. rewrite P3, P4, P5. repeat split; auto.
    + (* PULLBYTE *)
      Intros.
      assert (K4: (k < 4)%nat).
      { destruct (Nat.lt_ge_cases k 4); auto. lia. }
      assert (HH: 0 <= m_have (pullk k m) <= Int.max_signed) by (unfold m_have; rewrite P3, P10; lia).
      forward_if.
      * (* no input: leave *)
        forward. forward.
        assert (E: needbits n m = set_leave (pullk k m)).
        { match goal with H: needbits_f _ _ _ = needbits n m |- _ => rewrite <- H end.
          replace (4 - k)%nat with (S (3 - k)) by lia. rewrite needbits_f_S.
          destruct (m_bits (pullk k m) <? n) eqn:Ebn; [ | lia].
          destruct (m_have (pullk k m) =? 0) eqn:Eh; [ reflexivity | lia]. }
        rewrite E. unfold loop_state.
        replace (mem_rep (Fr gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush) (set_leave (pullk k m))) with (mem_rep (Fr gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush) m)
          by (rewrite <- (mem_rep_pullk (Fr gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush) k m); reflexivity).
        entailer!.
        unfold m_left. mnorm_goal. rewrite P3, P4, P5, P6, P7, P8. repeat split; auto.
      * (* pull a byte *)
        forward.
        destruct ib as [ | ish ip ilo inb ic]; cbn [in_ptr in_rep].
        { (* no input object: have = 0 *)
          exfalso.
          assert (m_have (pullk k m) = 0); [ | lia].
          unfold m_have. rewrite P3, P10.
          match goal with H: in_ok InNull (m_inp m) |- _ => unfold in_ok in H; rewrite H in * end.
          rewrite Zlength_nil in *. lia. }
        assert (Hj: 0 <= m_nx (pullk k m) < Zlength (m_inp m)).
        { match goal with H: m_have (pullk k m) <> 0 |- _ => revert H end. revert HH.
          unfold m_have. rewrite P3, P10. intros. lia. }
        match goal with H: in_ok (InBuf _ _ _ _ _) _ |- _ =>
          pose proof (in_byte _ _ _ _ _ _ (m_nx (pullk k m)) H Hj) as HBYTE;
          pose proof H as HINOK;
          destruct H as (Hish & Hip & Hilo & Hinb & Hic & Hinbm & Hsub & Hbytes) end.
        unfold mem_rep. cbn [in_ptr in_rep f_ib f_gv f_ob]. Intros.
        assert_PROP (field_compatible (tarray tuchar inb) [] ip) by entailer!.
        forward. forward.
        assert (HIX: 0 <= ilo + m_nx (pullk k m) < inb) by lia.
        rewrite (offset_val_field_address_tuchar inb (ilo + m_nx (pullk k m)) ip) by (auto; lia).
        pose proof (bytes_ok_Znth _ _ Hbytes Hj) as HBR.
        forward.
        { rewrite HBYTE. entailer!. rep_lia. }
        rewrite HBYTE.
        forward.
        { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
        forward.
        Exists (S k).
        rewrite !pullk_S.
        unfold mem_rep. frame_simpl_goal.
        entailer!.
        match goal with H: needbits_f (4 - k) n (pullk k m) = needbits n m |- _ => rename H into HNB end.
        match goal with H: m_bits (pullk k m) = (m_bits m + 8 * Z.of_nat k)%Z |- _ => rename H into HBK end.
        match goal with H: m_have (pullk k m) <> 0 |- _ => rename H into HHV end.
        match goal with H: m_bits (pullk k m) < n |- _ => rename H into HBN end.
        assert (HBX: 0 <= m_bits (pullk k m) + 8 < 2 ^ 32) by lia.
        split; [ | split; [ | split; [ | split; [ | split]]]].
        -- rewrite <- HNB. replace (4 - k)%nat with (S (4 - S k)) by lia. rewrite needbits_f_S.
          rewrite (proj2 (Z.ltb_lt _ _) HBN). rewrite (proj2 (Z.eqb_neq _ _) HHV). reflexivity.
        -- unfold pull. mnorm_goal. unfold u32. rewrite Z.mod_small by lia. rewrite HBK, Nat2Z.inj_succ. lia.
        -- rewrite <- (offset_val_field_address_tuchar (Zlength ic) (ilo + m_nx (pullk k m)) ip) by (auto; lia).
          unfold pull. mnorm_goal. rewrite offset_offset_val. f_equal. lia.
        -- unfold m_have, pull. mnorm_goal. f_equal. f_equal. lia.
        -- unfold pull. mnorm_goal. rewrite P3. f_equal. apply hold_add_eq; [ | lia].
          pose proof (bytes_ok_Znth _ _ Hbytes Hj). lia.
        -- unfold pull. mnorm_goal. unfold u32. rewrite Z.mod_small by lia. reflexivity.
  - (* after the loop *)
    unfold loop_state. entailer!.
Qed.
