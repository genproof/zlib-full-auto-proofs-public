(* Body proofs of harness/deflate_ref.h helpers: see DRefSpec.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.harness.inflate_common.DRefSpec.

#[local] Existing Instance Zlib.contracts.x_inflate_decode.Harness.CS.

(* ---------------------------------------------------------------------------------------------- *)
(* Pure facts (finite: checked by vm_compute)                                                     *)

Fixpoint zrange_all_n (n: nat) (x: Z) (f: Z -> bool) : bool :=
  match n with O => true | S n' => andb (f x) (zrange_all_n n' (x + 1) f) end.
Definition zrange_all (lo n: Z) (f: Z -> bool) : bool := zrange_all_n (Z.to_nat n) lo f.

Lemma zrange_all_n_ok n : forall lo f, zrange_all_n n lo f = true -> forall x, lo <= x < lo + Z.of_nat n -> f x = true.
Proof.
  induction n as [|n IH]; intros lo f H x Hx; simpl in *; [lia|].
  apply andb_prop in H; destruct H as [H1 H2].
  destruct (Z.eq_dec x lo); [subst; auto | apply (IH (lo + 1)); auto; lia].
Qed.

Lemma zrange_all_ok lo n f : zrange_all lo n f = true -> forall x, lo <= x < lo + n -> f x = true.
Proof.
  unfold zrange_all; intros H x Hx. apply (zrange_all_n_ok _ _ _ H). lia.
Qed.

(* the fixed literal/length code *)
Definition fix_len (v: Z) : Z := if v <? 144 then 8 else if v <? 256 then 9 else if v <? 280 then 7 else 8.
Definition fix_code (v: Z) : Z :=
  if v <? 144 then 48 + v else if v <? 256 then 400 + (v - 144) else if v <? 280 then v - 256 else 192 + (v - 280).

Lemma fixed_ll_b : zrange_all 0 288 (fun v => andb (Znth v fixed_ll =? fix_len v) (code fixed_ll v =? fix_code v)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma send_sym_fixed_ll v : 0 <= v < 288 -> send_sym fixed_ll v = bits_msb (fix_code v) (fix_len v).
Proof.
  intros Hv. pose proof (zrange_all_ok _ _ _ fixed_ll_b v ltac:(lia)) as H.
  apply andb_prop in H; destruct H as [H1 H2]; apply Z.eqb_eq in H1, H2.
  unfold send_sym; rewrite H1, H2; reflexivity.
Qed.

Lemma fixed_dl_b : zrange_all 0 30 (fun j => andb (Znth j fixed_dl =? 5) (code fixed_dl j =? j)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma send_sym_fixed_dl j : 0 <= j < 30 -> send_sym fixed_dl j = bits_msb j 5.
Proof.
  intros Hj. pose proof (zrange_all_ok _ _ _ fixed_dl_b j ltac:(lia)) as H.
  apply andb_prop in H; destruct H as [H1 H2]; apply Z.eqb_eq in H1, H2.
  unfold send_sym; rewrite H1, H2; reflexivity.
Qed.

Lemma Zlength_bits_le v n : 0 <= n -> Zlength (bits_le v n) = n.
Proof. intros; unfold bits_le; rewrite Zlength_map, Zlength_correct, seq_length; lia. Qed.

Lemma Zlength_bits_msb c n : 0 <= n -> Zlength (bits_msb c n) = n.
Proof. intros; unfold bits_msb; rewrite Zlength_rev; apply Zlength_bits_le; auto. Qed.

(* len_code: the loop's step (i + 1 <= len_code len exactly when base[i + 1] <= len) and the result *)
Lemma len_code_b :
  zrange_all 3 255 (fun len => andb (len_code len <=? 27)
    (zrange_all 0 27 (fun i => Bool.eqb (Znth (i + 1) len_base <=? len) (i + 1 <=? len_code len)))) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma len_code_lt len : 3 <= len < 258 -> 0 <= len_code len <= 27.
Proof.
  intros H. pose proof (zrange_all_ok _ _ _ len_code_b len ltac:(lia)) as H1.
  apply andb_prop in H1; destruct H1 as [H1 _]. apply Z.leb_le in H1.
  split; [unfold len_code; destruct (len =? 258); [lia | apply Zlength_nonneg] | auto].
Qed.

Lemma len_code_step len i : 3 <= len < 258 -> 0 <= i < 27 ->
  (Znth (i + 1) len_base <= len <-> i + 1 <= len_code len).
Proof.
  intros H Hi. pose proof (zrange_all_ok _ _ _ len_code_b len ltac:(lia)) as H1.
  apply andb_prop in H1; destruct H1 as [_ H1].
  pose proof (zrange_all_ok _ _ _ H1 i ltac:(lia)) as H2. apply Bool.eqb_prop in H2.
  rewrite <- Z.leb_le, H2, Z.leb_le. reflexivity.
Qed.

Lemma len_code_258 : len_code 258 = 28.
Proof. reflexivity. Qed.

Lemma len_code_facts_b :
  zrange_all 3 256 (fun len => andb (andb (len_code len <=? 28) (Znth (len_code len) len_base <=? len))
                               (Znth (len_code len) len_extra <=? 5)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma len_code_facts len : 3 <= len <= 258 ->
  0 <= len_code len <= 28 /\ Znth (len_code len) len_base <= len /\ 0 <= Znth (len_code len) len_extra <= 5.
Proof.
  intros H. pose proof (zrange_all_ok _ _ _ len_code_facts_b len ltac:(lia)) as H1.
  apply andb_prop in H1; destruct H1 as [H1 H3]; apply andb_prop in H1; destruct H1 as [H1 H2].
  apply Z.leb_le in H1, H2, H3.
  assert (0 <= len_code len) by (unfold len_code; destruct (len =? 258); [lia | apply Zlength_nonneg]).
  assert (0 <= Znth (len_code len) len_extra).
  { assert (Forall (fun x => 0 <= x) len_extra) by (repeat apply Forall_cons; try apply Forall_nil; lia).
    eapply Forall_forall; [eassumption | apply Znth_In; unfold len_extra; list_solve]. }
  lia.
Qed.

(* dist_code *)
Lemma dist_code_b :
  zrange_all 1 32768 (fun d => let c := dist_code d in
    andb (andb (andb (c <=? 29) (Znth c dist_base <=? d)) (Znth c dist_extra <=? 13))
    (zrange_all 0 29 (fun j => Bool.eqb (Znth (j + 1) dist_base <=? d) (j + 1 <=? c)))) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dist_code_facts d : 1 <= d <= 32768 ->
  0 <= dist_code d <= 29 /\ Znth (dist_code d) dist_base <= d /\ 0 <= Znth (dist_code d) dist_extra <= 13 /\
  (forall j, 0 <= j < 29 -> (Znth (j + 1) dist_base <= d <-> j + 1 <= dist_code d)).
Proof.
  intros H. pose proof (zrange_all_ok _ _ _ dist_code_b d ltac:(lia)) as H1. cbv zeta in H1.
  apply andb_prop in H1; destruct H1 as [H1 H4]; apply andb_prop in H1; destruct H1 as [H1 H3];
  apply andb_prop in H1; destruct H1 as [H1 H2]. apply Z.leb_le in H1, H2, H3.
  assert (0 <= dist_code d) by apply Zlength_nonneg.
  assert (0 <= Znth (dist_code d) dist_extra).
  { assert (Forall (fun x => 0 <= x) dist_extra) by (repeat apply Forall_cons; try apply Forall_nil; lia).
    eapply Forall_forall; [eassumption | apply Znth_In; unfold dist_extra; list_solve]. }
  split; [lia|]. split; [lia|]. split; [lia|].
  intros j Hj. pose proof (zrange_all_ok _ _ _ H4 j ltac:(lia)) as H6. apply Bool.eqb_prop in H6.
  rewrite <- Z.leb_le, H6, Z.leb_le. reflexivity.
Qed.

(* room for fewer bits *)
Lemma bw_room_less B cap k B' k' : bw_room B cap k -> 0 <= k' -> Zlength B' + k' <= Zlength B + k -> bw_room B' cap k'.
Proof.
  unfold bw_room; intros (H1 & H2 & H3) H4 H5. split; [lia|]. split; [|lia].
  eapply Z.le_trans; [|apply H2]. apply Z.div_le_mono; lia.
Qed.

Lemma Znth_zvals l k : 0 <= k < Zlength l -> Znth k (zvals l) = Vint (Int.repr (Znth k l)).
Proof. intros; unfold zvals; rewrite Znth_map by auto; reflexivity. Qed.

Lemma len_base_range k : 0 <= k < 29 -> 3 <= Znth k len_base <= 258.
Proof.
  intros. assert (Forall (fun x => 3 <= x <= 258) len_base) by (repeat apply Forall_cons; try apply Forall_nil; lia).
  rewrite Forall_forall in H0; apply H0, Znth_In; unfold len_base; list_solve.
Qed.

Lemma len_extra_range k : 0 <= k < 29 -> 0 <= Znth k len_extra <= 5.
Proof.
  intros. assert (Forall (fun x => 0 <= x <= 5) len_extra) by (repeat apply Forall_cons; try apply Forall_nil; lia).
  rewrite Forall_forall in H0; apply H0, Znth_In; unfold len_extra; list_solve.
Qed.

Lemma dist_base_range k : 0 <= k < 30 -> 1 <= Znth k dist_base <= 24577.
Proof.
  intros. assert (Forall (fun x => 1 <= x <= 24577) dist_base) by (repeat apply Forall_cons; try apply Forall_nil; lia).
  rewrite Forall_forall in H0; apply H0, Znth_In; unfold dist_base; list_solve.
Qed.

Lemma dist_extra_range k : 0 <= k < 30 -> 0 <= Znth k dist_extra <= 13.
Proof.
  intros. assert (Forall (fun x => 0 <= x <= 13) dist_extra) by (repeat apply Forall_cons; try apply Forall_nil; lia).
  rewrite Forall_forall in H0; apply H0, Znth_In; unfold dist_extra; list_solve.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The bodies                                                                                     *)

Lemma body_bw_fixed : semax_body Vprog_dref Gprog_bw_fixed HD.f_bw_fixed bw_fixed_spec.
Proof.
  start_function.
  assert (Hs := send_sym_fixed_ll v ltac:(lia)). unfold fix_code, fix_len in Hs.
  forward_if.
  { forward_call (sh, bsh, B, cap, buf, w, 48 + v, 8).
    all: try (apply (bw_room_less B cap 9); auto; lia).
    destruct (v <? 144) eqn:E; [|lia]; rewrite Hs; entailer!. }
  forward_if.
  { forward_call (sh, bsh, B, cap, buf, w, 400 + (v - 144), 9).
    all: try (apply (bw_room_less B cap 9); auto; lia).
    destruct (v <? 144) eqn:E; [lia|]. destruct (v <? 256) eqn:E2; [|lia]. rewrite Hs; entailer!. }
  forward_if.
  { forward_call (sh, bsh, B, cap, buf, w, v - 256, 7).
    all: try (apply (bw_room_less B cap 9); auto; lia).
    destruct (v <? 144) eqn:E; [lia|]. destruct (v <? 256) eqn:E2; [lia|].
    destruct (v <? 280) eqn:E3; [|lia]. rewrite Hs; entailer!. }
  forward_call (sh, bsh, B, cap, buf, w, 192 + (v - 280), 8).
  all: try (apply (bw_room_less B cap 9); auto; lia).
  destruct (v <? 144) eqn:E; [lia|]. destruct (v <? 256) eqn:E2; [lia|].
  destruct (v <? 280) eqn:E3; [lia|]. rewrite Hs; entailer!.
Qed.

Lemma body_len_code : semax_body (Vprog_tabs id_tabs) Gprog_len_code HD.f_len_code (len_code_spec id_tabs).
Proof.
  start_function.
  unfold dref_tabs, id_tabs. Intros.
  forward.
  forward_if (PROP () LOCAL (temp HD._i (Vint (Int.repr (len_code len))); temp HD._len (Vint (Int.repr len)); gvars gv)
              SEP (data_at tsh (tarray tushort 29) (zvals len_base) (gv HD._x_inflate_decode__ref_lbase);
                   data_at tsh (tarray tuchar 29) (zvals len_extra) (gv HD._x_inflate_decode__ref_lext);
                   data_at tsh (tarray tushort 30) (zvals dist_base) (gv HD._x_inflate_decode__ref_dbase);
                   data_at tsh (tarray tuchar 30) (zvals dist_extra) (gv HD._x_inflate_decode__ref_dext))).
  - forward.
    forward_loop
      (EX i: Z,
       PROP (0 <= i <= 27; i <= len_code len)
       LOCAL (temp HD._i (Vint (Int.repr i)); temp HD._len (Vint (Int.repr len)); gvars gv)
       SEP (data_at tsh (tarray tushort 29) (zvals len_base) (gv HD._x_inflate_decode__ref_lbase);
            data_at tsh (tarray tuchar 29) (zvals len_extra) (gv HD._x_inflate_decode__ref_lext);
            data_at tsh (tarray tushort 30) (zvals dist_base) (gv HD._x_inflate_decode__ref_dbase);
            data_at tsh (tarray tuchar 30) (zvals dist_extra) (gv HD._x_inflate_decode__ref_dext)))
      break: (PROP () LOCAL (temp HD._i (Vint (Int.repr (len_code len))); temp HD._len (Vint (Int.repr len));
                             gvars gv)
              SEP (data_at tsh (tarray tushort 29) (zvals len_base) (gv HD._x_inflate_decode__ref_lbase);
                   data_at tsh (tarray tuchar 29) (zvals len_extra) (gv HD._x_inflate_decode__ref_lext);
                   data_at tsh (tarray tushort 30) (zvals dist_base) (gv HD._x_inflate_decode__ref_dbase);
                   data_at tsh (tarray tuchar 30) (zvals dist_extra) (gv HD._x_inflate_decode__ref_dext))).
    { Exists 0. pose proof (len_code_lt len). entailer!. }
    Intros i.
    pose proof (len_code_lt len ltac:(lia)).
    forward_if (PROP ()
       LOCAL (temp HD._t'1 (Vint (if (i + 1 <? 28) && (Znth (i + 1) len_base <=? len) then Int.one else Int.zero)%bool);
              temp HD._i (Vint (Int.repr i)); temp HD._len (Vint (Int.repr len)); gvars gv)
       SEP (data_at tsh (tarray tushort 29) (zvals len_base) (gv HD._x_inflate_decode__ref_lbase);
            data_at tsh (tarray tuchar 29) (zvals len_extra) (gv HD._x_inflate_decode__ref_lext);
            data_at tsh (tarray tushort 30) (zvals dist_base) (gv HD._x_inflate_decode__ref_dbase);
            data_at tsh (tarray tuchar 30) (zvals dist_extra) (gv HD._x_inflate_decode__ref_dext))).
    + assert (Hb := Znth_zvals len_base (i + 1) ltac:(unfold len_base; list_solve)).
      pose proof (len_base_range (i + 1) ltac:(lia)).
      assert (Ht: tc_val tushort (Znth (i + 1) (zvals len_base)))
        by (rewrite Hb; simpl; rewrite Int.unsigned_repr by rep_lia; rep_lia).
      forward.
      forward.
      match goal with |- context [temp HD._t'2 ?x] =>
        replace x with (Vint (Int.repr (Znth (i + 1) len_base))) by (rewrite <- Hb; reflexivity) end.
      entailer!.
      replace (i + 1 <? 28) with true by lia. simpl. unfold Int.ltu. rewrite !Int.unsigned_repr by rep_lia.
      destruct (zlt len (Znth (i + 1) len_base)), (Znth (i + 1) len_base <=? len) eqn:E; simpl; auto; lia.
    + forward. entailer!. replace (i + 1 <? 28) with false by lia. reflexivity.
    + forward_if.
      * destruct ((i + 1 <? 28) && (Znth (i + 1) len_base <=? len))%bool eqn:E; [|exfalso; apply H4; reflexivity].
        apply andb_prop in E; destruct E as [E1 E2]. apply Z.ltb_lt in E1; apply Z.leb_le in E2.
        apply (len_code_step len i) in E2; [|lia|lia].
        forward. Exists (i + 1). entailer!.
      * destruct ((i + 1 <? 28) && (Znth (i + 1) len_base <=? len))%bool eqn:E;
          [apply Int.one_not_zero in H4; contradiction|].
        forward. entailer!. f_equal. f_equal.
        destruct (i + 1 <? 28) eqn:E1.
        -- destruct (Znth (i + 1) len_base <=? len) eqn:E2; [discriminate|].
           apply Z.ltb_lt in E1; apply Z.leb_gt in E2.
           assert (~ (i + 1 <= len_code len)) by (rewrite <- len_code_step; lia). lia.
        -- apply Z.ltb_ge in E1. lia.
  - forward. entailer!. replace len with 258 by lia. reflexivity.
  - forward. unfold dref_tabs, id_tabs. entailer!.
Qed.

Lemma body_dist_code : semax_body (Vprog_tabs id_tabs) Gprog_dist_code HD.f_dist_code (dist_code_spec id_tabs).
Proof.
  start_function.
  unfold dref_tabs, id_tabs. Intros.
  pose proof (dist_code_facts dist ltac:(lia)) as (Hc & _ & _ & Hstep).
  forward.
  forward_loop
    (EX j: Z,
     PROP (0 <= j <= 29; j <= dist_code dist)
     LOCAL (temp HD._j (Vint (Int.repr j)); temp HD._dist (Vint (Int.repr dist)); gvars gv)
     SEP (data_at tsh (tarray tushort 29) (zvals len_base) (gv HD._x_inflate_decode__ref_lbase);
          data_at tsh (tarray tuchar 29) (zvals len_extra) (gv HD._x_inflate_decode__ref_lext);
          data_at tsh (tarray tushort 30) (zvals dist_base) (gv HD._x_inflate_decode__ref_dbase);
          data_at tsh (tarray tuchar 30) (zvals dist_extra) (gv HD._x_inflate_decode__ref_dext)))
    break: (PROP () LOCAL (temp HD._j (Vint (Int.repr (dist_code dist))); temp HD._dist (Vint (Int.repr dist));
                           gvars gv)
            SEP (data_at tsh (tarray tushort 29) (zvals len_base) (gv HD._x_inflate_decode__ref_lbase);
                 data_at tsh (tarray tuchar 29) (zvals len_extra) (gv HD._x_inflate_decode__ref_lext);
                 data_at tsh (tarray tushort 30) (zvals dist_base) (gv HD._x_inflate_decode__ref_dbase);
                 data_at tsh (tarray tuchar 30) (zvals dist_extra) (gv HD._x_inflate_decode__ref_dext))).
  { Exists 0. entailer!. }
  Intros j.
  forward_if (PROP ()
     LOCAL (temp HD._t'1 (Vint (if (j + 1 <? 30) && (Znth (j + 1) dist_base <=? dist) then Int.one else Int.zero)%bool);
            temp HD._j (Vint (Int.repr j)); temp HD._dist (Vint (Int.repr dist)); gvars gv)
     SEP (data_at tsh (tarray tushort 29) (zvals len_base) (gv HD._x_inflate_decode__ref_lbase);
          data_at tsh (tarray tuchar 29) (zvals len_extra) (gv HD._x_inflate_decode__ref_lext);
          data_at tsh (tarray tushort 30) (zvals dist_base) (gv HD._x_inflate_decode__ref_dbase);
          data_at tsh (tarray tuchar 30) (zvals dist_extra) (gv HD._x_inflate_decode__ref_dext))).
  + assert (Hb := Znth_zvals dist_base (j + 1) ltac:(unfold dist_base; list_solve)).
    pose proof (dist_base_range (j + 1) ltac:(lia)).
    assert (Ht: tc_val tushort (Znth (j + 1) (zvals dist_base)))
      by (rewrite Hb; simpl; rewrite Int.unsigned_repr by rep_lia; rep_lia).
    forward.
    forward.
    match goal with |- context [temp HD._t'2 ?x] =>
      replace x with (Vint (Int.repr (Znth (j + 1) dist_base))) by (rewrite <- Hb; reflexivity) end.
    entailer!.
    replace (j + 1 <? 30) with true by lia. simpl. unfold Int.ltu. rewrite !Int.unsigned_repr by rep_lia.
    destruct (zlt dist (Znth (j + 1) dist_base)), (Znth (j + 1) dist_base <=? dist) eqn:E; simpl; auto; lia.
  + forward. entailer!. replace (j + 1 <? 30) with false by lia. reflexivity.
  + forward_if.
    * destruct ((j + 1 <? 30) && (Znth (j + 1) dist_base <=? dist))%bool eqn:E; [|exfalso; apply H2; reflexivity].
      apply andb_prop in E; destruct E as [E1 E2]. apply Z.ltb_lt in E1; apply Z.leb_le in E2.
      apply Hstep in E2; [|lia].
      forward. Exists (j + 1). entailer!.
    * destruct ((j + 1 <? 30) && (Znth (j + 1) dist_base <=? dist))%bool eqn:E;
        [apply Int.one_not_zero in H2; contradiction|].
      forward. entailer!. f_equal. f_equal.
      destruct (j + 1 <? 30) eqn:E1.
      -- destruct (Znth (j + 1) dist_base <=? dist) eqn:E2; [discriminate|].
         apply Z.ltb_lt in E1; apply Z.leb_gt in E2.
         assert (~ (j + 1 <= dist_code dist)) by (rewrite <- Hstep; lia). lia.
      -- apply Z.ltb_ge in E1. lia.
  + forward. unfold dref_tabs, id_tabs. entailer!.
Qed.

Lemma Zlength_send_fixed_ll v : 256 <= v < 288 -> 7 <= Zlength (send_sym fixed_ll v) <= 8.
Proof.
  intros; rewrite send_sym_fixed_ll by lia. unfold fix_len.
  destruct (Z.ltb_spec v 144), (Z.ltb_spec v 256), (Z.ltb_spec v 280); try lia;
  rewrite Zlength_bits_msb; lia.
Qed.

Lemma body_bw_fixed_match :
  semax_body (Vprog_tabs id_tabs) (Gprog_bw_fixed_match id_tabs) HD.f_bw_fixed_match (bw_fixed_match_spec id_tabs).
Proof.
  start_function.
  pose proof (len_code_facts len ltac:(lia)) as (Hi & Hib & Hie).
  pose proof (dist_code_facts dist ltac:(lia)) as (Hj & Hjb & Hje & _).
  forward_call (gv, tsh, len).
  forward_call (gv, tsh, dist).
  set (i := len_code len) in *. set (j := dist_code dist) in *.
  pose proof (Zlength_send_fixed_ll (257 + i) ltac:(lia)) as Hl1.
  forward_call (sh, bsh, B, cap, buf, w, 257 + i).
  { split; [lia|]. apply (bw_room_less B cap 31); auto; lia. }
  set (B1 := B ++ send_sym fixed_ll (257 + i)).
  assert (HB1: Zlength B1 <= Zlength B + 8) by (unfold B1; rewrite Zlength_app; lia).
  unfold dref_tabs, id_tabs. Intros.
  assert (Hb := Znth_zvals len_base i ltac:(unfold len_base; list_solve)).
  assert (He := Znth_zvals len_extra i ltac:(unfold len_extra; list_solve)).
  pose proof (len_base_range i ltac:(lia)).
  assert (Ht: tc_val tushort (Znth i (zvals len_base)))
    by (rewrite Hb; simpl; rewrite Int.unsigned_repr by rep_lia; rep_lia).
  assert (Ht': tc_val tuchar (Znth i (zvals len_extra)))
    by (rewrite He; simpl; rewrite Int.unsigned_repr by rep_lia; rep_lia).
  forward. forward.
  match goal with |- context [temp HD._t'5 ?x] =>
    replace x with (Vint (Int.repr (Znth i len_base))) by (rewrite <- Hb; reflexivity) end.
  match goal with |- context [temp HD._t'6 ?x] =>
    replace x with (Vint (Int.repr (Znth i len_extra))) by (rewrite <- He; reflexivity) end.
  forward_call (sh, bsh, B1, cap, buf, w, len - Znth i len_base, Znth i len_extra).
  { apply (bw_room_less B cap 31); auto; lia. }
  set (B2 := B1 ++ bits_le (len - Znth i len_base) (Znth i len_extra)).
  assert (HB2: Zlength B2 <= Zlength B + 13) by (unfold B2; rewrite Zlength_app, Zlength_bits_le; lia).
  forward_call (sh, bsh, B2, cap, buf, w, j, 5).
  all: try (apply (bw_room_less B cap 31); auto; lia).
  set (B3 := B2 ++ bits_msb j 5).
  assert (HB3: Zlength B3 <= Zlength B + 18) by (unfold B3; rewrite Zlength_app, Zlength_bits_msb; lia).
  assert (Hdb := Znth_zvals dist_base j ltac:(unfold dist_base; list_solve)).
  assert (Hde := Znth_zvals dist_extra j ltac:(unfold dist_extra; list_solve)).
  pose proof (dist_base_range j ltac:(lia)).
  assert (Hdt: tc_val tushort (Znth j (zvals dist_base)))
    by (rewrite Hdb; simpl; rewrite Int.unsigned_repr by rep_lia; rep_lia).
  assert (Hdt': tc_val tuchar (Znth j (zvals dist_extra)))
    by (rewrite Hde; simpl; rewrite Int.unsigned_repr by rep_lia; rep_lia).
  forward. forward.
  match goal with |- context [temp HD._t'3 ?x] =>
    replace x with (Vint (Int.repr (Znth j dist_base))) by (rewrite <- Hdb; reflexivity) end.
  match goal with |- context [temp HD._t'4 ?x] =>
    replace x with (Vint (Int.repr (Znth j dist_extra))) by (rewrite <- Hde; reflexivity) end.
  forward_call (sh, bsh, B3, cap, buf, w, dist - Znth j dist_base, Znth j dist_extra).
  { apply (bw_room_less B cap 31); auto; lia. }
  unfold dref_tabs, id_tabs. entailer!.
  unfold B3, B2, B1. simpl send_one. fold i j. rewrite send_sym_fixed_dl by lia. rewrite <- !app_assoc. cancel.
Qed.

Lemma dref_code_bodies_proof : dref_code_bodies.
Proof.
  split; [exact body_bw_fixed|]. split; [exact body_len_code|]. split; [exact body_dist_code|].
  exact body_bw_fixed_match.
Qed.
