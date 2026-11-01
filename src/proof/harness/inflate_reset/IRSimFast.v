(* Law inflate_reset, theory part: inflate_fast (Model.fast) from related machines.

   Idea: the two machines differ only in their states (srel) and gz_headers; write them as one machine m
   with the state and header replaced (irf_chg m sa ha, irf_chg m sb hb).  inflate_fast reads of the state
   only fields equal in LEN and the tables' reachable entries (treach_eq), and writes of it only mode, hold
   and bits: each iteration (and so the loop and the tail) maps the pair to a pair of the same form. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_reset.IRDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The machine m with state s and header h                                                       *)

Definition irf_chg (m: mst) (s: istate) (h: hstate) : mst := set_m_h (set_m_s m s) h.

Lemma irf_s m s h : m_s (irf_chg m s h) = s. Proof. reflexivity. Qed.
Lemma irf_inp m s h : m_inp (irf_chg m s h) = m_inp m. Proof. reflexivity. Qed.
Lemma irf_aout m s h : m_aout (irf_chg m s h) = m_aout m. Proof. reflexivity. Qed.
Lemma irf_nx m s h : m_nx (irf_chg m s h) = m_nx m. Proof. reflexivity. Qed.
Lemma irf_ow m s h : m_ow (irf_chg m s h) = m_ow m. Proof. reflexivity. Qed.
Lemma irf_hold m s h : m_hold (irf_chg m s h) = m_hold m. Proof. reflexivity. Qed.
Lemma irf_bits m s h : m_bits (irf_chg m s h) = m_bits m. Proof. reflexivity. Qed.

Lemma irf_pull m s h : pull (irf_chg m s h) = irf_chg (pull m) s h. Proof. reflexivity. Qed.
Lemma irf_fpull m s h : fpull (irf_chg m s h) = irf_chg (pull m) s h. Proof. reflexivity. Qed.
Lemma irf_set_bits m s h v : set_m_bits (irf_chg m s h) v = irf_chg (set_m_bits m v) s h.
Proof. reflexivity. Qed.
Lemma irf_set_hold m s h v : set_m_hold (irf_chg m s h) v = irf_chg (set_m_hold m v) s h.
Proof. reflexivity. Qed.
Lemma irf_set_nx m s h v : set_m_nx (irf_chg m s h) v = irf_chg (set_m_nx m v) s h.
Proof. reflexivity. Qed.
Lemma irf_set_ow m s h v : set_m_ow (irf_chg m s h) v = irf_chg (set_m_ow m v) s h.
Proof. reflexivity. Qed.
Lemma irf_set_bad m s h e : set_bad (irf_chg m s h) e = irf_chg (set_m_msg m (Some e)) (set_i_mode s BAD) h.
Proof. reflexivity. Qed.
Lemma irf_set_mode m s h v : set_mode (irf_chg m s h) v = irf_chg m (set_i_mode s v) h.
Proof. reflexivity. Qed.
Lemma irf_restore m s h :
  restore (irf_chg m s h) = irf_chg (restore m) (set_i_bits (set_i_hold s (m_hold m)) (m_bits m)) h.
Proof. reflexivity. Qed.

#[local] Hint Rewrite irf_s irf_inp irf_aout irf_nx irf_ow irf_hold irf_bits irf_pull irf_fpull irf_set_bits
  irf_set_hold irf_set_nx irf_set_ow irf_set_bad irf_set_mode irf_restore : irf.

Lemma irf_eta m : m = irf_chg m (m_s m) (m_h m).
Proof. destruct m; reflexivity. Qed.

Lemma irf_mode_eta s : set_i_mode s (i_mode s) = s.
Proof. destruct s; reflexivity. Qed.

(* the walk's link tests agree with Tables.islink on valid entries *)
Lemma irf_len_link1 op : islink LENS op = true -> len_link op = true.
Proof.
  unfold islink, len_link. change (LENS =? DISTS) with false. cbv iota.
  rewrite andb_true_iff, negb_true_iff, !Z.eqb_eq, Z.eqb_neq. intros [A B].
  assert (C: forall k, Z.land 240 k = k -> Z.land op k = 0).
  { intros k Hk. rewrite <- Hk, Z.land_assoc, B. apply Z.land_0_l. }
  rewrite (C 16 eq_refl), (C 64) by reflexivity.
  destruct (op =? 0) eqn:E; [apply Z.eqb_eq in E; lia|reflexivity].
Qed.

Lemma irf_dist_link1 op : islink DISTS op = true -> dist_link op = true.
Proof.
  unfold islink, dist_link. change (DISTS =? DISTS) with true. cbv iota.
  rewrite andb_true_l, Z.eqb_eq. intros B.
  assert (C: forall k, Z.land 240 k = k -> Z.land op k = 0).
  { intros k Hk. rewrite <- Hk, Z.land_assoc, B. apply Z.land_0_l. }
  rewrite (C 16 eq_refl), (C 64) by reflexivity. reflexivity.
Qed.

Lemma irf_len_link2 e : final_ok LENS e -> len_link (e_op e) = false.
Proof.
  unfold final_ok, len_link. change (LENS =? CODES) with false. change (LENS =? LENS) with true. cbv iota.
  intros [[-> _]|[[A _]|[A|[A _]]]].
  - reflexivity.
  - assert (e_op e = 16 \/ e_op e = 17 \/ e_op e = 18 \/ e_op e = 19 \/ e_op e = 20 \/ e_op e = 21) by lia.
    destruct H as [->|[->|[->|[->|[->| ->]]]]]; reflexivity.
  - rewrite A; reflexivity.
  - apply Z.eqb_neq in A. rewrite A. rewrite !orb_true_r. reflexivity.
Qed.

Lemma irf_dist_link2 e : final_ok DISTS e -> dist_link (e_op e) = false.
Proof.
  unfold final_ok, dist_link. change (DISTS =? CODES) with false. change (DISTS =? LENS) with false. cbv iota.
  intros [[A _]|[A _]].
  - assert (H: 16 <= e_op e < 32) by lia.
    assert (Z.land (e_op e) 16 <> 0).
    { intros X. destruct (Z.eq_dec (e_op e) 16) as [E|N]; [rewrite E in X; discriminate|].
      revert X. assert (e_op e = 17 \/ e_op e = 18 \/ e_op e = 19 \/ e_op e = 20 \/ e_op e = 21 \/
        e_op e = 22 \/ e_op e = 23 \/ e_op e = 24 \/ e_op e = 25 \/ e_op e = 26 \/ e_op e = 27 \/
        e_op e = 28 \/ e_op e = 29) by lia.
      repeat (destruct H0 as [->|H0]; [discriminate|]). rewrite H0; discriminate. }
    apply Z.eqb_neq in H0. rewrite H0. reflexivity.
  - apply Z.eqb_neq in A. rewrite A, orb_true_r. reflexivity.
Qed.

Definition irf_s_fill2 (m: mst) : mst := if m_bits m <? 15 then fpull (fpull m) else m.

Definition irf_s_lext (here: entry) (m: mst) : Z * mst :=
    let len := e_val here in
    let opx := Z.land (e_op here) 15 in
      if negb (opx =? 0) then
        let m := if m_bits m <? opx then fpull m else m in
        (u32 (len + m_hold m mod 2 ^ opx), set_m_bits (set_m_hold m (Z.shiftr (m_hold m) opx)) (u32 (m_bits m - opx)))
      else (len, m).

Definition irf_s_dext (opx: Z) (m: mst) : mst :=
  if m_bits m <? opx then (let m := fpull m in if m_bits m <? opx then fpull m else m) else m.

Definition irf_s_copy (s: istate) (m: mst) (dist len: Z) : bool * mst :=
      let op := Zlength (m_ow m) in        (* out - beg *)
      if op <? dist then
        let op := dist - op in
        if andb (i_whave s <? op) (negb (i_sane s =? 0)) then (false, set_bad m F_far) else
        let w := i_wdata s in
        let wsz := i_wsize s in let wnx := i_wnext s in
        let '(ow, sr, len) :=
          if wnx =? 0 then
            if op <? len then
              let '(ow, _) := copy_bytes w (SWin (wsz - op)) op (m_ow m) in
              (ow, SOut (Zlength ow - dist), len - op)
            else (m_ow m, SWin (wsz - op), len)
          else if wnx <? op then
            let op2 := op - wnx in
            if op2 <? len then
              let '(ow, _) := copy_bytes w (SWin (wsz + wnx - op)) op2 (m_ow m) in
              let len := len - op2 in
              if wnx <? len then
                let '(ow, _) := copy_bytes w (SWin 0) wnx ow in
                (ow, SOut (Zlength ow - dist), len - wnx)
              else (ow, SWin 0, len)
            else (m_ow m, SWin (wsz + wnx - op), len)
          else
            if op <? len then
              let '(ow, _) := copy_bytes w (SWin (wnx - op)) op (m_ow m) in
              (ow, SOut (Zlength ow - dist), len - op)
            else (m_ow m, SWin (wnx - op), len) in
        let '(ow, _) := copy_bytes w sr len ow in
        (true, set_m_ow m ow)
      else
        let '(ow, _) := copy_bytes (i_wdata s) (SOut (Zlength (m_ow m) - dist)) len (m_ow m) in
        (true, set_m_ow m ow).

Definition irf_fast_iter2 (m: mst) : bool * mst :=
  let s := m_s m in
  let m := irf_s_fill2 m in
  let '(here, m) := fwalk_f lenfix_list distfix_list 2 len_link (i_lencode s)
                      (tab_entry lenfix_list distfix_list s (i_lencode s) (m_hold m mod 2 ^ i_lenbits s)) m in
  let op := e_op here in
  if op =? 0 then (true, set_m_ow m (m_ow m ++ [e_val here mod 256]))
  else if negb (Z.land op 16 =? 0) then
    let '(len, m) := irf_s_lext here m in
    let m := irf_s_fill2 m in
    let '(here, m) := fwalk_f lenfix_list distfix_list 2 dist_link (i_distcode s)
                        (tab_entry lenfix_list distfix_list s (i_distcode s) (m_hold m mod 2 ^ i_distbits s)) m in
    let op := e_op here in
    if negb (Z.land op 16 =? 0) then
      let opx := Z.land op 15 in
      let m := irf_s_dext opx m in
      let dist := u32 (e_val here + m_hold m mod 2 ^ opx) in
      let m := dropbits opx m in
      irf_s_copy s m dist len
    else (false, set_bad m F_d_code)
  else if negb (Z.land op 32 =? 0) then (false, set_mode m Zlib.proof.inflate.Model.TYPE)
  else (false, set_bad m F_ll_code).

Lemma irf_fast_iter_eq m : fast_iter lenfix_list distfix_list m = irf_fast_iter2 m.
Proof. reflexivity. Qed.

Lemma irf_fill2 m s h : irf_s_fill2 (irf_chg m s h) = irf_chg (irf_s_fill2 m) s h.
Proof. unfold irf_s_fill2. rewrite irf_bits. destruct (m_bits m <? 15); reflexivity. Qed.
Lemma irf_lext e m s h :
  irf_s_lext e (irf_chg m s h) = (fst (irf_s_lext e m), irf_chg (snd (irf_s_lext e m)) s h).
Proof.
  unfold irf_s_lext. destruct (negb (Z.land (e_op e) 15 =? 0)); [|reflexivity].
  rewrite irf_bits. destruct (m_bits m <? Z.land (e_op e) 15); reflexivity.
Qed.
Lemma irf_dext k m s h : irf_s_dext k (irf_chg m s h) = irf_chg (irf_s_dext k m) s h.
Proof.
  unfold irf_s_dext, fpull. rewrite irf_bits. destruct (m_bits m <? k); [|reflexivity].
  rewrite irf_pull, irf_bits. destruct (m_bits (pull m) <? k); reflexivity.
Qed.
Lemma irf_drop k m s h : dropbits k (irf_chg m s h) = irf_chg (dropbits k m) s h.
Proof. reflexivity. Qed.

#[local] Hint Rewrite irf_fill2 irf_lext irf_dext irf_drop : irf.

Section Sim.
Variables (sa sb: istate) (ha hb: hstate).

(* the table walk: from the same root index, the same entry and the same machine *)
Lemma irf_fwalk kind il t rb sz X i :
  tvalid_g kind (tab_entry lenfix_list distfix_list sb t) rb sz ->
  treach_eq kind sa sb t rb ->
  (forall op, islink kind op = true -> il op = true) ->
  (forall e, final_ok kind e -> il (e_op e) = false) ->
  0 <= i < 2 ^ rb ->
  exists e Y,
    fwalk_f lenfix_list distfix_list 2 il t (tab_entry lenfix_list distfix_list sa t i) (irf_chg X sa ha) =
      (e, irf_chg Y sa ha) /\
    fwalk_f lenfix_list distfix_list 2 il t (tab_entry lenfix_list distfix_list sb t i) (irf_chg X sb hb) =
      (e, irf_chg Y sb hb).
Proof.
  intros [Rb Sz Root] Rch IL1 IL2 Hi.
  destruct (Rch i Hi) as [E0 E1]. cbv zeta in E0, E1. rewrite E0 in E1 |- *.
  specialize (Root i Hi). cbv zeta in Root. destruct Root as [Ok0 Root].
  cbn [fwalk_f]. autorewrite with irf.
  destruct (il (e_op (tab_entry lenfix_list distfix_list sb t i))) eqn:Hil.
  - destruct (islink kind (e_op (tab_entry lenfix_list distfix_list sb t i))) eqn:Hk.
    2:{ destruct Root as [_ F]. apply IL2 in F. congruence. }
    destruct Root as (_ & Hop & _ & Sub).
    match goal with |- context [m_hold ?Y1 mod 2 ^ ?o] =>
      assert (Hj: 0 <= m_hold Y1 mod 2 ^ o < 2 ^ o) by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia);
      rewrite (E1 eq_refl _ Hj);
      destruct (Sub _ Hj) as (_ & _ & _ & _ & F)
    end.
    cbv zeta in F. apply IL2 in F.
    cbn [fwalk_f]. autorewrite with irf. rewrite F.
    eexists _, _; split; reflexivity.
  - eexists _, _; split; reflexivity.
Qed.

Hypotheses
  (Hlc: i_lencode sa = i_lencode sb) (Hdc: i_distcode sa = i_distcode sb)
  (Hlb: i_lenbits sa = i_lenbits sb) (Hdb: i_distbits sa = i_distbits sb)
  (Hwh: i_whave sa = i_whave sb) (Hsn: i_sane sa = i_sane sb) (Hwd: i_wdata sa = i_wdata sb)
  (Hws: i_wsize sa = i_wsize sb) (Hwn: i_wnext sa = i_wnext sb)
  (Hma: i_mode sa = LEN) (Hmb: i_mode sb = LEN).
Variables (szl szd: Z).
Hypotheses
  (TL: tvalid_g LENS (tab_entry lenfix_list distfix_list sb (i_lencode sb)) (i_lenbits sb) szl)
  (TD: tvalid_g DISTS (tab_entry lenfix_list distfix_list sb (i_distcode sb)) (i_distbits sb) szd)
  (RL: treach_eq LENS sa sb (i_lencode sb) (i_lenbits sb))
  (RD: treach_eq DISTS sa sb (i_distcode sb) (i_distbits sb)).

Lemma irf_etaa : set_i_mode sa LEN = sa.
Proof. rewrite <- Hma. apply irf_mode_eta. Qed.
Lemma irf_etab : set_i_mode sb LEN = sb.
Proof. rewrite <- Hmb. apply irf_mode_eta. Qed.

Lemma irf_wlen X h : exists e Y,
    fwalk_f lenfix_list distfix_list 2 len_link (i_lencode sb)
      (tab_entry lenfix_list distfix_list sa (i_lencode sb) (h mod 2 ^ i_lenbits sb)) (irf_chg X sa ha) =
      (e, irf_chg Y sa ha) /\
    fwalk_f lenfix_list distfix_list 2 len_link (i_lencode sb)
      (tab_entry lenfix_list distfix_list sb (i_lencode sb) (h mod 2 ^ i_lenbits sb)) (irf_chg X sb hb) =
      (e, irf_chg Y sb hb).
Proof.
  eapply irf_fwalk; eauto using irf_len_link1, irf_len_link2.
  apply Z.mod_pos_bound, Z.pow_pos_nonneg; [lia|]. destruct TL; lia.
Qed.

Lemma irf_wdist X h : exists e Y,
    fwalk_f lenfix_list distfix_list 2 dist_link (i_distcode sb)
      (tab_entry lenfix_list distfix_list sa (i_distcode sb) (h mod 2 ^ i_distbits sb)) (irf_chg X sa ha) =
      (e, irf_chg Y sa ha) /\
    fwalk_f lenfix_list distfix_list 2 dist_link (i_distcode sb)
      (tab_entry lenfix_list distfix_list sb (i_distcode sb) (h mod 2 ^ i_distbits sb)) (irf_chg X sb hb) =
      (e, irf_chg Y sb hb).
Proof.
  eapply irf_fwalk; eauto using irf_dist_link1, irf_dist_link2.
  apply Z.mod_pos_bound, Z.pow_pos_nonneg; [lia|]. destruct TD; lia.
Qed.

Ltac irf_hdest x :=
  lazymatch x with
  | fwalk_f _ _ _ _ _ _ _ => fail
  | match ?c with _ => _ end => irf_hdest c
  | context [match ?c with _ => _ end] => irf_hdest c
  | _ => tryif is_var x then destruct x else (let E := fresh "E" in destruct x eqn:E)
  end.

Ltac irf_zeta1 :=
  match goal with |- context C [let x := ?v in @?b x] =>
    lazymatch v with
    | context [match _ with _ => _ end] => fail
    | _ => let t := context C [b v] in change t; cbv beta
    end
  end.

Ltac irf_step :=
  autorewrite with irf; rewrite ?Hlc, ?Hdc, ?Hlb, ?Hdb, ?Hwh, ?Hsn, ?Hwd, ?Hws, ?Hwn; cbv beta iota;
  first
  [ irf_zeta1
  | match goal with
    | |- context [fwalk_f _ _ 2 len_link _ (tab_entry _ _ sa _ (?h mod _)) (irf_chg ?X sa ha)] =>
        let e := fresh "e" in let Y := fresh "Y" in let E1 := fresh "W" in let E2 := fresh "W" in
        destruct (irf_wlen X h) as (e & Y & E1 & E2); rewrite E1, E2
    | |- context [fwalk_f _ _ 2 dist_link _ (tab_entry _ _ sa _ (?h mod _)) (irf_chg ?X sa ha)] =>
        let e := fresh "e" in let Y := fresh "Y" in let E1 := fresh "W" in let E2 := fresh "W" in
        destruct (irf_wdist X h) as (e & Y & E1 & E2); rewrite E1, E2
    end
  | match goal with |- context [match ?x with _ => _ end] => irf_hdest x end ].

Definition irf_md (md: Z) : Prop := md = LEN \/ md = Zlib.proof.inflate.Model.TYPE \/ md = BAD.

Ltac irf_close :=
  autorewrite with irf;
  match goal with
  | |- exists g m' md, (?g0, irf_chg ?Y sa ha) = _ /\ _ =>
      exists g0, Y, LEN; rewrite irf_etaa, irf_etab;
      split; [reflexivity|split; [reflexivity|split; [intros; reflexivity|left; reflexivity]]]
  | |- exists g m' md, (?g0, irf_chg ?Y (set_i_mode sa ?md0) ha) = _ /\ _ =>
      exists g0, Y, md0;
      split; [reflexivity|split; [reflexivity|split; [intros; discriminate|unfold irf_md; auto]]]
  end.

Lemma irf_copy m d l : exists g m' md,
  irf_s_copy sa (irf_chg m sa ha) d l = (g, irf_chg m' (set_i_mode sa md) ha) /\
  irf_s_copy sb (irf_chg m sb hb) d l = (g, irf_chg m' (set_i_mode sb md) hb) /\
  (g = true -> md = LEN) /\ irf_md md.
Proof. unfold irf_s_copy. repeat irf_step. all: irf_close. Qed.

Lemma irf_iter m : exists g m' md,
  fast_iter lenfix_list distfix_list (irf_chg m sa ha) = (g, irf_chg m' (set_i_mode sa md) ha) /\
  fast_iter lenfix_list distfix_list (irf_chg m sb hb) = (g, irf_chg m' (set_i_mode sb md) hb) /\
  (g = true -> md = LEN) /\ irf_md md.
Proof.
  rewrite (irf_fast_iter_eq (irf_chg m sa ha)), (irf_fast_iter_eq (irf_chg m sb hb)).
  unfold irf_fast_iter2. repeat irf_step.
  all: first [irf_close | apply irf_copy].
Qed.

Lemma irf_loop k m : exists m' md,
  fast_loop lenfix_list distfix_list k (irf_chg m sa ha) = irf_chg m' (set_i_mode sa md) ha /\
  fast_loop lenfix_list distfix_list k (irf_chg m sb hb) = irf_chg m' (set_i_mode sb md) hb /\ irf_md md.
Proof.
  revert m; induction k; intros m; cbn [fast_loop].
  - exists m, LEN. rewrite irf_etaa, irf_etab. split; [reflexivity|split; [reflexivity|left; reflexivity]].
  - destruct (irf_iter m) as (g & m1 & md & E1 & E2 & G & Md). rewrite E1, E2. cbv beta iota.
    autorewrite with irf.
    destruct ((g && (m_nx m1 <? Zlength (m_inp m1) - 5) && (Zlength (m_ow m1) <? m_aout m1 - 257))%bool) eqn:C.
    + assert (Hg: g = true) by (destruct g; [reflexivity|discriminate]).
      rewrite (G Hg), irf_etaa, irf_etab. apply IHk.
    + exists m1, md. auto.
Qed.

Lemma irf_fastl m : exists m' md,
  fast lenfix_list distfix_list (irf_chg m sa ha) =
    irf_chg m' (set_i_bits (set_i_hold (set_i_mode sa md) (m_hold m')) (m_bits m')) ha /\
  fast lenfix_list distfix_list (irf_chg m sb hb) =
    irf_chg m' (set_i_bits (set_i_hold (set_i_mode sb md) (m_hold m')) (m_bits m')) hb /\ irf_md md.
Proof.
  unfold fast. rewrite !irf_aout.
  destruct (irf_loop (Z.to_nat (m_aout m) + 1) m) as (M & md & E1 & E2 & Md). rewrite E1, E2.
  cbv zeta. autorewrite with irf.
  match goal with |- exists _ _, irf_chg (restore ?X) _ _ = _ /\ _ => exists (restore X), md end.
  split; [reflexivity|]. split; [reflexivity|exact Md].
Qed.

End Sim.

(* ---------------------------------------------------------------------------------------------- *)
(* What inflate_fast keeps (as inflate_codes' TheoryFast.v tf_keep)                               *)

Definition irk_keep (m m': mst) : Prop :=
  m_inp m' = m_inp m /\ m_aout m' = m_aout m.

Lemma irk_keep_trans m1 m2 m3 : irk_keep m1 m2 -> irk_keep m2 m3 -> irk_keep m1 m3.
Proof. unfold irk_keep; intros [A1 B1] [A2 B2]; split; congruence. Qed.

Lemma irk_fwalk fx dx k il t here m h' m' :
  fwalk_f fx dx k il t here m = (h', m') -> m_inp m' = m_inp m /\ m_aout m' = m_aout m.
Proof.
  revert here m; induction k; intros here m E; cbn [fwalk_f] in E.
  - inversion E; subst; cbn; split; reflexivity.
  - destruct (il (e_op here)).
    + apply IHk in E; destruct E as (-> & ->); cbn; split; reflexivity.
    + inversion E; subst; cbn; split; reflexivity.
Qed.

Ltac irk_hdest x :=
  lazymatch x with
  | match ?c with _ => _ end => irk_hdest c
  | context [match ?c with _ => _ end] => irk_hdest c
  | _ => tryif is_var x then destruct x else (let E := fresh "E" in destruct x eqn:E)
  end.
Ltac irk_hsplit :=
  repeat (cbv beta iota zeta;
          match goal with
          | |- context [match ?x with _ => _ end] => irk_hdest x
          end).
Ltac irk_huse :=
  repeat match goal with
  | E: fwalk_f _ _ _ _ _ _ _ = (_, _) |- _ =>
      apply irk_fwalk in E; destruct E as (? & ?)
  | E: copy_bytes _ _ _ _ = (_, _) |- _ => clear E
  end.
Ltac irk_rw :=
  repeat match goal with
  | H: m_inp ?a = _ |- context [m_inp ?a] => rewrite H
  | H: m_aout ?a = _ |- context [m_aout ?a] => rewrite H
  end.
Ltac irk_close :=
  unfold irk_keep; repeat progress (cbn -[copy_bytes fwalk_f fast_iter fast_loop fast]; irk_rw);
  split; reflexivity.

Lemma irk_iter fx dx m : irk_keep m (snd (fast_iter fx dx m)).
Proof. unfold fast_iter. irk_hsplit; irk_huse; irk_close. Qed.

Lemma irk_loop fx dx k m : irk_keep m (fast_loop fx dx k m).
Proof.
  revert m; induction k; intros m; cbn [fast_loop]; [split; reflexivity|].
  pose proof (irk_iter fx dx m) as A.
  destruct (fast_iter fx dx m) as [go m1] eqn:E; cbn in A |- *.
  destruct ((go && _ && _)%bool); [eapply irk_keep_trans; [exact A | apply IHk] | exact A].
Qed.

Lemma irk_fast fx dx m : irk_keep m (fast fx dx m).
Proof.
  unfold fast. cbv zeta.
  pose proof (irk_loop fx dx (Z.to_nat (m_aout m) + 1) m) as A; revert A.
  generalize (fast_loop fx dx (Z.to_nat (m_aout m) + 1) m); intros m1 A.
  eapply irk_keep_trans; [exact A|]. split; reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The relation after inflate_fast                                                              *)

Lemma irf_mrel_eq ma mb : mrel ma mb -> ma = irf_chg mb (m_s ma) (m_h ma).
Proof.
  intros []. destruct ma, mb; cbn in *; subst; reflexivity.
Qed.

Ltac irf_nomode X :=
  exfalso;
  repeat match goal with H: ?T |- _ =>
    lazymatch T with
    | irf_md _ => fail
    | _ => tryif constr_eq H X then fail else clear H
    end
  end;
  unfold irf_md, lenlive, decode_mode in *; cbn [i_mode set_i_bits set_i_hold set_i_mode] in X;
  unfold HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT, Zlib.proof.inflate.Model.TYPE,
    TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT,
    CHECK, LENGTH, DONE, BAD, MEM, SYNC in *; lia.

Lemma irf_srel no no' sa0 sb0 h1 b1 md h2 b2 :
  srel no sa0 sb0 -> i_mode sb0 = LEN -> irf_md md ->
  srel no' (set_i_bits (set_i_hold (set_i_mode (set_i_bits (set_i_hold sa0 h1) b1) md) h2) b2)
           (set_i_bits (set_i_hold (set_i_mode (set_i_bits (set_i_hold sb0 h1) b1) md) h2) b2).
Proof.
  intros R Hm Md.
  pose proof (sr_wbits _ _ _ R) as sr_wbits0. pose proof (sr_check _ _ _ R) as sr_check0.
  pose proof (sr_lenbits _ _ _ R) as sr_lenbits0. pose proof (sr_distbits _ _ _ R) as sr_distbits0.
  pose proof (sr_dectab _ _ _ R) as sr_dectab0.
  rewrite Hm in sr_wbits0, sr_check0, sr_lenbits0, sr_distbits0, sr_dectab0.
  destruct R.
  assert (DL: decode_mode LEN) by (unfold decode_mode; auto).
  constructor; cbn [i_mode i_last i_wrap i_havedict i_flags i_dmax i_total i_head i_wsize i_whave i_wnext
    i_wdata i_hold i_bits i_lencode i_distcode i_next i_sane i_back i_wbits i_check i_length i_offset i_extra
    i_lenbits i_distbits i_ncode i_nlen i_ndist i_have i_lens i_codes set_i_bits set_i_hold set_i_mode];
    try assumption; try reflexivity.
  - destruct sr_wbits0 as [E|E]; [left; exact E|exfalso; irf_nomode E].
  - destruct sr_check0 as [E|[E|[E _]]]; [left; exact E|right; left; exact E|exfalso; irf_nomode E].
  - intros X; exfalso; irf_nomode X.
  - intros X; exfalso; irf_nomode X.
  - intros X; exfalso; irf_nomode X.
  - intros X. destruct Md as [->|[->| ->]]; destruct X as [X|X];
      first [exact (sr_lenbits0 (or_intror DL)) | irf_nomode X].
  - intros X. destruct Md as [->|[->| ->]]; first [exact (sr_distbits0 DL) | irf_nomode X].
  - intros X; exfalso; irf_nomode X.
  - intros X; exfalso; irf_nomode X.
  - intros X; exfalso; irf_nomode X.
  - intros X; exfalso; irf_nomode X.
  - intros X; exfalso; irf_nomode X.
  - intros X. destruct Md as [->|[->| ->]]; first [exact (sr_dectab0 DL) | irf_nomode X].
Qed.

Lemma fast_sim : fast_sim_stmt.
Proof.
  intros W0 wrap src pos inp aout ma mb Hctx HK Wa Wb Hlv Hmd Hout Hhave Hleft Hbits.
  destruct HK as [HR Hinp Haout Hwrap Hhead Hwa Hwb Hhd].
  pose proof (mr_s _ _ HR) as Hs.
  unfold m_mode in Hmd.
  assert (DL: decode_mode (i_mode (m_s mb))) by (rewrite Hmd; unfold decode_mode; auto).
  destruct (md_tables _ (mw_md _ (mwf3_mwf _ Wb)) DL) as [(szl & _ & TL) (szd & _ & TD)].
  destruct (sr_dectab _ _ _ Hs DL) as [RL RD].
  assert (Ea: restore ma = irf_chg (restore mb) (set_i_bits (set_i_hold (m_s ma) (m_hold mb)) (m_bits mb)) (m_h ma)).
  { transitivity (restore (irf_chg mb (m_s ma) (m_h ma))); [f_equal; apply irf_mrel_eq, HR|reflexivity]. }
  destruct (irf_fastl (set_i_bits (set_i_hold (m_s ma) (m_hold mb)) (m_bits mb))
              (set_i_bits (set_i_hold (m_s mb) (m_hold mb)) (m_bits mb)) (m_h ma) (m_h mb)
              (sr_lencode _ _ _ Hs) (sr_distcode _ _ _ Hs) (sr_lenbits _ _ _ Hs (or_intror DL))
              (sr_distbits _ _ _ Hs DL) (sr_whave _ _ _ Hs) (sr_sane _ _ _ Hs) (sr_wdata _ _ _ Hs)
              (sr_wsize _ _ _ Hs) (sr_wnext _ _ _ Hs) (eq_trans (sr_mode _ _ _ Hs) Hmd) Hmd
              szl szd TL TD RL RD (restore mb)) as (M & md & E1 & E2 & Md).
  assert (Eb: fast lenfix_list distfix_list (restore mb) =
              irf_chg M (set_i_bits (set_i_hold (set_i_mode
                (set_i_bits (set_i_hold (m_s mb) (m_hold mb)) (m_bits mb)) md) (m_hold M)) (m_bits M)) (m_h mb)).
  { rewrite <- E2. f_equal. }
  pose proof (irk_fast lenfix_list distfix_list (restore mb)) as [Ki Ka].
  rewrite Eb in Ki, Ka. rewrite Ea, E1, Eb. clear E1 E2 Ea Eb.
  constructor.
  - constructor; try reflexivity.
    cbn [m_s irf_chg set_m_h set_m_s]. apply irf_srel with (no := m_ow mb = []); [exact Hs|exact Hmd|exact Md].
  - etransitivity; [exact Ki|exact Hinp].
  - etransitivity; [exact Ka|exact Haout].
  - exact Hwrap.
  - exact Hhead.
  - exact Hwa.
  - exact Hwb.
  - intros _ X. change (md = HEAD) in X. irf_nomode X.
Qed.
