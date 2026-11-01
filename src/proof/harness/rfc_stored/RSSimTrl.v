(* Law rfc_stored, the padding simulation: the trailer passes (CHECK, falling through LENGTH into DONE, LENGTH,
   DONE) read only bytes after the deflate stream, which the real input shares with the canonical one. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.harness.rfc_stored.RSSimKit.
Import ListNotations.
Local Open Scope Z_scope.

(* the real input agrees with the machine's from its position nx on *)
Definition rs_from (m: mst) (x: list Z) : Prop := forall i, m_nx m <= i -> Znth i x = Znth i (m_inp m).

(* NEEDBITS only moves nx forward and keeps the input *)
Lemma rs_needbits_nx k : forall n m, m_nx m <= m_nx (needbits_f k n m) /\ m_inp (needbits_f k n m) = m_inp m.
Proof.
  induction k as [|k IH]; intros n m; cbn [needbits_f]; [split; [lia | reflexivity]|].
  destruct (m_bits m <? n); [|split; [lia | reflexivity]].
  destruct (m_have m =? 0); [split; [cbn; lia | reflexivity]|].
  destruct (IH n (pull m)) as [A B]. cbn in A, B |- *. split; [lia | exact B].
Qed.

(* NEEDBITS(32) on an input that agrees from nx on *)
Lemma rs_needbits_from n m x : Zlength x = Zlength (m_inp m) -> 0 <= m_bits m -> n <= 32 -> rs_from m x ->
  needbits n (set_m_inp m x) = set_m_inp (needbits n m) x /\ rs_from (needbits n m) x.
Proof.
  intros Hl Hb Hn Ha. split.
  - apply rs_needbits_inp4; auto.
  - destruct (rs_needbits_nx 4 n m) as [A B]. intros i Hi. unfold needbits in *. rewrite B. apply Ha; lia.
Qed.

(* the LENGTH pass reads only the input from nx on *)
Lemma rs_c_LENGTH m x : Zlength x = Zlength (m_inp m) -> 0 <= m_bits m -> rs_from m x ->
  c_LENGTH (set_m_inp m x) = rs_iom x (c_LENGTH m).
Proof.
  intros Hl Hb Ha. unfold c_LENGTH. change (m_s (set_m_inp m x)) with (m_s m).
  destruct (negb (i_wrap (m_s m) =? 0) && negb (i_flags (m_s m) =? 0)); [|destruct m; reflexivity].
  destruct (rs_needbits_from 32 m x Hl Hb ltac:(lia) Ha) as [E _]. rewrite E.
  set (n := needbits 32 m). clearbody n.
  change (m_leave (set_m_inp n x)) with (m_leave n). change (m_s (set_m_inp n x)) with (m_s n).
  change (m_hold (set_m_inp n x)) with (m_hold n).
  destruct (m_leave n =? 1); [reflexivity|].
  destruct (_ && _); destruct n; reflexivity.
Qed.

(* the CHECK pass after its NEEDBITS(32): the counts and the check value, then the comparison *)
Definition rs_chk_mid (m: mst) : mst :=
  let out := u32 (m_out m - m_left m) in
  let m := set_m_tout m (u64 (m_tout m + out)) in
  let m := upd_s m (fun s => set_i_total s (u64 (i_total s + out))) in
  let m := if negb (Z.land (i_wrap (m_s m)) 4 =? 0) && negb (out =? 0) then
             let c := update_check (i_flags (m_s m)) (i_check (m_s m))
                        (sublist (Zlength (m_ow m) - out) (Zlength (m_ow m)) (m_ow m)) in
             set_m_adler (upd_s m (fun s => set_i_check s c)) c
           else m in
  set_m_out m (m_left m).

Definition rs_chk_tail (m: mst) : iout :=
  let s := m_s m in
  if negb (Z.land (i_wrap s) 4 =? 0) &&
     negb ((if i_flags s =? 0 then swap32 (m_hold m) else m_hold m) =? i_check s)
  then IBrk (set_bad m M_dcheck)
  else c_LENGTH (set_mode (initbits m) LENGTH).

Lemma rs_c_CHECK_eq m : c_CHECK m =
  if negb (i_wrap (m_s m) =? 0) then
    (let n := needbits 32 m in if m_leave n =? 1 then IBrk n else rs_chk_tail (rs_chk_mid n))
  else c_LENGTH (set_mode m LENGTH).
Proof. unfold c_CHECK, rs_chk_tail, rs_chk_mid. cbv zeta. reflexivity. Qed.

Lemma rs_chk_mid_inp n x : rs_chk_mid (set_m_inp n x) = set_m_inp (rs_chk_mid n) x.
Proof. unfold rs_chk_mid. cbv zeta. destruct (_ && _); destruct n; reflexivity. Qed.

Lemma rs_chk_mid_nx n : m_nx (rs_chk_mid n) = m_nx n /\ m_inp (rs_chk_mid n) = m_inp n.
Proof. unfold rs_chk_mid. cbv zeta. destruct (_ && _); split; reflexivity. Qed.

(* the CHECK pass (falling into LENGTH) reads only the input from nx on *)
Lemma rs_c_CHECK m x : Zlength x = Zlength (m_inp m) -> 0 <= m_bits m -> rs_from m x ->
  c_CHECK (set_m_inp m x) = rs_iom x (c_CHECK m).
Proof.
  intros Hl Hb Ha. rewrite !rs_c_CHECK_eq. change (m_s (set_m_inp m x)) with (m_s m).
  destruct (negb (i_wrap (m_s m) =? 0)).
  2:{ replace (set_mode (set_m_inp m x) LENGTH) with (set_m_inp (set_mode m LENGTH) x) by (destruct m; reflexivity).
      apply rs_c_LENGTH; auto. }
  destruct (rs_needbits_from 32 m x Hl Hb ltac:(lia) Ha) as [E Hn]. cbv zeta. rewrite E.
  assert (Hi : m_inp (needbits 32 m) = m_inp m) by apply (rs_needbits_nx 4 32 m).
  set (n := needbits 32 m) in *. clearbody n.
  change (m_leave (set_m_inp n x)) with (m_leave n).
  destruct (m_leave n =? 1); [reflexivity|].
  rewrite rs_chk_mid_inp. destruct (rs_chk_mid_nx n) as [E3 E4].
  set (n1 := rs_chk_mid n) in *. clearbody n1.
  unfold rs_chk_tail.
  change (m_s (set_m_inp n1 x)) with (m_s n1). change (m_hold (set_m_inp n1 x)) with (m_hold n1).
  destruct (_ && _); [destruct n1; reflexivity|].
  replace (set_mode (initbits (set_m_inp n1 x)) LENGTH) with (set_m_inp (set_mode (initbits n1) LENGTH) x)
    by (destruct n1; reflexivity).
  apply rs_c_LENGTH; [cbn; rewrite E4, Hi; exact Hl | cbn; lia |].
  intros i Hi'. cbn in Hi' |- *. rewrite E4. apply Hn. lia.
Qed.

(* at CHECK and LENGTH the bit position q = 8 c - bits is past the end of the deflate stream *)
Lemma rs_trl_q G s c hold bits out : at_mode G s c hold bits out -> i_mode s = CHECK \/ i_mode s = LENGTH ->
  0 <= bits /\ endpos G <= 8 * c - bits.
Proof.
  intros [Hh H] Hm. destruct Hh as [Hb _]. split; [lia|]. cbv zeta in H.
  destruct Hm as [Hm|Hm]; rewrite Hm in H;
    repeat match goal with
           | H: _ \/ _ |- _ => destruct H as [[E H]|H]; [try discriminate E|]
           end;
    unfold at_check, at_length in *; try lia;
    repeat match goal with H: _ /\ _ |- _ => destruct H end; try lia; try discriminate.
  all: exfalso; repeat match goal with E: _ \/ _ |- _ => destruct E as [E|E] end; discriminate.
Qed.

Lemma rs_pass_trl : rs_lay_stmt -> rs_pass_ok md_trl.
Proof.
  intros L G pos x inp' ob flush m' Hok Hst Hpos Hlen Hinp Hx Hkd Hw Hlv Hmd.
  assert (Hm : m_mode (set_m_inp m' x) = m_mode m') by (destruct m'; reflexivity).
  destruct Hx as [Hxl [_ Hxi]].
  pose proof (kd_inp _ _ _ _ _ Hkd) as Ki.
  assert (Hl : Zlength x = Zlength (m_inp m')) by (rewrite Ki; exact Hxl).
  (* the input agrees from nx on: the first bytes of blocks are before the end of the deflate stream *)
  assert (From : i_mode (m_s m') = CHECK \/ i_mode (m_s m') = LENGTH -> 0 <= m_bits m' /\ rs_from m' x).
  { intros Hc. destruct (rs_trl_q _ _ _ _ _ _ (kd_at _ _ _ _ _ Hkd) Hc) as [Hb Hq].
    split; [exact Hb|]. intros i Hi.
    destruct Hw as [W _]. pose proof (mwW_nx _ W) as Hnx.
    destruct (Z_lt_le_dec i (Zlength x)) as [Lt|Ge].
    - rewrite Ki. destruct (Hxi i ltac:(lia)) as [E|[[k [Hk Hp]] _]]; [exact E|].
      pose proof (rl_mono L G k (nblk G) Hst ltac:(lia) ltac:(lia)).
      pose proof (rl_end L G Hst). lia.
    - rewrite !Znth_overflow by lia. reflexivity. }
  destruct Hmd as [Hc|[Hc|Hc]].
  - assert (S : forall m, m_mode m = CHECK -> stepf2 flush lenfix_list distfix_list m = c_CHECK m)
      by (intros m E; unfold stepf2, step2; rewrite E; reflexivity).
    rewrite !S by congruence. destruct (From (or_introl Hc)) as [Hb Ha].
    apply rs_c_CHECK; auto.
  - assert (S : forall m, m_mode m = LENGTH -> stepf2 flush lenfix_list distfix_list m = c_LENGTH m)
      by (intros m E; unfold stepf2, step2; rewrite E; reflexivity).
    rewrite !S by congruence. destruct (From (or_intror Hc)) as [Hb Ha].
    apply rs_c_LENGTH; auto.
  - assert (S : forall m, m_mode m = DONE -> stepf2 flush lenfix_list distfix_list m = c_DONE m)
      by (intros m E; unfold stepf2, step2; rewrite E; reflexivity).
    rewrite !S by congruence. destruct m'; reflexivity.
Qed.
