(* Laws res_free_inflate and res_memory_inflate: the facts about the model and the counters that main's body
   proofs use.
   - The state inflateInit2_ makes (init_live): no window, no gz_header request, mode HEAD (so the wide
     invariant swfW holds).
   - One inflate() on a live stream with an output space and an input object runs the model (run2) and
     leaves the stream live.
   - The counters of struct count (cnt, computed in size_t) after the events of inflateInit2_, inflate() and
     inflateEnd: count.now is 0. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.za.inflate_api.USpec.
Require Import Zlib.proof.za.inflate.ZEvents.
Require Import Zlib.proof.harness.counted.Spec.
Require Import Zlib.proof.harness.res_inflate.ModelStmt.

Lemma init_head sp w : i_head (l_s (init_live sp w)) = false.
Proof. unfold init_live. destruct (reset2_wb w) as [[a b] | ]; reflexivity. Qed.

Lemma init_win sp w : i_win (l_s (init_live sp w)) = false.
Proof.
  unfold init_live. destruct (reset2_wb w) as [[a b] | ]; [ | reflexivity].
  unfold init_s, reset2_s, reset_full_s, reset_hdr_s.
  cbn [zero_s i_win i_wbits andb negb set_i_wbits set_i_wrap set_i_win i_wrap].
  destruct (Z.land _ 8 =? 0); reflexivity.
Qed.

Lemma init_mode sp w : i_mode (l_s (init_live sp w)) = HEAD.
Proof. unfold init_live. destruct (reset2_wb w) as [[a b] | ]; reflexivity. Qed.

Lemma init_swfW sp w : Zlib.proof.inflate.InvW.swfW (l_s (init_live sp w)).
Proof.
  unfold Zlib.proof.inflate.InvW.swfW. rewrite init_mode.
  split; intros E; discriminate E.
Qed.

(* inflate() on a live stream, an input object and an output space: the model's run, and a live stream *)
Lemma inflate_rel_some flush strmp z L ib inp o r z' st' ow :
  strmp <> nullval -> ib <> InNull ->
  inflate_rel flush strmp z (Some L) ib inp (Some o) r z' st' ow ->
  exists res winp, st' = Some (Live (l_sp L) winp (m_s (r_m res)) (m_h (r_m res)) (l_headp L) (l_hsh L)
                                   (l_xb L) (l_nb L) (l_cb L)) /\
    Zlib.proof.inflate.Model2.run2 flush lenfix_list distfix_list (m_init z L inp) res.
Proof.
  intros Hs Hi [(Hb & _) | (Hb & L1 & o1 & res & winp & E1 & E2 & Hrun & _ & _ & _ & _ & _ & Est)].
  - exfalso. unfold inflate_bad, is_live in Hb. rewrite if_false in Hb by auto.
    destruct Hb as [Hb | [Hb | [Hb _]]]; congruence.
  - injection E1 as E1. subst L1. exists res, winp. split; assumption.
Qed.

(* the size_t counter now is the bytes held modulo 2^64 *)
Lemma cnt_now_fold : forall tr a b c d, a = c mod 2 ^ 64 ->
  fst (fold_left cnt_step tr (a, b)) = fst (fold_left zev_step tr (c, d)) mod 2 ^ 64.
Proof.
  induction tr as [| e tr IH]; intros a b c d E; simpl.
  - exact E.
  - destruct e as [k | k | ]; simpl; apply IH; subst a.
    + rewrite Zplus_mod_idemp_l. reflexivity.
    + rewrite Zminus_mod_idemp_l. reflexivity.
    + reflexivity.
Qed.

Lemma cnt_now tr : fst (cnt tr) = za_now tr mod 2 ^ 64.
Proof. unfold cnt, za_now, za_count. apply cnt_now_fold. reflexivity. Qed.

(* res_free_inflate: inflateInit2_ allocated the state, inflate() the window (if any, or a failed allocation),
   inflateEnd freed both *)
Lemma free_count s0 s' :
  i_win s0 = false -> fst (cnt ([ZAlloc state_size] ++ win_ev s0 s' ++ end_ev s')) = 0.
Proof.
  intros W. rewrite cnt_now. unfold win_ev, end_ev. rewrite W. simpl andb.
  destruct (i_win s'); unfold za_now, za_count, state_size; simpl.
  - replace (7160 + 2 ^ i_wbits s' - 2 ^ i_wbits s' - 7160) with 0 by lia. reflexivity.
  - destruct (_ && _)%bool; reflexivity.
Qed.

(* inflateInit2_ failed: nothing or the state allocated and freed again *)
Lemma init_fail_count c ssize w a :
  init_ev false c ssize w a <> [ZAlloc state_size] -> fst (cnt (init_ev false c ssize w a)) = 0.
Proof.
  intros N. unfold init_ev in *.
  destruct (negb (c =? 49) || negb (ssize =? 112))%bool; [reflexivity | ].
  destruct (negb a); [reflexivity | ].
  destruct (wbits_ok w); [congruence | reflexivity].
Qed.

(* res_memory_inflate: the harness's w of an accepted windowBits is 8..15 *)
Lemma harness_w_range w : wbits_ok w = true -> 8 <= harness_w w <= 15.
Proof.
  unfold wbits_ok, reset2_wb, harness_w. intros H.
  assert (B : 0 <= Z.land w 15 <= 15).
  { change (Z.land w 15) with (Z.land w (Z.ones 4)). rewrite Z.land_ones by lia.
    pose proof (Z.mod_pos_bound w (2 ^ 4) ltac:(lia)). simpl in *. lia. }
  destruct (w <? 0) eqn:E0.
  - destruct (w <? -15) eqn:E1; [discriminate | ].
    destruct ((8 <=? - w) && (- w <=? 15))%bool eqn:E2; [ | discriminate].
    apply andb_true_iff in E2. destruct E2 as [E2 E3]. apply Z.leb_le in E2, E3. lia.
  - destruct (Z.land w 15 =? 0) eqn:E3; [lia | ]. apply Z.eqb_neq in E3.
    destruct (w <? 48) eqn:E4.
    + destruct ((Z.land w 15 =? 0) || ((8 <=? Z.land w 15) && (Z.land w 15 <=? 15)))%bool eqn:E5; [ | discriminate].
      apply orb_true_iff in E5. destruct E5 as [E5 | E5]; [apply Z.eqb_eq in E5; lia | ].
      apply andb_true_iff in E5. destruct E5 as [E5 _]. apply Z.leb_le in E5. lia.
    + apply Z.ltb_ge in E4. apply Z.ltb_ge in E0.
      destruct ((w =? 0) || ((8 <=? w) && (w <=? 15)))%bool eqn:E5; [ | discriminate].
      apply orb_true_iff in E5. destruct E5 as [E5 | E5]; [apply Z.eqb_eq in E5; lia | ].
      apply andb_true_iff in E5. destruct E5 as [_ E5]. apply Z.leb_le in E5. lia.
Qed.

(* count.peak is never negative *)
Lemma cnt_peak_fold : forall tr a b, 0 <= b -> 0 <= snd (fold_left cnt_step tr (a, b)).
Proof.
  induction tr as [| e tr IH]; intros a b B; simpl; [exact B | ].
  destruct e as [k | k | ]; simpl; apply IH; auto.
  match goal with |- context [if ?c then _ else _] => destruct c end; [ | exact B].
  apply Z.mod_pos_bound. lia.
Qed.

Lemma cnt_peak_nonneg tr : 0 <= snd (cnt tr).
Proof. apply cnt_peak_fold. lia. Qed.

(* the harness's computation of w: `w = window_bits & 15; if (window_bits < 0) w = -window_bits;
   if (w == 0) w = 15;` *)
Lemma harness_w_c w :
  harness_w w = let x := if w <? 0 then - w else Z.land w 15 in if x =? 0 then 15 else x.
Proof.
  unfold harness_w. simpl. destruct (Z.ltb_spec w 0); [ | reflexivity].
  destruct (Z.eqb_spec (- w) 0); [lia | reflexivity].
Qed.
