(* RT-I: copy of rfc1951/DecDecCopy.v over the generalized definitions RTIGDefs.v. *)
(* Part of DecDec.group_dec: MATCH's copy is lz_copy.  Statement: DecDecDefs.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTIGDecDecDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* the copy only appends *)
Lemma dcp_ext : forall n w sr ow, exists d, fst (copy_f n w sr ow) = ow ++ d.
Proof.
  induction n; intros w sr ow; simpl.
  - exists []. rewrite app_nil_r. reflexivity.
  - destruct sr as [i|i].
    + destruct (IHn w (SWin (i + 1)) (ow ++ [Znth i w])) as [d E].
      rewrite E; exists (Znth i w :: d); rewrite <- app_assoc; reflexivity.
    + destruct (IHn w (SOut (i + 1)) (ow ++ [Znth i ow])) as [d E].
      rewrite E; exists (Znth i ow :: d); rewrite <- app_assoc; reflexivity.
Qed.

(* a copy from the window: byte t is the byte |ob| + |ow| + t - dist of ob *)
Lemma dcp_win : forall n w i ob ow dist,
  (forall t, 0 <= t < Z.of_nat n ->
     0 <= Zlength ob + Zlength ow + t - dist < Zlength ob /\
     Znth (i + t) w = Znth (Zlength ob + Zlength ow + t - dist) ob) ->
  ob ++ fst (copy_f n w (SWin i) ow) = lz_copy n dist (ob ++ ow).
Proof.
  induction n; intros w i ob ow dist H; simpl.
  - reflexivity.
  - rewrite (IHn w (i + 1) ob (ow ++ [Znth i w]) dist).
    + rewrite app_assoc.
      destruct (H 0) as [B E]; [lia|]. rewrite Z.add_0_r in E, B. rewrite E, Zlength_app, app_Znth1 by lia.
      replace (Zlength ob + Zlength ow + 0 - dist) with (Zlength ob + Zlength ow - dist) by lia.
      reflexivity.
    + intros t Ht. rewrite Zlength_app, Zlength_cons, Zlength_nil.
      destruct (H (t + 1)) as [B E]; [lia|].
      replace (i + 1 + t) with (i + (t + 1)) by lia.
      replace (Zlength ob + (Zlength ow + Z.succ 0) + t - dist) with (Zlength ob + Zlength ow + (t + 1) - dist) by lia.
      split; [lia | exact E].
Qed.

(* a copy from the output, overlapping *)
Lemma dcp_out : forall n w ob ow dist, 1 <= dist <= Zlength ow ->
  ob ++ fst (copy_f n w (SOut (Zlength ow - dist)) ow) = lz_copy n dist (ob ++ ow).
Proof.
  induction n; intros w ob ow dist H; simpl.
  - reflexivity.
  - replace (Zlength ow - dist + 1) with (Zlength (ow ++ [Znth (Zlength ow - dist) ow]) - dist)
      by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    rewrite IHn by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    f_equal. rewrite app_assoc. f_equal. f_equal.
    rewrite Zlength_app, app_Znth2 by lia. f_equal. lia.
Qed.

(* copy_stmt with the missing hypothesis 0 <= wnext (mwf3 / Inv.sw_wnext); copy_stmt itself is false
   without it (wnext < 0 makes c_MATCH copy more than dist - |ow| bytes from the window) *)
Lemma copy_ok_fix :
  forall G m ob dist,
    win_ok G (m_s m) ob -> 0 <= i_wbits (m_s m) -> 0 <= i_wnext (m_s m) ->
    m_out m = m_aout m -> Zlength (m_ow m) <= m_aout m <= 2 ^ 31 - 1 -> 0 < m_left m ->
    i_offset (m_s m) = dist -> 1 <= dist <= Zlength (ob ++ m_ow m) -> dist <= 2 ^ i_wbits (m_s m) ->
    1 <= i_length (m_s m) ->
    exists c ow',
      1 <= c <= Z.min (i_length (m_s m)) (m_left m) /\
      ob ++ ow' = lz_copy (Z.to_nat c) dist (ob ++ m_ow m) /\ (exists d, ow' = m_ow m ++ d) /\
      c_MATCH m = IBrk (let m1 := upd_s (set_m_ow m ow') (fun s => set_i_length s (i_length (m_s m) - c)) in
                        if i_length (m_s m) - c =? 0 then set_mode m1 LEN else m1).
Proof.
  intros G m ob dist W WB WN0 OUT AO LEFT OFF D1 D2 L1.
  assert (C0: u32 (m_out m - m_left m) = Zlength (m_ow m)).
  { unfold u32, m_left. rewrite OUT. pose proof (Zlength_nonneg (m_ow m)).
    rewrite Z.mod_small; lia. }
  rewrite Zlength_app in D1.
  pose proof (Zlength_nonneg ob) as NB. pose proof (Zlength_nonneg (m_ow m)) as NW.
  unfold c_MATCH.
  replace (m_left m =? 0) with false by lia.
  rewrite C0, OFF.
  destruct (Zlength (m_ow m) <? dist) eqn:LT.
  - apply Z.ltb_lt in LT.
    remember (dist - Zlength (m_ow m)) as cp eqn:CPd.
    destruct W as [[WS OB]|[WS [WH WA]]].
    { subst ob. rewrite Zlength_nil in D1. lia. }
    assert (CW: cp <= i_whave (m_s m)).
    { rewrite WH, WS. pose proof (Z.min_glb_iff (Zlength ob) (2 ^ i_wbits (m_s m)) cp). lia. }
    replace (i_whave (m_s m) <? cp) with false by lia. simpl andb. cbv iota.
    (* the source and its length *)
    assert (SR: exists i cp', 1 <= cp' <= cp /\
               (if i_wnext (m_s m) <? cp then (SWin (i_wsize (m_s m) - (cp - i_wnext (m_s m))), cp - i_wnext (m_s m))
                else (SWin (i_wnext (m_s m) - cp), cp)) = (SWin i, cp') /\
               forall t, 0 <= t < cp' -> Znth (i + t) (i_wdata (m_s m)) = win_at (m_s m) (cp - t)).
    { unfold win_at. destruct (i_wnext (m_s m) <? cp) eqn:WN.
      - apply Z.ltb_lt in WN. exists (i_wsize (m_s m) - (cp - i_wnext (m_s m))), (cp - i_wnext (m_s m)).
        split; [lia|split; [reflexivity|]].
        intros t Ht. replace (cp - t <=? i_wnext (m_s m)) with false by lia. f_equal. lia.
      - apply Z.ltb_ge in WN. exists (i_wnext (m_s m) - cp), cp.
        split; [lia|split; [reflexivity|]].
        intros t Ht. replace (cp - t <=? i_wnext (m_s m)) with true by lia. f_equal. lia. }
    destruct SR as (i & cp' & B & -> & WT).
    set (c := Z.min (Z.min cp' (i_length (m_s m))) (m_left m)).
    destruct (copy_bytes (i_wdata (m_s m)) (SWin i) c (m_ow m)) as [ow' sr'] eqn:CB.
    exists c, ow'.
    assert (Cr: 1 <= c <= Z.min (i_length (m_s m)) (m_left m)).
    { unfold c. pose proof (Z.min_glb_iff cp' (i_length (m_s m)) 1). lia. }
    split; [exact Cr|]. split; [|split].
    + unfold copy_bytes in CB. replace ow' with (fst (copy_f (Z.to_nat c) (i_wdata (m_s m)) (SWin i) (m_ow m)))
        by (rewrite CB; reflexivity).
      apply dcp_win. intros t Ht. rewrite Z2Nat.id in Ht by lia.
      assert (t < cp') by (unfold c in Ht; lia).
      rewrite WT by lia. rewrite WA by lia. split; [lia|]. f_equal. lia.
    + unfold copy_bytes in CB. destruct (dcp_ext (Z.to_nat c) (i_wdata (m_s m)) (SWin i) (m_ow m)) as [d E].
      rewrite CB in E. exists d. exact E.
    + reflexivity.
  - apply Z.ltb_ge in LT.
    set (c := Z.min (i_length (m_s m)) (m_left m)).
    destruct (copy_bytes (i_wdata (m_s m)) (SOut (Zlength (m_ow m) - dist)) c (m_ow m)) as [ow' sr'] eqn:CB.
    exists c, ow'.
    split; [unfold c; lia|]. split; [|split].
    + unfold copy_bytes in CB.
      replace ow' with (fst (copy_f (Z.to_nat c) (i_wdata (m_s m)) (SOut (Zlength (m_ow m) - dist)) (m_ow m)))
        by (rewrite CB; reflexivity).
      apply dcp_out. lia.
    + unfold copy_bytes in CB. destruct (dcp_ext (Z.to_nat c) (i_wdata (m_s m)) (SOut (Zlength (m_ow m) - dist)) (m_ow m)) as [d E].
      rewrite CB in E. exists d. exact E.
    + reflexivity.
Qed.

Lemma copy_ok : copy_stmt.
Proof. exact copy_ok_fix. Qed.
