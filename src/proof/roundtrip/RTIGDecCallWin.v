(* RT-I: copy of rfc1951/DecCallWin.v over the generalized definitions RTIGDefs.v. *)
(* Part of dec_call: inf_leave's updatewindow keeps win_ok (DecodeDefs.v): the window gets the
   bytes d written by the call. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTIGDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* the window read back at distance d, on the raw fields *)
Definition dcw_wa (ws wn: Z) (w: list Z) (d: Z) : Z :=
  if d <=? wn then Znth (wn - d) w else Znth (ws - (d - wn)) w.

(* the window facts before the copy *)
Definition dcw_pre (ws wn wh: Z) (w ob: list Z) : Prop :=
  0 < ws /\ 0 <= wn < ws /\ 0 <= wh <= ws /\ (wh < ws -> wn = wh) /\ Zlength w = wh /\
  wh = Z.min (Zlength ob) ws /\ forall d, 1 <= d <= wh -> dcw_wa ws wn w d = Znth (Zlength ob - d) ob.

(* what win_ok asks after it *)
Definition dcw_post (ws wn wh: Z) (w ob: list Z) : Prop :=
  wh = Z.min (Zlength ob) ws /\ forall d, 1 <= d <= wh -> dcw_wa ws wn w d = Znth (Zlength ob - d) ob.

Lemma dcw_app_new : forall (ob data: list Z) d, 1 <= d <= Zlength data ->
  Znth (Zlength (ob ++ data) - d) (ob ++ data) = Znth (Zlength data - d) data.
Proof.
  intros. rewrite Zlength_app. rewrite app_Znth2 by (pose proof (Zlength_nonneg ob); lia).
  f_equal; lia.
Qed.

Lemma dcw_app_old : forall (ob data: list Z) d, Zlength data < d <= Zlength (ob ++ data) ->
  Znth (Zlength (ob ++ data) - d) (ob ++ data) = Znth (Zlength ob - (d - Zlength data)) ob.
Proof.
  intros. rewrite Zlength_app in *. rewrite app_Znth1 by lia. f_equal; lia.
Qed.

(* branch 1: the data fills the window *)
Lemma dcw_br1 : forall ws (ob data: list Z), 0 < ws -> ws <= Zlength data ->
  dcw_post ws 0 ws (sublist (Zlength data - ws) (Zlength data) data) (ob ++ data).
Proof.
  intros. split.
  - rewrite Zlength_app. pose proof (Zlength_nonneg ob). lia.
  - intros. unfold dcw_wa. destruct (d <=? 0) eqn:E; [lia|].
    rewrite Znth_sublist by lia. rewrite dcw_app_new by lia. f_equal; lia.
Qed.

(* reading the window after the copy into it at wn *)
Lemma dcw_full_lo : forall (w data: list Z) wn n i, 0 <= wn <= Zlength w -> Zlength data = n -> 0 <= i < wn ->
  Znth i (sublist 0 wn w ++ data ++ sublist (wn + n) (Zlength w) w) = Znth i w.
Proof.
  intros. rewrite app_Znth1 by (rewrite Zlength_sublist; lia). rewrite Znth_sublist by lia. f_equal; lia.
Qed.

Lemma dcw_full_mid : forall (w data: list Z) wn n i, 0 <= wn <= Zlength w -> Zlength data = n ->
  wn <= i < wn + n ->
  Znth i (sublist 0 wn w ++ data ++ sublist (wn + n) (Zlength w) w) = Znth (i - wn) data.
Proof.
  intros. rewrite app_Znth2 by (rewrite Zlength_sublist; lia). rewrite Zlength_sublist by lia.
  rewrite app_Znth1 by lia. f_equal; lia.
Qed.

Lemma dcw_full_hi : forall (w data: list Z) wn n i, 0 <= wn -> 0 <= n -> Zlength data = n ->
  wn + n <= i < Zlength w ->
  Znth i (sublist 0 wn w ++ data ++ sublist (wn + n) (Zlength w) w) = Znth i w.
Proof.
  intros. rewrite app_Znth2 by (rewrite Zlength_sublist; lia). rewrite Zlength_sublist by lia.
  rewrite app_Znth2 by lia. rewrite Znth_sublist by lia. f_equal; lia.
Qed.

(* branch 2: the copy wraps around the end of the window *)
Lemma dcw_br2 : forall ws wn wh w (ob data: list Z), dcw_pre ws wn wh w ob -> Zlength data < ws ->
  Zlength data - Z.min (ws - wn) (Zlength data) <> 0 ->
  dcw_post ws (Zlength data - Z.min (ws - wn) (Zlength data)) ws
    (sublist (Z.min (ws - wn) (Zlength data)) (Zlength data) data ++
     sublist (Zlength data - Z.min (ws - wn) (Zlength data))
       (Zlength (sublist 0 wn w ++ sublist 0 (Z.min (ws - wn) (Zlength data)) data ++
                 sublist (wn + Z.min (ws - wn) (Zlength data)) (Zlength w) w))
       (sublist 0 wn w ++ sublist 0 (Z.min (ws - wn) (Zlength data)) data ++
        sublist (wn + Z.min (ws - wn) (Zlength data)) (Zlength w) w))
    (ob ++ data).
Proof.
  intros ws wn wh w ob data (Hws & Hwn & Hwh & Hval & Hw & Hmin & Hwa) Hc Hc'.
  set (c := Zlength data) in *. set (dist := Z.min (ws - wn) c) in *.
  assert (Hcdef : c = Zlength data) by reflexivity. assert (Hddef : dist = Z.min (ws - wn) c) by reflexivity.
  assert (Hdist : dist = ws - wn) by lia.
  assert (Hcd : ws - wn < c) by (unfold dist in *; lia).
  assert (Hwnwh : wn <= wh) by (destruct (Z.lt_ge_cases wh ws); [rewrite Hval by lia|]; lia).
  pose proof (Zlength_nonneg ob).
  set (full := sublist 0 wn w ++ sublist 0 dist data ++ sublist (wn + dist) (Zlength w) w).
  assert (Hsd : Zlength (sublist 0 dist data) = dist) by (rewrite Zlength_sublist; lia).
  assert (Hfull : Zlength full = ws).
  { unfold full. rewrite !Zlength_app, Hsd. rewrite (Zlength_sublist 0 wn) by lia.
    rewrite sublist_over by lia. rewrite Zlength_nil. lia. }
  rewrite Hfull. split.
  - rewrite Zlength_app. lia.
  - intros d Hd. unfold dcw_wa.
    assert (Hs2 : Zlength (sublist dist c data) = c - dist) by (rewrite Zlength_sublist; lia).
    destruct (d <=? c - dist) eqn:E.
    + rewrite app_Znth1 by lia. rewrite Znth_sublist by lia. rewrite dcw_app_new by lia. f_equal; lia.
    + rewrite app_Znth2 by lia. rewrite Hs2. rewrite Znth_sublist by lia.
      destruct (Z.le_gt_cases d c).
      * unfold full. rewrite dcw_full_mid by lia. rewrite Znth_sublist by lia.
        rewrite dcw_app_new by lia. f_equal; lia.
      * unfold full. rewrite dcw_full_lo by lia. rewrite dcw_app_old by (rewrite Zlength_app in *; lia).
        rewrite <- Hwa by lia. unfold dcw_wa; fold c. destruct (d - c <=? wn) eqn:E2; [|lia]. f_equal; lia.
Qed.

(* branch 3: the copy fits before the end of the window *)
Lemma dcw_br3 : forall ws wn wh w (ob data: list Z), dcw_pre ws wn wh w ob -> Zlength data < ws ->
  Zlength data - Z.min (ws - wn) (Zlength data) = 0 ->
  dcw_post ws (if wn + Z.min (ws - wn) (Zlength data) =? ws then 0 else wn + Z.min (ws - wn) (Zlength data))
    (if wh <? ws then wh + Z.min (ws - wn) (Zlength data) else wh)
    (sublist 0 wn w ++ sublist 0 (Z.min (ws - wn) (Zlength data)) data ++
     sublist (wn + Z.min (ws - wn) (Zlength data)) (Zlength w) w)
    (ob ++ data).
Proof.
  intros ws wn wh w ob data (Hws & Hwn & Hwh & Hval & Hw & Hmin & Hwa) Hc Hc'.
  set (c := Zlength data) in *. set (dist := Z.min (ws - wn) c) in *.
  assert (Hcdef : c = Zlength data) by reflexivity. assert (Hddef : dist = Z.min (ws - wn) c) by reflexivity.
  assert (Hdist : dist = c) by lia.
  assert (Hwnwh : wn <= wh) by (destruct (Z.lt_ge_cases wh ws); [rewrite Hval by lia|]; lia).
  pose proof (Zlength_nonneg ob). pose proof (Zlength_nonneg data).
  assert (Hsd : Zlength (sublist 0 dist data) = dist) by (rewrite Zlength_sublist; lia).
  set (full := sublist 0 wn w ++ sublist 0 dist data ++ sublist (wn + dist) (Zlength w) w).
  assert (Hwh' : (if wh <? ws then wh + dist else wh) = Z.min (Zlength (ob ++ data)) ws).
  { rewrite Zlength_app. destruct (wh <? ws) eqn:E; [rewrite Hval in * by lia|]; lia. }
  split; [exact Hwh'|].
  intros d Hd. rewrite Hwh' in Hd. unfold dcw_wa.
  destruct (Z.le_gt_cases d c).
  - (* a byte of data *)
    rewrite dcw_app_new by lia.
    assert (Hi : forall i, i = wn + c - d -> Znth i full = Znth (c - d) data).
    { intros i ->. unfold full. rewrite dcw_full_mid by lia. rewrite Znth_sublist by lia. f_equal; lia. }
    destruct (wn + dist =? ws) eqn:E1.
    + destruct (d <=? 0) eqn:E2; [lia|]. apply Hi. lia.
    + destruct (d <=? wn + dist) eqn:E2; [|lia]. apply Hi. lia.
  - rewrite dcw_app_old by (rewrite Zlength_app in *; lia).
    destruct (wn + dist =? ws) eqn:E1.
    + destruct (d <=? 0) eqn:E2; [lia|]. unfold full. rewrite dcw_full_lo by lia.
      rewrite <- Hwa by (rewrite Zlength_app in Hd; lia). unfold dcw_wa; fold c.
      destruct (d - c <=? wn) eqn:E3; [|lia]. f_equal; lia.
    + destruct (d <=? wn + dist) eqn:E2.
      * unfold full. rewrite dcw_full_lo by lia.
        rewrite <- Hwa by (rewrite Zlength_app in Hd; lia). unfold dcw_wa; fold c.
        destruct (d - c <=? wn) eqn:E3; [|lia]. f_equal; lia.
      * assert (wh = ws) by (destruct (Z.lt_ge_cases wh ws); [rewrite Hval in * by lia; rewrite Zlength_app in Hd|]; lia).
        unfold full. rewrite dcw_full_hi by lia.
        rewrite <- Hwa by (rewrite Zlength_app in Hd; lia). unfold dcw_wa; fold c.
        destruct (d - c <=? wn) eqn:E3; [lia|]. f_equal; lia.
Qed.

Lemma dcw_ok_of_post : forall G s ob, i_wsize s = 2 ^ i_wbits s ->
  dcw_post (i_wsize s) (i_wnext s) (i_whave s) (i_wdata s) ob -> win_ok G s ob.
Proof.
  intros G s ob Hws [Hwh Hwa]. right. split; [exact Hws|]. split; [exact Hwh|]. exact Hwa.
Qed.

(* updatewindow on an allocated window *)
Lemma dcw_core : forall G s ob d, 0 < i_wsize s -> i_wsize s = 2 ^ i_wbits s ->
  dcw_pre (i_wsize s) (i_wnext s) (i_whave s) (i_wdata s) ob -> win_ok G (updatewindow s d) (ob ++ d).
Proof.
  intros G s ob d Hpos Hws Hpre. unfold updatewindow.
  destruct (i_wsize s =? 0) eqn:E; [lia|]. cbv zeta.
  destruct (i_wsize s <=? Zlength d) eqn:E1.
  - apply dcw_ok_of_post; cbn [i_wsize i_wbits i_wnext i_whave i_wdata set_i_wdata set_i_whave set_i_wnext];
      [exact Hws|]. apply dcw_br1; lia.
  - destruct (negb (Zlength d - Z.min (i_wsize s - i_wnext s) (Zlength d) =? 0)) eqn:E2.
    + apply dcw_ok_of_post; cbn [i_wsize i_wbits i_wnext i_whave i_wdata set_i_wdata set_i_whave set_i_wnext];
        [exact Hws|]. eapply dcw_br2; [exact Hpre | lia | lia].
    + apply dcw_ok_of_post; cbn [i_wsize i_wbits i_wnext i_whave i_wdata set_i_wdata set_i_whave set_i_wnext];
        [exact Hws|]. apply dcw_br3; [exact Hpre | lia | lia].
Qed.

Lemma dcw_win : forall G s ob d, swf s -> win_ok G s ob -> win_ok G (updatewindow s d) (ob ++ d).
Proof.
  intros G s ob d Hsw Hwin.
  pose proof (sw_wbits _ Hsw) as Hwb. pose proof (sw_whave _ Hsw) as Hwh0.
  pose proof (sw_wnext _ Hsw) as Hwn0. pose proof (sw_wvalid _ Hsw) as Hwv0.
  destruct (sw_wdata _ Hsw) as [Hwd0 _].
  assert (Hp : 0 < 2 ^ i_wbits s) by (apply Z.pow_pos_nonneg; lia).
  destruct Hwin as [[Hz Hob] | [Hws [Hwh Hwa]]].
  - subst ob.
    set (s0 := set_i_whave (set_i_wnext (set_i_wsize s (2 ^ i_wbits s)) 0) 0).
    assert (Hs0 : updatewindow s d = updatewindow s0 d).
    { unfold updatewindow at 1. rewrite Hz. cbn zeta. fold s0. unfold updatewindow.
      cbn [s0 i_wsize set_i_whave set_i_wnext set_i_wsize].
      destruct (2 ^ i_wbits s =? 0) eqn:E; [lia|]. reflexivity. }
    rewrite Hs0. apply dcw_core; unfold s0; cbn [i_wsize i_wbits i_wnext i_whave i_wdata set_i_whave set_i_wnext set_i_wsize];
      try lia.
    unfold dcw_pre. rewrite Zlength_nil.
    repeat split; lia.
  - apply dcw_core; [lia | exact Hws |].
    unfold dcw_pre. repeat split; try lia. exact Hwa.
Qed.
