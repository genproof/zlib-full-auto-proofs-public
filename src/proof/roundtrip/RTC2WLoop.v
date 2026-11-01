(** * compress2_z for any sizes with destLen = compressBound_z(n) (RTC2W.c2w_bound_stmt), from the deflateBound
    accounting of compress2_z's loop (LawFactsC2W.c2_facts).

    With a bound below 2^32, compress2_z's first deflate() call is offered all the data and all of the output
    space, and ends the stream.  Above, the loop is an induction on the input not consumed plus the output not
    produced: every call returns Z_OK with progress or Z_STREAM_END, and the output space never runs out before
    the end of the stream. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTC2W.
Require Zlib.proof.deflate.LawFactsC2W.
Import ListNotations.
Local Open Scope Z_scope.

(** compressBound_z(n) is at least n, and positive. *)
Lemma c2w_cb_ge : forall n, 0 <= n <= UMAX64 -> n <= compressBound_z n.
Proof.
  intros n Hn. unfold compressBound_z.
  destruct (u64 (n + Z.shiftr n 12 + Z.shiftr n 14 + Z.shiftr n 25 + 13) <? n) eqn:E.
  - lia.
  - apply Z.ltb_ge in E. lia.
Qed.

Lemma c2w_cb_pos : forall n, 0 <= n <= UMAX64 -> 0 < compressBound_z n.
Proof.
  intros n Hn. destruct (Z.eq_dec n 0) as [->|Hn0]; [vm_compute; reflexivity|].
  pose proof (c2w_cb_ge n Hn). lia.
Qed.

(** deflateResetKeep and deflateReset of a state whose status is INIT_STATE (deflateStateCheck accepts it)
    return Z_OK whenever the model run is defined. *)
Lemma c2w_resetkeep_ok : forall s z s' z' r,
  d_status s = INIT_STATE -> c_deflateResetKeep s z = Some (s', z', r) -> r = Z_OK.
Proof.
  intros s0 z0 s' z1 r Hs Er. unfold c_deflateResetKeep, bad_state, c_deflateStateCheck in Er.
  rewrite Hs in Er. cbn in Er.
  repeat match type of Er with
  | context [if ?x then _ else _] => destruct x; cbn in Er; try discriminate
  end;
  repeat match type of Er with
  | context [bind ?x _] => destruct x as [[[? ?] ?]|]; cbn in Er; try discriminate
  | context [bind ?x _] => destruct x as [[? ?]|]; cbn in Er; try discriminate
  | context [bind ?x _] => destruct x; cbn in Er; try discriminate
  end; inversion Er; reflexivity.
Qed.

Lemma c2w_reset_ok : forall s z s' z' r,
  d_status s = INIT_STATE -> c_deflateReset s z = Some (s', z', r) -> r = Z_OK.
Proof.
  intros s0 z0 s' z1 r Hs Er. unfold c_deflateReset in Er.
  destruct (c_deflateResetKeep s0 z0) as [[[s2 z2] r2]|] eqn:EK; cbn in Er; [|discriminate].
  pose proof (c2w_resetkeep_ok _ _ _ _ _ Hs EK); subst r2. cbn in Er.
  destruct (c_lm_init s2); cbn in Er; inversion Er; reflexivity.
Qed.

(** deflateInit2_(level, 8, 15, 8, 0) with level -1..9 returns Z_OK or Z_MEM_ERROR: the parameters are
    accepted, a failed allocation gives Z_MEM_ERROR, and deflateReset of the fresh state returns Z_OK.  The
    initial state, deflateReset and deflateEnd are abstracted before the simplification: the initial state holds
    the window and hash tables as lists of 2^15 and more elements, which the kernel must not unfold. *)
Lemma c2w_init_code : forall level a1 a2 a3 a4 a5 z os z' code,
  -1 <= level <= 9 ->
  c_deflateInit2_ true true false level 8 15 8 0 a1 a2 a3 a4 a5 z = Some (os, z', code) ->
  code = Z_OK \/ code = Z_MEM_ERROR.
Proof.
  intros level a1 a2 a3 a4 a5 z os z' code Hl E.
  assert (HI : forall w wb hb lb, d_status (init_dstate w wb hb lb) = INIT_STATE) by reflexivity.
  pose proof c2w_reset_ok as HR.
  unfold c_deflateInit2_ in E.
  revert E HI HR. generalize init_dstate as IDS. generalize c_deflateReset as RST.
  generalize c_deflateEnd as DE. intros DE RST IDS E HI HR.
  assert (C : ((if level =? Z_DEFAULT_COMPRESSION then 6 else level) <? 0) ||
              ((if level =? Z_DEFAULT_COMPRESSION then 6 else level) >? 9) = false).
  { unfold Z_DEFAULT_COMPRESSION. rewrite !Z.gtb_ltb. destruct (Z.eqb_spec level (-1)); [reflexivity|].
    destruct (Z.ltb_spec level 0), (Z.ltb_spec 9 level); cbn; try reflexivity; lia. }
  cbn [negb orb andb Z.ltb Z.gtb Z.eqb Z.compare Pos.compare Pos.compare_cont MAX_MEM_LEVEL Z_DEFLATED Z_FIXED] in E.
  rewrite ?orb_false_r, ?orb_false_l in E.
  revert C E. generalize (if level =? Z_DEFAULT_COMPRESSION then 6 else level) as lv. intros lv C E.
  rewrite C in E.
  destruct a1; cbn [negb] in E; [|inversion E; right; reflexivity].
  destruct (a2 && a3 && a4 && a5); cbn [negb] in E.
  - left. cbn [bind] in E.
    destruct (RST _ _) as [[[s1 z1] r1]|] eqn:ER; cbn in E; [|discriminate].
    inversion E; subst. eapply HR; [|exact ER]. cbn. apply HI.
  - cbn [bind] in E. destruct (DE _ _) as [[[o1 z1] r1]|]; cbn in E; [|discriminate].
    inversion E; right; reflexivity.
Qed.

Section Loop.
Variables (Bpre : LawFacts.bpre_inv) (Brun : LawFacts.brun_inv).
Hypothesis BF : LawFactsC2W.c2_facts Bpre Brun.
Variable src : list Z.
Hypothesis Hsrc : rbytes src.
Variable tout0 : Z.

Let n := Zlength src.
Variable b : Z.
Hypothesis Hbig : 4294967295 < b.

(** The invariant of compress2_z's loop before an iteration, with the state [s], the stream [z], the
    destination bytes [left] and source bytes [srcleft] not given yet, and the output [out] so far: the
    accounting [Brun] holds at the position [z_next_in z] in the data; the input consumed, offered and not
    given add up to n; once Z_FINISH was given no source is left; the output so far, the output space offered
    and the destination left add up to b; and an exhausted output space leaves destination bytes to give. *)
Definition c2w_inv (s : dstate) (z : strm) (left srcleft : Z) (out : list Z) : Prop :=
  exists fin,
    Brun n b (z_next_in z) fin s (z_total_in z) (z_total_out z) (z_adler z) /\
    0 <= z_avail_in z <= umax /\ 0 <= srcleft /\ z_next_in z + z_avail_in z + srcleft = n /\
    (fin = true -> srcleft = 0) /\
    0 <= z_avail_out z <= umax /\ 0 <= left /\ left + z_avail_out z + Zlength out = b /\
    Zlength out = z_total_out z - tout0 /\ 0 <= tout0 /\
    (z_avail_out z = 0 -> 0 < left).

(** The measure of the loop's termination: input not consumed and output not produced. *)
Definition c2w_meas (z : strm) : Z := (n - z_next_in z) + (b - z_total_out z).

Lemma c2w_meas_nonneg : forall s z left srcleft out, c2w_inv s z left srcleft out -> 0 <= c2w_meas z.
Proof.
  intros s z left srcleft out (fin & HB & _).
  destruct (LawFactsC2W.c2f_range _ _ BF _ _ _ _ _ _ _ _ HB). unfold c2w_meas. lia.
Qed.

(** One iteration: what c2_give offers. *)
Lemma c2w_give : forall s z left srcleft out z1 left' srcleft' flush,
  c2w_inv s z left srcleft out ->
  c2_give src z left srcleft = (z1, left', srcleft', flush) ->
  exists ao ai,
    z1 = mkST src (z_next_in z) ai (z_total_in z) [] ao (z_total_out z) (z_adler z) (z_msg z) /\
    0 < ao <= umax /\ 0 <= left' /\ left' + ao = left + z_avail_out z /\
    0 <= ai <= umax /\ 0 <= srcleft' <= srcleft /\ srcleft' + ai = srcleft + z_avail_in z /\
    (srcleft' <> 0 -> 0 < ai) /\
    flush = (if srcleft' =? 0 then Z_FINISH else Z_NO_FLUSH).
Proof.
  intros s z left srcleft out z1 left' srcleft' flush (fin & HB & Hai & Hsl & Hin & Hfin & Hao & Hl & Hout & _ & _ & Hfull) Hg.
  unfold c2_give in Hg.
  assert (Hu : umax = 4294967295) by reflexivity.
  destruct (z_avail_out z =? 0) eqn:Eo, (z_avail_in z =? 0) eqn:Ei;
    inversion Hg; subst; clear Hg;
    rewrite ?Z.eqb_eq, ?Z.eqb_neq in Eo, Ei;
    do 2 eexists; (split; [reflexivity|]);
    repeat split; try lia;
    repeat match goal with |- context [Z.min ?x ?y] => pose proof (Z.min_spec x y) end;
    try lia.
Qed.

(** One iteration: the call returns Z_OK (and the invariant holds again, with a smaller measure) or
    Z_STREAM_END (and the output fits). *)
Lemma c2w_step : forall s z left srcleft out z1 left' srcleft' flush,
  c2w_inv s z left srcleft out ->
  c2_give src z left srcleft = (z1, left', srcleft', flush) ->
  exists s' z' code,
    c_deflate s z1 flush = Some (s', z', code) /\ d_gzhead s' = d_gzhead s /\ c2_step z1 z' /\
    (code = Z_OK \/ code = Z_STREAM_END) /\
    (code = Z_OK -> c2w_inv s' z' left' srcleft' (out ++ z_out z') /\ c2w_meas z' < c2w_meas z) /\
    (code = Z_STREAM_END -> Zlength (out ++ z_out z') <= b).
Proof.
  intros s z left srcleft out z1 left' srcleft' flush J Hg.
  destruct (c2w_give _ _ _ _ _ _ _ _ _ J Hg)
    as (ao & ai & -> & Hao & Hl' & Hleft & Hai & Hsl' & Hsrc' & Hpos & Hfl).
  destruct J as (fin & HB & Hai0 & Hsl & Hin & Hfin & Hao0 & Hl & Hout & Hlen & Ht0 & Hfull).
  destruct (LawFactsC2W.c2f_range _ _ BF _ _ _ _ _ _ _ _ HB) as [Hp Ht].
  assert (Hu : umax = 4294967295) by reflexivity.
  assert (Hflush : flush = Z_NO_FLUSH \/ flush = Z_FINISH).
  { rewrite Hfl. destruct (srcleft' =? 0); auto. }
  assert (Hff : fin = true -> flush = Z_FINISH).
  { intros Ef. specialize (Hfin Ef). rewrite Hfl. replace srcleft' with 0 by lia. reflexivity. }
  assert (Hfn : flush = Z_FINISH -> srcleft' = 0).
  { rewrite Hfl. destruct (Z.eqb_spec srcleft' 0); auto. unfold Z_NO_FLUSH, Z_FINISH. lia. }
  assert (Hnf : flush = Z_NO_FLUSH -> 0 < ai).
  { rewrite Hfl. destruct (Z.eqb_spec srcleft' 0); [unfold Z_NO_FLUSH, Z_FINISH; lia|]. auto. }
  destruct (LawFactsC2W.c2f_split _ _ BF n b (z_next_in z) fin s (z_total_in z) (z_total_out z) (z_adler z)
              src (z_next_in z) ai ao flush (z_msg z) HB Hflush Hff Hsrc ltac:(lia) ltac:(lia)
              ltac:(fold n; lia) ltac:(lia) ltac:(intros E; specialize (Hfn E); lia) ltac:(lia))
    as (s' & z' & code & E & Hgz & _ & Hai' & Hni' & Hao' & Hzo & Hby & Hti' & Hto' & Htb &
        Hcode & Hbuf & Hprog & Hfullb & _ & Hend & Hrun).
  exists s', z', code. split; [exact E|]. split; [exact Hgz|].
  split; [unfold c2_step; cbn [z_avail_in z_next_in z_avail_out]; auto|].
  assert (Hc : code = Z_OK \/ code = Z_STREAM_END).
  { destruct Hcode as [Hc|[Hc|Hc]]; auto. exfalso.
    destruct (Hbuf Hc) as [Ha|[Ha Hf]]; [lia|]. specialize (Hnf Hf). lia. }
  split; [exact Hc|]. split.
  - intros Hok.
    assert (Hne : code <> Z_STREAM_END) by (rewrite Hok; unfold Z_OK, Z_STREAM_END; lia).
    specialize (Hrun Hne). specialize (Hfullb Hbig Hok).
    assert (Hpr : 0 < (ai - z_avail_in z') + (ao - z_avail_out z')).
    { apply Hprog; [exact Hok|lia|]. destruct Hflush as [Hf|Hf]; [left; auto|right; exact Hf]. }
    clear Hcode Hc Hbuf Hprog Hend Hflush Hfl Hff Hnf Hpos Hfin Hfull Hg E.
    split.
    + exists (flush =? Z_FINISH).
      rewrite Hni'. split; [exact Hrun|].
      rewrite Zlength_app.
      split; [lia|]. split; [lia|]. split; [lia|].
      split; [intros Ef; apply Hfn, Z.eqb_eq, Ef|].
      do 5 (split; [lia|]).
      intros H0. specialize (Hfullb H0). lia.
    + unfold c2w_meas. lia.
  - intros _. clear Hcode Hc Hbuf Hprog Hend Hflush Hfl Hff Hnf Hpos Hfin Hfull Hg E.
    rewrite Zlength_app. lia.
Qed.

(** The loop's runs exist from every state of the invariant. *)
Lemma c2w_run_exists : forall (k : nat) s z left srcleft out,
  c2w_inv s z left srcleft out -> (Z.to_nat (c2w_meas z) < k)%nat ->
  exists err out' sf zf, c2_run src s z left srcleft out err out' sf zf.
Proof.
  induction k as [|k IH]; intros s z left srcleft out J Hk; [lia|].
  destruct (c2_give src z left srcleft) as [[[z1 left'] srcleft'] flush] eqn:Hg.
  destruct (c2w_step _ _ _ _ _ _ _ _ _ J Hg) as (s' & z' & code & E & Hgz & Hst & Hc & Hok & _).
  destruct Hc as [Hc|Hc].
  - subst code. destruct (Hok eq_refl) as [J' Hm].
    pose proof (c2w_meas_nonneg _ _ _ _ _ J').
    destruct (IH s' z' left' srcleft' (out ++ z_out z') J' ltac:(lia)) as (err & out' & sf & zf & R).
    exists err, out', sf, zf. eapply c2r_more; eauto.
  - exists code, (out ++ z_out z'), s', z'. eapply c2r_last; eauto.
    subst code. unfold Z_OK, Z_STREAM_END. lia.
Qed.

(** Every run of the loop from a state of the invariant ends with Z_STREAM_END and an output that fits. *)
Lemma c2w_run_ends : forall s z left srcleft out err out' sf zf,
  c2_run src s z left srcleft out err out' sf zf -> c2w_inv s z left srcleft out ->
  err = Z_STREAM_END /\ Zlength out' <= b.
Proof.
  induction 1 as [s z left srcleft out z1 left' srcleft' flush s' z' err out' sf zf Hg E Hgz Hst R IH
                 |s z left srcleft out z1 left' srcleft' flush s' z' err Hg E Hgz Hst Hne];
    intros J.
  - destruct (c2w_step _ _ _ _ _ _ _ _ _ J Hg) as (s2 & z2 & code & E2 & _ & _ & _ & Hok & _).
    rewrite E in E2. inversion E2; subst s2 z2 code.
    exact (IH (proj1 (Hok eq_refl))).
  - destruct (c2w_step _ _ _ _ _ _ _ _ _ J Hg) as (s2 & z2 & code & E2 & _ & _ & Hc & _ & Hend).
    rewrite E in E2. inversion E2; subst s2 z2 code.
    destruct Hc as [Hc|Hc]; [contradiction|]. split; [exact Hc|]. exact (Hend Hc).
Qed.

End Loop.

(** A bound below 2^32: the first call is offered all the data and all of the output space, and ends the
    stream; it is the only call of every run. *)
Section Small.
Variables (Bpre : LawFacts.bpre_inv) (Brun : LawFacts.brun_inv).
Hypothesis BF : LawFactsC2W.c2_facts Bpre Brun.
Variable src : list Z.
Hypothesis Hsrc : rbytes src.

Let n := Zlength src.
Variable b : Z.
Hypothesis Hsmall : b <= 4294967295.
Hypothesis Hnb : n <= b.

Lemma c2w_small : forall s tin adler msg,
  Brun n b 0 false s tin 0 adler ->
  let z := mkST src 0 0 tin [] 0 0 adler msg in
  (exists err out sf zf, c2_run src s z b n [] err out sf zf) /\
  (forall err out sf zf, c2_run src s z b n [] err out sf zf -> err = Z_STREAM_END /\ Zlength out <= b).
Proof.
  intros s tin adler msg HB z.
  assert (Hn0 : 0 <= n) by apply Zlength_nonneg.
  assert (Hu : umax = 4294967295) by reflexivity.
  assert (Hg : c2_give src z b n = (mkST src 0 n tin [] b 0 adler msg, 0, 0, Z_FINISH)).
  { unfold c2_give, z. cbn [z_avail_out z_avail_in z_next_in z_total_in z_total_out z_adler z_msg Z.eqb].
    rewrite (Z.min_l b umax) by lia. rewrite (Z.min_l n umax) by lia. rewrite !Z.sub_diag. reflexivity. }
  destruct (LawFactsC2W.c2f_split _ _ BF n b 0 false s tin 0 adler src 0 n b Z_FINISH msg HB
              ltac:(right; reflexivity) ltac:(discriminate) Hsrc ltac:(lia) ltac:(lia) ltac:(fold n; lia)
              ltac:(lia) ltac:(intros _; lia) ltac:(lia))
    as (s' & z' & code & E & Hgz & _ & Hai' & Hni' & Hao' & Hzo & _ & _ & _ & _ & _ & _ & _ & _ & Hone & _).
  specialize (Hone eq_refl eq_refl eq_refl ltac:(lia)). subst code.
  assert (Hst : c2_step (mkST src 0 n tin [] b 0 adler msg) z').
  { unfold c2_step; cbn [z_avail_in z_next_in z_avail_out]. lia. }
  split.
  - exists Z_STREAM_END, ([] ++ z_out z'), s', z'. eapply c2r_last; eauto.
    unfold Z_OK, Z_STREAM_END. lia.
  - intros err out sf zf R. inversion R as [s0 z0 l0 sl0 o0 z1 l1 sl1 f1 s1 z2 e1 o1 sf1 zf1 Hg1 E1
                                           |s0 z0 l0 sl0 o0 z1 l1 sl1 f1 s1 z2 e1 Hg1 E1]; subst.
    + rewrite Hg in Hg1. injection Hg1 as <- <- <- <-. rewrite E in E1. discriminate E1.
    + rewrite Hg in Hg1. injection Hg1 as <- <- <- <-. rewrite E in E1. injection E1 as <- <- <-.
      split; [reflexivity|]. rewrite Zlength_app, Zlength_nil, Hzo. lia.
Qed.

End Small.

Theorem c2w_bound : LawFactsC2W.c2_facts_stmt -> c2w_bound_stmt.
Proof.
  intros (Bpre & Brun & BF) src level a1 a2 a3 a4 a5 z0 Hsrc Hn Hl.
  set (n := Zlength src).
  assert (Hn0 : 0 <= n) by apply Zlength_nonneg.
  assert (HU : n <= UMAX64) by (unfold UMAX64; lia).
  pose proof (c2w_cb_ge n (conj Hn0 HU)) as Hnb.
  destruct (LawFactsC2W.c2f_init _ _ BF level a1 a2 a3 a4 a5 z0 Hl) as [[[[os z1] code] Ei] Hinit].
  pose proof (c2w_init_code level a1 a2 a3 a4 a5 z0 os z1 code Hl Ei) as Hcode.
  (* after a successful deflateInit2_: the accounting at the start, nothing written *)
  assert (Start : forall s, os = Some s -> code = Z_OK ->
            d_gzhead s = None /\ z_total_out z1 = 0 /\
            Brun n (compressBound_z n) 0 false s (z_total_in z1) (z_total_out z1) (z_adler z1)).
  { intros s Es Ec. destruct (Hinit os z1 code Ei Ec) as (s1 & Es1 & Hgz & HP).
    rewrite Es in Es1. inversion Es1; subst s1.
    destruct (LawFactsC2W.c2f_start _ _ BF level s _ _ _ n HP Hl ltac:(lia)) as [Ht HB].
    auto. }
  (* the runs of the loop from the start *)
  assert (Runs : forall s, os = Some s -> code = Z_OK ->
    let z := mkST src 0 0 (z_total_in z1) [] 0 (z_total_out z1) (z_adler z1) (z_msg z1) in
    (exists err out sf zf, c2_run src s z (compressBound_z n) n [] err out sf zf) /\
    (forall err out sf zf, c2_run src s z (compressBound_z n) n [] err out sf zf ->
       err = Z_STREAM_END /\ Zlength out <= compressBound_z n)).
  { intros s Es Ec z. destruct (Start s Es Ec) as (_ & Ht & HB).
    destruct (Z_le_gt_dec (compressBound_z n) 4294967295) as [Hs|Hb].
    - unfold z. rewrite Ht in HB |- *.
      exact (c2w_small Bpre Brun BF src Hsrc (compressBound_z n) Hs Hnb s _ _ _ HB).
    - assert (J : c2w_inv Brun src (z_total_out z1) (compressBound_z n) s z (compressBound_z n) n []).
      { exists false. unfold z. cbn [z_next_in z_avail_in z_avail_out z_total_in z_total_out z_adler].
        split; [exact HB|].
        destruct (LawFactsC2W.c2f_range _ _ BF _ _ _ _ _ _ _ _ HB) as [_ Hto].
        assert (Hu : umax = 4294967295) by reflexivity.
        rewrite Zlength_nil. repeat split; try lia; discriminate. }
      split.
      + exact (c2w_run_exists Bpre Brun BF src Hsrc (z_total_out z1) (compressBound_z n) ltac:(lia)
                 _ _ _ _ _ _ J (Nat.lt_succ_diag_r _)).
      + intros err out sf zf R.
        exact (c2w_run_ends Bpre Brun BF src Hsrc (z_total_out z1) (compressBound_z n) ltac:(lia)
                 _ _ _ _ _ _ _ _ _ R J). }
  split.
  - destruct (Z.eq_dec code Z_OK) as [Ec|Ec].
    + destruct os as [s|].
      2:{ destruct (Hinit None z1 code Ei Ec) as (s1 & Es1 & _). discriminate. }
      destruct (Start s eq_refl Ec) as [Hgz _].
      destruct (proj1 (Runs s eq_refl Ec)) as (err & out & sf & zf & R).
      exists (if err =? Z_STREAM_END then Z_OK else err), out.
      exists (Some s), z1, code. split; [exact Ei|]. right. split; [exact Ec|].
      exists s, err, sf, zf. auto.
    + exists code, []. exists os, z1, code. split; [exact Ei|]. left. auto.
  - intros r out (os' & z1' & code' & Ei' & Hr).
    rewrite Ei in Ei'. inversion Ei'; subst os' z1' code'. clear Ei'.
    destruct Hr as [(Ec & -> & ->)|(Ec & s & err & sf & zf & Es & Hgz & R & ->)].
    + split; [destruct Hcode; [contradiction|auto]|]. rewrite Zlength_nil. pose proof (c2w_cb_pos n). lia.
    + destruct (proj2 (Runs s Es Ec) err out sf zf R) as [He Hle].
      rewrite He. split; [left; reflexivity|exact Hle].
Qed.
