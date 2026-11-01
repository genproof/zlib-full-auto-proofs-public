(** * Proof of RTC2WFinal.c2w_final_stmt: compress2_z's output for any sizes is the zlib stream of its data

    Along compress2_z's loop (RTC2.c2_run) from deflateInit2_'s state: each call is the call of
    LawFactsC2W.c2f_split (the model is a function: same stream, same result), which gives its counters and
    keeps the accounting invariant; InSlice.deflate_slice moves the call to the piece offered, the object of
    RTK7.kf7_deflate, which keeps the round-trip invariant and gives RTFinal.dfinal at Z_STREAM_END. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTC2WFinal.
Require Zlib.proof.roundtrip.RTK7.
Require Zlib.proof.deflate.LawFactsC2W.
Require Zlib.proof.deflate.InSlice.
Import ListNotations.
Local Open Scope Z_scope.

(** compressBound_z(n) is positive (at least 13 for n = 0, at least n otherwise), at least n and at most
    2^64 - 1. *)
Lemma c2f_cb_range : forall n, 0 <= n <= 18446744073709551615 ->
  0 < compressBound_z n <= 18446744073709551615 /\ n <= compressBound_z n.
Proof.
  intros n Hn. unfold compressBound_z.
  destruct (Z.eq_dec n 0) as [->|Hn0].
  { assert (E : compressBound_z 0 = 13) by (vm_compute; reflexivity). unfold compressBound_z in E. lia. }
  destruct (u64 (n + Z.shiftr n 12 + Z.shiftr n 14 + Z.shiftr n 25 + 13) <? n) eqn:E.
  - unfold UMAX64; lia.
  - apply Z.ltb_ge in E. unfold u64 in *.
    pose proof (Z.mod_pos_bound (n + Z.shiftr n 12 + Z.shiftr n 14 + Z.shiftr n 25 + 13)
                  18446744073709551616 ltac:(lia)). lia.
Qed.

(** The stream of one call cut down to the piece offered: the piece is the whole input object. *)
Lemma c2f_zslice_call : forall src ni ai tin ao tout adler msg,
  InSlice.zslice ni ai (mkST src ni ai tin [] ao tout adler msg) =
  rzcall (sublist ni (ni + ai) src) 0 ai tin ao tout adler msg.
Proof.
  intros. unfold InSlice.zslice, rzcall. cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out
    z_total_out z_adler z_msg]. rewrite Z.sub_diag. reflexivity.
Qed.

Section Loop.
Context (K : rinv) (HK : RTK7.kfacts7 K).
Context (Bpre : LawFacts.bpre_inv) (Brun : LawFacts.brun_inv) (BF : LawFactsC2W.c2_facts Bpre Brun).
Context (src : list Z) (Hsrc : rbytes src) (Hn : Zlength src <= 9223372036854775807).
Context (tout0 b : Z) (Hb : b <= 18446744073709551615) (Hbn : Zlength src <= b).

Let n := Zlength src.

(** The joint invariant of compress2_z's loop before an iteration, with the state [s], the stream [z], the
    destination bytes [left] and source bytes [srcleft] not given yet, and the output [out] so far:
    - the accounting [Brun] at the position [z_next_in z] in the data, the input consumed, offered and not
      given adding up to n, the output so far, the output space offered and the destination left adding up
      to b, an exhausted output space leaving destination bytes to give, the output so far the bytes counted
      by total_out since the start [tout0];
    - the round-trip invariant [K] on the data consumed (the prefix up to next_in) and the output so far,
      windowBits 15 and no gzip header; once Z_FINISH was given ([F = Some R]) no source is left and R is the
      input still offered;
    - with a bound below 2^32, the loop is still before its first call (which is then offered all of the data
      and all of the output space, and ends the stream). *)
Definition c2f_inv (s : dstate) (z : strm) (left srcleft : Z) (out : list Z) : Prop :=
  exists fin F,
    Brun n b (z_next_in z) fin s (z_total_in z) (z_total_out z) (z_adler z) /\
    0 <= z_avail_in z <= umax /\ 0 <= srcleft /\ z_next_in z + z_avail_in z + srcleft = n /\
    (fin = true -> srcleft = 0) /\
    0 <= z_avail_out z <= umax /\ 0 <= left /\ left + z_avail_out z + Zlength out = b /\
    (z_avail_out z = 0 -> 0 < left) /\ Zlength out = z_total_out z - tout0 /\ 0 <= tout0 /\
    d_w_bits s = 15 /\ d_gzhead s = None /\
    K [] 1 (sublist 0 (z_next_in z) src) out F s (z_total_in z) (z_total_out z) (z_adler z) /\
    (forall R, F = Some R -> srcleft = 0 /\ R = sublist (z_next_in z) (z_next_in z + z_avail_in z) src) /\
    (b <= umax -> z_next_in z = 0 /\ fin = false /\ z_avail_in z = 0 /\ z_avail_out z = 0 /\
                  z_total_out z = tout0).

(** What c2_give offers. *)
Lemma c2f_give : forall z left srcleft z1 left' srcleft' flush,
  0 <= z_avail_in z <= umax -> 0 <= srcleft -> 0 <= z_avail_out z <= umax -> 0 <= left ->
  (z_avail_out z = 0 -> 0 < left) ->
  c2_give src z left srcleft = (z1, left', srcleft', flush) ->
  exists ao ai,
    z1 = mkST src (z_next_in z) ai (z_total_in z) [] ao (z_total_out z) (z_adler z) (z_msg z) /\
    0 < ao <= umax /\ 0 <= left' /\ left' + ao = left + z_avail_out z /\
    0 <= ai <= umax /\ 0 <= srcleft' <= srcleft /\ srcleft' + ai = srcleft + z_avail_in z /\
    (srcleft' <> 0 -> 0 < ai) /\ (srcleft = 0 -> ai = z_avail_in z) /\
    (z_avail_out z = 0 -> left <= umax -> left' = 0) /\ (z_avail_in z = 0 -> srcleft <= umax -> srcleft' = 0) /\
    flush = (if srcleft' =? 0 then Z_FINISH else Z_NO_FLUSH).
Proof.
  intros z left srcleft z1 left' srcleft' flush Hai Hsl Hao Hl Hfull Hg.
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

(** One iteration from the invariant: Z_OK keeps it; any other code is Z_STREAM_END, and the output is then
    the zlib stream of the data. *)
Lemma c2f_step : forall s z left srcleft out z1 left' srcleft' flush s' z' code,
  c2f_inv s z left srcleft out ->
  c2_give src z left srcleft = (z1, left', srcleft', flush) ->
  c_deflate s z1 flush = Some (s', z', code) ->
  (code = Z_OK -> c2f_inv s' z' left' srcleft' (out ++ z_out z')) /\
  (code <> Z_OK -> code = Z_STREAM_END /\ dfinal [] 1 15 None src (out ++ z_out z')).
Proof.
  intros s z left srcleft out z1 left' srcleft' flush s' z' code J Hg Ed.
  destruct J as (fin & F & HB & Hai0 & Hsl & Hin & Hfin & Hao0 & Hl & Hout & Hfull & Hlo & Ht0 & Hwb & Hgz & HK0 & HF & Hsmall).
  destruct (c2f_give _ _ _ _ _ _ _ Hai0 Hsl Hao0 Hl Hfull Hg)
    as (ao & ai & -> & Hao & Hl' & Hleft & Hai & Hsl' & Hsrc' & Hpos & Hai_eq & Hlo0 & Hsl0 & Hfl).
  destruct (LawFactsC2W.c2f_range _ _ BF _ _ _ _ _ _ _ _ HB) as [Hp Ht].
  assert (Hu : umax = 4294967295) by reflexivity.
  set (ni := z_next_in z) in *.
  assert (Hflush : flush = Z_NO_FLUSH \/ flush = Z_FINISH).
  { rewrite Hfl. destruct (srcleft' =? 0); auto. }
  assert (Hff : fin = true -> flush = Z_FINISH).
  { intros Ef. specialize (Hfin Ef). rewrite Hfl. replace srcleft' with 0 by lia. reflexivity. }
  assert (Hfn : flush = Z_FINISH -> srcleft' = 0).
  { rewrite Hfl. destruct (Z.eqb_spec srcleft' 0); auto. unfold Z_NO_FLUSH, Z_FINISH. lia. }
  assert (Hnf : flush = Z_NO_FLUSH -> 0 < ai).
  { rewrite Hfl. destruct (Z.eqb_spec srcleft' 0); [unfold Z_NO_FLUSH, Z_FINISH; lia|]. auto. }
  assert (Hlen : ni + ai <= Zlength src) by (fold n; lia).
  destruct (LawFactsC2W.c2f_split _ _ BF n b ni fin s (z_total_in z) (z_total_out z) (z_adler z)
              src ni ai ao flush (z_msg z) HB Hflush Hff Hsrc ltac:(lia) ltac:(lia) Hlen
              ltac:(lia) ltac:(intros E; specialize (Hfn E); lia) ltac:(lia))
    as (s2 & z2 & code2 & E & Hgz' & Hzin & Hai' & Hni' & Hao' & Hzo & Hby & Hti' & Hto' & Htb &
        Hcode & Hbuf & _ & Hfullb & Hone & Hend & Hrun).
  rewrite Ed in E. injection E as <- <- <-.
  assert (Hnb : code <> Z_BUF_ERROR).
  { intros Hc. destruct (Hbuf Hc) as [Ha|[Ha Hf]]; [lia|]. specialize (Hnf Hf). lia. }
  (* the call on the piece offered *)
  set (inb := sublist ni (ni + ai) src).
  assert (Hinb : Zlength inb = ai) by (unfold inb; rewrite Zlength_sublist by lia; lia).
  assert (Esl : c_deflate s (InSlice.zslice ni ai (mkST src ni ai (z_total_in z) [] ao (z_total_out z)
                  (z_adler z) (z_msg z))) flush = Some (s', InSlice.zslice ni ai z', code)).
  { apply InSlice.deflate_slice; [cbn; lia.. | exact Ed]. }
  rewrite c2f_zslice_call in Esl. fold inb in Esl.
  assert (Esl' : c_deflate s (rzcall inb 0 (Zlength inb) (z_total_in z) ao (z_total_out z) (z_adler z) (z_msg z))
                   flush = Some (s', InSlice.zslice ni ai z', code)) by (rewrite Hinb; exact Esl).
  assert (Hrc : rcall_ok inb ao (z_total_in z) (z_total_out z) (InSlice.zslice ni ai z')).
  { unfold rcall_ok, InSlice.zslice.
    cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler z_msg].
    rewrite Hzin, Hinb. fold inb. split; [reflexivity|].
    clear -Hai' Hni' Hti' Hao' Hzo Hto' Hby. repeat split; try lia. exact Hby. }
  assert (Hdisc : forall R, F = Some R -> flush = Z_FINISH /\ inb = R).
  { intros R HR. destruct (HF R HR) as [E0 ->]. split; [rewrite Hfl; replace srcleft' with 0 by (clear -Hsl' E0; lia); reflexivity|].
    unfold inb. rewrite (Hai_eq E0). reflexivity. }
  destruct (RTK7.kf7_deflate K HK [] 1 _ out F s _ _ _ inb ao flush (z_msg z) s' (InSlice.zslice ni ai z') code HK0)
    as [Hwb' Hres].
  all: try exact Esl'; try exact Hdisc; try exact Hrc; try exact Hgz'.
  { clear -Hflush. unfold Z_NO_FLUSH, Z_FINISH in Hflush. lia. }
  { unfold inb. apply Forall_sublist. exact Hsrc. }
  { clear -Hinb Hai Hu. lia. }
  { rewrite Hinb. unfold n in Hp. rewrite Zlength_sublist by lia. clear -Hp Hn Hai Hu. lia. }
  { clear -Hao Hu. lia. }
  { clear -Hleft Hout Hb Hl' Hao Hao0 Hl. lia. }
  { destruct Hcode as [Hc|[Hc|Hc]]; auto. }
  { intros Hc. destruct (Hend Hc) as [Hf Ha]. split; [exact Hf|]. exact Ha. }
  { intros Hc; contradiction. }
  cbv zeta in Hres. rewrite InSlice.zs_avail_in, InSlice.zs_out, InSlice.zs_total_in, InSlice.zs_total_out,
    InSlice.zs_adler, Hinb in Hres.
  (* the data consumed and the input still offered, as slices of the source *)
  assert (HD : sublist 0 ni src ++ sublist 0 (ai - z_avail_in z') inb = sublist 0 (z_next_in z') src).
  { unfold inb. clear -Hp Hai' Hlen Hni'. destruct Hp as [Hp _].
    rewrite sublist_sublist' by lia. rewrite Z.add_0_l, sublist_rejoin by lia. f_equal. lia. }
  assert (HR : sublist (ai - z_avail_in z') ai inb = sublist (z_next_in z') (z_next_in z' + z_avail_in z') src).
  { unfold inb. clear -Hp Hai' Hlen Hni'. destruct Hp as [Hp _].
    rewrite sublist_sublist' by lia. f_equal; lia. }
  rewrite HD, HR in Hres.
  split.
  - intros Hok. subst code.
    (* a bound below 2^32: the first call ends the stream *)
    assert (Hbig : umax < b).
    { destruct (Z.le_gt_cases b umax) as [Hs|Hs]; [exfalso|exact Hs].
      destruct (Hsmall Hs) as (Hn0 & Hf0 & Hi0 & Ho0 & Ht00).
      assert (El : left = b) by (fold ni in Hn0; clear -Hout Ho0 Hlo Ht00; lia).
      assert (Hle : left <= umax) by (clear -El Hs; lia).
      assert (Ea : ao = b) by (specialize (Hlo0 Ho0 Hle); clear -Hlo0 Hleft Ho0 El; lia).
      assert (Es : srcleft' = 0) by (apply Hsl0; [exact Hi0 | fold n in Hbn; clear -Hin Hn0 Hi0 Hbn Hs; lia]).
      assert (Ef : flush = Z_FINISH) by (rewrite Hfl, Es; reflexivity).
      assert (Hse : Z_OK = Z_STREAM_END) by (apply Hone; [exact Ef | exact Hf0 | exact Hn0 | clear -Ht00 Ht0 Ea; lia]).
      discriminate Hse. }
    assert (Hne : Z_OK <> Z_STREAM_END) by (unfold Z_OK, Z_STREAM_END; lia).
    specialize (Hrun Hne). rewrite (proj2 (Z.eqb_neq _ _) Hne) in Hres.
    exists (flush =? Z_FINISH), (if flush =? Z_FINISH then Some (sublist (z_next_in z') (z_next_in z' + z_avail_in z') src) else None).
    rewrite <- Hni' in Hrun. rewrite Zlength_app.
    specialize (Hfullb Hbig eq_refl). clear Hflush Hcode Hbuf Hnb Hend Hfin Hfull Hpos Hai_eq Hnf Hff HF Hdisc.
    split; [exact Hrun|].
    split; [clear Hfn Hfullb; lia|]. split; [clear Hfn Hfullb; lia|]. split; [clear Hfn Hfullb; lia|].
    split; [intros Ef; apply Hfn, Z.eqb_eq, Ef|].
    split; [clear Hfn Hfullb; lia|]. split; [clear Hfn Hfullb; lia|]. split; [clear Hfn Hfullb; lia|].
    split; [intros H0; specialize (Hfullb H0); clear Hfn; lia|].
    split; [clear Hfn Hfullb; lia|]. split; [clear Hfn Hfullb; lia|].
    split; [congruence|]. split; [congruence|]. split; [exact Hres|].
    split; [|intros Hs; exfalso; clear -Hs Hbig; lia].
    intros R HR'. destruct (Z.eqb_spec flush Z_FINISH) as [Ef|Ef]; [|discriminate].
    injection HR' as <-. split; [exact (Hfn Ef)|reflexivity].
  - intros Hc. assert (Hse : code = Z_STREAM_END) by (destruct Hcode as [|[|]]; tauto).
    split; [exact Hse|]. subst code. rewrite Z.eqb_refl in Hres. rewrite Hwb, Hgz in Hres.
    destruct (Hend eq_refl) as [Hf Ha].
    replace (z_next_in z') with n in Hres by (specialize (Hfn Hf); clear -Hfn Hni' Ha Hsrc' Hin Hsl'; lia).
    unfold n in Hres. rewrite sublist_same in Hres by reflexivity. exact Hres.
Qed.

(** Every run of the loop from the invariant ends with Z_STREAM_END and the zlib stream of the data. *)
Lemma c2f_run : forall s z left srcleft out err out' sf zf,
  c2_run src s z left srcleft out err out' sf zf -> c2f_inv s z left srcleft out ->
  err = Z_STREAM_END /\ dfinal [] 1 15 None src out'.
Proof.
  induction 1 as [s z left srcleft out z1 left' srcleft' flush s' z' err out' sf zf Hg E Hgz Hst R IH
                 |s z left srcleft out z1 left' srcleft' flush s' z' err Hg E Hgz Hst Hne];
    intros J.
  - exact (IH (proj1 (c2f_step _ _ _ _ _ _ _ _ _ _ _ _ J Hg E) eq_refl)).
  - exact (proj2 (c2f_step _ _ _ _ _ _ _ _ _ _ _ _ J Hg E) Hne).
Qed.

End Loop.

Theorem c2w_final : Zlib.proof.roundtrip.RTK7.rt_k7_stmt -> Zlib.proof.deflate.LawFactsC2W.c2_facts_stmt ->
  c2w_final_stmt.
Proof.
  intros (K & HK) (Bpre & Brun & BF) src level a1 a2 a3 a4 a5 z0 r out Hsrc Hn Hl
    (os & z1 & code & Ei & Hr) Hok.
  set (n := Zlength src) in *.
  assert (Hn0 : 0 <= n) by apply Zlength_nonneg.
  destruct (c2f_cb_range n ltac:(lia)) as [[Hb0 Hb] Hbn].
  destruct Hr as [(Ec & -> & _)|(Ec & s & err & sf & zf & Es & _ & R & Er)]; [contradiction|].
  destruct (LawFactsC2W.c2f_init _ _ BF level a1 a2 a3 a4 a5 z0 Hl) as [_ Hinit].
  destruct (Hinit os z1 code Ei Ec) as (s1 & Es1 & Hgz & HP).
  rewrite Es in Es1. injection Es1 as <-.
  destruct (LawFactsC2W.c2f_start _ _ BF level s _ _ _ n HP Hl ltac:(lia)) as [Ht00 HB].
  destruct (LawFactsC2W.c2f_range _ _ BF _ _ _ _ _ _ _ _ HB) as [_ Ht].
  rewrite Es, Ec in Ei.
  destruct (RTK7.kf7_init K HK level 8 15 8 0 a1 a2 a3 a4 a5 z0 s z1) as (Hw & _ & HK0);
    try (unfold rs32; lia); [exact Ei|].
  assert (J : c2f_inv K Brun src (z_total_out z1) (compressBound_z n) s
                (mkST src 0 0 (z_total_in z1) [] 0 (z_total_out z1) (z_adler z1) (z_msg z1))
                (compressBound_z n) n []).
  { exists false, None. cbn [z_next_in z_avail_in z_avail_out z_total_in z_total_out z_adler].
    assert (Hu : umax = 4294967295) by reflexivity.
    rewrite Zlength_nil, sublist_nil.
    split; [exact HB|].
    repeat split; try lia; try exact Hw; try exact Hgz; try exact HK0;
      try (intros E; discriminate E); match goal with H : None = Some _ |- _ => discriminate H end. }
  destruct (c2f_run K HK Bpre Brun BF src Hsrc Hn (z_total_out z1) (compressBound_z n) Hb Hbn _ _ _ _ _ _ _ _ _ R J)
    as [_ Hf].
  exact Hf.
Qed.
