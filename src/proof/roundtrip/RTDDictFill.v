(* RT-D part DICT: fill_window inside deflateSetDictionary (wrap 0, no slide), through
   fill_fspec on the state with its head table replaced by [Hc] (any table making chain_ok hold; fill_window does
   not read the head table without a slide: RTDLTCDictFrame.fill_frame). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDV2.
Require Import Zlib.proof.roundtrip.RTDLTCDictKit Zlib.proof.roundtrip.RTDLTCDictFrame Zlib.proof.roundtrip.RTDLTCDictIns.
Require Import Zlib.proof.roundtrip.RTDLTCDictProj Zlib.proof.roundtrip.RTDLTCDict Zlib.proof.roundtrip.RTDLTCFill.
Import ListNotations.
Local Open Scope Z_scope.

Lemma hh_set s P H H' : set_d_head (set_d_head (set_d_prev s P) H) H' = set_d_head (set_d_prev s P) H'.
Proof. destruct s; reflexivity. Qed.

Lemma kwin_self s : wstruct s -> wpos s ->
  kwin (sublist 0 (d_strstart s + d_lookahead s) (mb_val (d_window s))) s.
Proof.
  intros (W1 & _ & W3 & _) (P1 & P2 & P3 & _). unfold kwin.
  rewrite Zlength_sublist by lia. split; [lia|]. intros i Hi.
  rewrite Znth_sublist by lia. f_equal; lia.
Qed.

Lemma fill_kw (Hff : fill_fspec) : forall x zd x' k Hc,
  prm x -> wstruct x -> wpos x -> wwin x -> d_insert x = 0 -> d_wrap x = 0 ->
  d_strstart x + d_lookahead x + z_avail_in zd <= d_w_size x ->
  zin_in zd -> z_total_in zd + z_avail_in zd < 18446744073709551616 ->
  Zlength Hc = d_hash_size x -> chain_ok (set_d_head x Hc) ->
  c_fill_window x zd = Some (x', zadv zd k) ->
  (forall W, kwin W x -> kwin (W ++ sublist (z_next_in zd) (z_next_in zd + k) (z_in zd)) x') /\
  (chain_hok (set_d_head x Hc) -> chain_hok (set_d_head x' Hc)) /\
  (MIN_MATCH <= d_lookahead x' -> 0 < k -> primed x' (d_strstart x')).
Proof.
  intros x zd x' k Hc Hprm Hws Hwp Hww Hins Hwr Hbnd Hzin Htot HHc Hch Ef.
  assert (Hprm0 : prm (set_d_head x Hc)) by (unfold prm in *; autorewrite with dproj; exact Hprm).
  assert (Hws0 : wstruct (set_d_head x Hc)).
  { destruct Hws as (W1 & W2 & W3 & W4 & W5). unfold wstruct. autorewrite with dproj.
    split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|exact HHc]. }
  assert (Hwp0 : wpos (set_d_head x Hc)) by (unfold wpos in *; autorewrite with dproj; exact Hwp).
  assert (Hww0 : wwin (set_d_head x Hc)) by (unfold wwin in *; autorewrite with dproj; exact Hww).
  set (zd0 := zframe zd [] 0 0).
  assert (Hzin0 : zin_in zd0) by (subst zd0; unfold zframe, zin_in in *; cbn; exact Hzin).
  assert (Hav0 : z_avail_in zd0 = z_avail_in zd) by reflexivity.
  destruct (fill_step fill_ok (set_d_head x Hc) zd0 Hprm0 Hws0 Hwp0 Hww0
              ltac:(autorewrite with dproj; exact Hins) ltac:(autorewrite with dproj; exact Hwr)
              ltac:(autorewrite with dproj; lia) Hzin0 ltac:(subst zd0; cbn; lia))
    as (s1 & k1 & E1 & _ & _ & _ & _ & Hi1 & Hk1 & Hh1 & Hp1 & Hst1 & _ & Hla1 & Hk1r & _).
  pose proof (prm_wsize x Hprm) as Hw.
  assert (Hla0 : 0 <= d_lookahead x /\ 0 <= d_strstart x) by (destruct Hwp as (Q1&Q2&_); lia).
  assert (Hai : 0 <= z_avail_in zd) by (destruct Hzin as (_&_&Z3&_); lia).
  destruct (fill_frame (set_d_head x Hc) zd0 (d_head x) (d_prev x) (z_out zd) (z_avail_out zd) (z_total_out zd)
     ltac:(autorewrite with dproj; lia) ltac:(autorewrite with dproj; exact Hins)
     ltac:(unfold MAX_DIST, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH; autorewrite with dproj; lia)) as [Efr _].
  rewrite E1 in Efr. subst zd0. rewrite head_twice, zframe_back in Efr. rewrite Efr in Ef.
  injection Ef as Ex' Ez.
  assert (k1 = k) by lia. subst k1 x'.
  autorewrite with dproj in Hh1, Hp1, Hst1, Hla1.
  replace (set_d_head (set_d_head (set_d_prev s1 (d_prev x)) (d_head x)) Hc) with s1
    by (rewrite hh_set, <- Hh1, <- Hp1, eta_head_prev; reflexivity).
  assert (Hpre : fill_pre (set_d_head x Hc)).
  { split; [exact Hprm0|]. split; [exact Hws0|]. split; [exact Hwp0|]. split; [exact Hww0|exact Hch]. }
  assert (Hzall : zall (zframe zd [] 0 0)).
  { split; [exact Hzin0|]. unfold zout_ok, zframe; cbn. lia. }
  assert (Had : adler_ok (d_wrap (set_d_head x Hc)) (z_adler (zframe zd [] 0 0))).
  { autorewrite with dproj. rewrite Hwr. split; intros; lia. }
  assert (Hrun : forall W, kwin W x -> exists k2,
     zstep (d_wrap (set_d_head x Hc)) (zframe zd [] 0 0)
       (mkST (z_in zd) (z_next_in zd + k) (z_avail_in zd - k) (z_total_in zd + k) [] 0 0 (z_adler zd) (z_msg zd)) k2 [] /\
     kwin (W ++ sublist (z_next_in (zframe zd [] 0 0)) (z_next_in (zframe zd [] 0 0) + k2) (z_in (zframe zd [] 0 0))) s1 /\
     (chain_hok (set_d_head x Hc) -> chain_hok s1) /\
     (MIN_MATCH <= d_lookahead s1 -> (0 < k2 \/ (d_insert (set_d_head x Hc) = 0 /\ primed (set_d_head x Hc) (d_strstart (set_d_head x Hc)))) ->
      d_insert s1 = 0 /\ primed s1 (d_strstart s1))).
  { intros W HW. apply (Hff _ _ _ _ W Hpre Hzall Had E1).
    unfold kwin in *. autorewrite with dproj. exact HW. }
  assert (Hk2 : forall k2, zstep (d_wrap (set_d_head x Hc)) (zframe zd [] 0 0)
       (mkST (z_in zd) (z_next_in zd + k) (z_avail_in zd - k) (z_total_in zd + k) [] 0 0 (z_adler zd) (z_msg zd)) k2 [] ->
       k2 = k).
  { intros k2 (_ & _ & Zn & _). cbn in Zn. lia. }
  pose proof (kwin_self x Hws Hwp) as Hkx.
  split; [|split].
  - intros W HW. destruct (Hrun W HW) as (k2 & Hz & Hkw & _). rewrite (Hk2 k2 Hz) in Hkw.
    unfold kwin in *. autorewrite with dproj. exact Hkw.
  - intros Hcx. destruct (Hrun _ Hkx) as (k2 & _ & _ & Hc2 & _). exact (Hc2 Hcx).
  - intros Hm Hk. destruct (Hrun _ Hkx) as (k2 & Hz & _ & _ & Hp2). rewrite (Hk2 k2 Hz) in Hp2.
    destruct (Hp2 Hm (or_introl Hk)) as [_ Hpr].
    unfold primed, update_hash in *. autorewrite with dproj. exact Hpr.
Qed.
