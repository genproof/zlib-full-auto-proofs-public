(** * The header part of the deflate laws' theory: the EXTRA_STATE stage of deflate()

    [extra_stage]: from the entry of the EXTRA stage ([gent]: the gzip header [H] of [h], bytes up to
    [gpos h EXTRA gzindex] put, strm->adler their CRC-32 when the header has an HCRC), [c_deflate_extra]
    either falls through at the entry of the NAME stage or returns Z_OK in the middle of the extra field
    ([hstop]: [hret] and [hinv]).  Kit: RTDLTHdrKit.v (dput_bytes_mid, pb_write_mid, hcrc_update_mid,
    flush_mid, loop_measure). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTHdrKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** The extra field's bytes sit at [12 ..] in the header. *)
Lemma extra_H : forall h xfl x, hdr_ok h -> gz_extra h = Some x ->
  exists A R, gz_hdr_bytes (Some h) xfl = A ++ x ++ R /\ Zlength A = 12.
Proof.
  intros h xfl x Hok Ex.
  destruct Hok as [_ [_ [_ [_ [Hel [Hx _]]]]]]. destruct (Hx x Ex) as [Lx _].
  assert (Eland : Z.land (gz_extra_len h) 65535 = gz_extra_len h).
  { change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
  unfold gz_hdr_bytes, gz_body, gz_extra_bytes. rewrite Ex, Eland.
  rewrite sublist_same by lia.
  eexists (gz_pre h xfl ++ map u8 [Z.land (gz_extra_len h) 255; Z.land (Z.shiftr (gz_extra_len h) 8) 255]).
  eexists. split.
  - rewrite <- !app_assoc. reflexivity.
  - reflexivity.
Qed.

Lemma extra_sub : forall h xfl x i j, hdr_ok h -> gz_extra h = Some x -> 0 <= i <= j -> j <= gz_extra_len h ->
  12 + j <= Zlength (gz_hdr_bytes (Some h) xfl) /\
  sublist (12 + i) (12 + j) (gz_hdr_bytes (Some h) xfl) = sublist i j x.
Proof.
  intros h xfl x i j Hok Ex Hij Hj.
  pose proof Hok as Hok'. destruct Hok' as [_ [_ [_ [_ [Hel [Hx _]]]]]]. destruct (Hx x Ex) as [Lx _].
  destruct (extra_H h xfl x Hok Ex) as [A [R [E LA]]]. rewrite E.
  split.
  - rewrite !Zlength_app. pose proof (Zlength_nonneg R). lia.
  - rewrite sublist_app2 by lia. rewrite LA. rewrite sublist_app1 by lia. f_equal; lia.
Qed.

(** The loop state of the extra copy. *)
Definition xinv (s0 : dstate) (z0 : strm) (H : list Z) (k0 : Z) (h : gzh) (a : dstate * strm * Z * Z) : Prop :=
  let '(s, z, beg, lft) := a in
  d_status s = EXTRA_STATE /\ hmid s0 z0 H k0 s z (12 + d_gzindex s) /\
  0 <= d_gzindex s <= gz_extra_len h /\ lft = gz_extra_len h - d_gzindex s /\
  0 <= beg <= d_pending s /\ z_adler z = hadler h H (12 + d_gzindex s - d_pending s + beg).

Definition xout (s0 : dstate) (z0 : strm) (H : list Z) (k0 : Z) (h : gzh)
    (b : (dstate * strm * Z * Z) + (dstate * strm)) : Prop :=
  match b with
  | inl a => xinv s0 z0 H k0 h a /\ let '(s, z, beg, lft) := a in d_pending s + lft <= d_pending_buf_size s
  | inr (s, z) => d_status s = EXTRA_STATE /\ hret s0 z0 H k0 s z (12 + d_gzindex s) /\
      0 <= d_gzindex s < gz_extra_len h /\ z_adler z = hadler h H (12 + d_gzindex s)
  end.

Definition xmeasure (a : dstate * strm * Z * Z) : Z :=
  let '(s, z, beg, lft) := a in 2 * lft + (if d_pending s >? 0 then 1 else 0).

Lemma hmid_pbs : forall s0 z0 H k0 s z kk,
  hmid s0 z0 H k0 s z kk -> 512 <= d_pending_buf_size s <= 131072.
Proof.
  intros s0 z0 H k0 s z kk [[_ [Hp _]] _].
  destruct Hp as [_ [_ [_ [[Hh1 Hh2] [_ [_ [_ [HL [P1 _]]]]]]]]].
  assert (2 ^ (d_hash_bits s - 1) <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
  assert (2 ^ 7 <= 2 ^ (d_hash_bits s - 1)) by (apply Z.pow_le_mono_r; lia).
  lia.
Qed.

Lemma extra_step : forall s0 z0 H k0 h xfl x a,
  hdr_ok h -> gz_extra h = Some x -> H = gz_hdr_bytes (Some h) xfl ->
  xinv s0 z0 H k0 h a ->
  0 <= xmeasure a /\ exists r, extra_body h x a = Some r /\
    match r with inl a' => xinv s0 z0 H k0 h a' /\ xmeasure a' < xmeasure a | inr b => xout s0 z0 H k0 h b end.
Proof.
  intros s0 z0 H k0 h xfl x [[[s z] beg] lft] Hok Ex HH [Hst [Hm [Hgi [Hl [Hb Ha]]]]].
  pose proof (hmid_pbs _ _ _ _ _ _ _ Hm) as Hpbs.
  destruct (hmid_buf_len _ _ _ _ _ _ _ Hm) as [Lb [Lm [Hp0 Hp1]]].
  pose proof Hok as Hok'. destruct Hok' as [_ [_ [_ [_ [Hel [Hx _]]]]]]. destruct (Hx x Ex) as [Lx Bx].
  split; [unfold xmeasure; destruct (_ >? _); lia|].
  unfold extra_body.
  replace (u64 (d_pending s + lft)) with (d_pending s + lft) by (unfold u64; rewrite Z.mod_small; lia).
  destruct (d_pending s + lft >? d_pending_buf_size s) eqn:Ec; [apply Z.gtb_lt in Ec|].
  - replace (u64 (d_pending_buf_size s - d_pending s)) with (d_pending_buf_size s - d_pending s)
      by (unfold u64; rewrite Z.mod_small; lia).
    set (copy := d_pending_buf_size s - d_pending s).
    unfold rds.
    replace ((0 <=? d_gzindex s) && (0 <=? copy) && (d_gzindex s + copy <=? Zlength x)) with true
      by (symmetry; rewrite !andb_true_iff, !Z.leb_le; lia).
    cbn [bind].
    set (b := sublist (d_gzindex s) (d_gzindex s + copy) x).
    assert (Lbb : Zlength b = copy) by (unfold b; rewrite Zlength_sublist; lia).
    destruct (extra_sub h xfl x (d_gzindex s) (d_gzindex s + copy) Hok Ex ltac:(lia) ltac:(lia)) as [HkH Hsub].
    rewrite <- HH in HkH, Hsub.
    destruct (pb_write_mid s0 z0 H k0 s z (12 + d_gzindex s) b Hm) as [pb [Ew Hm1]].
    { lia. }
    { lia. }
    { rewrite Lbb. replace (12 + d_gzindex s + copy) with (12 + (d_gzindex s + copy)) by lia. exact Hsub. }
    { apply Forall_sublist. exact Bx. }
    rewrite Ew. cbn [bind].
    change (d_pending_buf_size (set_d_pb s pb)) with (d_pending_buf_size s).
    replace (d_pending_buf_size s) with (d_pending s + Zlength b) by lia.
    set (s1 := set_d_pending (set_d_pb s pb) (d_pending s + Zlength b)) in *.
    assert (HbH : bytes H) by (rewrite HH; apply gz_hdr_bytes_bytes; exact Hok).
    rewrite (hcrc_update_mid s0 z0 H k0 s1 z (12 + d_gzindex s + Zlength b) h beg Hm1 HbH).
    2:{ change (d_pending s1) with (d_pending s + Zlength b). lia. }
    2:{ rewrite Ha. f_equal. change (d_pending s1) with (d_pending s + Zlength b). lia. }
    cbn [bind].
    change (d_gzindex s1) with (d_gzindex s).
    replace (u64 (d_gzindex s + copy)) with (d_gzindex s + copy) by (unfold u64; rewrite Z.mod_small; lia).
    set (s2 := set_d_gzindex s1 (d_gzindex s + copy)).
    assert (Hm2 : hmid s0 z0 H k0 s2 (set_z_adler z (hadler h H (12 + d_gzindex s + Zlength b)))
                    (12 + d_gzindex s + Zlength b)).
    { apply hmid_adler. apply hmid_gzindex. exact Hm1. }
    destruct (flush_mid _ _ _ _ _ _ _ Hm2) as [s3 [z3 [Ef [Est [Egz [Elf [Ead Hc]]]]]]].
    rewrite Ef. cbn [bind].
    change (d_gzindex s2) with (d_gzindex s + copy) in Egz.
    change (d_status s2) with (d_status s) in Est.
    change (z_adler (set_z_adler z (hadler h H (12 + d_gzindex s + Zlength b)))) with
      (hadler h H (12 + d_gzindex s + Zlength b)) in Ead.
    destruct Hc as [[P0 Hm3]|[P0 [Av Ha3]]].
    + rewrite P0. cbn [Z.eqb negb].
      eexists. split; [reflexivity|]. split.
      * unfold xinv. rewrite Est, Egz, P0. split; [exact Hst|].
        split; [replace (12 + (d_gzindex s + copy)) with (12 + d_gzindex s + Zlength b) by lia; exact Hm3|].
        split; [lia|]. split; [unfold u64; rewrite Z.mod_small; lia|]. split; [lia|].
        rewrite Ead. f_equal. lia.
      * unfold xmeasure. rewrite P0. cbn [Z.gtb Z.compare].
        replace (u64 (lft - copy)) with (lft - copy) by (unfold u64; rewrite Z.mod_small; lia).
        destruct (d_pending s >? 0) eqn:Eq; [lia|]. rewrite Z.gtb_ltb, Z.ltb_ge in Eq. lia.
    + destruct (d_pending s3 =? 0) eqn:EP; [apply Z.eqb_eq in EP; contradiction|]. cbn [negb].
      eexists. split; [reflexivity|].
      cbn [xout]. change (d_status (set_d_last_flush s3 (-1))) with (d_status s3).
      change (d_gzindex (set_d_last_flush s3 (-1))) with (d_gzindex s3).
      rewrite Est, Egz. split; [exact Hst|].
      split; [|split; [lia|rewrite Ead; f_equal; lia]].
      split; [replace (12 + (d_gzindex s + copy)) with (12 + d_gzindex s + Zlength b) by lia; exact Ha3|].
      split; [reflexivity|]. split; [exact Av|exact P0].
  - rewrite Z.gtb_ltb, Z.ltb_ge in Ec.
    eexists. split; [reflexivity|]. cbn [xout].
    split; [|exact Ec]. exact (conj Hst (conj Hm (conj Hgi (conj Hl (conj Hb Ha))))).
Qed.

Lemma hacc_wg : forall s0 z0 H k0 s z kk,
  hacc s0 z0 H k0 s z kk -> d_wrap s = d_wrap s0 /\ d_gzhead s = d_gzhead s0.
Proof. intros s0 z0 H k0 s z kk [_ [_ [_ [_ [_ [_ [Hw [Hg _]]]]]]]]. auto. Qed.

Lemma name_gidx : forall h, hdr_ok h ->
  match gz_name h with Some l => 0 <= 0 < Zlength l | None => 0 = 0 end.
Proof.
  intros h [_ [_ [_ [_ [_ [_ [Hn _]]]]]]]. destruct (gz_name h) as [l|] eqn:E; [|reflexivity].
  destruct (Hn l eq_refl) as [l0 [-> _]]. rewrite Zlength_app, Zlength_cons, Zlength_nil.
  pose proof (Zlength_nonneg l0). lia.
Qed.

Lemma extra_stage : forall s0 z0 H k0 s z,
  gent s0 z0 H k0 EXTRA_STATE s z ->
  exists s' z' r, c_deflate_extra s z = Some (s', z', r) /\
    match r with
    | None => gent s0 z0 H k0 NAME_STATE s' z'
    | Some c => c = Z_OK /\ hstop s0 z0 H k0 s' z'
    end.
Proof.
  intros s0 z0 H k0 s z [Hst [Hw [h [xfl [Hg [Hok [HH [Hgi [Hm Ha]]]]]]]]].
  unfold gidx_ok, gpos in Hgi, Hm, Ha. rewrite Z.eqb_refl in Hgi, Hm, Ha.
  unfold c_deflate_extra. rewrite Hst, Z.eqb_refl. unfold c_gzhead. rewrite Hg. cbn [bind].
  destruct (gz_extra h) as [x|] eqn:Ex.
  - pose proof Hok as Hok'. destruct Hok' as [_ [_ [_ [_ [Hel [Hx _]]]]]]. destruct (Hx x Ex) as [Lx Bx].
    destruct (hacc_wg _ _ _ _ _ _ _ (proj1 Hm)) as [Hw0 Hg0].
    assert (Eland : Z.land (gz_extra_len h) 65535 = gz_extra_len h).
    { change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
    rewrite Eland.
    replace (u64 (gz_extra_len h - d_gzindex s)) with (gz_extra_len h - d_gzindex s)
      by (unfold u64; rewrite Z.mod_small; lia).
    replace (10 + (2 + d_gzindex s)) with (12 + d_gzindex s) in Hm, Ha by lia.
    destruct (hmid_buf_len _ _ _ _ _ _ _ Hm) as [_ [_ [Hp0 Hp1]]].
    destruct (loop_measure (extra_body h x) (xinv s0 z0 H k0 h) (xout s0 z0 H k0 h) xmeasure
                (fun a Ha => extra_step s0 z0 H k0 h xfl x a Hok Ex HH Ha)
                (s, z, d_pending s, gz_extra_len h - d_gzindex s)) as [e [Eloop Hq]].
    { unfold xinv. split; [exact Hst|]. split; [exact Hm|]. split; [lia|]. split; [reflexivity|].
      split; [lia|]. rewrite Ha. f_equal. lia. }
    { unfold xmeasure. destruct (_ >? _); lia. }
    rewrite Eloop. cbn [bind].
    destruct e as [[[[s1 z1] beg1] lft1]|[s1 z1]].
    + destruct Hq as [[Hst1 [Hm1 [Hgi1 [Hl1 [Hb1 Ha1]]]]] Hroom].
      destruct (hmid_buf_len _ _ _ _ _ _ _ Hm1) as [_ [_ [Hq0 Hq1]]].
      destruct (hacc_wg _ _ _ _ _ _ _ (proj1 Hm1)) as [Hw1 Hg1].
      pose proof (hmid_pbs _ _ _ _ _ _ _ Hm1) as Hpbs.
      unfold rds.
      replace ((0 <=? d_gzindex s1) && (0 <=? lft1) && (d_gzindex s1 + lft1 <=? Zlength x)) with true
        by (symmetry; rewrite !andb_true_iff, !Z.leb_le; lia).
      cbn [bind].
      set (b := sublist (d_gzindex s1) (d_gzindex s1 + lft1) x).
      assert (Lbb : Zlength b = lft1) by (unfold b; rewrite Zlength_sublist; lia).
      destruct (extra_sub h xfl x (d_gzindex s1) (d_gzindex s1 + lft1) Hok Ex ltac:(lia) ltac:(lia)) as [HkH Hsub].
      rewrite <- HH in HkH, Hsub.
      destruct (pb_write_mid s0 z0 H k0 s1 z1 (12 + d_gzindex s1) b Hm1) as [pb [Ew Hm2]].
      { lia. }
      { lia. }
      { rewrite Lbb. replace (12 + d_gzindex s1 + lft1) with (12 + (d_gzindex s1 + lft1)) by lia. exact Hsub. }
      { apply Forall_sublist. exact Bx. }
      rewrite Ew. cbn [bind].
      change (d_pending (set_d_pb s1 pb)) with (d_pending s1).
      replace (u64 (d_pending s1 + lft1)) with (d_pending s1 + Zlength b) by (unfold u64; rewrite Z.mod_small; lia).
      set (s2 := set_d_pending (set_d_pb s1 pb) (d_pending s1 + Zlength b)) in *.
      assert (HbH : bytes H) by (rewrite HH; apply gz_hdr_bytes_bytes; exact Hok).
      rewrite (hcrc_update_mid s0 z0 H k0 s2 z1 (12 + d_gzindex s1 + Zlength b) h beg1 Hm2 HbH).
      2:{ change (d_pending s2) with (d_pending s1 + Zlength b). lia. }
      2:{ rewrite Ha1. f_equal. change (d_pending s2) with (d_pending s1 + Zlength b). lia. }
      cbn [bind then_stage].
      do 3 eexists. split; [reflexivity|].
      unfold gent. split; [reflexivity|].
      change (d_wrap (set_d_status (set_d_gzindex s2 0) NAME_STATE)) with (d_wrap s2).
      change (d_gzhead (set_d_status (set_d_gzindex s2 0) NAME_STATE)) with (d_gzhead s2).
      change (d_gzindex (set_d_status (set_d_gzindex s2 0) NAME_STATE)) with 0.
      change (d_wrap s2) with (d_wrap s1). change (d_gzhead s2) with (d_gzhead s1).
      split; [congruence|]. exists h, xfl. split; [congruence|]. split; [exact Hok|]. split; [exact HH|].
      unfold gidx_ok, gpos.
      replace (NAME_STATE =? EXTRA_STATE) with false by reflexivity. rewrite Z.eqb_refl.
      assert (Lx2 : Zlength (gz_extra_bytes h) = 2 + gz_extra_len h).
      { unfold gz_extra_bytes. rewrite Ex, Eland, sublist_same by lia. rewrite Zlength_app, Lx. reflexivity. }
      rewrite Lx2. split; [apply name_gidx; exact Hok|].
      replace (10 + (2 + gz_extra_len h) + 0) with (12 + d_gzindex s1 + Zlength b) by lia.
      split; [apply hmid_status, hmid_gzindex, hmid_adler; exact Hm2|].
      reflexivity.
    + cbn [then_stage]. do 3 eexists. split; [reflexivity|]. split; [reflexivity|].
      destruct Hq as [Hst1 [Hr1 [Hgi1 Ha1]]].
      destruct (hacc_wg _ _ _ _ _ _ _ (proj1 Hr1)) as [Hw1 Hg1].
      exists (12 + d_gzindex s1). split; [exact Hr1|].
      split; [congruence|]. exists h, xfl. split; [congruence|]. split; [exact Hok|]. split; [exact HH|].
      rewrite Hst1. split; [left; split; [reflexivity|]; split; [congruence|lia]|].
      unfold gidx_ok, gpos. rewrite Z.eqb_refl, Ex. split; [lia|]. split; [lia|].
      exact Ha1.
  - cbn [then_stage bind]. do 3 eexists. split; [reflexivity|].
    unfold gent. split; [reflexivity|]. split; [exact Hw|]. exists h, xfl.
    split; [exact Hg|]. split; [exact Hok|]. split; [exact HH|].
    unfold gidx_ok, gpos. cbn [d_status set_d_status]. change (d_gzindex (set_d_status s NAME_STATE)) with (d_gzindex s).
    rewrite Hgi.
    replace (NAME_STATE =? EXTRA_STATE) with false by reflexivity. rewrite Z.eqb_refl.
    assert (Lx : Zlength (gz_extra_bytes h) = 0) by (unfold gz_extra_bytes; rewrite Ex; reflexivity).
    rewrite Lx. split; [apply name_gidx; exact Hok|].
    split; [apply hmid_status; exact Hm|exact Ha].
Qed.
