(** * deflate_bound theory: the header stages of deflate() inside [Mid]

    From [hf_run] (hdr_facts) in the phases P0 / P1 of [Brun], [hdr_stages_busy] in P2 / P3. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTBOut Zlib.proof.deflate.LTBArith.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** The header stages never overdraw the output space: next_out is written only by flush_pending (through
    [out_put], which checks the room); [hdr_post] does not say it, the model does. *)
Lemma mb_read_len : forall b lo len l, mb_read b lo len = Some l -> Zlength l = len.
Proof.
  intros b lo len l H. unfold mb_read, mb_definedb in H.
  destruct ((0 <=? len) && _) eqn:E; [|discriminate]. inversion H; subst.
  rewrite !andb_true_iff, !Z.leb_le in E. rewrite Zlength_sublist; lia.
Qed.

Lemma u64_small : forall x, 0 <= x < 18446744073709551616 -> u64 x = x.
Proof. intros x Hx. unfold u64. apply Z.mod_small; exact Hx. Qed.

Ltac hav_step := match goal with
  | H : bind ?e _ = Some _ |- _ => cbv beta iota zeta delta [bind] in H
  | H : match ?e with _ => _ end = Some _ |- _ =>
      let E := fresh "E" in destruct e eqn:E; cbv beta iota zeta delta [bind] in H
  | H : Some _ = Some _ |- _ => injection H; clear H; intros; subst
  | H : None = Some _ |- _ => discriminate H
  | H : inl _ = inr _ |- _ => discriminate H
  | H : inr _ = inl _ |- _ => discriminate H
  | H : inl _ = inl _ |- _ => injection H; clear H; intros; subst
  | H : inr _ = inr _ |- _ => injection H; clear H; intros; subst
  end.
Ltac hav_dest := repeat hav_step.

Lemma fp_av : forall s z s' z', c_flush_pending s z = Some (s', z') ->
  0 <= z_avail_out z -> 0 <= z_avail_out z'.
Proof.
  intros s z s' z' H A. unfold c_flush_pending, out_put in H. hav_dest; cbn [z_avail_out set_z_avail_out set_z_total_out set_z_out]; try lia.
  match goal with R : mb_read _ _ _ = Some _ |- _ => apply mb_read_len in R end.
  match goal with L : (_ <=? _) = true |- _ => apply Z.leb_le in L end. lia.
Qed.

Lemma hcrc_av : forall h s z beg z', c_hcrc_update h s z beg = Some z' -> z_avail_out z' = z_avail_out z.
Proof. intros. unfold c_hcrc_update in H. hav_dest; cbn [z_avail_out set_z_adler]; reflexivity. Qed.

Local Strategy opaque [rds u64 mb_write mb_read c_hcrc_update c_flush_pending c_putShortMSB c_dput_bytes c_dput_byte loop loop2].

Ltac hav_fin := repeat match goal with
  | E : c_flush_pending _ _ = Some (_, _) |- _ => pose proof (fp_av _ _ _ _ E); clear E
  | E : c_hcrc_update _ _ _ _ = Some _ |- _ => pose proof (hcrc_av _ _ _ _ _ E); clear E
  end; cbn [z_avail_out set_z_adler fst snd] in *;
  repeat match goal with H : 0 <= _ -> _ |- _ => specialize (H ltac:(lia)) end; first [assumption | lia].

Definition rav (r : option dres) : Prop := forall s' z' o, r = Some (s', z', o) -> 0 <= z_avail_out z'.

Lemma then_stage_av : forall r k, rav r -> (forall s z, 0 <= z_avail_out z -> rav (k s z)) -> rav (then_stage r k).
Proof.
  intros r k R K s' z' o H. unfold then_stage in H.
  destruct r as [[[s1 z1] o1]|]; cbn [bind] in H; [|discriminate].
  destruct o1 as [c|].
  - inversion H; subst. eapply R; reflexivity.
  - eapply K; [eapply R; reflexivity|exact H].
Qed.

Lemma for_av : forall s z, 0 <= z_avail_out z -> rav (c_flush_or_return s z).
Proof. intros s z A s' z' o H. unfold c_flush_or_return in H. hav_dest; hav_fin. Qed.

Lemma extra_loop_av : forall h x a r, runs (extra_body h x) a r -> 0 <= z_avail_out (snd (fst (fst a))) ->
  0 <= z_avail_out (match r with inl (_, z, _, _) => z | inr (_, z) => z end).
Proof.
  intros h x a r H. induction H as [a r H|a a' r H _ IH]; destruct a as [[[s z] beg] lft]; cbn [fst snd]; intros A;
    unfold extra_body in H; hav_dest; hav_fin.
Qed.

Lemma str_loop_av : forall h str a r, runs (str_body h str) a r -> 0 <= z_avail_out (snd (fst a)) ->
  0 <= z_avail_out (match r with inl (_, z, _) => z | inr (_, z) => z end).
Proof.
  intros h str a r H. induction H as [a r H|a a' r H _ IH]; destruct a as [[s z] beg]; cbn [fst snd]; intros A;
    unfold str_body in H; hav_dest; hav_fin.
Qed.

Lemma zlib_av : forall s z, 0 <= z_avail_out z -> rav (c_deflate_zlib_header s z).
Proof.
  intros s z A s' z' o H. unfold c_deflate_zlib_header in H. hav_dest; try hav_fin;
    refine (for_av _ _ _ _ _ _ H); cbn [z_avail_out set_z_adler]; lia.
Qed.

Lemma gzip_av : forall s z, 0 <= z_avail_out z -> rav (c_deflate_gzip_header s z).
Proof.
  intros s z A s' z' o H. unfold c_deflate_gzip_header in H. hav_dest; try hav_fin;
    refine (for_av _ _ _ _ _ _ H); cbn [z_avail_out set_z_adler]; lia.
Qed.

Lemma extra_av : forall s z, 0 <= z_avail_out z -> rav (c_deflate_extra s z).
Proof.
  intros s z A s' z' o H. unfold c_deflate_extra, then_stage in H. hav_dest; try hav_fin;
    match goal with E : loop _ _ _ = Some _ |- _ => apply loop_runs, extra_loop_av in E end; hav_fin.
Qed.

Lemma str_av : forall h o b s z, 0 <= z_avail_out z -> rav (c_deflate_str h o b s z).
Proof.
  intros h o b s z A s' z' o' H. unfold c_deflate_str in H. hav_dest; try hav_fin;
    match goal with E : loop _ _ _ = Some _ |- _ => apply loop_runs, str_loop_av in E end; hav_fin.
Qed.

Lemma name_av : forall s z, 0 <= z_avail_out z -> rav (c_deflate_name s z).
Proof.
  intros s z A. unfold c_deflate_name. destruct (d_status s =? NAME_STATE).
  - intros s' z' o H. destruct (c_gzhead s) as [h|]; cbn [bind] in H; [|discriminate].
    revert s' z' o H. apply then_stage_av; [apply str_av; exact A|].
    intros s1 z1 A1 s' z' o H. inversion H; subst; exact A1.
  - intros s' z' o H. inversion H; subst; exact A.
Qed.

Lemma comment_av : forall s z, 0 <= z_avail_out z -> rav (c_deflate_comment s z).
Proof.
  intros s z A. unfold c_deflate_comment. destruct (d_status s =? COMMENT_STATE).
  - intros s' z' o H. destruct (c_gzhead s) as [h|]; cbn [bind] in H; [|discriminate].
    revert s' z' o H. apply then_stage_av; [apply str_av; exact A|].
    intros s1 z1 A1 s' z' o H. inversion H; subst; exact A1.
  - intros s' z' o H. inversion H; subst; exact A.
Qed.

Lemma hcrc_stage_av : forall s z, 0 <= z_avail_out z -> rav (c_deflate_hcrc s z).
Proof.
  intros s z A. unfold c_deflate_hcrc. destruct (d_status s =? HCRC_STATE).
  - intros s' z' o H. destruct (c_gzhead s) as [h|]; cbn [bind] in H; [|discriminate].
    destruct (if gz_hcrc h =? 0 then _ else _) as [r|] eqn:R; cbn [bind] in H; [|discriminate].
    revert s' z' o H. apply then_stage_av.
    + rewrite <- R. destruct (gz_hcrc h =? 0).
      * intros ? ? ? E; inversion E; subst; exact A.
      * apply then_stage_av.
        -- destruct (_ >? _); [apply for_av; exact A|]. intros ? ? ? E; inversion E; subst; exact A.
        -- intros s2 z2 A2 s3 z3 o3 E. hav_dest; cbn [z_avail_out set_z_adler]; exact A2.
    + intros s1 z1 A1. apply for_av; exact A1.
  - intros s' z' o H. inversion H; subst; exact A.
Qed.

Lemma hdr_stages_av : forall s z, 0 <= z_avail_out z -> rav (hdr_stages s z).
Proof.
  intros s z A. unfold hdr_stages.
  apply then_stage_av; [apply zlib_av; exact A|]. intros s1 z1 A1.
  apply then_stage_av; [apply gzip_av; exact A1|]. intros s2 z2 A2.
  apply then_stage_av; [apply extra_av; exact A2|]. intros s3 z3 A3.
  apply then_stage_av; [apply name_av; exact A3|]. intros s4 z4 A4.
  apply then_stage_av; [apply comment_av; exact A4|]. intros s5 z5 A5.
  apply hcrc_stage_av; exact A5.
Qed.

(** ** The header bytes are bytes *)
Lemma byte_u8 : forall x, 0 <= u8 x < 256.
Proof. intros x. unfold u8. apply Z.mod_pos_bound; lia. Qed.

Lemma byte_land : forall x, 0 <= Z.land x 255 < 256.
Proof.
  intros x. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound x (2 ^ 8) ltac:(lia)) as B. change (2 ^ 8) with 256 in B. exact B.
Qed.

Lemma bytes_map_u8 : forall l, bytes (map u8 l).
Proof.
  intros l. unfold bytes. apply Forall_forall. intros y Hy. apply in_map_iff in Hy.
  destruct Hy as (x & <- & _). apply byte_u8.
Qed.

Lemma bytes_msb2 : forall b, bytes (msb2 b).
Proof.
  intros b. unfold msb2, bytes. repeat (apply Forall_cons; [apply byte_u8|]). apply Forall_nil.
Qed.

Lemma bytes_cstr : forall o, cstr_ok o -> bytes (cstr_bytes o).
Proof.
  intros o Ho. unfold cstr_bytes. destruct o as [l|]; [|apply Forall_nil].
  destruct (Ho l eq_refl) as (l0 & -> & _ & F). unfold bytes. apply Forall_app. split.
  - eapply Forall_impl; [|exact F]. intros a Ha; cbv beta in Ha; lia.
  - repeat constructor; lia.
Qed.

Lemma bytes_gz_some : forall h xfl, hdr_ok h -> bytes (gz_hdr_bytes (Some h) xfl).
Proof.
  intros h xfl Hh. destruct Hh as (_ & _ & _ & _ & _ & Hx & Hn & Hc).
  unfold gz_hdr_bytes, gz_body, bytes. rewrite !Forall_app. split; [split; [|split; [|split]]|].
  - apply bytes_map_u8.
  - unfold gz_extra_bytes. destruct (gz_extra h) as [x|] eqn:E; [|apply Forall_nil].
    apply Forall_app. split; [apply bytes_map_u8|]. apply Forall_sublist. apply (Hx x eq_refl).
  - apply bytes_cstr; exact Hn.
  - apply bytes_cstr; exact Hc.
  - destruct (gz_hcrc h =? 0); [apply Forall_nil|].
    repeat (apply Forall_cons; [apply byte_land|]). apply Forall_nil.
Qed.

Lemma bytes_hdr : forall s a, gzh_ok s -> bytes (hdr_bytes s a).
Proof.
  intros s a Hg. unfold hdr_bytes.
  destruct (d_wrap s =? 1).
  - unfold zlib_hdr_bytes, bytes. apply Forall_app. split; [apply bytes_msb2|].
    destruct (d_strstart s =? 0); [apply Forall_nil|]. apply Forall_app; split; apply bytes_msb2.
  - destruct (d_wrap s =? 2); [|apply Forall_nil].
    destruct (d_gzhead s) as [h|] eqn:E.
    + apply bytes_gz_some. apply Hg. exact E.
    + unfold gz_hdr_bytes, bytes, xfl_byte, OS_CODE.
      repeat (apply Forall_cons; [try (destruct (_ =? _)); try (destruct (_ || _)); lia|]). apply Forall_nil.
Qed.

(** ** Small arithmetic *)
Lemma body_nonneg : forall c n, 0 <= n -> 0 <= body c n.
Proof.
  intros c n Hn. pose proof (proj2 (Z.shiftr_nonneg n 3) Hn). pose proof (proj2 (Z.shiftr_nonneg n 5) Hn).
  pose proof (proj2 (Z.shiftr_nonneg n 7) Hn). pose proof (proj2 (Z.shiftr_nonneg n 8) Hn).
  pose proof (proj2 (Z.shiftr_nonneg n 9) Hn). pose proof (proj2 (Z.shiftr_nonneg n 11) Hn).
  pose proof (proj2 (Z.shiftr_nonneg n 12) Hn). pose proof (proj2 (Z.shiftr_nonneg n 14) Hn).
  pose proof (proj2 (Z.shiftr_nonneg n 25) Hn).
  destruct c; unfold body; lia.
Qed.

Lemma tlen_nonneg : forall w, 0 <= tlen w.
Proof. intros w. unfold tlen. destruct (w =? 1); [lia|]. destruct (w =? 2); lia. Qed.

Lemma xb_00 : forall c h, xb c h 0 0 = 8 * h.
Proof. intros c h. destruct c; unfold xb; lia. Qed.

Lemma adler_ok_hdr : forall w a, 0 <= w <= 2 -> adler_ok w (hdr_adler w a).
Proof.
  intros w a Hw. unfold adler_ok, hdr_adler.
  destruct (w =? 1) eqn:E1; [apply Z.eqb_eq in E1; subst|].
  - split; [|lia]. intros _. unfold Zlib.proof.adler32.Model.adler_valid, Zlib.proof.adler32.Model.adler_lo,
      Zlib.proof.adler32.Model.adler_hi, Zlib.proof.adler32.Model.ADLER_BASE. vm_compute. repeat split; discriminate.
  - apply Z.eqb_neq in E1. destruct (w =? 2) eqn:E2; [apply Z.eqb_eq in E2; subst|].
    + split; [lia|]. intros _. lia.
    + apply Z.eqb_neq in E2. split; intros; lia.
Qed.

Lemma pend_len : forall s, prm s -> outok s -> Zlength (pend s) = d_pending s /\ 0 <= d_pending s.
Proof.
  intros s Hp Ho. destruct Ho as (_ & (_ & _ & Hpn) & Hpo & Hle & _).
  destruct Hp as (_ & _ & _ & _ & _ & _ & _ & _ & Hpbs & Hbuf & _).
  unfold pend. unfold d_pending in *. rewrite Zlength_sublist; lia.
Qed.

Section Hdr.
Variable W : dstate -> Prop.
Variable HI : hdr_inv.
Hypothesis CF : core_facts W.
Hypothesis HF : hdr_facts HI.

Lemma hdr_stage : forall n b pos0 inb aout tin0 tout0 flush gz0 s z,
  Mid W HI n b pos0 inb aout tin0 tout0 flush gz0 s z -> z_next_in z = 0 ->
  d_pending s = 0 -> d_po s = 0 -> d_bi_valid s <= 7 -> (d_status s = FINISH_STATE -> z_avail_in z = 0) ->
  exists s2 z2 o, hdr_stages s z = Some (s2, z2, o) /\
    Mid W HI n b pos0 inb aout tin0 tout0 flush gz0 s2 z2 /\ z_next_in z2 = 0 /\
    (o = None -> (d_status s2 = BUSY_STATE \/ d_status s2 = FINISH_STATE) /\
                 d_pending s2 = 0 /\ d_po s2 = 0 /\ d_bi_valid s2 <= 7 /\
                 (d_status s2 = FINISH_STATE -> d_status s = FINISH_STATE /\ z_avail_in z2 = 0)) /\
    (forall c, o = Some c -> c = Z_OK) /\
    (flush = Z_FINISH -> pos0 = 0 -> b <= tout0 + aout -> o = None).
Proof.
  intros n b pos0 inb aout tin0 tout0 flush gz0 s z HM Hni Hpd Hpo Hbv Hfin.
  pose proof HM as HM0.
  destruct HM as (Hcf & Hinb & Hpos0 & Hpn & Hfl & Hfn & Haout & Htin0 & Htout0 & Hgz & HB).
  destruct HB as (Hd & w0 & HW & Hok & Hw0 & Hb & HH & Hn & Hpos & Htin & Htout & Hgzh & Hlf & Hph).
  pose proof (cf_prm W CF s HW) as Hprm.
  destruct Hcf as (Czi & Cni & Cnia & Cti & Cao & Clen & Cto & Cby).
  (* P2 / P3: nothing to do *)
  assert (Hbusy : d_status s = BUSY_STATE \/ d_status s = FINISH_STATE ->
    exists s2 z2 o, hdr_stages s z = Some (s2, z2, o) /\
    Mid W HI n b pos0 inb aout tin0 tout0 flush gz0 s2 z2 /\ z_next_in z2 = 0 /\
    (o = None -> (d_status s2 = BUSY_STATE \/ d_status s2 = FINISH_STATE) /\
                 d_pending s2 = 0 /\ d_po s2 = 0 /\ d_bi_valid s2 <= 7 /\
                 (d_status s2 = FINISH_STATE -> d_status s = FINISH_STATE /\ z_avail_in z2 = 0)) /\
    (forall c, o = Some c -> c = Z_OK) /\
    (flush = Z_FINISH -> pos0 = 0 -> b <= tout0 + aout -> o = None)).
  { intros Hst. exists s, z, None. rewrite hdr_stages_busy by exact Hst.
    split; [reflexivity|]. split; [exact HM0|]. split; [exact Hni|].
    split; [intros _; repeat split; auto|]. split; [intros c Hc; discriminate|]. intros; reflexivity. }
  (* P0 / P1: the facts for hf_run *)
  assert (Hk : (d_status s = BUSY_STATE \/ d_status s = FINISH_STATE) \/
    exists k, hdr_pre HI s z Hd k /\ z_total_out z = k /\ d_wrap s = w0 /\ pos0 + z_next_in z = 0 /\ ub s = 0 /\
              0 <= k /\ bytes Hd).
  { destruct Hph as [P0 | [P1 | [P2 | P3]]].
    - destruct P0 as (Pst & Pw & PH & Pp & Pt & Ppd & Pbv & Psym & Pub & Pad).
      pose proof (Zlength_nonneg (z_out z)).
      right. exists 0. split; [|split; [lia|split; [exact Pw|split; [exact Pp|split; [exact Pub|split; [lia|]]]]]].
      + unfold hdr_pre. split; [exact Hprm|]. split; [exact Hok|]. split; [exact Hpd|]. split; [exact Psym|].
        split; [exact Pbv|]. split; [lia|]. split; [lia|]. split; [intros h Eh; apply Hgzh; exact Eh|].
        destruct (w0 =? 2) eqn:E2.
        * apply Z.eqb_eq in E2. right; left. split; [exact Pst|]. split; [congruence|]. split; [exact PH|reflexivity].
        * apply Z.eqb_neq in E2. left. split; [exact Pst|]. split; [lia|]. split; [exact PH|reflexivity].
      + subst Hd; apply bytes_hdr; exact Hgzh.
    - destruct P1 as (Pw0 & Pw & (k & PHI & Pk) & Pp & Pbv & Psym & Pub).
      destruct (hf_status HI HF s (z_adler z) Hd k PHI) as (_ & (h & Eh) & _ & (xfl & EH) & Hkr).
      pose proof (Zlength_nonneg (z_out z)).
      right. exists k. split; [|split; [lia|split; [congruence|split; [exact Pp|split; [exact Pub|split; [lia|]]]]]].
      + unfold hdr_pre. split; [exact Hprm|]. split; [exact Hok|]. split; [exact Hpd|]. split; [exact Psym|].
        split; [exact Pbv|]. split; [lia|]. split; [lia|]. split; [intros h' Eh'; apply Hgzh; exact Eh'|].
        right; right; exact PHI.
      + subst Hd. rewrite Eh. apply bytes_gz_some. apply Hgzh. exact Eh.
    - left. left. apply (proj1 P2).
    - left. right. apply (proj1 P3). }
  destruct Hk as [Hst | (k & Hpre & Htk & Hwk & Hp0 & Hub & Hk0 & HbH)]; [apply Hbusy; exact Hst|].
  destruct (hf_run HI HF s z Hd k Hpre) as (s' & z' & r & Hrun & Hpost).
  pose proof (hdr_stages_av s z Cao s' z' r Hrun) as Hav.
  destruct Hpost as (Hce & Hok' & Hw' & Hgz' & Hbv' & x & k' & Hkk & Hx & Hzs & Hr).
  destruct Hzs as (Zi & Zni & Zai & Zti & Zo & Zao & Zto & Zad & Zmsg).
  pose proof (cf_frame W CF s s' HW Hce) as HW'.
  pose proof (cf_prm W CF s' HW') as Hprm'.
  destruct (pend_len s' Hprm' Hok') as (Hpl & Hpn').
  assert (Hlx : Zlength x + d_pending s' = k' - k).
  { rewrite <- Hpl, <- Zlength_app, Hx. rewrite Zlength_sublist; lia. }
  assert (Hbx : bytes x).
  { assert (B : bytes (x ++ pend s')) by (rewrite Hx; apply Forall_sublist; exact HbH).
    apply Forall_app in B. apply B. }
  assert (Hlx0 : 0 <= Zlength x) by apply Zlength_nonneg.
  rewrite u64_small in Zto by lia.
  pose proof (bcls_core_eq s s' Hce) as Hcls.
  pose proof (ub_core_eq s s' Hce) as Hub'.
  destruct (core_eq_fields s s' Hce) as (_ & _ & _ & _ & _ & _ & _ & _ & Hsym' & _).
  destruct Hpre as (_ & _ & _ & Hsym & Hbv0 & _).
  assert (HbHd : Zlength Hd <= b).
  { pose proof (body_nonneg (bcls_of s) n ltac:(lia)). pose proof (tlen_nonneg w0). lia. }
  assert (Hadl : adler_ok w0 (hdr_adler (d_wrap s) (z_adler z))) by (rewrite Hwk; apply adler_ok_hdr; lia).
  assert (Hmid : forall (ph : bphase HI n (pos0 + z_next_in z') (flush =? Z_FINISH) s' (z_total_out z')
                              (z_adler z') Hd w0) (lf : -2 <= d_last_flush s' <= 5),
            Mid W HI n b pos0 inb aout tin0 tout0 flush gz0 s' z').
  { intros ph lf. unfold Mid, cframe. rewrite Zi, Zni, Zai, Zti, Zo, Zao, Zto. rewrite Zlength_app.
    split.
    { split; [exact Czi|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [lia|]. unfold bytes; apply Forall_app; split; assumption. }
    split; [exact Hinb|]. split; [exact Hpos0|]. split; [exact Hpn|]. split; [exact Hfl|]. split; [exact Hfn|].
    split; [exact Haout|]. split; [exact Htin0|]. split; [exact Htout0|]. split; [congruence|].
    exists Hd, w0. split; [exact HW'|]. split; [exact Hok'|]. split; [exact Hw0|]. split; [rewrite Hcls; exact Hb|].
    split; [exact HH|]. split; [exact Hn|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [unfold gzh_ok; rewrite Hgz'; exact Hgzh|]. split; [exact lf|]. rewrite <- Zni, <- Zto. exact ph. }
  exists s', z', r. split; [exact Hrun|].
  destruct r as [c|].
  - destruct Hr as (Hc & Hao' & Hpd' & Hlf' & Hrr).
    assert (Hlast : k' <= Zlength Hd) by lia.
    split.
    + apply Hmid; [|lia]. destruct Hrr as [(Hst' & Hk' & Had') | HI'].
      * right; right; left. split; [exact Hst'|]. split; [congruence|]. split; [lia|].
        split; [rewrite Had'; exact Hadl|]. exists 0, 0. split; [rewrite Hub'; lia|].
        unfold acct. rewrite xb_00. unfold Gb. rewrite Zto. lia.
      * destruct (hf_status HI HF s' (z_adler z') Hd k' HI') as (Hw2 & _).
        right; left. split; [congruence|]. split; [exact Hw2|]. split; [exists k'; split; [exact HI'|]; rewrite Zto; lia|].
        split; [lia|]. split; [lia|]. split; [lia|]. rewrite Hub'; exact Hub.
    + split; [rewrite Zni; exact Hni|]. split; [intros E; discriminate|].
      split; [intros c0 E; injection E; intros <-; exact Hc|].
      intros _ _ Hroom. exfalso. rewrite Zao in Hao'. rewrite Zto in *. lia.
  - destruct Hr as (Hk' & Hst' & Hpd' & Hpo' & Had' & Hlf').
    split.
    + apply Hmid; [|lia]. right; right; left. split; [exact Hst'|]. split; [congruence|]. split; [lia|].
      split; [rewrite Had'; exact Hadl|]. exists 0, 0. split; [rewrite Hub'; lia|].
      unfold acct. rewrite xb_00. unfold Gb. rewrite Zto. lia.
    + split; [rewrite Zni; exact Hni|].
      split; [intros _; split; [left; exact Hst'|]; split; [exact Hpd'|]; split; [exact Hpo'|]; split; [lia|];
              intros E; rewrite Hst' in E; discriminate|].
      split; [intros c0 E; discriminate|]. intros; reflexivity.
Qed.

End Hdr.
