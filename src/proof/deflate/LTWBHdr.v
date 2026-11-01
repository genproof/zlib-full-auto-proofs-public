(** * The deflateBound accounting for the short laws: stages 2 to 7 of deflate() (the headers) inside [MidW]

    Port of LTBHdrSt.hdr_stage to the invariants of LTWBDefs.v, with LTWIface.hdr_facts_w (headers [hdr_ok_w],
    any output space below 2^32) in place of hdr_facts; the core part of the state is unchanged. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTWBKit.
Require Import Zlib.proof.deflate.LTBHdrSt.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** The header bytes of the short laws' headers are bytes (LTBHdrSt.bytes_hdr for [hdr_ok_w]) *)
Lemma bytes_cstr_w : forall o, cstr_ok_w o -> bytes (cstr_bytes o).
Proof.
  intros o Ho. unfold cstr_bytes. destruct o as [l|]; [|apply Forall_nil].
  destruct (Ho l eq_refl) as (l0 & -> & _ & F). unfold bytes. apply Forall_app. split.
  - eapply Forall_impl; [|exact F]. intros a Ha; cbv beta in Ha; lia.
  - repeat constructor; lia.
Qed.

Lemma bytes_gz_some_w : forall h xfl, hdr_ok_w h -> bytes (gz_hdr_bytes (Some h) xfl).
Proof.
  intros h xfl Hh. destruct Hh as (_ & _ & _ & _ & _ & Hx & Hn & Hc).
  unfold gz_hdr_bytes, gz_body, bytes. rewrite !Forall_app. split; [split; [|split; [|split]]|].
  - apply bytes_map_u8.
  - unfold gz_extra_bytes. destruct (gz_extra h) as [x|] eqn:E; [|apply Forall_nil].
    apply Forall_app. split; [apply bytes_map_u8|]. apply Forall_sublist. apply (Hx x eq_refl).
  - apply bytes_cstr_w; exact Hn.
  - apply bytes_cstr_w; exact Hc.
  - destruct (gz_hcrc h =? 0); [apply Forall_nil|].
    repeat (apply Forall_cons; [apply byte_land|]). apply Forall_nil.
Qed.

Lemma bytes_hdr_w : forall s a, gzh_ok_w s -> bytes (hdr_bytes s a).
Proof.
  intros s a Hg. unfold hdr_bytes.
  destruct (d_wrap s =? 1).
  - unfold zlib_hdr_bytes, bytes. apply Forall_app. split; [apply bytes_msb2|].
    destruct (d_strstart s =? 0); [apply Forall_nil|]. apply Forall_app; split; apply bytes_msb2.
  - destruct (d_wrap s =? 2); [|apply Forall_nil].
    destruct (d_gzhead s) as [h|] eqn:E.
    + apply bytes_gz_some_w. apply Hg. exact E.
    + unfold gz_hdr_bytes, bytes, xfl_byte, OS_CODE.
      repeat (apply Forall_cons; [try (destruct (_ =? _)); try (destruct (_ || _)); lia|]). apply Forall_nil.
Qed.

Lemma hdr_stage_w : forall W HI, core_facts_w W -> hdr_facts_w HI ->
  forall n b pos0 inb aout tin0 tout0 flush gz0 s z,
  MidW W HI n b pos0 inb aout tin0 tout0 flush gz0 s z -> z_next_in z = 0 ->
  d_pending s = 0 -> d_po s = 0 -> d_bi_valid s <= 7 -> (d_status s = FINISH_STATE -> z_avail_in z = 0) ->
  exists s2 z2 o, hdr_stages s z = Some (s2, z2, o) /\
    MidW W HI n b pos0 inb aout tin0 tout0 flush gz0 s2 z2 /\ z_next_in z2 = 0 /\ core_eq s s2 /\
    (o = None -> (d_status s2 = BUSY_STATE \/ d_status s2 = FINISH_STATE) /\
                 d_pending s2 = 0 /\ d_po s2 = 0 /\ d_bi_valid s2 <= 7 /\
                 (d_status s2 = FINISH_STATE -> d_status s = FINISH_STATE /\ z_avail_in z2 = 0)) /\
    (forall c, o = Some c -> c = Z_OK) /\
    (flush = Z_FINISH -> pos0 = 0 -> b <= tout0 + aout -> o = None).
Proof.
  intros W HI CF HF n b pos0 inb aout tin0 tout0 flush gz0 s z HM Hni Hpd Hpo Hbv Hfin.
  pose proof HM as HM0.
  destruct HM as (Hcf & Hinb & Hpos0 & Hpn & Hfl & Hfn & Haout & Htin0 & Htout0 & Hgz & HB).
  destruct HB as (Hd & w0 & HW & Hok & Hw0 & Hb & HH & Hn & Hpos & Htin & Htout & Hgzh & Hlf & Hph).
  pose proof (cw_prm W CF s HW) as Hprm.
  destruct Hcf as (Czi & Cni & Cnia & Cti & Cao & Clen & Cto & Cby).
  (* P2 / P3: nothing to do *)
  assert (Hbusy : d_status s = BUSY_STATE \/ d_status s = FINISH_STATE ->
    exists s2 z2 o, hdr_stages s z = Some (s2, z2, o) /\
    MidW W HI n b pos0 inb aout tin0 tout0 flush gz0 s2 z2 /\ z_next_in z2 = 0 /\ core_eq s s2 /\
    (o = None -> (d_status s2 = BUSY_STATE \/ d_status s2 = FINISH_STATE) /\
                 d_pending s2 = 0 /\ d_po s2 = 0 /\ d_bi_valid s2 <= 7 /\
                 (d_status s2 = FINISH_STATE -> d_status s = FINISH_STATE /\ z_avail_in z2 = 0)) /\
    (forall c, o = Some c -> c = Z_OK) /\
    (flush = Z_FINISH -> pos0 = 0 -> b <= tout0 + aout -> o = None)).
  { intros Hst. exists s, z, None. rewrite hdr_stages_busy by exact Hst.
    split; [reflexivity|]. split; [exact HM0|]. split; [exact Hni|]. split; [apply core_eq_refl|].
    split; [intros _; repeat split; auto|]. split; [intros c Hc; discriminate|]. intros; reflexivity. }
  (* P0 / P1: the facts for hf_run *)
  assert (Hk : (d_status s = BUSY_STATE \/ d_status s = FINISH_STATE) \/
    exists k, hdr_pre_w HI s z Hd k /\ z_total_out z = k /\ d_wrap s = w0 /\ pos0 + z_next_in z = 0 /\ ub s = 0 /\
              0 <= k /\ bytes Hd).
  { destruct Hph as [P0 | [P1 | [P2 | P3]]].
    - destruct P0 as (Pst & Pw & PH & Pp & Pt & Ppd & Pbv & Psym & Pub & Pad).
      pose proof (Zlength_nonneg (z_out z)).
      right. exists 0. split; [|split; [lia|split; [exact Pw|split; [exact Pp|split; [exact Pub|split; [lia|]]]]]].
      + unfold hdr_pre_w. split; [exact Hprm|]. split; [exact Hok|]. split; [exact Hpd|]. split; [exact Psym|].
        split; [exact Pbv|]. split; [lia|]. split; [lia|]. split; [intros h Eh; apply Hgzh; exact Eh|].
        destruct (w0 =? 2) eqn:E2.
        * apply Z.eqb_eq in E2. right; left. split; [exact Pst|]. split; [congruence|]. split; [exact PH|reflexivity].
        * apply Z.eqb_neq in E2. left. split; [exact Pst|]. split; [lia|]. split; [exact PH|reflexivity].
      + subst Hd; apply bytes_hdr_w; exact Hgzh.
    - destruct P1 as (Pw0 & Pw & (k & PHI & Pk) & Pp & Pbv & Psym & Pub).
      destruct (hw_status HI HF s (z_adler z) Hd k PHI) as (_ & (h & Eh) & _ & (xfl & EH) & Hkr).
      pose proof (Zlength_nonneg (z_out z)).
      right. exists k. split; [|split; [lia|split; [congruence|split; [exact Pp|split; [exact Pub|split; [lia|]]]]]].
      + unfold hdr_pre_w. split; [exact Hprm|]. split; [exact Hok|]. split; [exact Hpd|]. split; [exact Psym|].
        split; [exact Pbv|]. split; [lia|]. split; [lia|]. split; [intros h' Eh'; apply Hgzh; exact Eh'|].
        right; right; exact PHI.
      + subst Hd. rewrite Eh. apply bytes_gz_some_w. apply Hgzh. exact Eh.
    - left. left. apply (proj1 P2).
    - left. right. apply (proj1 P3). }
  destruct Hk as [Hst | (k & Hpre & Htk & Hwk & Hp0 & Hub & Hk0 & HbH)]; [apply Hbusy; exact Hst|].
  destruct (hw_run HI HF s z Hd k Hpre) as (s' & z' & r & Hrun & Hpost).
  pose proof (hdr_stages_av s z Cao s' z' r Hrun) as Hav.
  destruct Hpost as (Hce & Hok' & Hw' & Hgz' & Hbv' & x & k' & Hkk & Hx & Hzs & Hr).
  destruct Hzs as (Zi & Zni & Zai & Zti & Zo & Zao & Zto & Zad & Zmsg).
  pose proof (cw_frame W CF s s' HW Hce) as HW'.
  pose proof (cw_prm W CF s' HW') as Hprm'.
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
            MidW W HI n b pos0 inb aout tin0 tout0 flush gz0 s' z').
  { intros ph lf. unfold MidW, cframe. rewrite Zi, Zni, Zai, Zti, Zo, Zao, Zto. rewrite Zlength_app.
    split.
    { split; [exact Czi|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [lia|]. unfold bytes; apply Forall_app; split; assumption. }
    split; [exact Hinb|]. split; [exact Hpos0|]. split; [exact Hpn|]. split; [exact Hfl|]. split; [exact Hfn|].
    split; [exact Haout|]. split; [exact Htin0|]. split; [exact Htout0|]. split; [congruence|].
    exists Hd, w0. split; [exact HW'|]. split; [exact Hok'|]. split; [exact Hw0|]. split; [rewrite Hcls; exact Hb|].
    split; [exact HH|]. split; [exact Hn|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [unfold gzh_ok_w; rewrite Hgz'; exact Hgzh|]. split; [exact lf|]. rewrite <- Zni, <- Zto. exact ph. }
  exists s', z', r. split; [exact Hrun|].
  destruct r as [c|].
  - destruct Hr as (Hc & Hao' & Hpd' & Hlf' & Hrr).
    assert (Hlast : k' <= Zlength Hd) by lia.
    split.
    + apply Hmid; [|lia]. destruct Hrr as [(Hst' & Hk' & Had') | HI'].
      * right; right; left. split; [exact Hst'|]. split; [congruence|]. split; [lia|].
        split; [rewrite Had'; exact Hadl|]. exists 0, 0. split; [rewrite Hub'; lia|].
        unfold acct. rewrite xb_00. unfold Gb. rewrite Zto. lia.
      * destruct (hw_status HI HF s' (z_adler z') Hd k' HI') as (Hw2 & _).
        right; left. split; [congruence|]. split; [exact Hw2|]. split; [exists k'; split; [exact HI'|]; rewrite Zto; lia|].
        split; [lia|]. split; [lia|]. split; [lia|]. rewrite Hub'; exact Hub.
    + split; [rewrite Zni; exact Hni|]. split; [exact Hce|]. split; [intros E; discriminate|].
      split; [intros c0 E; injection E; intros <-; exact Hc|].
      intros _ _ Hroom. exfalso. rewrite Zao in Hao'. rewrite Zto in *. lia.
  - destruct Hr as (Hk' & Hst' & Hpd' & Hpo' & Had' & Hlf').
    split.
    + apply Hmid; [|lia]. right; right; left. split; [exact Hst'|]. split; [congruence|]. split; [lia|].
      split; [rewrite Had'; exact Hadl|]. exists 0, 0. split; [rewrite Hub'; lia|].
      unfold acct. rewrite xb_00. unfold Gb. rewrite Zto. lia.
    + split; [rewrite Zni; exact Hni|]. split; [exact Hce|].
      split; [intros _; split; [left; exact Hst'|]; split; [exact Hpd'|]; split; [exact Hpo'|]; split; [lia|];
              intros E; rewrite Hst' in E; discriminate|].
      split; [intros c0 E; discriminate|]. intros; reflexivity.
Qed.

