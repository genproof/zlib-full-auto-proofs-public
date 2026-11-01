(* RT-I: shared definitions and small facts of the inflate side of the round trip.  Over the model only (Model2.run2 from Spec5.m_init). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import compcert.lib.Integers.
Require Export Zlib.proof.roundtrip.RTIIface.
Require Export Zlib.proof.rfc1951.Format.
Require Export Zlib.proof.inflate.Inv3.
Require Zlib.proof.rfc1951.DecodeDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* the decode context of a gzip stream O of deflate (header fhdr_of gh xfl), entered after the header with
   inflateInit2's windowBits 32 seen as 32 + wb (same wrap 7; wbits 0 became 15 >= wb in HEAD) *)
Definition gz_ctx (gh: option DS.gzh) (xfl wb: Z) (bs: list block) (O: list Z) :=
  Zlib.proof.rfc1951.DecodeDefs.DCtx (WGzip (RF.fhdr_of gh xfl)) wb [] bs (32 + wb) O.

(* the header fields inflate reports (if_gzhead's conclusion) *)
Definition head_ok (g: DS.gzh) (x nm cm: list Z) (h: hstate) : Prop :=
  h_done h = 1 /\ h_text h = DS.gz_text g /\ h_time h = DS.gz_time g /\ h_os h = DS.gz_os g /\
  h_hcrc h = DS.gz_hcrc g /\ h_extra_len h = DS.gz_extra_len g /\
  h_xbuf h = x /\ h_nbuf h = nm /\ h_cbuf h = cm.

(* inflateGetHeader's buffers of exactly the fields' sizes (if_gzhead's hypotheses) *)
Definition head_bufs (g: DS.gzh) (x nm cm: list Z) (h: hstate) : Prop :=
  DS.gz_extra g = Some x /\ DS.gz_name g = Some nm /\ DS.gz_comment g = Some cm /\
  h_xp h = true /\ h_extra_max h = Zlength x /\ Zlength (h_xbuf h) = Zlength x /\
  h_np h = true /\ h_name_max h = Zlength nm /\ Zlength (h_nbuf h) = Zlength nm /\
  h_cp h = true /\ h_comm_max h = Zlength cm /\ Zlength (h_cbuf h) = Zlength cm.

(* ---------------------------------------------------------------------------------------------- *)

Lemma rti_mwf3_init z L inp :
  live_ok L -> zf_ok z -> zf_ao z <= Int.max_signed -> Zlength inp <= Int.max_signed -> bytes_ok inp ->
  i_mode (l_s L) <> Zlib.proof.inflate.Model.TYPE ->
  mwf3 (m_init z L inp).
Proof.
  intros LV ZF AO LI BI NT.
  destruct LV as (SP & SW & MW & HW & S3 & WS & LV1 & LV2 & LV3).
  destruct ZF as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
  unfold m_init. cbv zeta. rewrite (proj2 (Z.eqb_neq _ _) NT).
  split; [|exact S3].
  constructor; cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_tin m_tout
    m_snx m_sow]; rewrite ?Zlength_nil; unfold urange, lrange, Z_OK in *; auto.
  all: first [apply (sw_hold _ SW) | apply (sw_bits _ SW) | split; [change Int.max_signed with 2147483647 in *; lia | constructor] |
              pose proof (Zlength_nonneg inp); change Int.max_unsigned with 4294967295 in *;
              change Int.max_signed with 2147483647 in *; change Int64.max_unsigned with 18446744073709551615 in *; lia].
Qed.

(* inf_leave does not touch the application's gz_header *)
Lemma rti_leave_h flush m res : inf_leave flush m res -> m_h (r_m res) = m_h m.
Proof.
  intros H. inversion H; subst; [reflexivity|].
  unfold leave_fin. cbv zeta.
  destruct (leave_ok flush m); cbn;
  destruct (negb (Z.land _ 4 =? 0) && _); reflexivity.
Qed.
