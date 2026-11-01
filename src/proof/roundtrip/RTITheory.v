(* Round-trip laws, part RT-I: deflate_roundtrip's inflation of a finished deflate stream
   (RTIIface.ifacts), from the decode theory (rfc1951/Decode.v; its parts are proved by the inflate area). *)
Require Import Zlib.proof.roundtrip.RTIIface.
Require Zlib.proof.rfc1951.Decode.
Require Import Zlib.proof.roundtrip.RTIKit.
Require Zlib.proof.roundtrip.RTIPlain Zlib.proof.roundtrip.RTIRawDict Zlib.proof.roundtrip.RTIZDict Zlib.proof.roundtrip.RTIGz.
From Coq Require Import ZArith List Lia Bool.
Import ListNotations.
Local Open Scope Z_scope.

(* raw / zlib: the decode theory (RTIPlain, RTIRawDict, RTIZDict); gzip: the
   header passes, then the generalized decode theory (RTIGz) *)

Lemma rti_gz_wrap wrap : wrap <> 0 -> wrap <> 1 -> iw_of wrap 0 = 32 /\ forall wb, iw_of wrap wb = 32.
Proof.
  intros A B. unfold iw_of. rewrite (proj2 (Z.eqb_neq _ _) A), (proj2 (Z.eqb_neq _ _) B). auto.
Qed.

(* dfinal of a gzip wrapper *)
Lemma rti_dfinal_gz dict wrap wb gh D O : wrap <> 0 -> wrap <> 1 -> RF.dfinal dict wrap wb gh D O ->
  9 <= wb <= 15 /\ dict = [] /\
  exists bs xfl, wf (2 ^ wb) dict bs /\ data dict bs = D /\ (xfl = 0 \/ xfl = 2 \/ xfl = 4) /\
    O = stream_bytes (WGzip (RF.fhdr_of gh xfl)) [] bs.
Proof.
  intros A B (W & bs & Wf & Dd & M).
  assert (M': dict = [] /\ exists xfl, (xfl = 0 \/ xfl = 2 \/ xfl = 4) /\
                O = stream_bytes (WGzip (RF.fhdr_of gh xfl)) [] bs).
  { destruct wrap as [|p|p]; [contradiction| |exact M]. destruct p; try exact M. contradiction. }
  destruct M' as (Ed & xfl & X & EO).
  split; [exact W|]. split; [exact Ed|]. exists bs, xfl. auto.
Qed.

Lemma rti_init32_s sp : l_s (init_live sp 32) = init_s 7 0.
Proof. reflexivity. Qed.

Theorem rt_ifacts : Zlib.proof.rfc1951.Decode.decode_parts -> ifacts.
Proof.
  intros DP. constructor.
  - intros wrap wb D O sp z res DF LD LO LV ZC RUN.
    destruct (Z.eq_dec wrap 0) as [E0|N0];
      [exact (Zlib.proof.roundtrip.RTIPlain.rti_plain_rz DP wrap wb D O sp z res (or_introl E0) DF LD LO LV ZC RUN)|].
    destruct (Z.eq_dec wrap 1) as [E1|N1];
      [exact (Zlib.proof.roundtrip.RTIPlain.rti_plain_rz DP wrap wb D O sp z res (or_intror E1) DF LD LO LV ZC RUN)|].
    destruct (rti_dfinal_gz _ _ _ _ _ _ N0 N1 DF) as (W & _ & bs & xfl & Wf & Dd & X & EO).
    rewrite (proj2 (rti_gz_wrap wrap N0 N1) wb) in LV, RUN.
    refine (proj1 (Zlib.proof.roundtrip.RTIGz.rti_gz_run DP None xfl wb bs D O (init_live sp 32) z res
                     W Wf Dd X EO _ LD LO LV ZC (or_introl (rti_init32_s sp)) RUN)).
    intros g E. discriminate.
  - exact (Zlib.proof.roundtrip.RTIRawDict.rti_rawdict DP).
  - exact (Zlib.proof.roundtrip.RTIZDict.rti_zdict DP).
  - intros wb gh x nm cm D O sp z res h headp hsh xb nb cb DF HOK Ex En Ec LD LO
      X1 X2 X3 N1 N2 N3 C1 C2 C3 LV ZC RUN.
    destruct (rti_dfinal_gz [] 2 wb (Some gh) D O ltac:(lia) ltac:(lia) DF)
      as (W & _ & bs & xfl & Wf & Dd & X & EO).
    set (L := head_live (init_live sp 32) h headp hsh xb nb cb) in *.
    assert (HB: head_bufs gh x nm cm (l_h L)).
    { unfold head_bufs. cbn. repeat split; assumption. }
    assert (HL: l_s L = set_i_head (init_s 7 0) true /\ h_done (l_h L) = 0 /\
                exists g x0 nm0 cm0, Some gh = Some g /\ head_bufs g x0 nm0 cm0 (l_h L)).
    { split; [reflexivity|]. split; [reflexivity|]. exists gh, x, nm, cm. auto. }
    destruct (Zlib.proof.roundtrip.RTIGz.rti_gz_run DP (Some gh) xfl wb bs D O L z res
                W Wf Dd X EO ltac:(intros g E; injection E as <-; exact HOK) LD LO LV ZC (or_intror HL) RUN)
      as (R & H).
    split; [exact R|]. intros _.
    exact (H gh x nm cm eq_refl eq_refl HB).
Qed.
