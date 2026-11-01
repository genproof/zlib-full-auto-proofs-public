(* Law rt_session, sessions with a gzip header: one inflate() call after the gzip header (SGzDefs.sgz_call_d_stmt):
   the decode theory RTIGW on the machine with a small gz_header (RTH8SimKit: the passes after the header do not
   read it), the application's gz_header kept. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.rt_session.SGzDefs.
Require Import Zlib.proof.harness.rt_session.SGzTail.
Require Zlib.proof.uncompr.URunFrame.
Require Zlib.proof.harness.inflate_buffers.IBTheory.
Import ListNotations.
Local Open Scope Z_scope.

Lemma sgz_call_d : sgz_call_d_stmt.
Proof.
  intros G pos out L z inp flush res OK DV LV ZF AO LI P0 PL IE HP PF RUN. cbv zeta.
  assert (BI: bytes_ok inp).
  { destruct OK as (_ & _ & _ & _ & _ & BO & _). rewrite IE.
    apply Zlib.proof.harness.inflate_buffers.IBTheory.ib_bytes_sublist; exact BO. }
  destruct (sgz_canon_init G pos out L z inp OK DV LV ZF AO LI BI) as (KD & MW).
  set (m0 := m_init z L inp) in *.
  pose proof (g2_dinv_mode _ _ _ _ _ DV) as MD.
  assert (MD0: Zlib.proof.inflate.Model.TYPE <= i_mode (m_s m0) <= DONE).
  { unfold m0, m_init. cbv zeta. destruct (i_mode (l_s L) =? Zlib.proof.inflate.Model.TYPE); cbn [m_s];
      [cbn; unfold TYPEDO, DONE, Zlib.proof.inflate.Model.TYPE; lia | exact MD]. }
  assert (VM: URunFrame.vmode (i_mode (m_s m0)))
    by (unfold URunFrame.vmode; unfold BAD, DONE, HEAD, Zlib.proof.inflate.Model.TYPE in *; lia).
  pose proof (URunFrame.run2_frame _ _ _ _ _ VM RUN) as (FI & FA & FS & FH & _).
  destruct RUN as (o0 & LP & RO).
  assert (HK: SK.hk m0) by (right; apply g2_hdr_mode_after; unfold m_mode; lia).
  destruct (sgz_tail G pos inp out flush m0 o0 res OK P0 PL IE KD MW eq_refl HK HP PF LP RO)
    as [MEM | (RC & SNX & SOW & AOT & HH & FR & DV' & EN)]; [left; exact MEM|].
  right. split; [exact RC|]. split; [exact SNX|]. split; [exact SOW|]. split; [exact AOT|].
  split; [exact HH|].
  split; [rewrite FH; unfold m0, m_init; cbv zeta; destruct (_ =? _); reflexivity|].
  split; [exact FR|]. split; [exact DV'|]. exact EN.
Qed.
