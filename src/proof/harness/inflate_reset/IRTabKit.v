(* Law inflate_reset, theory part TABLE / LENLENS / CODELENS (IRSimTab.v): the kit shared by its parts.
   - the pass from TABLE / LENLENS / CODELENS up to LEN_ without flush (copy of inflate_codes' TheoryTab.v
     ttab_ functions): irt_tab, irt_ll, irt_llpost, irt_cl, irt_clpost and their equations with c_TABLE ..;
   - irt_rr: the two passes end alike (both break with Kr, or both reach LEN_ with Kr, leave 0);
   - two ways to build Kr from Kr: a machine-only change (irk_mach), a new state (irk_state);
   - the part statements (IRTabCL*.v, IRTabLL.v) and the one-stream facts of Step3Tables.v (mwf3x). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_reset.IRDefs.
Require Zlib.proof.inflate.Step3Tables.
Require Zlib.proof.inflate.Cover3.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The pass (flush is read only at CODELENS's end: `if flush == Z_TREES`)                          *)

Inductive irt_res := ITDone (o: iout) | ITLen (m: mst).

Definition irt_run (flush: Z) (p: irt_res) : iout :=
  match p with
  | ITDone o => o
  | ITLen m => if flush =? Z_TREES then IBrk (set_leave m)
               else c_LEN_ lenfix_list distfix_list (fast lenfix_list distfix_list) m
  end.

Definition irt_clpost (m: mst) : irt_res :=
  let s := m_s m in
  if Znth 256 (i_lens s) =? 0 then ITDone (IBrk (set_bad m M_eob)) else
  let s := set_i_lenbits (set_i_lencode (set_i_next s 0) (TCodes 0)) 9 in
  let '(r, codes, nxt, lb) := call_table LENS 0 (i_nlen s) 9 s in
  let s := set_i_lenbits (set_i_next (set_i_codes s codes) nxt) lb in
  let m := set_m_ret (set_m_s m s) r in
  if negb (r =? 0) then ITDone (IBrk (set_bad m M_ll_set)) else
  let s := set_i_distbits (set_i_distcode s (TCodes (i_next s))) 6 in
  let '(r, codes, nxt, db) := call_table DISTS (i_nlen s) (i_ndist s) 6 s in
  let s := set_i_distbits (set_i_next (set_i_codes s codes) nxt) db in
  let m := set_m_ret (set_m_s m s) r in
  if negb (r =? 0) then ITDone (IBrk (set_bad m M_d_set)) else
  ITLen (set_mode m LEN_).

Definition irt_cl (m: mst) : irt_res :=
  match codelens_loop lenfix_list distfix_list 320 m with
  | CLleave m => ITDone (IBrk m)
  | CLbad m => ITDone (IBrk m)
  | CLnext m => irt_clpost m
  end.

Definition irt_llpost (m: mst) : irt_res :=
  let s := lenlens_zero 19 (m_s m) in
  let s := set_i_lenbits (set_i_distcode (set_i_lencode (set_i_next s 0) (TCodes 0)) (TCodes 0)) 7 in
  let '(r, codes, nxt, lb) := call_table CODES 0 19 7 s in
  let s := set_i_lenbits (set_i_next (set_i_codes s codes) nxt) lb in
  let m := set_m_ret (set_m_s m s) r in
  if negb (r =? 0) then ITDone (IBrk (set_bad m M_cl_set)) else
  irt_cl (set_mode (upd_s m (fun s => set_i_have s 0)) CODELENS).

Definition irt_ll (m: mst) : irt_res :=
  let m := lenlens_loop 19 m in
  if m_leave m =? 1 then ITDone (IBrk m) else irt_llpost m.

Definition irt_tab (m: mst) : irt_res :=
  let m := needbits 14 m in
  if m_leave m =? 1 then ITDone (IBrk m) else
  let nlen := bitsn m 5 + 257 in let m := dropbits 5 m in
  let ndist := bitsn m 5 + 1 in let m := dropbits 5 m in
  let ncode := bitsn m 4 + 4 in let m := dropbits 4 m in
  let m := upd_s m (fun s => set_i_ncode (set_i_ndist (set_i_nlen s nlen) ndist) ncode) in
  if orb (286 <? nlen) (30 <? ndist) then ITDone (IBrk (set_bad m M_toomany)) else
  irt_ll (set_mode (upd_s m (fun s => set_i_have s 0)) LENLENS).

Lemma irt_cl_eq flush m :
  c_CODELENS flush lenfix_list distfix_list (fast lenfix_list distfix_list) m = irt_run flush (irt_cl m).
Proof.
  unfold c_CODELENS, irt_cl. destruct (codelens_loop lenfix_list distfix_list 320 m) as [m1|m1|m1];
    try reflexivity.
  unfold irt_clpost. cbv zeta.
  destruct (Znth 256 (i_lens (m_s m1)) =? 0); [reflexivity|].
  destruct (call_table _ _ _ _ _) as [[[r c] n] b].
  destruct (negb (r =? 0)); [reflexivity|].
  destruct (call_table _ _ _ _ _) as [[[r2 c2] n2] b2].
  destruct (negb (r2 =? 0)); reflexivity.
Qed.

Lemma irt_ll_eq flush m :
  c_LENLENS flush lenfix_list distfix_list (fast lenfix_list distfix_list) m = irt_run flush (irt_ll m).
Proof.
  unfold c_LENLENS, irt_ll. cbv zeta.
  destruct (m_leave (lenlens_loop 19 m) =? 1); [reflexivity|].
  unfold irt_llpost. cbv zeta.
  destruct (call_table _ _ _ _ _) as [[[r c] n] b].
  destruct (negb (r =? 0)); [reflexivity|]. apply irt_cl_eq.
Qed.

Lemma irt_tab_eq flush m :
  c_TABLE flush lenfix_list distfix_list (fast lenfix_list distfix_list) m = irt_run flush (irt_tab m).
Proof.
  unfold c_TABLE, irt_tab. cbv zeta.
  destruct (m_leave (needbits 14 m) =? 1); [reflexivity|].
  match goal with |- context [if ?c then _ else _] => destruct c end; [reflexivity|].
  apply irt_ll_eq.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The relation of the two passes' results                                                        *)

Definition irt_rr (W0 wrap: Z) (src: list Z) (pos: Z) (inp: list Z) (aout: Z) (pa pb: irt_res) : Prop :=
  match pa, pb with
  | ITDone (IBrk ma'), ITDone (IBrk mb') => Kr W0 wrap src pos inp aout ma' mb'
  | ITLen ma', ITLen mb' => Kr W0 wrap src pos inp aout ma' mb' /\ m_leave mb' = 0 /\ m_mode mb' = LEN_
  | _, _ => False
  end.

(* ---------------------------------------------------------------------------------------------- *)
(* Building Kr                                                                                    *)

(* the machine's own fields (all but the state and the gz_header) *)
Definition irk_mf (m: mst) :=
  (m_inp m, m_aout m, m_nx m, m_ow m, m_hold m, m_bits m, m_in m, m_out m, m_ret m, m_leave m, m_adler m,
   m_msg m, m_tin m, m_tout m, m_snx m, m_sow m).

Lemma irk_mf_of_Kr W0 wrap src pos inp aout ma mb :
  Kr W0 wrap src pos inp aout ma mb -> irk_mf ma = irk_mf mb.
Proof.
  intros K. destruct K as [[_ ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?] _ _ _ _ _ _ _]. unfold irk_mf. congruence.
Qed.

(* a change of the machine's own fields only (NEEDBITS, PULLBYTE, DROPBITS, leave, ret, lookups) *)
Lemma irk_mach W0 wrap src pos inp aout ma mb ma' mb' :
  Kr W0 wrap src pos inp aout ma mb -> m_mode mb <> HEAD ->
  m_s ma' = m_s ma -> m_s mb' = m_s mb -> irk_mf ma' = irk_mf mb' ->
  m_inp mb' = m_inp mb -> m_aout mb' = m_aout mb -> m_ow mb' = m_ow mb ->
  Kr W0 wrap src pos inp aout ma' mb'.
Proof.
  intros K Hh Ea Eb E Ei Eo Ew. destruct K as [[S] Ki Ka Kw Kh Kwa Kwb Khd].
  unfold irk_mf in E. injection E; intros.
  constructor; try congruence.
  all: try (constructor; try congruence; rewrite Ea, Eb, Ew; exact S).
  all: try (rewrite Ea; exact Kwa).
  all: try (rewrite Eb; exact Kwb).
  all: intros _ Hm; exfalso; apply Hh; unfold m_mode in *; congruence.
Qed.

(* a new state on both sides (srel with the same noout: the output is unchanged), wbits kept *)
Lemma irk_state W0 wrap src pos inp aout ma mb sa sb :
  Kr W0 wrap src pos inp aout ma mb ->
  srel (m_ow mb = []) sa sb -> i_mode sb <> HEAD ->
  i_wrap sb = wrap -> i_head sb = false ->
  i_wbits sa = i_wbits (m_s ma) -> i_wbits sb = i_wbits (m_s mb) ->
  Kr W0 wrap src pos inp aout (set_m_s ma sa) (set_m_s mb sb).
Proof.
  intros K S Hh Hw Hd Ea Eb. destruct K as [[_] Ki Ka Kw Kh Kwa Kwb Khd].
  constructor; cbn [m_s set_m_s m_inp m_aout m_ow m_mode]; auto.
  - constructor; cbn [m_s set_m_s m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_msg
      m_tin m_tout m_snx m_sow]; auto.
  - rewrite Ea. exact Kwa.
  - rewrite Eb. exact Kwb.
  - intros _ Hm. exfalso. apply Hh. unfold m_mode in Hm. exact Hm.
Qed.

(* the machine-only operations keep irk_mf related and the state *)
Lemma irk_pull ma mb : irk_mf ma = irk_mf mb -> irk_mf (pull ma) = irk_mf (pull mb).
Proof. unfold irk_mf, pull, m_have. intros E. injection E; intros. destruct ma, mb; cbn in *; subst; reflexivity. Qed.

Lemma irk_dropbits n ma mb : irk_mf ma = irk_mf mb -> irk_mf (dropbits n ma) = irk_mf (dropbits n mb).
Proof. unfold irk_mf, dropbits. intros E. injection E; intros. destruct ma, mb; cbn in *; subst; reflexivity. Qed.

Lemma irk_leave ma mb : irk_mf ma = irk_mf mb -> irk_mf (set_leave ma) = irk_mf (set_leave mb).
Proof. unfold irk_mf, set_leave. intros E. injection E; intros. destruct ma, mb; cbn in *; subst; reflexivity. Qed.

Lemma irk_ret r ma mb : irk_mf ma = irk_mf mb -> irk_mf (set_m_ret ma r) = irk_mf (set_m_ret mb r).
Proof. unfold irk_mf. intros E. injection E; intros. destruct ma, mb; cbn in *; subst; reflexivity. Qed.

Lemma irk_set_s ma mb sa sb : irk_mf ma = irk_mf mb -> irk_mf (set_m_s ma sa) = irk_mf (set_m_s mb sb).
Proof. unfold irk_mf. intros E. destruct ma, mb; exact E. Qed.

Lemma irk_needbits : forall k n ma mb, irk_mf ma = irk_mf mb ->
  irk_mf (needbits_f k n ma) = irk_mf (needbits_f k n mb) /\
  m_s (needbits_f k n ma) = m_s ma /\ m_s (needbits_f k n mb) = m_s mb /\
  m_inp (needbits_f k n mb) = m_inp mb /\ m_aout (needbits_f k n mb) = m_aout mb /\
  m_ow (needbits_f k n mb) = m_ow mb.
Proof.
  induction k; intros n ma mb E; cbn [needbits_f]; [repeat split; auto|].
  assert (Eb: m_bits ma = m_bits mb) by (unfold irk_mf in E; congruence).
  assert (Eh: m_have ma = m_have mb) by (unfold irk_mf, m_have in *; injection E; intros; congruence).
  rewrite Eb, Eh.
  destruct (m_bits mb <? n); [|repeat split; auto].
  destruct (m_have mb =? 0).
  - repeat split; auto. apply irk_leave; auto.
  - destruct (IHk n (pull ma) (pull mb) (irk_pull ma mb E)) as (A & B & C & D & F & G).
    repeat split; auto; first [rewrite B | rewrite C | rewrite D | rewrite F | rewrite G]; reflexivity.
Qed.

(* the one-stream invariant of Step3Tables.v: mwf3x, the same as Inv3.mwf3 *)
Notation mwf3x := Zlib.proof.inflate.Step3Inv.mwf3x.

Lemma irk_mwf3x_iff: forall m, Inv3.mwf3 m <-> mwf3x m.
Proof.
  intros m. split.
  - intros [W [A B C D]]. constructor; auto. constructor; auto.
    intros E. destruct (B E) as (sz & S1 & S2 & S3). exists sz. split; auto. split; auto.
    intros i Hi. specialize (S3 i Hi). unfold Inv2.len_ok in S3. unfold Zlib.proof.inflate.StepInv.len_ok.
    intros R; specialize (S3 R); lia.
  - intros [W [A B C D]]. split; auto. constructor; auto.
    intros E. destruct (D E) as (sz & S1 & S2 & S3). exists sz. split; auto. split; auto.
    intros i Hi. specialize (S3 i Hi). unfold Inv2.len_ok. unfold Zlib.proof.inflate.StepInv.len_ok in S3.
    intros R; specialize (S3 R); lia.
Qed.

Lemma irk_cover2 : Zlib.proof.inflate.Cover3.cover3_stmt -> Zlib.proof.inflate.Cover2Def.cover2_stmt.
Proof.
  intros C type lens req old root used t A B D E F.
  destruct (C type lens req old root used t A B D E F) as (G & H & _). auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The parts                                                                                      *)

(* CODELENS's while loop, in lockstep (IRTabCLLoop.v) *)
Definition irt_clloop_stmt : Prop :=
  forall k W0 wrap src pos inp aout ma mb,
    Kr W0 wrap src pos inp aout ma mb -> mwf3x ma -> mwf3x mb -> m_leave mb = 0 -> m_mode mb = CODELENS ->
    match codelens_loop lenfix_list distfix_list k ma, codelens_loop lenfix_list distfix_list k mb with
    | CLnext ma', CLnext mb' => Kr W0 wrap src pos inp aout ma' mb'
    | CLleave ma', CLleave mb' => Kr W0 wrap src pos inp aout ma' mb'
    | CLbad ma', CLbad mb' => Kr W0 wrap src pos inp aout ma' mb'
    | _, _ => False
    end.

(* CODELENS after the loop: the LENS and DISTS tables (IRTabCLPost.v) *)
Definition irt_clpost_stmt : Prop :=
  forall W0 wrap src pos inp aout ma mb,
    Kr W0 wrap src pos inp aout ma mb -> mwf3x ma -> mwf3x mb -> m_leave mb = 0 -> m_mode mb = CODELENS ->
    i_nlen (m_s mb) + i_ndist (m_s mb) <= i_have (m_s mb) ->
    irt_rr W0 wrap src pos inp aout (irt_clpost ma) (irt_clpost mb).

(* CODELENS: loop and tables (IRSimTab.v from the two above) *)
Definition irt_cl_stmt : Prop :=
  forall W0 wrap src pos inp aout ma mb,
    Kr W0 wrap src pos inp aout ma mb -> mwf3x ma -> mwf3x mb -> m_leave mb = 0 -> m_mode mb = CODELENS ->
    irt_rr W0 wrap src pos inp aout (irt_cl ma) (irt_cl mb).

(* LENLENS: loop, zeros, the code length code, then CODELENS (IRTabLL.v) *)
Definition irt_ll_stmt : Prop :=
  forall W0 wrap src pos inp aout ma mb,
    Kr W0 wrap src pos inp aout ma mb -> mwf3x ma -> mwf3x mb -> m_leave mb = 0 -> m_mode mb = LENLENS ->
    irt_rr W0 wrap src pos inp aout (irt_ll ma) (irt_ll mb).

(* TABLE, then LENLENS (IRSimTab.v) *)
Definition irt_tab_stmt : Prop :=
  forall W0 wrap src pos inp aout ma mb,
    Kr W0 wrap src pos inp aout ma mb -> mwf3x ma -> mwf3x mb -> m_leave mb = 0 -> m_mode mb = TABLE ->
    irt_rr W0 wrap src pos inp aout (irt_tab ma) (irt_tab mb).
