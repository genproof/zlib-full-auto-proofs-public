(* RT-D part PARAMS: lemmas for deflateParams.
   - [deflate_block_codes]: the return codes of deflate(strm, Z_BLOCK), for any output space (the LT theory's
     api_deflate needs avail_out <= 2^20, kf_params_stmt allows 2^21);
   - [hinv_facts]: hdr_facts hinv (the body of RTDLTHdr.hdr_theory). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDV2.
Require Import Zlib.proof.roundtrip.RTDLTHdrKit Zlib.proof.roundtrip.RTDLTHdrStages Zlib.proof.roundtrip.RTDLTHdr.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Return codes of the stages *)
Definition okc (r : option dres) : Prop := forall s z c, r = Some (s, z, Some c) -> c = Z_OK.

Ltac kcrush :=
  repeat match goal with
  | H : Some _ = Some _ |- _ => injection H; clear H; intros; subst
  | H : None = Some _ |- _ => discriminate H
  | H : bind ?x _ = Some _ |- _ => destruct x eqn:?; cbn [bind] in H
  | H : (if ?b then _ else _) = Some _ |- _ => destruct b eqn:?
  | H : (match ?x with _ => _ end) = Some _ |- _ => destruct x eqn:?
  | H : (let '(_, _) := ?x in _) = Some _ |- _ => destruct x eqn:?
  end.

Lemma then_stage_okc : forall r k, okc r -> (forall s z, okc (k s z)) -> okc (then_stage r k).
Proof.
  intros r k Hr Hk s z c E. unfold then_stage in E.
  destruct r as [[[s1 z1] [o|]]|]; cbn [bind] in E; [|exact (Hk s1 z1 s z c E)|discriminate].
  injection E; intros; subst. exact (Hr _ _ _ eq_refl).
Qed.

Lemma okc_none : forall s z, okc (Some (s, z, None)).
Proof. intros s z s' z' c E. discriminate. Qed.

Lemma flush_or_return_okc : forall s z, okc (c_flush_or_return s z).
Proof. intros s z s' z' c E. unfold c_flush_or_return in E. kcrush; reflexivity. Qed.

Lemma zlib_header_okc : forall s z, okc (c_deflate_zlib_header s z).
Proof.
  intros s z. unfold c_deflate_zlib_header.
  destruct (_ =? INIT_STATE); [|apply okc_none].
  intros s' z' c E. kcrush; eapply flush_or_return_okc; eassumption.
Qed.

Lemma gzip_header_okc : forall s z, okc (c_deflate_gzip_header s z).
Proof.
  intros s z s' z' c E. unfold c_deflate_gzip_header in E. kcrush; try eapply flush_or_return_okc; eassumption.
Qed.

Lemma extra_okc : forall s z, okc (c_deflate_extra s z).
Proof.
  intros s z. unfold c_deflate_extra. destruct (_ =? EXTRA_STATE); [|apply okc_none].
  intros s' z' c E. kcrush; try reflexivity.
  all: revert E; apply then_stage_okc; [intros ? ? ? E; kcrush; reflexivity|intros; apply okc_none].
Qed.

Lemma str_okc : forall h o r s z, okc (c_deflate_str h o r s z).
Proof. intros h o r s z s' z' c E. unfold c_deflate_str in E. kcrush; reflexivity. Qed.

Lemma name_okc : forall s z, okc (c_deflate_name s z).
Proof.
  intros s z. unfold c_deflate_name. destruct (_ =? NAME_STATE); [|apply okc_none].
  destruct (c_gzhead s) as [h|]; cbn [bind]; [|intros ? ? ? E; discriminate].
  apply then_stage_okc; [apply str_okc|intros; apply okc_none].
Qed.

Lemma comment_okc : forall s z, okc (c_deflate_comment s z).
Proof.
  intros s z. unfold c_deflate_comment. destruct (_ =? COMMENT_STATE); [|apply okc_none].
  destruct (c_gzhead s) as [h|]; cbn [bind]; [|intros ? ? ? E; discriminate].
  apply then_stage_okc; [apply str_okc|intros; apply okc_none].
Qed.

Lemma hcrc_okc : forall s z, okc (c_deflate_hcrc s z).
Proof.
  intros s z. unfold c_deflate_hcrc. destruct (_ =? HCRC_STATE); [|apply okc_none].
  destruct (c_gzhead s) as [h|]; cbn [bind]; [|intros ? ? ? E; discriminate].
  apply then_stage_okc; [|intros; apply flush_or_return_okc].
  destruct (gz_hcrc h =? 0); [apply okc_none|].
  apply then_stage_okc.
  - destruct (_ >? _); [apply flush_or_return_okc|apply okc_none].
  - intros s1 z1 s' z' c E. kcrush.
Qed.

Lemma compress_okc : forall s z flush, okc (c_deflate_compress s z flush).
Proof. intros s z flush s' z' c E. unfold c_deflate_compress in E. kcrush; reflexivity. Qed.

Lemma flush_pending_status : forall s z s' z', c_flush_pending s z = Some (s', z') -> d_status s' = d_status s.
Proof. intros s z s' z' E. unfold c_flush_pending in E. kcrush; [reflexivity|].
  match goal with |- context [if ?b then _ else _] => destruct b; reflexivity end.
Qed.

Lemma entry_block_codes : forall s z s' z' o,
  c_deflate_entry s z Z_BLOCK = Some (s', z', o) ->
  o = None \/ o = Some Z_OK \/ o = Some Z_STREAM_ERROR \/
  (o = Some Z_BUF_ERROR /\ z_avail_in z' = z_avail_in z /\ z_avail_out z' = z_avail_out z).
Proof.
  intros s z s' z' o E. unfold c_deflate_entry, then_stage in E. kcrush; auto.
  all: try (right; right; right; repeat split; reflexivity).
  all: try discriminate.
  all: exfalso; repeat match goal with H: c_flush_pending _ _ = Some _ |- _ => apply flush_pending_status in H end.
  all: change (d_status (set_d_last_flush ?x ?y)) with (d_status x) in *.
  all: rewrite ?andb_true_iff, ?andb_false_iff in *; unfold Z_BLOCK, Z_FINISH in *; cbn [negb Z.eqb Pos.eqb] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H | H : _ \/ _ |- _ => destruct H end;
    try discriminate; congruence.
Qed.

(** deflate(strm, Z_BLOCK) returns Z_OK, Z_STREAM_ERROR, or Z_BUF_ERROR without progress. *)
Lemma deflate_block_codes : forall s z s1 z1 c,
  c_deflate s z Z_BLOCK = Some (s1, z1, c) ->
  c = Z_OK \/ c = Z_STREAM_ERROR \/
  (c = Z_BUF_ERROR /\ z_avail_in z1 = z_avail_in z /\ z_avail_out z1 = z_avail_out z).
Proof.
  intros s z s1 z1 c E. unfold c_deflate in E.
  destruct (_ || _ || _).
  { injection E; intros; subst; auto. }
  unfold then_stage at 1 in E.
  destruct (c_deflate_entry s z Z_BLOCK) as [[[s0 z0] o0]|] eqn:Ee; cbn [bind] in E; [|discriminate].
  destruct (entry_block_codes _ _ _ _ _ Ee) as [->|[->|[->|(-> & A1 & A2)]]].
  - match type of E with bind ?r _ = _ => assert (Hr : okc r) end.
    { repeat (apply then_stage_okc; [first [apply zlib_header_okc | apply gzip_header_okc | apply extra_okc |
        apply name_okc | apply comment_okc | apply hcrc_okc]|intros]). apply compress_okc. }
    revert E Hr. match goal with |- bind ?r _ = _ -> _ => destruct r as [[[s2 z2] [o2|]]|] end;
      cbn [bind]; intros E Hr; [| |discriminate].
    + injection E; intros; subst. left. exact (Hr _ _ _ eq_refl).
    + unfold c_deflate_trailer in E. cbn in E. injection E; intros; subst; auto.
  - cbn in E. injection E; intros; subst; auto.
  - cbn in E. injection E; intros; subst; auto.
  - cbn in E. injection E; intros; subst; auto.
Qed.

(** ** hdr_facts hinv (the proof of RTDLTHdr.hdr_theory, verbatim) *)
Lemma hinv_facts : hdr_facts hinv.
Proof.
  split.
  - exact hinv_frame.
  - exact hinv_status.
  - intros s z H k [Hp [Ho [P0 [Hs [Hbv [Hav [Ht [Hok Hcase]]]]]]]].
    assert (Hav' : 0 <= z_avail_out z) by lia.
    rewrite hdr_stages_eq.
    destruct Hcase as [[Hst [Hw [EH ->]]] | [[Hst [Hw [EH ->]]] | Hi]].
    + (* INIT: zlib header or raw *)
      destruct (zlib_stage s z Hp Ho P0 Hs Hbv Hav' Ht Hst Hw) as [s1 [z1 [r1 [E [Es Hpost]]]]].
      rewrite E. subst H. destruct r1 as [c|].
      * exists s1, z1, (Some c). split; [reflexivity|exact Hpost].
      * cbn [then_stage bind]. rewrite (proj1 (busy_rest s1 z1 Es)).
        exists s1, z1, None. split; [reflexivity|exact Hpost].
    + (* GZIP *)
      rewrite zlib_id by (rewrite Hst; discriminate). cbn [then_stage bind].
      assert (EH' : H = gz_hdr_bytes (d_gzhead s) (xfl_byte s)) by (rewrite EH; unfold hdr_bytes; rewrite Hw; reflexivity).
      rewrite EH'.
      destruct (gzip_stage s z Hp Ho P0 Hs Hbv Hav' Ht Hst Hw Hok) as [s1 [z1 [r1 [E Hr]]]].
      rewrite E. destruct Hr as [[-> Hg] | [Es Hpost]].
      * cbn [then_stage bind]. apply chain_extra. exact Hg.
      * destruct r1 as [c|].
        -- exists s1, z1, (Some c). split; [reflexivity|exact Hpost].
        -- cbn [then_stage bind]. rewrite (proj2 (busy_rest s1 z1 Es)).
           exists s1, z1, None. split; [reflexivity|exact Hpost].
    + (* resume in the middle of a gzip header *)
      pose proof (hinv_gent s z H k Hp Ho P0 Hs Hbv Hav' Ht Hi) as Hg.
      destruct (hinv_status _ _ _ _ Hi) as [_ [_ [Hst _]]].
      assert (N1 : d_status s <> INIT_STATE) by (destruct Hst as [S|[S|[S|S]]]; rewrite S; discriminate).
      assert (N2 : d_status s <> GZIP_STATE) by (destruct Hst as [S|[S|[S|S]]]; rewrite S; discriminate).
      rewrite zlib_id by assumption. cbn [then_stage bind]. rewrite gzip_id by assumption. cbn [then_stage bind].
      destruct Hst as [S|[S|[S|S]]]; rewrite S in Hg.
      * apply chain_extra. exact Hg.
      * unfold from_extra. rewrite extra_id by (rewrite S; discriminate). cbn [then_stage bind].
        apply chain_name. exact Hg.
      * unfold from_extra. rewrite extra_id by (rewrite S; discriminate). cbn [then_stage bind].
        unfold from_name. rewrite name_id by (rewrite S; discriminate). cbn [then_stage bind].
        apply chain_comment. exact Hg.
      * unfold from_extra. rewrite extra_id by (rewrite S; discriminate). cbn [then_stage bind].
        unfold from_name. rewrite name_id by (rewrite S; discriminate). cbn [then_stage bind].
        unfold from_comment. rewrite comment_id by (rewrite S; discriminate). cbn [then_stage bind].
        apply hcrc_stage. exact Hg.
Qed.
