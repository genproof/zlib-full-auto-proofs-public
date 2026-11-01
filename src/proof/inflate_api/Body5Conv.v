(* Facts the body assembly of inflate() (Body5_inflate.v) needs besides the parts: the machine at the
   loop head (m_init, Spec5.v) satisfies the invariants; the memory of a final machine is the stream of
   inflate_spec's postcondition. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate_api.Body5Parts.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* The machine at the loop head                                                                   *)

Definition s_typedo (s: istate) : istate :=
  if i_mode s =? Zlib.proof.inflate.Model.TYPE then set_i_mode s TYPEDO else s.

Ltac mode_consts := unfold HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT,
  Zlib.proof.inflate.Model.TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN,
  LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE, BAD, MEM, SYNC in *.

Lemma s_typedo_swf: forall s, swf s -> swf (s_typedo s).
Proof.
  intros s H. unfold s_typedo. destruct (Z.eqb_spec (i_mode s) Zlib.proof.inflate.Model.TYPE); [ | exact H].
  destruct H; constructor; simpl; auto. mode_consts. lia.
Qed.

Lemma s_typedo_modewf: forall s, modewf s -> modewf (s_typedo s).
Proof.
  intros s H. unfold s_typedo. destruct (Z.eqb_spec (i_mode s) Zlib.proof.inflate.Model.TYPE); [ | exact H].
  constructor; simpl; unfold decode_mode; mode_consts; intros; lia.
Qed.

Lemma s_typedo_swf3: forall s, swf3 s -> swf3 (s_typedo s).
Proof.
  intros s H. unfold s_typedo. destruct (Z.eqb_spec (i_mode s) Zlib.proof.inflate.Model.TYPE); [ | exact H].
  destruct H; constructor; simpl; auto; unfold decode_mode; mode_consts; intros; lia.
Qed.

Lemma s_typedo_win_inv5: forall s, win_inv5 s -> win_inv5 (s_typedo s).
Proof.
  intros s H. unfold s_typedo. destruct (Z.eqb_spec (i_mode s) Zlib.proof.inflate.Model.TYPE); [ | exact H].
  destruct H as [H1 H2]. split; simpl; auto.
  intros A B. destruct (H2 A B) as [C D]. split; [exact C | ]. mode_consts. lia.
Qed.

Lemma m_init_s: forall z L inp, m_s (m_init z L inp) = s_typedo (l_s L).
Proof. reflexivity. Qed.

Lemma live_win_inv5: forall L, live_ok L -> win_inv5 (l_s L).
Proof.
  intros L (_ & _ & _ & _ & _ & _ & W1 & _ & W2). split; assumption.
Qed.

Lemma m_init_mwf3: forall z L inp,
  live_ok L -> zf_ok z -> zf_ao z <= Int.max_signed ->
  Zlength inp <= Int.max_signed -> bytes_ok inp ->
  mwf3 (m_init z L inp).
Proof.
  intros z L inp (HP & HS & HM & HH & HS3 & _) HZ HA HI HB.
  destruct HZ as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
  pose proof (Zlength_nonneg inp).
  split.
  - pose proof (sw_hold _ HS). pose proof (sw_bits _ HS).
    constructor; unfold m_init; simpl;
      try (fold (s_typedo (l_s L)));
      try (apply s_typedo_modewf; exact HM);
      try (apply s_typedo_swf; exact HS);
      try exact HH;
      unfold urange, lrange, Z_OK in *; rewrite ?Zlength_nil;
      try solve [lia | split; [lia | auto] | split; [lia | constructor] | left; reflexivity].
  - apply s_typedo_swf3. exact HS3.
Qed.

Lemma m_init_out_inv: forall z L inp, 0 <= zf_ao z -> out_inv (m_init z L inp).
Proof.
  intros z L inp H. unfold out_inv, m_left, m_init. simpl. rewrite Zlength_nil. split; [lia | split; [lia | auto]].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The memory of a final machine as inflate_spec's postcondition                                 *)

(* the stream fields and the live part the memory mem_rep F m represents *)
Definition z_of (F: frame) (m: mst) : zfields :=
  ZF (in_ptr (f_ib F) (m_snx m)) (Zlength (m_inp m) - m_snx m) (m_tin m) (out_ptr (f_ob F) (m_sow m))
     (m_aout m - m_sow m) (m_tout m) (m_msg m) (f_dt F) (m_adler m) (f_vres F).

Definition live_of (F: frame) (m: mst) : live :=
  Live (f_sp F) (f_winp F) (m_s m) (m_h m) (f_headp F) (f_hsh F) (f_xb F) (f_nb F) (f_cb F).

Lemma mem_rep_istream5: forall F m,
  live_ok (live_of F m) -> zf_ok (z_of F m) -> writable_share (f_shs F) -> f_strmp F <> nullval ->
  mem_rep F m * hdr_tok F m * malloc_token Ews t_state (f_sp F) * state_pad (f_sp F) |--
  istream_opt (f_gv F) (f_shs F) (f_strmp F) (z_of F m) (Some (live_of F m)) *
  head_opt (is_live (f_strmp F) (Some (live_of F m))) * in_rep (f_ib F) *
  out_opt (Some (f_ob F)) (m_ow m) * tables_rep (f_gsh F) (f_gv F) * crc_table_at (f_tsh F) (f_gv F).
Proof.
  intros F m HL HZ HW HN.
  unfold istream_opt, is_live. destruct (eq_dec (f_strmp F) nullval) as [E | _]; [contradiction | ].
  unfold istream, zstrm_at, state_mem, head_opt, head_mem, mem_rep, head_part, hdr_tok, out_opt.
  unfold z_of, live_of; simpl.
  destruct (i_head (m_s m)); entailer!.
Qed.

Lemma fin_ok5_live: forall F m, fin_ok5 m -> hd_ok F m -> isptr (f_sp F) -> writable_share (f_hsh F) ->
  srange (f_dt F) ->
  live_ok (live_of F m) /\ zf_ok (z_of F m).
Proof.
  intros F m (A & B & C & D & [W1 W2] & E1 & E2 & E3 & E4 & E5 & E6 & E7) H P WH Q.
  split.
  - unfold live_ok, live_of; simpl. unfold hd_ok in H. auto 10.
  - unfold zf_ok, z_of, srange, lrange in *; simpl. rep_lia.
Qed.

Lemma mwf3_fin_ok5: forall m, mwf3 m -> win_inv5 (m_s m) -> fin_ok5 m.
Proof.
  intros m [W S3] WI.
  pose proof (mw_inp _ W). pose proof (mw_ow _ W). pose proof (mw_sow _ W). pose proof (mw_snx _ W).
  pose proof (mw_aout _ W). pose proof (Zlength_nonneg (m_ow m)).
  pose proof (mw_tin _ W). pose proof (mw_tout _ W). pose proof (mw_adler _ W).
  unfold fin_ok5, lrange in *.
  refine (conj (mw_s _ W) (conj (mw_md _ W) (conj (mw_h _ W) (conj S3 (conj WI _))))).
  repeat split; lia.
Qed.
