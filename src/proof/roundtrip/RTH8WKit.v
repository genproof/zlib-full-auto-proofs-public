(* The machine invariant of the header cases with an application header of any uInt buffer sizes, in the form
   the header-case proofs read it (round 1's port docs/port-hl/cfg_rth8w.py of the v6 header-case proofs,
   RTHCaseHEAD6 .. RTHCasesNC6 and RTH8CaseHCRC; here docs/port-hl/cfg_rth9h.py builds on it).

   Inv.v's mwf holds the header invariant hwf, which caps extra_max / name_max / comm_max at 65536.  [hwf8r] is
   RTH8Spec.hwf8 as a record (the three sizes any uInt), [mwf8] is mwf with hwf8r in place of hwf, and [mwf3w] is
   Inv3.mwf3 with mwf8.  The case proofs destruct and project the invariant; with these records the projections
   (the fields mw8_ and h8_) have the types of Inv.v's (mw_ and hw_) but for the three bounds.  [mwf3w] is equivalent to
   RTH8W.mwf3_8 ([mwf3w_iff]), so the cases proved with mwf3w give RTH8W.cases8w_all ([cases8w_all_of_v]).

   The lemmas of mwf that the case proofs use (MwfLemmas, HdrKit5, ExKit5, CaseEXLEN5, CaseNAME5, CaseCOMMENT5,
   HeadGzipW5) are moved to mwf8 here: their facts about the fields other than the header are those of the
   machine with the empty header [hz] (which has hwf), and the header's fact is shown directly.  One of them
   needs more: the copy of case EXTRA into the extra buffer tests `len + copy > extra_max` in 32 bits, which may
   wrap once extra_max may be close to 2^32; [mwf8_extra_upd] takes the header invariant's bound
   0 <= length <= extra_len (RTHSpec.hinv6), under which len + copy <= extra_len does not wrap. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTH8Spec.
Require Import Zlib.proof.roundtrip.RTHCase.
Require Import Zlib.proof.roundtrip.RTH8Defs.
Require Import Zlib.proof.roundtrip.RTH8CaseKit.
Require Import Zlib.proof.roundtrip.RTH8W.
Require Import Zlib.proof.inflate.MwfLemmas.
Require Import Zlib.proof.inflate.HdrKit5.
Require Import Zlib.proof.inflate.ExKit5.
Require Import Zlib.proof.inflate.CaseEXLEN5.
Require Import Zlib.proof.inflate.CaseNAME5.
Require Import Zlib.proof.inflate.CaseCOMMENT5.
Require Import Zlib.proof.inflate.HeadGzipW5.
Require Import Zlib.proof.inflate.NCMach5.
Require Import Zlib.proof.inflate.NCKit5.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Module IM := Zlib.proof.inflate.Model.

(* ---------------------------------------------------------------------------------------------- *)
(* the invariant                                                                                  *)

Record hwf8r (h: hstate) : Prop := {
  h8_text : srange (h_text h);
  h8_time : lrange (h_time h);
  h8_xflags : srange (h_xflags h);
  h8_os : srange (h_os h);
  h8_extra_len : urange (h_extra_len h);
  h8_extra_max : 0 <= h_extra_max h <= Int.max_unsigned;
  h8_name_max : 0 <= h_name_max h <= Int.max_unsigned;
  h8_comm_max : 0 <= h_comm_max h <= Int.max_unsigned;
  h8_xbuf : Zlength (h_xbuf h) = h_extra_max h /\ bytes_ok (h_xbuf h);
  h8_nbuf : Zlength (h_nbuf h) = h_name_max h /\ bytes_ok (h_nbuf h);
  h8_cbuf : Zlength (h_cbuf h) = h_comm_max h /\ bytes_ok (h_cbuf h);
  h8_hcrc : srange (h_hcrc h);
  h8_done : srange (h_done h) }.

Record mwf8 (m: mst) : Prop := {
  mw8_md : modewf (m_s m);
  mw8_s : swf (m_s m);
  mw8_h : hwf8r (m_h m);
  mw8_inp : Zlength (m_inp m) <= Int.max_signed /\ bytes_ok (m_inp m);
  mw8_aout : 0 <= m_aout m <= Int.max_signed;
  mw8_nx : 0 <= m_nx m <= Zlength (m_inp m);
  mw8_ow : Zlength (m_ow m) <= m_aout m /\ bytes_ok (m_ow m);
  mw8_hold : lrange (m_hold m);
  mw8_bits : 0 <= m_bits m <= 39;
  mw8_in : m_in m = Zlength (m_inp m);
  mw8_out : urange (m_out m);
  mw8_ret : -5 <= m_ret m <= 2;
  mw8_leave : 0 <= m_leave m <= 1;
  mw8_adler : lrange (m_adler m);
  mw8_tin : lrange (m_tin m);
  mw8_tout : lrange (m_tout m);
  mw8_snx : 0 <= m_snx m <= Zlength (m_inp m);
  mw8_sow : 0 <= m_sow m <= Zlength (m_ow m);
  mw8_outeq : m_out m = m_aout m \/ m_mode m = LENGTH \/ m_mode m = DONE \/ m_mode m = BAD }.

Definition mwf3w (m: mst) : Prop := mwf8 m /\ swf3 (m_s m).

Lemma hwf8r_iff: forall h, hwf8 h <-> hwf8r h.
Proof.
  intros h. unfold hwf8. split.
  - intros (A & B & C & D & E & F & G & H & I & J & K & L & M). constructor; auto.
  - intros []. tauto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* mwf8 and mwf: the same facts but the header's                                                  *)

(* the empty header *)
Definition hz : hstate := HS 0 0 0 0 false 0 0 [] false 0 [] false 0 [] 0 0.

Lemma hwf_hz: hwf hz.
Proof.
  constructor; cbn; unfold srange, lrange, urange; try rep_lia; split; try reflexivity; constructor.
Qed.

Lemma mwf8_of_any: forall m h, mwf (set_m_h m h) -> hwf8r (m_h m) -> mwf8 m.
Proof. intros m h W H. destruct W. constructor; cbn in *; auto. Qed.

Lemma mwf_of_mwf8: forall m h, mwf8 m -> hwf h -> mwf (set_m_h m h).
Proof. intros m h W H. destruct W. constructor; cbn in *; auto. Qed.

Lemma mwf8_of: forall m, mwf (set_m_h m hz) -> hwf8r (m_h m) -> mwf8 m.
Proof. intros m. apply mwf8_of_any. Qed.

Lemma mwf8_to: forall m, mwf8 m -> mwf (set_m_h m hz).
Proof. intros m W. apply mwf_of_mwf8; [exact W | exact hwf_hz]. Qed.

Lemma mwf_set_h: forall m h, mwf m -> hwf h -> mwf (set_m_h m h).
Proof. intros m h W H. destruct W. constructor; cbn in *; auto. Qed.

Lemma mwf3w_of: forall m, mwf3 (set_m_h m hz) -> hwf8r (m_h m) -> mwf3w m.
Proof. intros m [W S] H. split; [apply mwf8_of; auto | exact S]. Qed.

Lemma mwf3w_to: forall m, mwf3w m -> mwf3 (set_m_h m hz).
Proof. intros m [W S]. split; [apply mwf8_to; auto | exact S]. Qed.

(* a machine whose fields other than the header are those of a machine with mwf (with any header) *)
Lemma mwf8_tr: forall m m', mwf m' -> set_m_h m hz = set_m_h m' hz -> hwf8r (m_h m) -> mwf8 m.
Proof.
  intros m m' W E H. apply mwf8_of; [ | exact H]. rewrite E. apply mwf_set_h; [exact W | exact hwf_hz].
Qed.

Lemma mwf3w_tr: forall m m', mwf3 m' -> set_m_h m hz = set_m_h m' hz -> hwf8r (m_h m) -> mwf3w m.
Proof.
  intros m m' [W S] E H. split; [apply (mwf8_tr m m' W E H) | ].
  change (swf3 (m_s (set_m_h m hz))). rewrite E. exact S.
Qed.

(* the small header of RTH8W.mcanon has hwf *)
Lemma cz_range: forall n, 0 <= cz n <= 1.
Proof. intros n. unfold cz. destruct (n =? 0); lia. Qed.

Lemma bytes_ok_zeros: forall k, bytes_ok (repeat 0 k).
Proof. intros k. unfold bytes_ok. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst; rep_lia. Qed.

Lemma Zlength_zeros: forall n, Zlength (repeat 0 (Z.to_nat (cz n))) = cz n.
Proof. intros n. rewrite Zlength_repeat; pose proof (cz_range n); lia. Qed.

Lemma hwf_hcanon: forall h, hwf (hcanon h).
Proof.
  intros h. pose proof (cz_range (h_extra_max h)). pose proof (cz_range (h_name_max h)).
  pose proof (cz_range (h_comm_max h)).
  constructor; cbn; unfold srange, lrange, urange; try rep_lia;
    (split; [apply Zlength_zeros | apply bytes_ok_zeros]).
Qed.

Lemma mwf3w_iff: forall m, mwf3_8 m <-> mwf3w m.
Proof.
  intros m. unfold mwf3_8, mcanon. split.
  - intros [[W S] H]. split; [apply (mwf8_of_any m (hcanon (m_h m))); [exact W | apply hwf8r_iff; exact H] | exact S].
  - intros [W S]. split; [split; [apply mwf_of_mwf8; [exact W | apply hwf_hcanon] | exact S] | ].
    apply hwf8r_iff. apply (mw8_h _ W).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the header facts                                                                               *)

Ltac hwf8_set := intros; match goal with H: hwf8r _ |- _ => destruct H end; constructor; simpl; auto.

Lemma hwf8_set_text: forall h v, hwf8r h -> srange v -> hwf8r (set_h_text h v). Proof. hwf8_set. Qed.
Lemma hwf8_set_time: forall h v, hwf8r h -> lrange v -> hwf8r (set_h_time h v). Proof. hwf8_set. Qed.
Lemma hwf8_set_xflags_os: forall h v w, hwf8r h -> srange v -> srange w ->
  hwf8r (set_h_os (set_h_xflags h v) w).
Proof. hwf8_set. Qed.
Lemma hwf8_set_extra_len: forall h v, hwf8r h -> urange v -> hwf8r (set_h_extra_len h v). Proof. hwf8_set. Qed.
Lemma hwf8_set_xp: forall h v, hwf8r h -> hwf8r (set_h_xp h v). Proof. hwf8_set. Qed.
Lemma hwf8_set_np: forall h v, hwf8r h -> hwf8r (set_h_np h v). Proof. hwf8_set. Qed.
Lemma hwf8_set_cp: forall h v, hwf8r h -> hwf8r (set_h_cp h v). Proof. hwf8_set. Qed.
Lemma hwf8_set_xbuf: forall h v, hwf8r h -> Zlength v = h_extra_max h -> bytes_ok v -> hwf8r (set_h_xbuf h v).
Proof. hwf8_set. Qed.
Lemma hwf8_set_nbuf: forall h v, hwf8r h -> Zlength v = h_name_max h -> bytes_ok v -> hwf8r (set_h_nbuf h v).
Proof. hwf8_set. Qed.
Lemma hwf8_set_cbuf: forall h v, hwf8r h -> Zlength v = h_comm_max h -> bytes_ok v -> hwf8r (set_h_cbuf h v).
Proof. hwf8_set. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the lemmas of mwf used by the header cases, over mwf8                                          *)

Lemma needbits_f_set_h: forall k n m h, needbits_f k n (set_m_h m h) = set_m_h (needbits_f k n m) h.
Proof.
  induction k; intros n m h; [reflexivity |]. cbn [needbits_f].
  change (m_bits (set_m_h m h)) with (m_bits m). change (m_have (set_m_h m h)) with (m_have m).
  destruct (m_bits m <? n); [| reflexivity]. destruct (m_have m =? 0); [reflexivity |].
  change (pull (set_m_h m h)) with (set_m_h (pull m) h). apply IHk.
Qed.

Lemma mwf8_have: forall m, mwf8 m -> 0 <= m_have m <= Int.max_signed.
Proof. intros m W. exact (mwf_have _ (mwf8_to m W)). Qed.

Lemma mwf8_needbits: forall n m, mwf8 m -> n <= 32 -> mwf8 (needbits n m).
Proof.
  intros n m W N. apply (mwf8_tr _ (needbits n (set_m_h m hz))).
  - apply mwf_needbits; [apply mwf8_to; exact W | exact N].
  - unfold needbits. rewrite needbits_f_set_h. reflexivity.
  - rewrite (proj2 (needbits_sh n m)). apply (mw8_h _ W).
Qed.

Lemma mwf8_initbits: forall m, mwf8 m -> mwf8 (initbits m).
Proof.
  intros m W. apply (mwf8_tr _ (initbits (set_m_h m hz))); [apply mwf_initbits, mwf8_to; exact W | reflexivity |].
  apply (mw8_h _ W).
Qed.

Lemma mwf8_crc_if: forall m d, mwf8 m -> is_bytes d -> mwf8 (crc_if m d).
Proof.
  intros m d W B. apply (mwf8_tr _ (crc_if (set_m_h m hz) d)).
  - apply mwf_crc_if; [apply mwf8_to; exact W | exact B].
  - rewrite !crc_if_eq. reflexivity.
  - rewrite crc_if_eq. apply (mw8_h _ W).
Qed.

Lemma mwf8_upd_h: forall m f, mwf8 m -> hwf8r (f (m_h m)) -> mwf8 (upd_h m f).
Proof. intros m f W H. apply (mwf8_tr _ (set_m_h m hz)); [apply mwf8_to; exact W | reflexivity | exact H]. Qed.

Lemma mwf3w_set_mode_hdr: forall m md,
  mwf8 m -> HEAD <= m_mode m <= TYPEDO -> FLAGS <= md <= TYPEDO -> mwf3w (set_mode m md).
Proof.
  intros m md W HM Hmd. apply (mwf3w_tr _ (set_mode (set_m_h m hz) md)).
  - apply mwf3_set_mode_hdr; [apply mwf8_to; exact W | exact HM | exact Hmd].
  - reflexivity.
  - apply (mw8_h _ W).
Qed.

Lemma mwf3w_exlen_fin: forall m1, mwf8 m1 -> m_mode m1 = EXLEN ->
  mwf3w (set_mode (exlen_fin m1) EXTRA) /\ m_leave (set_mode (exlen_fin m1) EXTRA) = m_leave m1.
Proof.
  intros m1 W HM.
  destruct (mwf3_exlen_fin (set_m_h m1 hz) (mwf8_to m1 W) HM) as [W1 L1].
  assert (E: set_m_h (set_mode (exlen_fin m1) EXTRA) hz = set_m_h (set_mode (exlen_fin (set_m_h m1 hz)) EXTRA) hz).
  { unfold exlen_fin. cbv zeta. rewrite !crc_if_eq. cbn -[crc_val].
    destruct (i_head (m_s m1)); reflexivity. }
  split.
  - apply (mwf3w_tr _ _ W1 E).
    unfold exlen_fin. cbv zeta.
    change (i_head (m_s (upd_s m1 (fun s => set_i_length s (u32 (m_hold m1)))))) with (i_head (m_s m1)).
    destruct (i_head (m_s m1)); rewrite crc_if_eq; cbn;
      [apply hwf8_set_extra_len; [apply (mw8_h _ W) | apply u32_range] | apply (mw8_h _ W)].
  - change (m_leave (set_m_h (set_mode (exlen_fin m1) EXTRA) hz) = m_leave (set_m_h m1 hz)).
    rewrite E. exact L1.
Qed.

Lemma mwf3w_exlen_skip: forall m, mwf8 m -> m_mode m = EXLEN ->
  mwf3w (set_mode (exlen_skip m) EXTRA) /\ m_leave (set_mode (exlen_skip m) EXTRA) = m_leave m.
Proof.
  intros m W HM.
  destruct (mwf3_exlen_skip (set_m_h m hz) (mwf8_to m W) HM) as [W1 L1].
  split; [ | unfold exlen_skip; destruct (i_head (m_s m)); reflexivity].
  apply (mwf3w_tr _ _ W1).
  - unfold exlen_skip. change (i_head (m_s (set_m_h m hz))) with (i_head (m_s m)).
    destruct (i_head (m_s m)); reflexivity.
  - unfold exlen_skip. destruct (i_head (m_s m)); cbn; [apply hwf8_set_xp | ]; apply (mw8_h _ W).
Qed.

Lemma mwf3w_extra_fin: forall m, mwf8 m -> m_mode m = EXTRA ->
  mwf3w (extra_fin m) /\ m_leave (extra_fin m) = m_leave m.
Proof.
  intros m W HM.
  destruct (mwf3_extra_fin (set_m_h m hz) (mwf8_to m W) HM) as [W1 L1].
  split; [ | exact L1].
  apply (mwf3w_tr _ _ W1); [reflexivity | apply (mw8_h _ W)].
Qed.

Lemma mwf3w_fin_c: forall m1, mwf8 m1 -> m_mode m1 = COMMENT -> mwf3w (fin_c m1).
Proof.
  intros m1 W HM. apply (mwf3w_tr _ _ (mwf3_fin_c (set_m_h m1 hz) (mwf8_to m1 W) HM));
    [reflexivity | apply (mw8_h _ W)].
Qed.

Lemma mwf3w_fin_n: forall m1, mwf8 m1 -> m_mode m1 = NAME -> mwf3w (fin_n m1).
Proof.
  intros m1 W HM. apply (mwf3w_tr _ _ (mwf3_fin_n (set_m_h m1 hz) (mwf8_to m1 W) HM));
    [reflexivity | apply (mw8_h _ W)].
Qed.

Lemma mwf8_ex_m3: forall m1, mwf8 m1 -> m_mode m1 = EXLEN -> mwf8 (ex_m3 m1).
Proof.
  intros m1 W HM. apply (mwf8_tr _ _ (mwf_ex_m3 (set_m_h m1 hz) (mwf8_to m1 W) HM)).
  - unfold ex_m3. change (i_head (m_s (set_m_h m1 hz))) with (i_head (m_s m1)).
    destruct (i_head (m_s m1)); reflexivity.
  - unfold ex_m3. destruct (i_head (m_s m1)); cbn; [apply hwf8_set_extra_len; [ | apply u32_range] | ];
      apply (mw8_h _ W).
Qed.

Lemma mwf8_cp_false: forall m,
  mwf8 m -> mwf8 (if i_head (m_s m) then upd_h m (fun h => set_h_cp h false) else m).
Proof.
  intros m W. destruct (i_head (m_s m)); [ | exact W]. apply mwf8_upd_h; [exact W | apply hwf8_set_cp, (mw8_h _ W)].
Qed.

Lemma mwf8_np_false: forall m,
  mwf8 m -> mwf8 (if i_head (m_s m) then upd_h m (fun h => set_h_np h false) else m).
Proof.
  intros m W. destruct (i_head (m_s m)); [ | exact W]. apply mwf8_upd_h; [exact W | apply hwf8_set_np, (mw8_h _ W)].
Qed.

Lemma bytes_ok_nil: bytes_ok [].
Proof. constructor. Qed.

Lemma mwf8_nm_loop: forall m ln bf,
  mwf8 m -> m_mode m = NAME -> urange ln -> Zlength bf = h_name_max (m_h m) -> bytes_ok bf ->
  mwf8 (nm_loop m ln bf).
Proof.
  intros m ln bf W HM RL LB BB.
  apply (mwf8_tr _ _ (mwf_nm_loop (set_m_h m hz) ln [] (mwf8_to m W) HM RL eq_refl bytes_ok_nil));
    [reflexivity | ].
  cbn. apply hwf8_set_nbuf; [apply (mw8_h _ W) | exact LB | exact BB].
Qed.

Lemma mwf8_cm_loop: forall m ln bf,
  mwf8 m -> m_mode m = COMMENT -> urange ln -> Zlength bf = h_comm_max (m_h m) -> bytes_ok bf ->
  mwf8 (cm_loop m ln bf).
Proof.
  intros m ln bf W HM RL LB BB.
  apply (mwf8_tr _ _ (mwf_cm_loop (set_m_h m hz) ln [] (mwf8_to m W) HM RL eq_refl bytes_ok_nil));
    [reflexivity | ].
  cbn. apply hwf8_set_cbuf; [apply (mw8_h _ W) | exact LB | exact BB].
Qed.

Lemma mwf8_nm_name: forall m c ln bf,
  mwf8 m -> m_mode m = NAME -> urange ln -> Zlength bf = h_name_max (m_h m) -> bytes_ok bf ->
  0 <= c <= m_have m -> mwf8 (nm_name m c ln bf).
Proof.
  intros m c ln bf W HM RL LB BB C.
  apply (mwf8_tr _ _ (mwf_nm_name (set_m_h m hz) c ln [] (mwf8_to m W) HM RL eq_refl bytes_ok_nil C)).
  - unfold nm_name. rewrite !crc_if_eq. reflexivity.
  - unfold nm_name. rewrite crc_if_eq. cbn. apply hwf8_set_nbuf; [apply (mw8_h _ W) | exact LB | exact BB].
Qed.

Lemma mwf8_cm_comment: forall m c ln bf,
  mwf8 m -> m_mode m = COMMENT -> urange ln -> Zlength bf = h_comm_max (m_h m) -> bytes_ok bf ->
  0 <= c <= m_have m -> mwf8 (nm_comment m c ln bf).
Proof.
  intros m c ln bf W HM RL LB BB C.
  apply (mwf8_tr _ _ (mwf_cm_comment (set_m_h m hz) c ln [] (mwf8_to m W) HM RL eq_refl bytes_ok_nil C)).
  - unfold nm_comment. rewrite !crc_if_eq. reflexivity.
  - unfold nm_comment. rewrite crc_if_eq. cbn. apply hwf8_set_cbuf; [apply (mw8_h _ W) | exact LB | exact BB].
Qed.

(* EXTRA's copy count when len + copy does not wrap (ExKit5.extra_n_range without the cap 65536) *)
Lemma extra_n_range8: forall len copy max,
  0 <= len < max -> 0 <= copy -> len + copy <= Int.max_unsigned ->
  0 <= extra_n len copy max <= copy /\ len + extra_n len copy max <= max.
Proof.
  intros len copy max A B C. unfold extra_n, u32.
  rewrite Z.mod_small by rep_lia.
  destruct (Z.ltb_spec max (len + copy)); lia.
Qed.

(* case EXTRA's update; the header invariant's bound on length (RTHSpec.hinv6) keeps len + copy from wrapping *)
Lemma mwf8_extra_upd: forall m, mwf8 m -> m_mode m = EXTRA ->
  (i_head (m_s m) = true -> h_xp (m_h m) = true -> 0 <= i_length (m_s m) <= h_extra_len (m_h m)) ->
  mwf8 (extra_upd m) /\ m_mode (extra_upd m) = EXTRA /\ m_leave (extra_upd m) = m_leave m.
Proof.
  intros m W HM HX.
  destruct (mwf_extra_upd (set_m_h m hz) (mwf8_to m W) HM) as (W1 & M1 & L1).
  assert (E: set_m_h (extra_upd m) hz = set_m_h (extra_upd (set_m_h m hz)) hz).
  { unfold extra_upd. cbv zeta.
    change (m_s (set_m_h m hz)) with (m_s m). change (m_have (set_m_h m hz)) with (m_have m).
    destruct (negb _); [ | reflexivity].
    destruct (andb (andb _ (h_xp (m_h (set_m_h m hz)))) _), (andb (andb _ (h_xp (m_h m))) _);
      rewrite !crc_if_eq; reflexivity. }
  assert (HU: hwf8r (m_h (extra_upd m))).
  { pose proof (mw8_h _ W) as H8.
    unfold extra_upd. cbv zeta.
    destruct (negb (Z.min (i_length (m_s m)) (m_have m) =? 0)); [ | exact H8].
    pose proof (mwf8_have m W) as HV.
    pose proof (sw_length _ (mw8_s _ W)) as LN. unfold urange in LN.
    set (copy := Z.min (i_length (m_s m)) (m_have m)) in *.
    assert (CP: 0 <= copy <= m_have m /\ copy <= i_length (m_s m)) by lia.
    set (len := u32 (h_extra_len (m_h m) - i_length (m_s m))).
    destruct (andb (andb (i_head (m_s m)) (h_xp (m_h m))) (len <? h_extra_max (m_h m))) eqn:EC;
      rewrite crc_if_eq; cbn [m_h set_m_nx upd_s set_m_s upd_h set_m_h]; [ | exact H8].
    apply andb_prop in EC. destruct EC as [EC EL]. apply andb_prop in EC. destruct EC as [EH EP].
    apply Z.ltb_lt in EL.
    specialize (HX EH EP).
    pose proof (h8_extra_len _ H8) as UXL. unfold urange in UXL.
    assert (U0: len = h_extra_len (m_h m) - i_length (m_s m)) by (unfold len, u32; apply Z.mod_small; rep_lia).
    destruct (extra_n_range8 len copy (h_extra_max (m_h m))) as [N1 N2]; [lia | lia | rep_lia | ].
    unfold extra_n in N1, N2.
    set (n := if h_extra_max (m_h m) <? u32 (len + copy) then h_extra_max (m_h m) - len else copy) in *.
    pose proof (mw8_nx _ W) as NX. pose proof (mw8_inp _ W) as INP.
    assert (LB: Zlength (inbytes m n) = n) by (apply inbytes_len; unfold m_have in *; lia).
    pose proof (h8_xbuf _ H8) as [X1 X2].
    apply hwf8_set_xbuf; [exact H8 | rewrite put_bytes_len; lia | ].
    apply put_bytes_ok; auto; try lia. apply inbytes_ok. tauto. }
  split; [apply (mwf8_tr _ _ W1 E HU) | ].
  split.
  - change (m_mode (set_m_h (extra_upd m) hz) = EXTRA). rewrite E. exact M1.
  - change (m_leave (set_m_h (extra_upd m) hz) = m_leave (set_m_h m hz)). rewrite E. exact L1.
Qed.

(* HeadGzipW5.head_gzip_nowin over mwf3w *)
Lemma head_gzip_nowin8: forall m,
  mwf3w m -> m_mode m = HEAD -> i_wrap (m_s m) <> 0 ->
  i_wbits (m_s (needbits 16 m)) = 0 -> i_win (m_s (needbits 16 m)) = false.
Proof.
  intros m [_ S3] HM Hw Hb. unfold needbits in *. rewrite hg_needbits_f_s in *.
  exact (proj2 (s3_head _ S3 HM Hb Hw)).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the header cases' statements over mwf3w                                                        *)

(* RTHCase.fall_post6 with mwf3w *)
Definition fall_post8v (F: frame) (m: mst) (Y: Z) : environ -> mpred :=
  EX m': mst,
    !! (stepf2 (f_flush F) lenfix_list distfix_list m = stepf2 (f_flush F) lenfix_list distfix_list m' /\
        m_mode m' = Y /\ m_leave m' = 0 /\ mwf3w m' /\ hd_ok F m' /\ hdr_tok F m' = hdr_tok F m /\
        i_head (m_s m') = true) &&
    (loop_stateH F m' * (fun _ => hd6 F m')).

(* RTH8Defs.case_ok8 with mwf3w *)
Definition case_ok8v {Espec: OracleKind} (F: frame) (Y: Z) (i: nat) : Prop :=
  forall m n, m_mode m = Y -> m_leave m = 0 -> mwf3w m -> hd_ok F m -> i_head (m_s m) = true ->
    hpass8 (f_flush F) (S n) m ->
    semax Delta_cases5 (loop_stateH F m * (fun _ => hdr_tok F m * hd6 F m))
      (seq_of_labeled_statement (ls_drop i inflate_LS))
      (frame_ret_assert (switch_ret_assert (case_post8 F m)) (fun _ => hdr_tok F m)).

Lemma case_ok8w_of_v {Espec: OracleKind}: forall F Y i, case_ok8v F Y i -> case_ok8w F Y i.
Proof. intros F Y i C m n HM HL W. apply C; auto. apply mwf3w_iff; exact W. Qed.

(* RTH8CaseKit.case_fallthrough8 with mwf3w *)
Lemma case_fallthrough8v {Espec: OracleKind} (F: frame) (m: mst) (n: nat) (Y: Z) (i: nat):
  (i < 32)%nat -> hdr_mode Y = true -> hdr_mode (m_mode m) = true -> hpass8 (f_flush F) (S n) m ->
  case_ok8v F Y (S i) ->
  semax Delta_cases5 (loop_stateH F m * (fun _ => hdr_tok F m * hd6 F m)) (case_body i)
    (overridePost (fall_post8v F m Y * (fun _ => hdr_tok F m))
       (frame_ret_assert (switch_ret_assert (case_post8 F m)) (fun _ => hdr_tok F m))) ->
  semax Delta_cases5 (loop_stateH F m * (fun _ => hdr_tok F m * hd6 F m))
    (seq_of_labeled_statement (ls_drop i inflate_LS))
    (frame_ret_assert (switch_ret_assert (case_post8 F m)) (fun _ => hdr_tok F m)).
Proof.
  intros Hi HY Hm HP HC HB. rewrite seq_split by lia.
  eapply semax_seq; [exact HB | ].
  unfold fall_post8v. rewrite exp_sepcon1. apply extract_exists_pre. intros m'.
  rewrite sepcon_andp_prop'. apply semax_extract_prop. intros (E & HM & HL & W & HD & HT & HH).
  rewrite (case_post8_eq F m m' E). rewrite <- HT.
  assert (HP': hpass8 (f_flush F) (S n) m') by (apply (hpass8_same _ n m m'); auto; rewrite HM; exact HY).
  eapply semax_pre; [ | apply (HC m' n); auto].
  intros rho. simpl. apply andp_left2. cancel.
Qed.

(* the parts *)
Definition rth_head_stmt8v : Prop :=
  forall {Espec: OracleKind} (F: frame), frame_ok5 F -> case_ok8v F IM.HEAD 0.

Definition rth_fto_stmt8v : Prop :=
  forall {Espec: OracleKind} (F: frame), frame_ok5 F ->
    (case_ok8v F IM.TIME 2 -> case_ok8v F IM.FLAGS 1) /\ (case_ok8v F IM.OS 3 -> case_ok8v F IM.TIME 2) /\
    (case_ok8v F IM.EXLEN 4 -> case_ok8v F IM.OS 3).

Definition rth_ex_stmt8v : Prop :=
  forall {Espec: OracleKind} (F: frame), frame_ok5 F ->
    (case_ok8v F IM.EXTRA 5 -> case_ok8v F IM.EXLEN 4) /\ (case_ok8v F IM.NAME 6 -> case_ok8v F IM.EXTRA 5).

Definition rth_nc_stmt8v : Prop :=
  forall {Espec: OracleKind} (F: frame), frame_ok5 F ->
    (case_ok8v F IM.COMMENT 7 -> case_ok8v F IM.NAME 6) /\ (case_ok8v F IM.HCRC 8 -> case_ok8v F IM.COMMENT 7).

Definition rth_hcrc_stmt8v : Prop :=
  forall {Espec: OracleKind} (F: frame), frame_ok5 F -> case_ok8v F IM.HCRC 8.

Lemma cases8w_all_of_parts:
  rth_head_stmt8v -> rth_fto_stmt8v -> rth_ex_stmt8v -> rth_nc_stmt8v -> rth_hcrc_stmt8v -> cases8w_all.
Proof.
  intros HH FT XE NC HC Espec F HF.
  pose proof (HC Espec F HF) as C8.
  destruct (NC Espec F HF) as [N6 N7]. pose proof (N7 C8) as C7. pose proof (N6 C7) as C6.
  destruct (XE Espec F HF) as [E4 E5]. pose proof (E5 C6) as C5. pose proof (E4 C5) as C4.
  destruct (FT Espec F HF) as (F1 & F2 & F3). pose proof (F3 C4) as C3. pose proof (F2 C3) as C2.
  pose proof (F1 C2) as C1. pose proof (HH Espec F HF) as C0.
  intros i Hi. apply case_ok8w_of_v.
  do 9 (destruct i as [|i]; [ eassumption | ]). exfalso; lia.
Qed.
