(* The machine invariant of the header cases for calls of any uInt size with an application header of any uInt
   buffer sizes, in the form the header-case proofs read it (the port docs/port-hl/cfg_rth9h.py of the header cases'
   proofs uses this file), and the statement of a header case that may leave or fail (RTH9HDefs.case_ok9h).

   RTH8WKit's [mwf8] is Inv.mwf with RTH8WKit.hwf8r (header buffers of any uInt size) in place of Inv.hwf; [mwf9]
   is the same with avail_in / avail_out up to Int.max_unsigned (as InvW.mwfW), and [mwf39] adds Inv3.swf3 and
   InvW.hdrW (the bit buffer before EXLEN and the extra length in EXTRA) as InvW.mwf3W does.  [mwf39] is equivalent
   to RTH9HDefs.mwf3_9 ([mwf39_iff]).  The lemmas of mwf8 that the case proofs use are moved to mwf9 as RTH8WKit
   does: their facts about the fields other than the header are those of the wide machine with the empty header
   RTH8WKit.hz (the lemmas of the za port, whose invariant Inv.mwf_za is the wide mwf), the header's fact is shown
   directly.  Where InvW.hdrW of the successor needs a fact of the machine, the lemma takes it as the za port's
   lemma does (the end of EXLEN: the bit buffer below 2^24; EXLEN without an extra field: the flag clear).

   [case_ok9v] is RTH9HDefs.case_ok9h with mwf39 for mwf3_9: a header case from a header mode, with the partial
   header, ends in the machine of one pass of the model, with RTH9HDefs.hd9 (a header mode, after a leave or a
   fall-through, keeps the partial header; past the header modes the header is passed or left raw). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTH8Spec.
Require Import Zlib.proof.roundtrip.RTHCase.
Require Import Zlib.proof.roundtrip.RTH8W.
Require Import Zlib.proof.roundtrip.RTH8WKit.
Require Import Zlib.proof.roundtrip.RTH9HDefs.
Require Import Zlib.proof.inflate.InvW.
Require Import Zlib.proof.inflate.HeadGzipW5.
Require Import Zlib.proof.inflate.NCMach5.
Require Import Zlib.proof.inflate.NCKit5.
Require Import Zlib.proof.za.inflate.Inv.
Require Import Zlib.proof.za.inflate.Inv3.
Require Import Zlib.proof.za.inflate.MwfLemmas.
Require Import Zlib.proof.za.inflate.ExHdrKit5.
Require Import Zlib.proof.za.inflate.ExKit5.
Require Import Zlib.proof.za.inflate.CaseEXLEN5.
Require Import Zlib.proof.za.inflate.CaseNAME5.
Require Import Zlib.proof.za.inflate.CaseCOMMENT5.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Module IM := Zlib.proof.inflate.Model.

(* ---------------------------------------------------------------------------------------------- *)
(* the invariant                                                                                  *)

Record mwf9 (m: mst) : Prop := {
  mw9_md : modewf (m_s m);
  mw9_s : swf (m_s m);
  mw9_h : hwf8r (m_h m);
  mw9_inp : Zlength (m_inp m) <= Int.max_unsigned /\ bytes_ok (m_inp m);
  mw9_aout : 0 <= m_aout m <= Int.max_unsigned;
  mw9_nx : 0 <= m_nx m <= Zlength (m_inp m);
  mw9_ow : Zlength (m_ow m) <= m_aout m /\ bytes_ok (m_ow m);
  mw9_hold : lrange (m_hold m);
  mw9_bits : 0 <= m_bits m <= 39;
  mw9_in : m_in m = Zlength (m_inp m);
  mw9_out : urange (m_out m);
  mw9_ret : -5 <= m_ret m <= 2;
  mw9_leave : 0 <= m_leave m <= 1;
  mw9_adler : lrange (m_adler m);
  mw9_tin : lrange (m_tin m);
  mw9_tout : lrange (m_tout m);
  mw9_snx : 0 <= m_snx m <= Zlength (m_inp m);
  mw9_sow : 0 <= m_sow m <= Zlength (m_ow m);
  mw9_outeq : m_out m = m_aout m \/ m_mode m = LENGTH \/ m_mode m = DONE \/ m_mode m = BAD }.

Definition mwf39 (m: mst) : Prop := mwf9 m /\ swf3 (m_s m) /\ hdrW m.

(* ---------------------------------------------------------------------------------------------- *)
(* mwf9 and the za port's wide mwf_za: the same facts but the header's                            *)

Lemma mwf9_of_any: forall m h, mwf_za (set_m_h m h) -> hwf8r (m_h m) -> mwf9 m.
Proof. intros m h W H. destruct W. constructor; cbn in *; auto. Qed.

Lemma mwf_za_of_mwf9: forall m h, mwf9 m -> hwf h -> mwf_za (set_m_h m h).
Proof. intros m h W H. destruct W. constructor; cbn in *; auto. Qed.

Lemma mwf9_to: forall m, mwf9 m -> mwf_za (set_m_h m hz).
Proof. intros m W. apply mwf_za_of_mwf9; [exact W | exact hwf_hz]. Qed.

Lemma mwf_za_set_h: forall m h, mwf_za m -> hwf h -> mwf_za (set_m_h m h).
Proof. intros m h W H. destruct W. constructor; cbn in *; auto. Qed.

(* a machine whose fields other than the header are those of a machine with mwf_za (with any header) *)
Lemma mwf9_tr: forall m m', mwf_za m' -> set_m_h m hz = set_m_h m' hz -> hwf8r (m_h m) -> mwf9 m.
Proof.
  intros m m' W E H. apply (mwf9_of_any m hz); [ | exact H]. rewrite E. apply mwf_za_set_h; [exact W | exact hwf_hz].
Qed.

Lemma mwf39_tr: forall m m', mwf3_za m' -> set_m_h m hz = set_m_h m' hz -> hwf8r (m_h m) -> mwf39 m.
Proof.
  intros m m' (W & S & HW) E H. split; [apply (mwf9_tr m m' W E H) | split].
  - change (swf3 (m_s (set_m_h m hz))). rewrite E. exact S.
  - change (hdrW (set_m_h m hz)). rewrite E. exact HW.
Qed.

(* RTH9HDefs' form of the invariant: InvW.mwf3W of the machine with the small header, hwf8 of the header *)
Lemma mwf39_iff: forall m, mwf3_9 m <-> mwf39 m.
Proof.
  intros m. unfold mwf3_9, mwf3W, mcanon. split.
  - intros [(W & S & HW) H]. split; [ | split; [exact S | exact HW]].
    destruct W. apply hwf8r_iff in H. constructor; cbn in *; auto.
  - intros (W & S & HW). split; [split; [ | split; [exact S | exact HW]] | apply hwf8r_iff, (mw9_h _ W)].
    destruct W. constructor; cbn in *; auto. apply hwf_hcanon.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the lemmas of mwf used by the header cases, over mwf9                                          *)

Lemma mwf9_have: forall m, mwf9 m -> 0 <= m_have m <= Int.max_unsigned.
Proof. intros m W. exact (mwf_have_za _ (mwf9_to m W)). Qed.

Lemma mwf9_needbits: forall n m, mwf9 m -> n <= 32 -> mwf9 (needbits n m).
Proof.
  intros n m W N. apply (mwf9_tr _ (needbits n (set_m_h m hz))).
  - apply mwf_needbits_za; [apply mwf9_to; exact W | exact N].
  - unfold needbits. rewrite needbits_f_set_h. reflexivity.
  - rewrite (proj2 (needbits_sh n m)). apply (mw9_h _ W).
Qed.

Lemma mwf9_initbits: forall m, mwf9 m -> mwf9 (initbits m).
Proof.
  intros m W. apply (mwf9_tr _ (initbits (set_m_h m hz))); [apply mwf_initbits_za, mwf9_to; exact W | reflexivity |].
  apply (mw9_h _ W).
Qed.

Lemma mwf9_crc_if: forall m d, mwf9 m -> is_bytes d -> mwf9 (crc_if m d).
Proof.
  intros m d W B. apply (mwf9_tr _ (crc_if (set_m_h m hz) d)).
  - apply mwf_crc_if_za; [apply mwf9_to; exact W | exact B].
  - rewrite !crc_if_eq. reflexivity.
  - rewrite crc_if_eq. apply (mw9_h _ W).
Qed.

Lemma mwf9_upd_h: forall m f, mwf9 m -> hwf8r (f (m_h m)) -> mwf9 (upd_h m f).
Proof. intros m f W H. apply (mwf9_tr _ (set_m_h m hz)); [apply mwf9_to; exact W | reflexivity | exact H]. Qed.

(* a header mode set from a header mode; InvW.hdrW of the new machine is the caller's *)
Lemma mwf39_set_mode_hdr: forall m md,
  mwf9 m -> HEAD <= m_mode m <= TYPEDO -> FLAGS <= md <= TYPEDO -> hdrW (set_mode m md) -> mwf39 (set_mode m md).
Proof.
  intros m md W HM Hmd HW. apply (mwf39_tr _ (set_mode (set_m_h m hz) md)).
  - apply mwf3_set_mode_hdr_za; [apply mwf9_to; exact W | exact HM | exact Hmd | exact HW].
  - reflexivity.
  - apply (mw9_h _ W).
Qed.

(* the end of EXLEN with an extra field: the length read from a bit buffer below 2^24 *)
Lemma mwf39_exlen_fin: forall m1, mwf9 m1 -> m_mode m1 = EXLEN -> m_hold m1 < 2 ^ 24 ->
  mwf39 (set_mode (exlen_fin m1) EXTRA) /\ m_leave (set_mode (exlen_fin m1) EXTRA) = m_leave m1.
Proof.
  intros m1 W HM HB.
  destruct (mwf3_exlen_fin_za (set_m_h m1 hz) (mwf9_to m1 W) HM HB) as [W1 L1].
  assert (E: set_m_h (set_mode (exlen_fin m1) EXTRA) hz = set_m_h (set_mode (exlen_fin (set_m_h m1 hz)) EXTRA) hz).
  { unfold exlen_fin. cbv zeta. rewrite !crc_if_eq. cbn -[crc_val].
    destruct (i_head (m_s m1)); reflexivity. }
  split.
  - apply (mwf39_tr _ _ W1 E).
    unfold exlen_fin. cbv zeta.
    change (i_head (m_s (upd_s m1 (fun s => set_i_length s (u32 (m_hold m1)))))) with (i_head (m_s m1)).
    destruct (i_head (m_s m1)); rewrite crc_if_eq; cbn;
      [apply hwf8_set_extra_len; [apply (mw9_h _ W) | apply u32_range] | apply (mw9_h _ W)].
  - change (m_leave (set_m_h (set_mode (exlen_fin m1) EXTRA) hz) = m_leave (set_m_h m1 hz)).
    rewrite E. exact L1.
Qed.

(* EXLEN without an extra field *)
Lemma mwf39_exlen_skip: forall m, mwf9 m -> m_mode m = EXLEN -> Z.land (i_flags (m_s m)) 1024 = 0 ->
  mwf39 (set_mode (exlen_skip m) EXTRA) /\ m_leave (set_mode (exlen_skip m) EXTRA) = m_leave m.
Proof.
  intros m W HM HF.
  destruct (mwf3_exlen_skip_za (set_m_h m hz) (mwf9_to m W) HM HF) as [W1 L1].
  split; [ | unfold exlen_skip; destruct (i_head (m_s m)); reflexivity].
  apply (mwf39_tr _ _ W1).
  - unfold exlen_skip. change (i_head (m_s (set_m_h m hz))) with (i_head (m_s m)).
    destruct (i_head (m_s m)); reflexivity.
  - unfold exlen_skip. destruct (i_head (m_s m)); cbn; [apply hwf8_set_xp | ]; apply (mw9_h _ W).
Qed.

Lemma mwf39_extra_fin: forall m, mwf9 m -> m_mode m = EXTRA ->
  mwf39 (extra_fin m) /\ m_leave (extra_fin m) = m_leave m.
Proof.
  intros m W HM.
  destruct (mwf3_extra_fin_za (set_m_h m hz) (mwf9_to m W) HM) as [W1 L1].
  split; [ | exact L1].
  apply (mwf39_tr _ _ W1); [reflexivity | apply (mw9_h _ W)].
Qed.

Lemma mwf39_fin_c: forall m1, mwf9 m1 -> m_mode m1 = COMMENT -> mwf39 (fin_c m1).
Proof.
  intros m1 W HM. apply (mwf39_tr _ _ (mwf3_fin_c_za (set_m_h m1 hz) (mwf9_to m1 W) HM));
    [reflexivity | apply (mw9_h _ W)].
Qed.

Lemma mwf39_fin_n: forall m1, mwf9 m1 -> m_mode m1 = NAME -> mwf39 (fin_n m1).
Proof.
  intros m1 W HM. apply (mwf39_tr _ _ (mwf3_fin_n_za (set_m_h m1 hz) (mwf9_to m1 W) HM));
    [reflexivity | apply (mw9_h _ W)].
Qed.

Lemma mwf9_ex_m3: forall m1, mwf9 m1 -> m_mode m1 = EXLEN -> mwf9 (ex_m3 m1).
Proof.
  intros m1 W HM. apply (mwf9_tr _ _ (mwf_ex_m3_za (set_m_h m1 hz) (mwf9_to m1 W) HM)).
  - unfold ex_m3. change (i_head (m_s (set_m_h m1 hz))) with (i_head (m_s m1)).
    destruct (i_head (m_s m1)); reflexivity.
  - unfold ex_m3. destruct (i_head (m_s m1)); cbn; [apply hwf8_set_extra_len; [ | apply u32_range] | ];
      apply (mw9_h _ W).
Qed.

Lemma mwf9_cp_false: forall m,
  mwf9 m -> mwf9 (if i_head (m_s m) then upd_h m (fun h => set_h_cp h false) else m).
Proof.
  intros m W. destruct (i_head (m_s m)); [ | exact W]. apply mwf9_upd_h; [exact W | apply hwf8_set_cp, (mw9_h _ W)].
Qed.

Lemma mwf9_np_false: forall m,
  mwf9 m -> mwf9 (if i_head (m_s m) then upd_h m (fun h => set_h_np h false) else m).
Proof.
  intros m W. destruct (i_head (m_s m)); [ | exact W]. apply mwf9_upd_h; [exact W | apply hwf8_set_np, (mw9_h _ W)].
Qed.

Lemma mwf9_nm_loop: forall m ln bf,
  mwf9 m -> m_mode m = NAME -> urange ln -> Zlength bf = h_name_max (m_h m) -> bytes_ok bf ->
  mwf9 (nm_loop m ln bf).
Proof.
  intros m ln bf W HM RL LB BB.
  apply (mwf9_tr _ _ (mwf_nm_loop_za (set_m_h m hz) ln [] (mwf9_to m W) HM RL eq_refl bytes_ok_nil));
    [reflexivity | ].
  cbn. apply hwf8_set_nbuf; [apply (mw9_h _ W) | exact LB | exact BB].
Qed.

Lemma mwf9_cm_loop: forall m ln bf,
  mwf9 m -> m_mode m = COMMENT -> urange ln -> Zlength bf = h_comm_max (m_h m) -> bytes_ok bf ->
  mwf9 (cm_loop m ln bf).
Proof.
  intros m ln bf W HM RL LB BB.
  apply (mwf9_tr _ _ (mwf_cm_loop_za (set_m_h m hz) ln [] (mwf9_to m W) HM RL eq_refl bytes_ok_nil));
    [reflexivity | ].
  cbn. apply hwf8_set_cbuf; [apply (mw9_h _ W) | exact LB | exact BB].
Qed.

Lemma mwf9_nm_name: forall m c ln bf,
  mwf9 m -> m_mode m = NAME -> urange ln -> Zlength bf = h_name_max (m_h m) -> bytes_ok bf ->
  0 <= c <= m_have m -> mwf9 (nm_name m c ln bf).
Proof.
  intros m c ln bf W HM RL LB BB C.
  apply (mwf9_tr _ _ (mwf_nm_name_za (set_m_h m hz) c ln [] (mwf9_to m W) HM RL eq_refl bytes_ok_nil C)).
  - unfold nm_name. rewrite !crc_if_eq. reflexivity.
  - unfold nm_name. rewrite crc_if_eq. cbn. apply hwf8_set_nbuf; [apply (mw9_h _ W) | exact LB | exact BB].
Qed.

Lemma mwf9_cm_comment: forall m c ln bf,
  mwf9 m -> m_mode m = COMMENT -> urange ln -> Zlength bf = h_comm_max (m_h m) -> bytes_ok bf ->
  0 <= c <= m_have m -> mwf9 (nm_comment m c ln bf).
Proof.
  intros m c ln bf W HM RL LB BB C.
  apply (mwf9_tr _ _ (mwf_cm_comment_za (set_m_h m hz) c ln [] (mwf9_to m W) HM RL eq_refl bytes_ok_nil C)).
  - unfold nm_comment. rewrite !crc_if_eq. reflexivity.
  - unfold nm_comment. rewrite crc_if_eq. cbn. apply hwf8_set_cbuf; [apply (mw9_h _ W) | exact LB | exact BB].
Qed.

(* case EXTRA's update: the extra length below 2^31 (InvW.hdrW with an extra field) for the wide machine, and the
   header invariant's bound on length (RTHSpec.hinv6), which keeps len + copy from wrapping *)
Lemma mwf9_extra_upd: forall m, mwf9 m -> m_mode m = EXTRA -> i_length (m_s m) <= Int.max_signed ->
  (i_head (m_s m) = true -> h_xp (m_h m) = true -> 0 <= i_length (m_s m) <= h_extra_len (m_h m)) ->
  mwf9 (extra_upd m) /\ m_mode (extra_upd m) = EXTRA /\ m_leave (extra_upd m) = m_leave m.
Proof.
  intros m W HM HLM HX.
  destruct (mwf_extra_upd_za (set_m_h m hz) (mwf9_to m W) HM HLM) as (W1 & M1 & L1).
  assert (E: set_m_h (extra_upd m) hz = set_m_h (extra_upd (set_m_h m hz)) hz).
  { unfold extra_upd. cbv zeta.
    change (m_s (set_m_h m hz)) with (m_s m). change (m_have (set_m_h m hz)) with (m_have m).
    destruct (negb _); [ | reflexivity].
    destruct (andb (andb _ (h_xp (m_h (set_m_h m hz)))) _), (andb (andb _ (h_xp (m_h m))) _);
      rewrite !crc_if_eq; reflexivity. }
  assert (HU: hwf8r (m_h (extra_upd m))).
  { pose proof (mw9_h _ W) as H8.
    unfold extra_upd. cbv zeta.
    destruct (negb (Z.min (i_length (m_s m)) (m_have m) =? 0)); [ | exact H8].
    pose proof (mwf9_have m W) as HV.
    pose proof (sw_length _ (mw9_s _ W)) as LN. unfold urange in LN.
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
    pose proof (mw9_nx _ W) as NX. pose proof (mw9_inp _ W) as INP.
    assert (LB: Zlength (inbytes m n) = n) by (apply inbytes_len; unfold m_have in *; lia).
    pose proof (h8_xbuf _ H8) as [X1 X2].
    apply hwf8_set_xbuf; [exact H8 | rewrite put_bytes_len; lia | ].
    apply put_bytes_ok; auto; try lia. apply inbytes_ok. tauto. }
  split; [apply (mwf9_tr _ _ W1 E HU) | ].
  split.
  - change (m_mode (set_m_h (extra_upd m) hz) = EXTRA). rewrite E. exact M1.
  - change (m_leave (set_m_h (extra_upd m) hz) = m_leave (set_m_h m hz)). rewrite E. exact L1.
Qed.

(* HeadGzipW5.head_gzip_nowin over mwf39 *)
Lemma head_gzip_nowin9: forall m,
  mwf39 m -> m_mode m = HEAD -> i_wrap (m_s m) <> 0 ->
  i_wbits (m_s (needbits 16 m)) = 0 -> i_win (m_s (needbits 16 m)) = false.
Proof.
  intros m [_ [S3 _]] HM Hw Hb. unfold needbits in *. rewrite hg_needbits_f_s in *.
  exact (proj2 (s3_head _ S3 HM Hb Hw)).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the header cases' statements over mwf39                                                        *)

Lemma case_post9_eq: forall F m m',
  stepf2 (f_flush F) lenfix_list distfix_list m = stepf2 (f_flush F) lenfix_list distfix_list m' ->
  case_post9 F m = case_post9 F m'.
Proof. intros F m m' E. unfold case_post9. rewrite E. reflexivity. Qed.

(* the end of a header case's body falling into the header mode Y (RTHCase.fall_post6 with mwf39) *)
Definition fall_post9v (F: frame) (m: mst) (Y: Z) : environ -> mpred :=
  EX m': mst,
    !! (stepf2 (f_flush F) lenfix_list distfix_list m = stepf2 (f_flush F) lenfix_list distfix_list m' /\
        m_mode m' = Y /\ m_leave m' = 0 /\ mwf39 m' /\ hd_ok F m' /\ hdr_tok F m' = hdr_tok F m /\
        i_head (m_s m') = true) &&
    (loop_stateH F m' * (fun _ => hd6 F m')).

(* RTH9HDefs.case_ok9h with mwf39 *)
Definition case_ok9v {Espec: OracleKind} (F: frame) (Y: Z) (i: nat) : Prop :=
  forall m, m_mode m = Y -> m_leave m = 0 -> mwf39 m -> hd_ok F m -> i_head (m_s m) = true ->
    semax Delta_cases5 (loop_stateH F m * (fun _ => hdr_tok F m * hd6 F m))
      (seq_of_labeled_statement (ls_drop i inflate_LS))
      (frame_ret_assert (switch_ret_assert (case_post9 F m)) (fun _ => hdr_tok F m)).

Lemma case_ok9h_of_v {Espec: OracleKind}: forall F Y i, case_ok9v F Y i -> case_ok9h F Y i.
Proof. intros F Y i C m HM HL W. apply C; auto. apply mwf39_iff; exact W. Qed.

(* a header case whose body falls into the header mode Y is proved by the case of Y *)
Lemma case_fallthrough9v {Espec: OracleKind} (F: frame) (m: mst) (Y: Z) (i: nat):
  (i < 32)%nat -> case_ok9v F Y (S i) ->
  semax Delta_cases5 (loop_stateH F m * (fun _ => hdr_tok F m * hd6 F m)) (case_body i)
    (overridePost (fall_post9v F m Y * (fun _ => hdr_tok F m))
       (frame_ret_assert (switch_ret_assert (case_post9 F m)) (fun _ => hdr_tok F m))) ->
  semax Delta_cases5 (loop_stateH F m * (fun _ => hdr_tok F m * hd6 F m))
    (seq_of_labeled_statement (ls_drop i inflate_LS))
    (frame_ret_assert (switch_ret_assert (case_post9 F m)) (fun _ => hdr_tok F m)).
Proof.
  intros Hi HC HB. rewrite seq_split by lia.
  eapply semax_seq; [exact HB | ].
  unfold fall_post9v. rewrite exp_sepcon1. apply extract_exists_pre. intros m'.
  rewrite sepcon_andp_prop'. apply semax_extract_prop. intros (E & HM & HL & W & HD & HT & HH).
  rewrite (case_post9_eq F m m' E). rewrite <- HT.
  eapply semax_pre; [ | apply (HC m'); auto].
  intros rho. simpl. apply andp_left2. cancel.
Qed.

(* the parts *)
Definition rth_head_stmt9v : Prop :=
  forall {Espec: OracleKind} (F: frame), frame_ok5 F -> case_ok9v F IM.HEAD 0.

Definition rth_fto_stmt9v : Prop :=
  forall {Espec: OracleKind} (F: frame), frame_ok5 F ->
    (case_ok9v F IM.TIME 2 -> case_ok9v F IM.FLAGS 1) /\ (case_ok9v F IM.OS 3 -> case_ok9v F IM.TIME 2) /\
    (case_ok9v F IM.EXLEN 4 -> case_ok9v F IM.OS 3).

Definition rth_ex_stmt9v : Prop :=
  forall {Espec: OracleKind} (F: frame), frame_ok5 F ->
    (case_ok9v F IM.EXTRA 5 -> case_ok9v F IM.EXLEN 4) /\ (case_ok9v F IM.NAME 6 -> case_ok9v F IM.EXTRA 5).

Definition rth_nc_stmt9v : Prop :=
  forall {Espec: OracleKind} (F: frame), frame_ok5 F ->
    (case_ok9v F IM.COMMENT 7 -> case_ok9v F IM.NAME 6) /\ (case_ok9v F IM.HCRC 8 -> case_ok9v F IM.COMMENT 7).

Definition rth_hcrc_stmt9v : Prop :=
  forall {Espec: OracleKind} (F: frame), frame_ok5 F -> case_ok9v F IM.HCRC 8.

Lemma cases9h_all_of_parts:
  rth_head_stmt9v -> rth_fto_stmt9v -> rth_ex_stmt9v -> rth_nc_stmt9v -> rth_hcrc_stmt9v -> cases9h_all.
Proof.
  intros HH FT XE NC HC Espec F HF.
  pose proof (HC Espec F HF) as C8.
  destruct (NC Espec F HF) as [N6 N7]. pose proof (N7 C8) as C7. pose proof (N6 C7) as C6.
  destruct (XE Espec F HF) as [E4 E5]. pose proof (E5 C6) as C5. pose proof (E4 C5) as C4.
  destruct (FT Espec F HF) as (F1 & F2 & F3). pose proof (F3 C4) as C3. pose proof (F2 C3) as C2.
  pose proof (F1 C2) as C1. pose proof (HH Espec F HF) as C0.
  intros i Hi. apply case_ok9h_of_v.
  do 9 (destruct i as [|i]; [ eassumption | ]). exfalso; lia.
Qed.
