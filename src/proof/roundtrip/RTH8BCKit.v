(* The interface of inflate()'s body with a partial header (RTH8Paths.hd8pre_b, hd8pre_c).

   The run is split at the end of the header modes.  In the header modes the real machine (its header of any
   buffer sizes, RTH8W.mwf3_8) passes the header with the header cases (RTH8W.cases8w_all).  After the header
   the headless loop and exit run on the machine with the small header RTH8W.mcanon, and the header head_rep8a
   of the real machine sits in the frame; the run is transferred back to the real machine (RTH8W.sim_stmt).

   The statements of the parts, all on the real machine:
   - [nhloop8_stmt]: the main loop from a machine past the header;
   - [hloop8_stmt]: the main loop from a header machine whose call passes the header (hpass8);
   - [exit8_stmt]: the exit inf_leave from a machine past the header.
   A return inside the loop and the exit give the function's return by [ret8] and [exit_ok8], in terms of the
   real machine.  The lemmas below say that the memory of the loop does not depend on the header model beyond
   whether each buffer size is 0 (mcanon keeps it), and that a stream with a header of any sizes is a Spec5
   stream with the small header. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTH8Spec.
Require Export Zlib.proof.roundtrip.RTH8Paths.
Require Import Zlib.proof.inflate_api.Body5Conv.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* the pure invariants of the loop from the first machine m0                                      *)

(* at the loop head (as in RTHBody6H): out_inv, the window flag and facts, the input *)
Definition pinv8 (m0 m: mst) : Prop :=
  out_inv m /\ i_win (m_s m) = i_win (m_s m0) /\ win_inv5 (m_s m) /\ m_inp m = m_inp m0.

(* at a return *)
Definition qinv8 (m0 m: mst) : Prop :=
  i_win (m_s m) = i_win (m_s m0) /\ win_inv5 (m_s m) /\ m_inp m = m_inp m0.

(* ---------------------------------------------------------------------------------------------- *)
(* the statements of the parts                                                                    *)

(* after the loop: the real machine m reached from m0 with leave = 1, past the header *)
Definition loop_exit8 (F: frame) (X: mpred) (m0: mst) : environ -> mpred :=
  EX m: mst,
    !! (loop2 (f_flush F) lenfix_list distfix_list m0 (IBrk m) /\ mwf3_8 m /\ hd_ok F m /\ m_leave m = 1 /\
        hdr_mode (m_mode m) = false /\ i_head (m_s m) = true /\ pinv8 m0 m) &&
    lstateH F (X * hd8a F m) m.

(* a return inside the switch gives the function's return *)
Definition ret8 (F: frame) (X: mpred) (m0: mst) (R: ret_assert) : Prop :=
  forall r m', loop2 (f_flush F) lenfix_list distfix_list m0 (IRet r m') -> mwf3_8 m' -> hd_ok F m' ->
    hdr_mode (m_mode m') = false -> i_head (m_s m') = true -> qinv8 m0 m' ->
    ENTAIL Delta_inflate5_hl,
      PROPx [] (LOCALx (ret_locals F)
        (SEPx [mem_rep_hl F m'; locals_rep F; hdr_tok F m'; mem_mgr (f_gv F); zfuncs (f_gv F); X * hd8a F m']))
      |-- RA_return R (Some (zv r)).

(* the main loop from a machine m past the header, reached from m0 *)
Definition nhloop8_stmt : Prop :=
  forall {Espec: OracleKind} (F: frame) (X: mpred) (m0 m: mst) (R: ret_assert),
  frame_ok5 F -> ret8 F X m0 R ->
  (forall o, loop2 (f_flush F) lenfix_list distfix_list m o -> loop2 (f_flush F) lenfix_list distfix_list m0 o) ->
  mwf3_8 m -> m_leave m = 0 -> hd_ok F m -> hdr_mode (m_mode m) = false -> i_head (m_s m) = true ->
  pinv8 m0 m ->
  semax Delta_inflate5_hl (lstateH F (X * hd8a F m) m) inflate_mainloop (overridePost (loop_exit8 F X m0) R).

(* the main loop from a header machine m reached from m0, whose passes reach the end of the header *)
Definition hloop8_stmt : Prop :=
  forall {Espec: OracleKind} (F: frame) (X: mpred) (m0: mst) (R: ret_assert),
  frame_ok5 F -> ret8 F X m0 R ->
  forall n m, hpass8 (f_flush F) n m -> hdr_mode (m_mode m) = true -> i_head (m_s m) = true ->
    mwf3_8 m -> m_leave m = 0 -> hd_ok F m -> pinv8 m0 m ->
    (forall o, loop2 (f_flush F) lenfix_list distfix_list m o -> loop2 (f_flush F) lenfix_list distfix_list m0 o) ->
    semax Delta_inflate5_hl (lstateH F (X * hd6 F m) m) inflate_mainloop (overridePost (loop_exit8 F X m0) R).

(* what the exit inf_leave from the real machine m past the header gives (Body5Parts.leave_fin5_stmt on the
   machine with the small header): the final machine is a live stream's, with m's header and input, past the
   header *)
Definition leave8 (m: mst) (res: result) : Prop :=
  fin_ok5 (mcanon (r_m res)) /\ (forall d, r_dtype res = Some d -> srange d) /\
  m_h (r_m res) = m_h m /\ i_head (m_s (r_m res)) = i_head (m_s m) /\ m_inp (r_m res) = m_inp m /\
  hdr_mode (m_mode (r_m res)) = false.

(* each outcome res of inf_leave from the real machine m gives the function's return (winp: the window
   pointer after the exit, the old one when the window existed) *)
Definition exit_ok8 (F: frame) (X: mpred) (m: mst) (R: ret_assert) : Prop :=
  forall res winp, inf_leave (f_flush F) m res -> leave8 m res -> (i_win (m_s m) = true -> winp = f_winp F) ->
    ENTAIL Delta_inflate5_hl,
      PROPx [] (LOCALx (ret_locals F)
        (SEPx [mem_rep_hl (set_f_winp_dt F winp (res_dt F res)) (r_m res); locals_rep F; hdr_tok F m;
               mem_mgr (f_gv F); zfuncs (f_gv F); X * hd8a F (r_m res)]))
      |-- RA_return R (Some (zv (r_ret res))).

(* the exit from a machine past the header *)
Definition exit8_stmt : Prop :=
  forall {Espec: OracleKind} (F: frame) (X: mpred) (m: mst) (R: ret_assert),
  frame_ok5 F -> mwf3_8 m -> m_leave m = 1 -> out_inv m -> win_inv5 (m_s m) -> hdr_mode (m_mode m) = false ->
  exit_ok8 F X m R ->
  semax Delta_inflate5_hl (lstateH F (X * hd8a F m) m) inflate_exit R.

(* ---------------------------------------------------------------------------------------------- *)
(* the small header                                                                               *)

Lemma mcanon_s: forall m, m_s (mcanon m) = m_s m.
Proof. reflexivity. Qed.

Lemma mcanon_h: forall m, m_h (mcanon m) = hcanon (m_h m).
Proof. reflexivity. Qed.

Lemma set_m_h_same: forall m, set_m_h m (m_h m) = m.
Proof. intros []; reflexivity. Qed.

Lemma set_m_h_twice: forall m h h', set_m_h (set_m_h m h) h' = set_m_h m h'.
Proof. intros []; reflexivity. Qed.

(* the real machine back from the small one *)
Lemma mcanon_back: forall m, set_m_h (mcanon m) (m_h m) = m.
Proof. intros []; reflexivity. Qed.

Lemma m_init_lcanon: forall z L inp, m_init z (lcanon L) inp = mcanon (m_init z L inp).
Proof. reflexivity. Qed.

Lemma mkF_lcanon: forall gv shs strmp L ib o gsh tsh z vh vl vb flush,
  mkF gv shs strmp (lcanon L) ib o gsh tsh z vh vl vb flush = mkF gv shs strmp L ib o gsh tsh z vh vl vb flush.
Proof. reflexivity. Qed.

Lemma xfr_lcanon: forall L itok otok ib o, xfr (lcanon L) itok otok ib o = xfr L itok otok ib o.
Proof. reflexivity. Qed.

Lemma btok_cz: forall b n, btok b (cz n) = btok b n.
Proof.
  intros b n. unfold btok, cz.
  destruct (eq_dec b nullval); [reflexivity | ].
  destruct (Z.eqb_spec n 0) as [E | E]; [subst n; reflexivity | ].
  destruct (zeq 1 0); [lia | ]. destruct (zeq n 0); [contradiction | reflexivity].
Qed.

(* the tokens of the zero-size buffers do not see the small header *)
Lemma hdr_tok_set_canon: forall F m h, hdr_tok F (set_m_h m (hcanon h)) = hdr_tok F (set_m_h m h).
Proof.
  intros F m h. unfold hdr_tok. destruct m; simpl. rewrite !btok_cz. reflexivity.
Qed.

Lemma hdr_tok_mcanon: forall F m, hdr_tok F (mcanon m) = hdr_tok F m.
Proof.
  intros F m. unfold mcanon. rewrite hdr_tok_set_canon, set_m_h_same. reflexivity.
Qed.

(* the headless memory does not see the header model *)
Lemma mem_repH_set_h: forall F m h, mem_repH F (set_m_h m h) = mem_repH F m.
Proof. intros F [] h. reflexivity. Qed.

Lemma mem_rep_hl_set_h: forall F m h, mem_rep_hl F (set_m_h m h) = mem_rep_hl F m.
Proof. intros F [] h. reflexivity. Qed.

Lemma mem_rep_hl_H: forall F m, mem_rep_hl F m = mem_repH F m.
Proof. reflexivity. Qed.

Lemma lstate_hl_H: forall F X m, lstate_hl F X m = lstateH F X m.
Proof. reflexivity. Qed.

Lemma lstateH_mcanon: forall F X m, lstateH F X (mcanon m) = lstateH F X m.
Proof.
  intros F X m. unfold lstateH. rewrite hdr_tok_mcanon.
  unfold mcanon. rewrite mem_repH_set_h. destruct m; reflexivity.
Qed.

(* hd_ok of the small header: no field marked present *)
Lemma hd_ok_mcanon: forall F m, hd_ok F (mcanon m).
Proof. intros F m _. simpl. split; [ | split]; discriminate. Qed.

Lemma hd_ok_set_h: forall F m m', hd_ok F m -> i_head (m_s m') = i_head (m_s m) -> m_h m' = m_h m -> hd_ok F m'.
Proof. intros F m m' H E1 E2 HI. rewrite E2. apply H. congruence. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* streams with a header of any sizes                                                             *)

Lemma cz_range: forall n, 0 <= cz n <= 1.
Proof. intros n. unfold cz. destruct (n =? 0); lia. Qed.

Lemma bytes_ok_repeat0: forall k, bytes_ok (repeat 0 k).
Proof.
  induction k as [|k IH]; simpl; constructor; [ | exact IH]. rep_lia.
Qed.

Lemma hwf_hcanon: forall h, hwf (hcanon h).
Proof.
  intros h.
  pose proof (cz_range (h_extra_max h)). pose proof (cz_range (h_name_max h)).
  pose proof (cz_range (h_comm_max h)).
  constructor; simpl; try (unfold srange, lrange, urange; rep_lia).
  all: split; [rewrite Zlength_repeat; lia | apply bytes_ok_repeat0].
Qed.

Lemma live_ok8_canon: forall L, live_ok8 L -> live_ok (lcanon L).
Proof.
  intros L (A & B & C & D & E & F & G & H & I).
  unfold live_ok, lcanon, set_l_head; simpl.
  refine (conj A (conj B (conj C (conj (hwf_hcanon _) (conj E (conj F (conj G (conj _ I)))))))).
  intros _. split; [ | split]; discriminate.
Qed.

Lemma live_ok8_of_canon: forall L, live_ok (lcanon L) -> hwf8 (l_h L) ->
  (i_head (l_s L) = true ->
     (h_xp (l_h L) = true -> l_xb L <> nullval) /\ (h_np (l_h L) = true -> l_nb L <> nullval) /\
     (h_cp (l_h L) = true -> l_cb L <> nullval)) ->
  live_ok8 L.
Proof.
  intros L (A & B & C & D & E & F & G & H & I) W P.
  unfold lcanon, set_l_head in *; simpl in *.
  exact (conj A (conj B (conj C (conj W (conj E (conj F (conj G (conj P I)))))))).
Qed.

(* the stream of inflate_spec8 is Spec5's stream with the small header *)
Lemma istream8_canon: forall gv shs strmp z L,
  istream8 gv shs strmp z (Some L) |-- !! live_ok8 L && istream gv shs strmp z (Some (lcanon L)).
Proof.
  intros. unfold istream8, istream. Intros.
  pose proof (live_ok8_canon L H1).
  unfold state_mem, lcanon, set_l_head; simpl. entailer!.
Qed.

Lemma istream_canon_8: forall gv shs strmp z L, live_ok8 L ->
  istream gv shs strmp z (Some (lcanon L)) |-- istream8 gv shs strmp z (Some L).
Proof.
  intros. unfold istream8, istream. Intros.
  unfold state_mem, lcanon, set_l_head; simpl. entailer!.
Qed.

Lemma htok6_lcanon: forall L, i_head (l_s L) = true -> htok6 (Some (lcanon L)) = btoks8 L.
Proof.
  intros L E. unfold htok6, lcanon, set_l_head, hdr_btoks, btoks8; simpl. rewrite E.
  rewrite !btok_cz. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the final machine as inflate_spec8's postcondition                                             *)

Lemma live_of_mcanon: forall F m, live_of F (mcanon m) = lcanon (live_of F m).
Proof. reflexivity. Qed.

Lemma z_of_set_h: forall F m h, z_of F (set_m_h m h) = z_of F m.
Proof. intros F [] h. reflexivity. Qed.

(* Body5Conv.fin_ok5_live with a header of any sizes *)
Lemma fin_ok8_live: forall F m, fin_ok5 (mcanon m) -> hwf8 (m_h m) -> hd_ok F m -> isptr (f_sp F) ->
  writable_share (f_hsh F) -> srange (f_dt F) ->
  live_ok8 (live_of F m) /\ zf_ok (z_of F m).
Proof.
  intros F m FO W D P WH Q.
  destruct (fin_ok5_live F (mcanon m) FO (hd_ok_mcanon F m) P WH Q) as [L1 Z1].
  split.
  - apply live_ok8_of_canon; [exact L1 | exact W | exact D].
  - exact Z1.
Qed.

(* Body5Conv.mem_rep_istream5 for the headless memory with the header head_rep8a past the header modes *)
Lemma mem_rep_istream8: forall F m,
  live_ok8 (live_of F m) -> zf_ok (z_of F m) -> writable_share (f_shs F) -> f_strmp F <> nullval ->
  i_head (m_s m) = true -> hdr_mode (m_mode m) = false ->
  mem_rep_hl F m * hdr_tok F m * malloc_token Ews t_state (f_sp F) * state_pad (f_sp F) * hd8a F m |--
  istream8_opt (f_gv F) (f_shs F) (f_strmp F) (z_of F m) (Some (live_of F m)) *
  head_opt8 (is_live (f_strmp F) (Some (live_of F m))) * in_rep (f_ib F) *
  out_opt (Some (f_ob F)) (m_ow m) * tables_rep (f_gsh F) (f_gv F) * crc_table_at (f_tsh F) (f_gv F).
Proof.
  intros F m HL HZ HW HN HI HM.
  unfold istream8_opt, is_live. destruct (eq_dec (f_strmp F) nullval) as [E | _]; [contradiction | ].
  unfold istream8, zstrm_at, state_mem, head_opt8, head_mem8, mem_rep_hl, head_part_hl, hdr_tok, out_opt, hd8a.
  unfold z_of, live_of; simpl. unfold m_mode in HM. rewrite HI, HM.
  entailer!.
  apply orp_right2. apply andp_right; [apply prop_right; reflexivity | apply derives_refl].
Qed.
