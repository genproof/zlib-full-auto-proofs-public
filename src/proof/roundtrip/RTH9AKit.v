(* The interface of inflate()'s body against RTH9Spec.inflate_spec9 assembled from its parts (RTH9Asm.body9_of).

   A call may start, stay and return in the header modes, so the body has ONE main loop over the machines of the
   call, each with its header RTH9HDefs.hd9 next to the headless loop state (lstateH F (X * hd9 F m) m):
   - from a header mode a pass is a header case (RTH9HDefs.cases9h_all) on the real machine (its header of any
     buffer sizes, RTH9HDefs.mwf3_9); the pure invariants of the pass are [hdr9_inv_stmt];
   - past the header modes a pass is a headless case (RTH9Defs.cases_nh9) on the machine with the small header
     RTH8W.mcanon, the header hd9a of the real machine in the frame, the run transferred back by RTH8W.sim_stmt.
   The exit (RTH9Parts.exit_part9_stmt) runs on the machine with the small header, the header in the frame.

   The statements of the parts, all on the real machine:
   - [loop9_for fast]: the main loop from the first machine of a call ([loop9_stmt]: from the switch cases);
   - [exit9_for]: the exit inf_leave from the machine after the loop ([exit9_stmt]: from exit_part9_stmt);
   - [hdr9_inv_stmt]: one pass from a header mode keeps mwf3_9 and the loop's pure invariants (round 1's RTH8W2.hdr8_inv2_stmt
     for wide machines).
   The contexts: Delta_inflate5_hl, Delta_inflate5, Delta_cases5 and Delta_cases9 fast are sub-contexts of
   Delta_inflate9 fast when fast is stronger than the headless inflate_fast specification ([rth9_sub_hl] ...).
   The wide machine facts of the port src/proof/za (stepf_inv5_za, stepf2_hdr_za, leave_fin5_za, ...) do not
   depend on the allocator: they are restated here for InvW.mwf3W ([stepf_inv9], [stepf2_hdr9], [leave_fin9]). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTH8Spec.
Require Export Zlib.proof.roundtrip.RTH9HDefs.
Require Export Zlib.proof.roundtrip.RTH8BCKit.
Require Import Zlib.proof.roundtrip.RTH8Fast.
Require Import Zlib.proof.inflate.StepW.
Require Import Zlib.proof.inflate_api.Body5Conv.
Require Zlib.proof.za.inflate_api.Body5StepInv.
Require Zlib.proof.za.inflate_api.Body5StepHdr.
Require Zlib.proof.za.inflate_api.Body5Fin.
Require Zlib.proof.za.inflate_api.Body5Conv.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* the contexts                                                                                   *)

Lemma rth9_fast3 (fast: funspec) :
  funspec_sub fast (snd inflate_fast_spec3_hl) -> funspec_sub fast (snd inflate_fast_spec3).
Proof. intros H. exact (funspec_sub_trans _ _ _ H rth8_fast_sub). Qed.

Lemma rth9_map_fst (fast: funspec) (l: funspecs) :
  map fst (map (fun f : ident * funspec => if ident_eq (fst f) _inflate_fast then (_inflate_fast, fast) else f) l)
  = map fst l.
Proof.
  induction l as [ | [i f] l IH]; [reflexivity | ]. simpl. rewrite IH.
  destruct (ident_eq i _inflate_fast) as [E | E]; simpl; [rewrite E | ]; reflexivity.
Qed.

Lemma rth9_sub_hl (fast: funspec) :
  funspec_sub fast (snd inflate_fast_spec3_hl) -> tycontext_sub Delta_inflate5_hl (Delta_inflate9 fast).
Proof.
  intros FS. unfold Delta_inflate5_hl, Delta_inflate9. apply rth8_tsub.
  unfold Gprog_inflate8, Gprog_inflate3, Gprog_inflate3_hl, Gprog_cases3, Gprog_cases3_hl.
  cbn [map app].
  do 2 (apply Forall2_cons; [split; [reflexivity | apply funspec_sub_refl] | ]).
  apply Forall2_cons.
  { destruct (ident_eq (fst inflate_fast_spec3) _inflate_fast) as [E | E];
      [ | exfalso; apply E; reflexivity].
    split; [change (_inflate_fast = _inflate_fast); reflexivity | exact FS]. }
  repeat (apply Forall2_cons;
    [match goal with |- context [ident_eq ?a ?b] =>
       destruct (ident_eq a b) as [E | E]; [exfalso; lazy in E; discriminate | ] end;
     split; [reflexivity | apply funspec_sub_refl] | ]).
  apply Forall2_nil.
Qed.

Lemma rth9_sub_5 (fast: funspec) :
  funspec_sub fast (snd inflate_fast_spec3_hl) -> tycontext_sub Delta_inflate5 (Delta_inflate9 fast).
Proof.
  intros FS. eapply tycontext_sub_trans; [apply rth8_sub_inflate5 | apply rth9_sub_hl; exact FS].
Qed.

Lemma rth9_sub_cases5 (fast: funspec) :
  funspec_sub fast (snd inflate_fast_spec3_hl) -> tycontext_sub Delta_cases5 (Delta_inflate9 fast).
Proof.
  intros FS. eapply tycontext_sub_trans; [apply sub_cases_inflate5 | apply rth9_sub_5; exact FS].
Qed.

Lemma rth9_sub_cases9 (fast: funspec) : tycontext_sub (Delta_cases9 fast) (Delta_inflate9 fast).
Proof.
  unfold Delta_cases9, Delta_inflate9, Gprog_cases9, Gprog_inflate8, Gprog_inflate3.
  apply VST.veric.semax_prog.func_tycontext_sub.
  - apply incl_refl.
  - rewrite map_app. apply incl_appl. apply incl_refl.
  - rewrite rth9_map_fst. apply list_norepet_NoDup. apply compute_list_norepet_e. vm_compute. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the wide machine facts of the port src/proof/za, for InvW.mwf3W                                *)

Lemma mwf3W_za: forall m, mwf3W m -> Zlib.proof.za.inflate.Inv3.mwf3_za m.
Proof.
  intros m [W [S H]]. split; [ | split; [exact S | exact H]].
  destruct W; constructor; assumption.
Qed.

Lemma za_mwf3W: forall m, Zlib.proof.za.inflate.Inv3.mwf3_za m -> mwf3W m.
Proof.
  intros m [W [S H]]. split; [ | split; [exact S | exact H]].
  destruct W; constructor; assumption.
Qed.

(* Body5Parts.fin_ok5 with avail_in, avail_out any uInt (the port's fin_ok5_za) *)
Definition fin_ok9 (m: mst) : Prop :=
  swf (m_s m) /\ modewf (m_s m) /\ hwf (m_h m) /\ swf3 (m_s m) /\ win_inv5 (m_s m) /\
  0 <= m_snx m <= Zlength (m_inp m) /\ Zlength (m_inp m) <= Int.max_unsigned /\
  0 <= m_sow m <= m_aout m /\ m_aout m <= Int.max_unsigned /\
  lrange (m_tin m) /\ lrange (m_tout m) /\ lrange (m_adler m).

(* one pass keeps out_inv, the window flag and win_inv5 (Body5Parts.stepf_inv5_stmt) *)
Lemma stepf_inv9: forall flush m, mwf3W m -> m_leave m = 0 -> out_inv m -> win_inv5 (m_s m) ->
  match stepf2 flush lenfix_list distfix_list m with
  | IBrk m' => out_inv m' /\ i_win (m_s m') = i_win (m_s m) /\ win_inv5 (m_s m')
  | IRet _ m' => i_win (m_s m') = i_win (m_s m) /\ win_inv5 (m_s m')
  end.
Proof.
  intros flush m W L O V.
  exact (Zlib.proof.za.inflate_api.Body5StepInv.stepf_inv5_za flush m (mwf3W_za m W) L O V).
Qed.

(* one pass keeps the header's presence and its buffers' sizes, and the input (Body5Parts.stepf2_hdr_stmt) *)
Lemma stepf2_hdr9: forall flush m, mwf3W m -> m_leave m = 0 ->
  match stepf2 flush lenfix_list distfix_list m with
  | IBrk m' => hdr_same m m' /\ m_inp m' = m_inp m
  | IRet _ m' => hdr_same m m' /\ m_inp m' = m_inp m
  end.
Proof.
  intros flush m W L.
  exact (Zlib.proof.za.inflate_api.Body5StepHdr.stepf2_hdr_za flush m (mwf3W_za m W) L).
Qed.

(* the machine after inf_leave is a live stream's, with InvW.swfW (Body5Parts.leave_fin5_stmt) *)
Lemma leave_fin9: forall flush m res, mwf3W m -> out_inv m -> win_inv5 (m_s m) -> inf_leave flush m res ->
  swfW (m_s (r_m res)) /\ fin_ok9 (r_m res) /\ (forall d, r_dtype res = Some d -> srange d) /\
  m_h (r_m res) = m_h m /\ i_head (m_s (r_m res)) = i_head (m_s m) /\ m_inp (r_m res) = m_inp m.
Proof.
  intros flush m res W O V L.
  exact (Zlib.proof.za.inflate_api.Body5Fin.leave_fin5_za flush m res (mwf3W_za m W) O V L).
Qed.

Lemma mwf3W_fin_ok9: forall m, mwf3W m -> win_inv5 (m_s m) -> fin_ok9 m.
Proof.
  intros m W V.
  exact (Zlib.proof.za.inflate_api.Body5Conv.mwf3_fin_ok5_za m (mwf3W_za m W) V).
Qed.

Lemma m_init_mwf3W: forall z L inp,
  live_ok L -> zf_ok z -> swfW (l_s L) -> Zlength inp <= Int.max_unsigned -> bytes_ok inp ->
  mwf3W (m_init z L inp).
Proof.
  intros z L inp A B C D E.
  exact (za_mwf3W _ (Zlib.proof.za.inflate_api.Body5Conv.m_init_mwf3_za z L inp A B C D E)).
Qed.

(* Body5Conv.fin_ok5_live for fin_ok9 *)
Lemma fin_ok9_live: forall F m, fin_ok9 m -> hd_ok F m -> isptr (f_sp F) -> writable_share (f_hsh F) ->
  srange (f_dt F) -> live_ok (live_of F m) /\ zf_ok (z_of F m).
Proof.
  intros F m FO.
  exact (Zlib.proof.za.inflate_api.Body5Conv.fin_ok5_live_za F m FO).
Qed.

(* RTH8BCKit.fin_ok8_live for fin_ok9: a final machine with a header of any sizes is a live stream's *)
Lemma fin_ok9_live8: forall F m, fin_ok9 (mcanon m) -> hwf8 (m_h m) -> hd_ok F m -> isptr (f_sp F) ->
  writable_share (f_hsh F) -> srange (f_dt F) ->
  live_ok8 (live_of F m) /\ zf_ok (z_of F m).
Proof.
  intros F m FO W D P WH Q.
  destruct (fin_ok9_live F (mcanon m) FO (hd_ok_mcanon F m) P WH Q) as [L1 Z1].
  split.
  - apply live_ok8_of_canon; [exact L1 | exact W | exact D].
  - exact Z1.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the header modes with a wide machine and a header of any sizes                                 *)

(* one pass from a header mode keeps mwf3_9, the header's presence and sizes, the input and the loop's pure
   invariants (round 1's RTH8W2.hdr8_inv2_stmt with mwf3_9; RTHSpec.hinv6 holds in the partial header) *)
Definition hdr9_inv_stmt : Prop :=
  forall flush m, mwf3_9 m -> m_leave m = 0 -> hdr_mode (m_mode m) = true -> out_inv m -> win_inv5 (m_s m) ->
  (i_head (m_s m) = true -> hinv6 (m_s m) (m_h m)) ->
  match stepf2 flush lenfix_list distfix_list m with
  | IBrk m' => mwf3_9 m' /\ hdr_same m m' /\ m_inp m' = m_inp m /\
               out_inv m' /\ i_win (m_s m') = i_win (m_s m) /\ win_inv5 (m_s m')
  | IRet _ m' => mwf3_9 m' /\ hdr_same m m' /\ m_inp m' = m_inp m /\
                 i_win (m_s m') = i_win (m_s m) /\ win_inv5 (m_s m')
  end.

(* ---------------------------------------------------------------------------------------------- *)
(* the main loop                                                                                  *)

(* after the loop: the real machine m reached from m0 with leave = 1, in any mode *)
Definition loop_exit9 (F: frame) (X: mpred) (m0: mst) : environ -> mpred :=
  EX m: mst,
    !! (loop2 (f_flush F) lenfix_list distfix_list m0 (IBrk m) /\ mwf3_9 m /\ hd_ok F m /\ m_leave m = 1 /\
        i_head (m_s m) = true /\ pinv8 m0 m) &&
    lstateH F (X * hd9 F m) m.

(* a return inside the switch (only past the header modes) gives the function's return *)
Definition ret9 (fast: funspec) (F: frame) (X: mpred) (m0: mst) (R: ret_assert) : Prop :=
  forall r m', loop2 (f_flush F) lenfix_list distfix_list m0 (IRet r m') -> mwf3_9 m' -> hd_ok F m' ->
    hdr_mode (m_mode m') = false -> i_head (m_s m') = true -> qinv8 m0 m' -> swfW (m_s m') ->
    ENTAIL Delta_inflate9 fast,
      PROPx [] (LOCALx (ret_locals F)
        (SEPx [mem_rep_hl F m'; locals_rep F; hdr_tok F m'; mem_mgr (f_gv F); zfuncs (f_gv F); X * hd9a F m']))
      |-- RA_return R (Some (zv r)).

(* the main loop from the first machine m0 of a call *)
Definition loop9_for (fast: funspec) : Prop :=
  forall {Espec: OracleKind} (F: frame) (X: mpred) (m0: mst) (R: ret_assert),
  frame_ok5 F -> ret9 fast F X m0 R ->
  mwf3_9 m0 -> m_leave m0 = 0 -> hd_ok F m0 -> i_head (m_s m0) = true -> pinv8 m0 m0 ->
  semax (Delta_inflate9 fast) (lstateH F (X * hd9 F m0) m0) inflate_mainloop
    (overridePost (loop_exit9 F X m0) R).

Definition loop9_stmt : Prop :=
  forall fast : funspec,
    funspec_sub fast (snd inflate_fast_spec3_hl) -> cases_nh9 fast -> cases9h_all -> hdr9_inv_stmt ->
    loop9_for fast.

(* ---------------------------------------------------------------------------------------------- *)
(* the exit                                                                                       *)

(* what the exit inf_leave from the real machine m gives: the final machine is a live stream's (fin_ok9 on the
   small header, InvW.swfW), with m's header model, header presence and input *)
Definition leave9 (m: mst) (res: result) : Prop :=
  fin_ok9 (mcanon (r_m res)) /\ swfW (m_s (r_m res)) /\ (forall d, r_dtype res = Some d -> srange d) /\
  m_h (r_m res) = m_h m /\ i_head (m_s (r_m res)) = i_head (m_s m) /\ m_inp (r_m res) = m_inp m.

(* each outcome res of inf_leave from the real machine m gives the function's return, with the header hd9 of
   the final machine (winp: the window pointer after the exit, the old one when the window existed) *)
Definition exit_ok9 (F: frame) (X: mpred) (m: mst) (R: ret_assert) : Prop :=
  forall res winp, inf_leave (f_flush F) m res -> leave9 m res -> (i_win (m_s m) = true -> winp = f_winp F) ->
    ENTAIL Delta_inflate5_hl,
      PROPx [] (LOCALx (ret_locals F)
        (SEPx [mem_rep_hl (set_f_winp_dt F winp (res_dt F res)) (r_m res); locals_rep F; hdr_tok F m;
               mem_mgr (f_gv F); zfuncs (f_gv F); X * hd9 F (r_m res)]))
      |-- RA_return R (Some (zv (r_ret res))).

(* the exit from the machine after the loop, in any mode *)
Definition exit9_for : Prop :=
  forall {Espec: OracleKind} (F: frame) (X: mpred) (m: mst) (R: ret_assert),
  frame_ok5 F -> mwf3_9 m -> m_leave m = 1 -> out_inv m -> win_inv5 (m_s m) -> i_head (m_s m) = true ->
  exit_ok9 F X m R ->
  semax Delta_inflate5_hl (lstateH F (X * hd9 F m) m) inflate_exit R.

Definition exit9_stmt : Prop := exit_part9_stmt -> exit9_for.
