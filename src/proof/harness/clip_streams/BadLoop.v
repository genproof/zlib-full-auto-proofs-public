(* Law rj_bad_checksum: the calls of inflate() on the changed input, pass by pass (BadKit.v's phases).

   - inf_leave on another input of the same length, and on the raw view (BadKit.bview): RESTORE, the window,
     the counters, the check value, data_type and the return code read the input only through its length
     and the bytes consumed; the raw view differs in the check value (not folded: wrap 0) and in the counts
     of input bytes (the shift);
   - the header loop: the zlib machine is the machine of the decode theory on the true stream with src's bytes
     in place of O's (BadHdr.bad_pass_hdr), up to TYPE;
   - the block loop: the raw view of the zlib machine is the raw stream's machine (BadView.bad_view_step and
     the decode theory on BadKit.rawctx), up to a CHECK head (BadKit.chead) or the end of the call. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Zlib.proof.uncompr.URunFrame.
Require Import Zlib.proof.harness.clip_streams.BadKit.
Require Import Zlib.proof.harness.clip_streams.BadRaw Zlib.proof.harness.clip_streams.BadHdr
  Zlib.proof.harness.clip_streams.BadView Zlib.proof.harness.clip_streams.BadModes.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The state of the raw view                                                                      *)

Definition vst (hh bb w c t f: Z) (s: istate) : istate :=
  set_i_flags (set_i_total (set_i_check (set_i_wrap (set_i_bits (set_i_hold s hh) bb) w) c) t) f.

Lemma bview_s d x hh bb w c t f m : m_s (bview d x hh bb w c t f m) = vst hh bb w c t f (m_s m).
Proof. reflexivity. Qed.

Section Vst.
Variables (hh bb w c t f: Z).
Lemma vst_wsize s : i_wsize (vst hh bb w c t f s) = i_wsize s. Proof. reflexivity. Qed.
Lemma vst_wbits s : i_wbits (vst hh bb w c t f s) = i_wbits s. Proof. reflexivity. Qed.
Lemma vst_wnext s : i_wnext (vst hh bb w c t f s) = i_wnext s. Proof. reflexivity. Qed.
Lemma vst_whave s : i_whave (vst hh bb w c t f s) = i_whave s. Proof. reflexivity. Qed.
Lemma vst_wdata s : i_wdata (vst hh bb w c t f s) = i_wdata s. Proof. reflexivity. Qed.
Lemma vst_set_wsize s v : set_i_wsize (vst hh bb w c t f s) v = vst hh bb w c t f (set_i_wsize s v).
Proof. reflexivity. Qed.
Lemma vst_set_wnext s v : set_i_wnext (vst hh bb w c t f s) v = vst hh bb w c t f (set_i_wnext s v).
Proof. reflexivity. Qed.
Lemma vst_set_whave s v : set_i_whave (vst hh bb w c t f s) v = vst hh bb w c t f (set_i_whave s v).
Proof. reflexivity. Qed.
Lemma vst_set_wdata s v : set_i_wdata (vst hh bb w c t f s) v = vst hh bb w c t f (set_i_wdata s v).
Proof. reflexivity. Qed.
Lemma vst_set_win s v : set_i_win (vst hh bb w c t f s) v = vst hh bb w c t f (set_i_win s v).
Proof. reflexivity. Qed.

Lemma bad_uw_vst s data :
  updatewindow (vst hh bb w c t f s) data = vst hh bb w c t f (updatewindow s data).
Proof.
  unfold updatewindow. cbv zeta. rewrite vst_wsize.
  destruct (i_wsize s =? 0);
  repeat rewrite ?vst_set_wsize, ?vst_set_wnext, ?vst_set_whave, ?vst_set_wdata, ?vst_wsize, ?vst_wbits,
    ?vst_wnext, ?vst_whave, ?vst_wdata;
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
  repeat rewrite ?vst_set_wsize, ?vst_set_wnext, ?vst_set_whave, ?vst_set_wdata; reflexivity.
Qed.
End Vst.

(* ---------------------------------------------------------------------------------------------- *)
(* inf_leave on the raw view                                                                      *)

Lemma bad_leave_ok_view flush d x hh bb w c t f m :
  leave_ok flush (bview d x hh bb w c t f m) = leave_ok flush m.
Proof. reflexivity. Qed.

(* inf_leave's two halves: RESTORE and the window; the counters, the check value, data_type and the code *)
Definition lwin (flush: Z) (m: mst) : mst :=
  let upd := leave_ok flush m in
  let m := restore m in
  if upd then
    let copy := u32 (m_out m - m_left m) in
    upd_s m (fun s => set_i_win (updatewindow s (sublist (Zlength (m_ow m) - copy) (Zlength (m_ow m)) (m_ow m))) true)
  else m.

Definition lpost (flush: Z) (m: mst) : result :=
  let inn := u32 (m_in m - m_have m) in
  let out := u32 (m_out m - m_left m) in
  let m := set_m_tout (set_m_tin m (u64 (m_tin m + inn))) (u64 (m_tout m + out)) in
  let m := upd_s m (fun s => set_i_total s (u64 (i_total s + out))) in
  let m := if negb (Z.land (i_wrap (m_s m)) 4 =? 0) && negb (out =? 0) then
             let c := update_check (i_flags (m_s m)) (i_check (m_s m))
                        (sublist (Zlength (m_ow m) - out) (Zlength (m_ow m)) (m_ow m)) in
             set_m_adler (upd_s m (fun s => set_i_check s c)) c
           else m in
  let s := m_s m in
  let dt := m_bits m + (if i_last s =? 0 then 0 else 64) + (if i_mode s =? Zlib.proof.inflate.Model.TYPE then 128 else 0)
            + (if (i_mode s =? LEN_) || (i_mode s =? COPY_) then 256 else 0) in
  let r := if (((inn =? 0) && (out =? 0)) || (flush =? Z_FINISH)) && (m_ret m =? Z_OK)
           then Z_BUF_ERROR else m_ret m in
  Res r m (Some dt).

Lemma bad_leave_fin_eq flush m : leave_fin flush m = lpost flush (lwin flush m).
Proof. reflexivity. Qed.

Lemma bad_restore_view d x hh bb w c t f m :
  restore (bview d x hh bb w c t f m) = bview d (m_nx m - d) (m_hold m) (m_bits m) w c t f (restore m).
Proof. destruct m; reflexivity. Qed.

Lemma bad_updw_view d x hh bb w c t f m data :
  upd_s (bview d x hh bb w c t f m) (fun s => set_i_win (updatewindow s data) true) =
  bview d x hh bb w c t f (upd_s m (fun s => set_i_win (updatewindow s data) true)).
Proof.
  unfold upd_s. rewrite bview_s, bad_uw_vst, vst_set_win.
  set (U := set_i_win _ true). clearbody U. destruct m; reflexivity.
Qed.

Lemma bad_lwin_view flush d x hh bb w c t f m :
  lwin flush (bview d x hh bb w c t f m) = bview d (m_nx m - d) (m_hold m) (m_bits m) w c t f (lwin flush m).
Proof.
  unfold lwin. rewrite bad_leave_ok_view, bad_restore_view. destruct (leave_ok flush m); [|reflexivity].
  cbv zeta. apply bad_updw_view.
Qed.

Lemma bad_lpost_view flush d x c M :
  0 <= d <= m_nx M -> m_nx M <= Zlength (m_inp M) -> x = m_snx M - d ->
  let R := lpost flush M in
  let R2 := lpost flush (bview d x (i_hold (m_s M)) (i_bits (m_s M)) 0 c (i_total (m_s M)) (i_flags (m_s M)) M) in
  let out := u32 (m_out M - m_left M) in
  m_s (r_m R2) = set_i_check (set_i_wrap (m_s (r_m R)) 0) c /\
  m_snx (r_m R) = m_snx (r_m R2) + d /\ m_sow (r_m R2) = m_sow (r_m R) /\
  m_aout (r_m R2) = m_aout (r_m R) /\ m_ow (r_m R2) = m_ow (r_m R) /\ m_ow (r_m R) = m_ow M /\
  m_tout (r_m R2) = m_tout (r_m R) /\ m_inp (r_m R) = m_inp M /\ m_aout (r_m R) = m_aout M /\
  m_snx (r_m R) = m_snx M /\ m_sow (r_m R) = m_sow M /\
  i_wrap (m_s (r_m R)) = i_wrap (m_s M) /\ i_flags (m_s (r_m R)) = i_flags (m_s M) /\
  i_mode (m_s (r_m R)) = i_mode (m_s M) /\ i_head (m_s (r_m R)) = i_head (m_s M) /\
  i_total (m_s (r_m R)) = u64 (i_total (m_s M) + out) /\
  i_check (m_s (r_m R)) =
    (if negb (Z.land (i_wrap (m_s M)) 4 =? 0) && negb (out =? 0)
     then update_check (i_flags (m_s M)) (i_check (m_s M))
            (sublist (Zlength (m_ow M) - out) (Zlength (m_ow M)) (m_ow M))
     else i_check (m_s M)) /\
  (m_ret M <> Z_OK -> r_ret R = m_ret M /\ r_ret R2 = m_ret M) /\
  (m_ret M = Z_OK -> (r_ret R = Z_OK \/ r_ret R = Z_BUF_ERROR) /\ (r_ret R2 = Z_OK \/ r_ret R2 = Z_BUF_ERROR)).
Proof.
  intros D1 D2 X. cbv zeta. unfold lpost. cbv zeta.
  destruct M as [s h inp aout nx ow hold bits in_ out ret leave adler msg tin tout snx sow]. cbn in D1, D2 |- *.
  set (o := u32 (out - (aout - Zlength ow))).
  assert (Ew : (Z.land 0 4 =? 0) = true) by reflexivity.
  destruct (negb (Z.land (i_wrap s) 4 =? 0) && negb (o =? 0)) eqn:C.
  all: destruct s; cbn in *; repeat split; try reflexivity; try lia.
  all: match goal with
       | H: ?r <> Z_OK |- _ => rewrite (proj2 (Z.eqb_neq _ _) H), andb_false_r; reflexivity
       | H: ?r = Z_OK |- _ =>
           rewrite H; match goal with |- context [if ?b then _ else _] => destruct b end; auto
       end.
Qed.

(* updatewindow changes only the window *)
Lemma bad_uw_keep s data :
  i_hold (updatewindow s data) = i_hold s /\ i_bits (updatewindow s data) = i_bits s /\
  i_total (updatewindow s data) = i_total s /\ i_flags (updatewindow s data) = i_flags s /\
  i_wrap (updatewindow s data) = i_wrap s /\ i_check (updatewindow s data) = i_check s /\
  i_mode (updatewindow s data) = i_mode s /\ i_head (updatewindow s data) = i_head s.
Proof.
  unfold updatewindow. cbv zeta.
  destruct (i_wsize s =? 0); repeat match goal with |- context [if ?b then _ else _] => destruct b end;
  repeat split.
Qed.

Lemma bad_lwin_keep flush m :
  let M := lwin flush m in
  i_hold (m_s M) = m_hold m /\ i_bits (m_s M) = m_bits m /\ i_total (m_s M) = i_total (m_s m) /\
  i_flags (m_s M) = i_flags (m_s m) /\ i_wrap (m_s M) = i_wrap (m_s m) /\ i_check (m_s M) = i_check (m_s m) /\
  i_mode (m_s M) = i_mode (m_s m) /\ i_head (m_s M) = i_head (m_s m) /\
  m_snx M = m_nx m /\ m_sow M = Zlength (m_ow m) /\ m_nx M = m_nx m /\ m_inp M = m_inp m /\
  m_ow M = m_ow m /\ m_out M = m_out m /\ m_aout M = m_aout m /\ m_ret M = m_ret m.
Proof.
  unfold lwin. destruct (leave_ok flush m); cbv zeta; [|repeat split].
  unfold upd_s. cbn -[updatewindow].
  match goal with |- context [updatewindow ?s ?d] => destruct (bad_uw_keep s d) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8) end.
  cbn in *. repeat split; assumption.
Qed.

(* the raw view after inf_leave: the state with wrap 0 and the check value not folded, the input positions
   shifted; the return code Z_OK / Z_BUF_ERROR (they may differ: the raw call consumed d bytes fewer) *)
Lemma bad_leave_view flush d x hh bb c m :
  0 <= d <= m_nx m -> m_nx m <= Zlength (m_inp m) ->
  let R := leave_fin flush m in
  let R2 := leave_fin flush (bview d x hh bb 0 c (i_total (m_s m)) (i_flags (m_s m)) m) in
  let out := u32 (m_out m - m_left m) in
  m_s (r_m R2) = set_i_check (set_i_wrap (m_s (r_m R)) 0) c /\
  m_snx (r_m R) = m_snx (r_m R2) + d /\ m_sow (r_m R2) = m_sow (r_m R) /\
  m_aout (r_m R2) = m_aout (r_m R) /\ m_ow (r_m R2) = m_ow (r_m R) /\ m_ow (r_m R) = m_ow m /\
  m_tout (r_m R2) = m_tout (r_m R) /\ m_inp (r_m R) = m_inp m /\ m_aout (r_m R) = m_aout m /\
  m_snx (r_m R) = m_nx m /\ m_sow (r_m R) = Zlength (m_ow m) /\
  i_wrap (m_s (r_m R)) = i_wrap (m_s m) /\ i_flags (m_s (r_m R)) = i_flags (m_s m) /\
  i_mode (m_s (r_m R)) = i_mode (m_s m) /\ i_head (m_s (r_m R)) = i_head (m_s m) /\
  i_total (m_s (r_m R)) = u64 (i_total (m_s m) + out) /\
  i_check (m_s (r_m R)) =
    (if negb (Z.land (i_wrap (m_s m)) 4 =? 0) && negb (out =? 0)
     then update_check (i_flags (m_s m)) (i_check (m_s m))
            (sublist (Zlength (m_ow m) - out) (Zlength (m_ow m)) (m_ow m))
     else i_check (m_s m)) /\
  (m_ret m <> Z_OK -> r_ret R = m_ret m /\ r_ret R2 = m_ret m) /\
  (m_ret m = Z_OK -> (r_ret R = Z_OK \/ r_ret R = Z_BUF_ERROR) /\ (r_ret R2 = Z_OK \/ r_ret R2 = Z_BUF_ERROR)).
Proof.
  intros D1 D2. cbv zeta. rewrite !bad_leave_fin_eq, bad_lwin_view.
  destruct (bad_lwin_keep flush m) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16).
  set (M := lwin flush m) in *.
  rewrite <- K1, <- K2, <- K3, <- K4.
  assert (L : m_left M = m_left m) by (unfold m_left; rewrite K13, K15; reflexivity).
  destruct (bad_lpost_view flush d (m_nx m - d) c M ltac:(lia) ltac:(rewrite K11, K12; lia) ltac:(lia))
    as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19).
  cbv zeta in *. rewrite L, K14, K13, K3, K4, K5, K6, K16 in *.
  repeat split; try assumption; try congruence;
  try (match goal with H: m_ret m <> Z_OK |- _ => apply P18 in H; tauto end);
  try (match goal with H: m_ret m = Z_OK |- _ => apply P19 in H; tauto end).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The modes a header pass ends in                                                                *)

(* HEAD .. TYPEDO, or BAD *)
Definition early (md: Z) : Prop := (HEAD <= md <= TYPEDO) \/ md = BAD.
Definition early_out (o: iout) : Prop :=
  match o with IBrk m => early (m_mode m) | IRet _ _ => True end.

Lemma bad_md_needbits_f k n m : m_mode (needbits_f k n m) = m_mode m.
Proof.
  revert m; induction k as [|k IH]; intros m; [reflexivity|]. cbn [needbits_f].
  destruct (m_bits m <? n); [|reflexivity]. destruct (m_have m =? 0); [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma bad_md_needbits n m : m_mode (needbits n m) = m_mode m.
Proof. apply bad_md_needbits_f. Qed.

Lemma bad_md_crc_if m d : m_mode (crc_if m d) = m_mode m.
Proof. unfold crc_if. destruct (_ && _); reflexivity. Qed.

Lemma bad_imd_needbits n m : i_mode (m_s (needbits n m)) = i_mode (m_s m).
Proof. apply bad_md_needbits_f. Qed.
Lemma bad_imd_crc_if m d : i_mode (m_s (crc_if m d)) = i_mode (m_s m).
Proof. apply bad_md_crc_if. Qed.

Ltac early_leaf :=
  do 3 (cbn -[needbits crc_if] in *;
        rewrite ?bad_md_needbits, ?bad_md_crc_if, ?bad_imd_needbits, ?bad_imd_crc_if;
        unfold m_mode in *);
  unfold early, HEAD, TYPEDO, BAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID,
    Zlib.proof.inflate.Model.TYPE in *; lia.

Ltac early_split := repeat match goal with
  | |- context [if ?b then _ else _] => destruct b
  | |- context [match ?e with (_, _) => _ end] => destruct e
  end.

Lemma bad_early_hcrc m : early (m_mode m) -> early_out (c_HCRC m).
Proof. intros E. unfold c_HCRC. early_split; early_leaf. Qed.

Lemma bad_early_comment m : early (m_mode m) -> early_out (c_COMMENT2 m).
Proof.
  intros E. unfold c_COMMENT2. cbv zeta. early_split;
  try (apply bad_early_hcrc; early_leaf); early_leaf.
Qed.

Lemma bad_early_name m : early (m_mode m) -> early_out (c_NAME2 m).
Proof.
  intros E. unfold c_NAME2. cbv zeta. early_split;
  try (apply bad_early_comment; early_leaf); early_leaf.
Qed.

Lemma bad_early_extra m : early (m_mode m) -> early_out (c_EXTRA2 m).
Proof.
  intros E. unfold c_EXTRA2. cbv zeta. early_split;
  try (apply bad_early_name; early_leaf); early_leaf.
Qed.

Lemma bad_early_exlen m : early (m_mode m) -> early_out (c_EXLEN2 m).
Proof.
  intros E. unfold c_EXLEN2. cbv zeta. early_split;
  try (apply bad_early_extra; early_leaf); early_leaf.
Qed.

Lemma bad_early_os m : early (m_mode m) -> early_out (c_OS2 m).
Proof.
  intros E. unfold c_OS2. cbv zeta. early_split;
  try (apply bad_early_exlen; early_leaf); early_leaf.
Qed.

Lemma bad_early_time m : early (m_mode m) -> early_out (c_TIME2 m).
Proof.
  intros E. unfold c_TIME2. cbv zeta. early_split;
  try (apply bad_early_os; early_leaf); early_leaf.
Qed.

Lemma bad_early_flags m : early (m_mode m) -> early_out (c_FLAGS2 m).
Proof.
  intros E. unfold c_FLAGS2. cbv zeta. early_split;
  try (apply bad_early_time; early_leaf); early_leaf.
Qed.

Lemma bad_early_head m : early (m_mode m) -> early_out (c_HEAD2 m).
Proof. intros E. unfold c_HEAD2. cbv zeta. early_split; early_leaf. Qed.

(* a header pass ends in HEAD .. TYPEDO or BAD *)
Lemma bad_early_step flush m : md_hdr (m_mode m) -> early_out (stepf2 flush lenfix_list distfix_list m).
Proof.
  intros [E|[E|[E|E]]]; unfold stepf2, step2; rewrite E; cbn -[c_HEAD2 c_FLAGS2 c_TIME2 c_OS2].
  - apply bad_early_head. early_leaf.
  - apply bad_early_flags. early_leaf.
  - apply bad_early_time. early_leaf.
  - apply bad_early_os. early_leaf.
Qed.

(* the modes at a loop head of the decode theory *)
Lemma bad_at_groups G s c h b o : at_mode G s c h b o ->
  md_hdr (i_mode s) \/ md_type (i_mode s) \/ md_tab (i_mode s) \/ md_dec (i_mode s) \/ md_trl (i_mode s).
Proof.
  intros [_ D]. unfold md_hdr, md_type, md_tab, md_dec, md_trl.
  repeat match goal with H: _ \/ _ |- _ => destruct H as [H|H] end;
  repeat match goal with H: _ /\ _ |- _ => let E := fresh "E" in destruct H as [E _] end;
  repeat match goal with E: _ \/ _ |- _ => destruct E as [E|E] end; tauto.
Qed.

(* after a header pass, at a loop head of the decode theory: a header mode, or the start of the blocks *)
Lemma bad_hdr_next G s c h b o : at_mode G s c h b o -> early (i_mode s) ->
  md_hdr (i_mode s) \/ i_mode s = Zlib.proof.inflate.Model.TYPE \/ i_mode s = TYPEDO.
Proof.
  intros A E. destruct (bad_at_groups _ _ _ _ _ _ A) as [M|[M|[M|[M|M]]]]; [left; exact M|..];
  unfold md_type, md_tab, md_dec, md_trl, early in *;
  unfold HEAD, TYPEDO, BAD, Zlib.proof.inflate.Model.TYPE, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN,
    LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE in *; lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* inf_leave on another input of the same length                                                  *)

Lemma bad_lwin_inp flush m x : lwin flush (set_m_inp m x) = set_m_inp (lwin flush m) x.
Proof.
  unfold lwin. change (leave_ok flush (set_m_inp m x)) with (leave_ok flush m).
  destruct (leave_ok flush m); [|destruct m; reflexivity]. cbv zeta. unfold upd_s.
  change (m_s (restore (set_m_inp m x))) with (m_s (restore m)).
  set (U := set_i_win _ true). clearbody U. destruct m; reflexivity.
Qed.

Lemma bad_lpost_inp flush M x : Zlength x = Zlength (m_inp M) ->
  lpost flush (set_m_inp M x) = Res (r_ret (lpost flush M)) (set_m_inp (r_m (lpost flush M)) x) (r_dtype (lpost flush M)).
Proof.
  intros Hl. destruct M. cbn in Hl. unfold lpost, m_have. cbn. rewrite Hl.
  destruct (negb (Z.land _ 4 =? 0) && _); reflexivity.
Qed.

Lemma bad_leave_inp flush m x : Zlength x = Zlength (m_inp m) ->
  leave_fin flush (set_m_inp m x) =
  Res (r_ret (leave_fin flush m)) (set_m_inp (r_m (leave_fin flush m)) x) (r_dtype (leave_fin flush m)).
Proof.
  intros Hl. rewrite !bad_leave_fin_eq, bad_lwin_inp. apply bad_lpost_inp.
  unfold lwin. destruct (leave_ok flush m); destruct m; exact Hl.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The layout facts used at the start of the blocks                                              *)

Lemma bad_enc_len p last b : 1 <= Zlength (enc_block p last b).
Proof.
  unfold enc_block. rewrite Zlength_cons.
  match goal with |- context [Z.succ (Zlength ?l)] => pose proof (Zlength_nonneg l) end. lia.
Qed.

Lemma bad_epos_ge bs : forall p k, (k <= length bs)%nat -> p + Z.of_nat k <= epos p bs k.
Proof.
  induction bs as [|b r IH]; intros p k Hk.
  - cbn in Hk. destruct k; [cbn; lia|lia].
  - destruct k as [|k]; [cbn; lia|]. cbn [epos length] in *.
    pose proof (bad_enc_len p false b). specialize (IH (p + Zlength (enc_block p false b)) k ltac:(lia)). lia.
Qed.

(* at TYPE / TYPEDO with at most the header consumed: the first block, nothing in the bit buffer *)
Lemma bad_type_start G src s c h b o : bad_ctx G -> bad_src G src ->
  at_mode G s c h b o -> (i_mode s = Zlib.proof.inflate.Model.TYPE \/ i_mode s = TYPEDO) -> c <= hlen G ->
  c = hlen G /\ b = 0 /\ h = 0 /\ o = [] /\ i_last s = 0.
Proof.
  intros BC BS A M Lc.
  destruct (bad_raw_type G src s c h b o 0 BC BS A M Lc) as (E1 & E2 & E3 & E4 & _).
  repeat split; auto.
  destruct (bad_raw_ok G src BC BS) as (_ & _ & _ & _ & D0E & _).
  destruct A as [_ D].
  destruct D as [[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[Mx X]]]]]]]]]]]]]]]]];
  try (exfalso; destruct M as [M|M]; rewrite M in Mx;
       unfold Zlib.proof.inflate.Model.TYPE, TYPEDO, HEAD, FLAGS, TIME, OS, STORED, COPY_, COPY, TABLE, LENLENS,
         CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE in Mx; lia).
  destruct X as (k & Hk & Hq & _ & _ & HL). rewrite HL.
  unfold bpos, nblk in *. rewrite D0E in Hq.
  pose proof (bad_epos_ge (dc_bs G) 0 (Z.to_nat k) ltac:(rewrite Zlength_correct in Hk; lia)).
  destruct (Z.eqb_spec k 0); [reflexivity|]. lia.
Qed.

(* TYPE / TYPEDO at the start of the blocks, the bit buffer empty, when the call leaves at once (no input, or
   Z_BLOCK / Z_TREES at TYPE): the pass reads no input *)
Lemma bad_type_leave flush m x : (m_mode m = Zlib.proof.inflate.Model.TYPE \/ m_mode m = TYPEDO) ->
  i_last (m_s m) = 0 -> m_bits m = 0 ->
  (m_have m = 0 \/ (m_mode m = Zlib.proof.inflate.Model.TYPE /\ (flush = Z_BLOCK \/ flush = Z_TREES))) ->
  Zlength x = Zlength (m_inp m) ->
  stepf2 flush lenfix_list distfix_list m = IBrk (set_leave m) /\
  stepf2 flush lenfix_list distfix_list (set_m_inp m x) = IBrk (set_leave (set_m_inp m x)).
Proof.
  intros M La B H Hl.
  assert (Hv : m_have (set_m_inp m x) = m_have m) by (unfold m_have; cbn; rewrite Hl; reflexivity).
  assert (TD : forall m0, m_mode m0 = TYPEDO -> i_last (m_s m0) = 0 -> m_bits m0 = 0 -> m_have m0 = 0 ->
            stepf2 flush lenfix_list distfix_list m0 = IBrk (set_leave m0)).
  { intros m0 E0 L0 B0 H0. unfold stepf2, step2. rewrite E0. cbn -[c_TYPEDO].
    unfold c_TYPEDO. rewrite L0. cbn -[needbits]. unfold needbits. cbn [needbits_f]. rewrite B0, H0.
    reflexivity. }
  assert (TY : forall m0, m_mode m0 = Zlib.proof.inflate.Model.TYPE -> i_last (m_s m0) = 0 -> m_bits m0 = 0 ->
            (m_have m0 = 0 \/ flush = Z_BLOCK \/ flush = Z_TREES) ->
            stepf2 flush lenfix_list distfix_list m0 = IBrk (set_leave m0)).
  { intros m0 E0 L0 B0 H0. unfold stepf2, step2. rewrite E0. cbn -[c_TYPE].
    unfold c_TYPE. destruct (Z.eqb_spec flush Z_BLOCK); destruct (Z.eqb_spec flush Z_TREES); cbn [orb];
      try reflexivity.
    destruct H0 as [H0|[H0|H0]]; [|congruence|congruence].
    unfold c_TYPEDO. rewrite L0. cbn -[needbits]. unfold needbits. cbn [needbits_f]. rewrite B0, H0.
    reflexivity. }
  destruct M as [M|M].
  - destruct H as [H|(_ & H)].
    + split; apply TY; auto. rewrite Hv. auto.
    + split; apply TY; auto.
  - destruct H as [H|(H' & _)]; [|rewrite M in H'; discriminate].
    split; apply TD; auto. rewrite Hv. exact H.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The header loop                                                                                *)

Lemma bad_leave01 m : mwf3W m -> m_leave m <> 1 -> m_leave m = 0.
Proof. intros (W & _ & _) L. pose proof (mwW_leave _ W). lia. Qed.

Section HLoop.
Variables (DS: dc_step7a_stmt) (SM: stepf2_mwf3W_stmt).
Variables (G: dctx) (src: list Z) (pos: Z) (inp' x ob: list Z) (flush: Z).
Hypotheses (BC: bad_ctx G) (BS: bad_src G src) (C: dctx_ok7a G) (P0: 0 <= pos)
  (PL: pos + Zlength inp' <= Zlength (dc_src G)) (IE: inp' = sublist pos (pos + Zlength inp') (dc_src G))
  (XL: Zlength x = Zlength inp') (XB: bytes_ok x)
  (XA: forall i, 0 <= i < Zlength x -> pos + i < hlen G -> Znth i x = Znth i inp').

(* where the header loop may be: a header mode, or the start of the blocks *)
Definition hstart (m': mst) : Prop :=
  md_hdr (m_mode m') \/
  ((m_mode m' = Zlib.proof.inflate.Model.TYPE \/ m_mode m' = TYPEDO) /\ pos + m_nx m' <= hlen G).

(* one header pass: the same on both inputs, the next loop head of the decode theory, still in the header or
   at the start of the blocks *)
Lemma bad_hpass m' : Kd G pos inp' ob m' -> mwf3W m' -> m_leave m' = 0 -> md_hdr (m_mode m') ->
  exists m1', stepf2 flush lenfix_list distfix_list m' = IBrk m1' /\
    stepf2 flush lenfix_list distfix_list (set_m_inp m' x) = IBrk (set_m_inp m1' x) /\
    Kd G pos inp' ob m1' /\ mwf3W m1' /\ m_ow m1' = m_ow m' /\ (m_leave m1' = 1 \/ hstart m1') /\
    pos + m_nx m1' <= hlen G /\
    (md_hdr (m_mode m1') \/ m_mode m1' = Zlib.proof.inflate.Model.TYPE \/ m_mode m1' = TYPEDO).
Proof.
  intros K W L0 Hh.
  destruct (bad_pass_hdr G pos inp' x ob flush m' C P0 PL IE XL XB XA K W L0 Hh) as [E1 E2].
  pose proof (DS G pos inp' ob flush m' C P0 PL IE K W L0) as D.
  pose proof (SM flush m' W L0) as W1.
  pose proof (bad_early_step flush m' Hh) as Ea.
  destruct (stepf2 flush lenfix_list distfix_list m') as [m1'|r m1'] eqn:Es; [|destruct D].
  destruct D as (K1 & _ & _). destruct (E2 m1' eq_refl) as [N1 O1].
  exists m1'. split; [reflexivity|]. split; [exact E1|]. split; [exact K1|]. split; [exact W1|].
  split; [exact O1|].
  pose proof (bad_hdr_next G _ _ _ _ _ (kd_at _ _ _ _ _ K1) Ea) as MM.
  split; [|split; [exact N1|exact MM]].
  destruct (Z.eqb_spec (m_leave m1') 1) as [Lv|Lv]; [left; exact Lv|right].
  destruct MM as [M|M]; [left; exact M|].
  right. split; [exact M|exact N1].
Qed.

(* at the start of the blocks: the call leaves at once (reading nothing), or the blocks begin *)
Lemma bad_hloop_type m' o : Kd G pos inp' ob m' -> mwf3W m' -> m_leave m' = 0 ->
  (m_mode m' = Zlib.proof.inflate.Model.TYPE \/ m_mode m' = TYPEDO) -> pos + m_nx m' <= hlen G ->
  loop2 flush lenfix_list distfix_list (set_m_inp m' x) o ->
  (exists mE', loop2 flush lenfix_list distfix_list m' (IBrk mE') /\ o = IBrk (set_m_inp mE' x) /\
     m_inp mE' = inp' /\ pos + m_nx mE' <= hlen G /\ m_ow mE' = m_ow m' /\
     (md_hdr (m_mode mE') \/ m_mode mE' = Zlib.proof.inflate.Model.TYPE \/ m_mode mE' = TYPEDO)) \/
  (exists mT', Kd G pos inp' ob mT' /\ mwf3W mT' /\ m_leave mT' = 0 /\
     (m_mode mT' = Zlib.proof.inflate.Model.TYPE \/ m_mode mT' = TYPEDO) /\ pos + m_nx mT' = hlen G /\
     m_bits mT' = 0 /\ m_hold mT' = 0 /\ i_last (m_s mT') = 0 /\ m_ow mT' = m_ow m' /\ 0 < m_have mT' /\
     (m_mode mT' = Zlib.proof.inflate.Model.TYPE -> flush <> Z_BLOCK /\ flush <> Z_TREES) /\
     loop2 flush lenfix_list distfix_list (set_m_inp mT' x) o).
Proof.
  intros K W L0 Ht Hc LP.
  destruct (bad_type_start G src (m_s m') (pos + m_nx m') (m_hold m') (m_bits m') (ob ++ m_ow m') BC BS
              (kd_at _ _ _ _ _ K) Ht Hc) as (Ec & Eb & Eh & _ & El).
  assert (Hl : Zlength x = Zlength (m_inp m')) by (rewrite (kd_inp _ _ _ _ _ K); exact XL).
  assert (Hv0 : 0 <= m_have m') by (destruct W as (Wf & _); pose proof (mwW_nx _ Wf); unfold m_have; lia).
  destruct (Z.eq_dec (m_have m') 0) as [Hv|Hv];
  [|destruct (Z.eq_dec (m_mode m') Zlib.proof.inflate.Model.TYPE) as [Hm|Hm];
    [destruct (Z.eq_dec flush Z_BLOCK) as [Hf|Hf]; [|destruct (Z.eq_dec flush Z_TREES) as [Hf'|Hf']]|]].
  (* the call leaves at once *)
  1,2,3: assert (LV : m_have m' = 0 \/ (m_mode m' = Zlib.proof.inflate.Model.TYPE /\ (flush = Z_BLOCK \/ flush = Z_TREES)))
           by auto;
         destruct (bad_type_leave flush m' x Ht El Eb LV Hl) as [E1 E2];
         left; exists (set_leave m'); split; [apply loop2_leave; [exact E1|reflexivity]|];
         split; [|split; [destruct m'; exact (kd_inp _ _ _ _ _ K)|split; [destruct m'; exact Hc|split; [destruct m'; reflexivity|
                  unfold m_mode in *; destruct m'; right; exact Ht]]]];
         inversion LP as [? ? ? E|? ? E Lv|? ? ? E Lv _]; subst; rewrite E2 in E;
         try discriminate E; injection E as <-; [destruct m'; reflexivity|exfalso; apply Lv; reflexivity].
  (* the blocks begin *)
  all: right; exists m'; repeat (split; [assumption|]); repeat split; try assumption; try lia; try congruence.
Qed.

Lemma bad_hloop : forall m o, loop2 flush lenfix_list distfix_list m o ->
  forall m', m = set_m_inp m' x -> Kd G pos inp' ob m' -> mwf3W m' -> m_leave m' = 0 -> hstart m' ->
  (exists mE', loop2 flush lenfix_list distfix_list m' (IBrk mE') /\ o = IBrk (set_m_inp mE' x) /\
     m_inp mE' = inp' /\ pos + m_nx mE' <= hlen G /\ m_ow mE' = m_ow m' /\
     (md_hdr (m_mode mE') \/ m_mode mE' = Zlib.proof.inflate.Model.TYPE \/ m_mode mE' = TYPEDO)) \/
  (exists mT', Kd G pos inp' ob mT' /\ mwf3W mT' /\ m_leave mT' = 0 /\
     (m_mode mT' = Zlib.proof.inflate.Model.TYPE \/ m_mode mT' = TYPEDO) /\ pos + m_nx mT' = hlen G /\
     m_bits mT' = 0 /\ m_hold mT' = 0 /\ i_last (m_s mT') = 0 /\ m_ow mT' = m_ow m' /\ 0 < m_have mT' /\
     (m_mode mT' = Zlib.proof.inflate.Model.TYPE -> flush <> Z_BLOCK /\ flush <> Z_TREES) /\
     loop2 flush lenfix_list distfix_list (set_m_inp mT' x) o).
Proof.
  intros m o LP. induction LP as [m r m1 E | m m1 E L1 | m m1 o E L1 LP IH]; intros m' -> K W L0 HS.
  all: destruct HS as [Hh|(Ht & Hc)].
  all: try (apply bad_hloop_type; [assumption..|];
            first [apply loop2_ret; exact E | apply loop2_leave; assumption | eapply loop2_next; eassumption]).
  all: destruct (bad_hpass m' K W L0 Hh) as (m1' & E1 & E2 & K1 & W1 & O1 & H1 & N1 & MM1); rewrite E2 in E;
       try discriminate E; injection E as <-.
  - left. exists m1'. split; [apply loop2_leave; [exact E1|exact L1]|].
    split; [reflexivity|]. split; [exact (kd_inp _ _ _ _ _ K1)|]. split; [exact N1|]. split; [exact O1|exact MM1].
  - assert (L1' : m_leave m1' = 0) by (apply bad_leave01; [exact W1|exact L1]).
    destruct H1 as [H1|H1]; [rewrite L1' in H1; discriminate|].
    destruct (IH m1' eq_refl K1 W1 L1' H1) as [(mE' & LE & EO & IEq & NE & OE & ME)|(mT' & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12)].
    + left. exists mE'. split; [|repeat split; try assumption; congruence]. apply loop2_next with m1'; [exact E1|lia|exact LE].
    + right. exists mT'. repeat (split; [assumption|]). split; [congruence|]. auto.
Qed.
End HLoop.

(* ---------------------------------------------------------------------------------------------- *)
(* The block loop                                                                                 *)

Lemma bad_bview_id m :
  bview 0 (m_snx m) (i_hold (m_s m)) (i_bits (m_s m)) (i_wrap (m_s m)) (i_check (m_s m)) (i_total (m_s m))
    (i_flags (m_s m)) m = m.
Proof.
  destruct m as [s h inp aout nx ow hold bits in_ out ret leave adler msg tin tout snx sow].
  unfold bview. cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_msg m_tin
    m_tout m_snx m_sow].
  rewrite sublist_same by lia. rewrite !Z.sub_0_r. destruct s; reflexivity.
Qed.

(* a block pass keeps the fields of the wrapper: wrap, check value, total, flags *)
Lemma bad_blk_keep flush m m1 : blk_mode (m_mode m) -> 0 <= m_nx m <= Zlength (m_inp m) ->
  stepf2 flush lenfix_list distfix_list m = IBrk m1 ->
  i_wrap (m_s m1) = i_wrap (m_s m) /\ i_check (m_s m1) = i_check (m_s m) /\
  i_total (m_s m1) = i_total (m_s m) /\ i_flags (m_s m1) = i_flags (m_s m).
Proof.
  intros M N E.
  destruct (bad_view_step flush 0 (m_snx m) (i_hold (m_s m)) (i_bits (m_s m)) (i_wrap (m_s m)) (i_check (m_s m))
              (i_total (m_s m)) (i_flags (m_s m)) m ltac:(lia) ltac:(lia) M) as (x' & hh' & bb' & V).
  rewrite bad_bview_id, E in V. cbn in V. injection V as V.
  rewrite V at 1 2 3 4. repeat split.
Qed.

Lemma bad_vmode_blk md : blk_mode md \/ md = CHECK -> URunFrame.vmode md.
Proof.
  intros H. unfold URunFrame.vmode, blk_mode, md_type, md_tab, md_dec in *.
  unfold HEAD, BAD, Zlib.proof.inflate.Model.TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN,
    LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK in *. lia.
Qed.

Lemma bad_at_notbad G s c h b o : at_mode G s c h b o -> i_mode s <> BAD.
Proof.
  intros A. destruct (bad_at_groups _ _ _ _ _ _ A) as [M|[M|[M|[M|M]]]];
  unfold md_hdr, md_type, md_tab, md_dec, md_trl in M;
  unfold HEAD, FLAGS, TIME, OS, BAD, Zlib.proof.inflate.Model.TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS,
    CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE in *; lia.
Qed.

(* a pass keeps the input (URunFrame) *)
Lemma bad_pass_inp flush m m1 : URunFrame.vmode (m_mode m) ->
  stepf2 flush lenfix_list distfix_list m = IBrk m1 -> m_inp m1 = m_inp m.
Proof.
  intros V E. pose proof (URunFrame.step2_ok flush lenfix_list distfix_list (fast lenfix_list distfix_list)
                            (URunFrame.fast_fr lenfix_list distfix_list) m V) as S.
  change (step2 flush lenfix_list distfix_list (fast lenfix_list distfix_list) m) with
    (stepf2 flush lenfix_list distfix_list m) in S.
  rewrite E in S. apply S.
Qed.

Section BLoop.
Variables (DS: dc_step7a_stmt) (SM: stepf2_mwf3W_stmt).
Variables (G2: dctx) (pos2 d: Z) (x ob: list Z) (flush c t f: Z).
Hypotheses (C2: dctx_ok7a G2) (P20: 0 <= pos2) (D0: 0 <= d <= Zlength x)
  (PL2: pos2 + Zlength (sublist d (Zlength x) x) <= Zlength (dc_src G2))
  (IE2: sublist d (Zlength x) x =
        sublist pos2 (pos2 + Zlength (sublist d (Zlength x) x)) (dc_src G2)).

Lemma bad_view_nx xs hh bb m : mwf3W (bview d xs hh bb 0 c t f m) -> m_inp m = x -> d <= m_nx m <= Zlength x.
Proof.
  intros (W & _ & _) I. pose proof (mwW_nx _ W) as N. unfold bview in N. cbn in N. rewrite I in N.
  rewrite Zlength_sublist in N by lia. lia.
Qed.

Lemma bad_bloop : forall m o, loop2 flush lenfix_list distfix_list m o ->
  forall xs hh bb,
  Kd G2 pos2 (sublist d (Zlength x) x) ob (bview d xs hh bb 0 c t f m) -> mwf3W (bview d xs hh bb 0 c t f m) ->
  m_leave m = 0 -> m_inp m = x -> (blk_mode (m_mode m) \/ m_mode m = CHECK) ->
  i_total (m_s m) = t -> i_flags (m_s m) = f ->
  (exists mE xs' hh' bb', o = IBrk mE /\ m_leave mE = 1 /\
     loop2 flush lenfix_list distfix_list (bview d xs hh bb 0 c t f m) (IBrk (bview d xs' hh' bb' 0 c t f mE)) /\
     Kd G2 pos2 (sublist d (Zlength x) x) ob (bview d xs' hh' bb' 0 c t f mE) /\
     mwf3W (bview d xs' hh' bb' 0 c t f mE) /\ (blk_mode (m_mode mE) \/ m_mode mE = CHECK) /\
     i_wrap (m_s mE) = i_wrap (m_s m) /\ i_check (m_s mE) = i_check (m_s m) /\
     i_total (m_s mE) = t /\ i_flags (m_s mE) = f /\ m_inp mE = x /\ d <= m_nx mE <= Zlength x) \/
  (exists mC xs' hh' bb', m_mode mC = CHECK /\ m_leave mC = 0 /\ loop2 flush lenfix_list distfix_list mC o /\
     Kd G2 pos2 (sublist d (Zlength x) x) ob (bview d xs' hh' bb' 0 c t f mC) /\
     mwf3W (bview d xs' hh' bb' 0 c t f mC) /\
     i_wrap (m_s mC) = i_wrap (m_s m) /\ i_check (m_s mC) = i_check (m_s m) /\
     i_total (m_s mC) = t /\ i_flags (m_s mC) = f /\ m_inp mC = x /\ d <= m_nx mC <= Zlength x).
Proof.
  intros m o LP. induction LP as [m r m1 E | m m1 E L1 | m m1 o E L1 LP IH]; intros xs hh bb K W L0 I Md Tt Ff.
  all: pose proof (bad_view_nx xs hh bb m W I) as N.
  all: destruct Md as [Mb|Mc];
       [|right; exists m, xs, hh, bb; split; [exact Mc|]; split; [exact L0|];
         split; [first [apply loop2_ret; exact E | apply loop2_leave; assumption | eapply loop2_next; eassumption]|];
         repeat (split; [assumption|]); repeat split; try reflexivity; try assumption; lia].
  all: destruct (bad_view_step flush d xs hh bb 0 c t f m ltac:(lia) ltac:(rewrite I; lia) Mb)
         as (xs' & hh' & bb' & VS).
  all: assert (L0' : m_leave (bview d xs hh bb 0 c t f m) = 0) by exact L0.
  all: pose proof (DS G2 pos2 _ ob flush _ C2 P20 PL2 IE2 K W L0') as DP; rewrite VS, E in DP; cbn [iomap] in DP.
  1: destruct DP.
  all: destruct DP as (K1 & _ & _).
  all: pose proof (SM flush _ W L0') as W1; rewrite VS, E in W1; cbn [iomap] in W1.
  all: assert (V0 : URunFrame.vmode (m_mode m)) by (apply bad_vmode_blk; left; exact Mb).
  all: pose proof (bad_pass_inp flush m m1 V0 E) as I1; rewrite I in I1.
  all: destruct (bad_blk_keep flush m m1 Mb ltac:(rewrite I; lia) E) as (A1 & A2 & A3 & A4).
  all: assert (Md1 : blk_mode (m_mode m1) \/ m_mode m1 = CHECK)
         by (pose proof (bad_blk_next flush m Mb) as B; rewrite E in B;
             destruct B as [B|[B|B]]; [left; exact B|right; exact B|exfalso];
             exact (bad_at_notbad _ _ _ _ _ _ (kd_at _ _ _ _ _ K1) B)).
  - left. exists m1, xs', hh', bb'. split; [reflexivity|]. split; [exact L1|].
    split; [apply loop2_leave; [rewrite VS, E; reflexivity|exact L1]|].
    split; [exact K1|]. split; [exact W1|]. split; [exact Md1|].
    repeat (split; [congruence|]). exact (bad_view_nx xs' hh' bb' m1 W1 I1).
  - assert (L1' : m_leave m1 = 0).
    { apply bad_leave01 in W1; [exact W1|exact L1]. }
    destruct (IH xs' hh' bb' K1 W1 L1' I1 Md1 ltac:(congruence) ltac:(congruence))
      as [(mE & xs2 & hh2 & bb2 & B1 & B2 & B3 & B3a & B3b & B3c & B4 & B5 & B6 & B7 & B8 & B9)|
          (mC & xs2 & hh2 & bb2 & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11)].
    + left. exists mE, xs2, hh2, bb2. split; [exact B1|]. split; [exact B2|].
      split; [apply loop2_next with (bview d xs' hh' bb' 0 c t f m1); [rewrite VS, E; reflexivity|exact L1|exact B3]|].
      split; [exact B3a|]. split; [exact B3b|]. split; [exact B3c|].
      repeat (split; [congruence|]). exact B9.
    + right. exists mC, xs2, hh2, bb2. repeat (split; [assumption|]).
      repeat (split; [congruence|]). exact B11.
Qed.

End BLoop.
