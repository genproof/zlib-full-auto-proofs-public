(** * Kit for the body of trees.c's compress_block (Body_compress_block.v)

    - the six send_bits / send_code macro statements of [f_compress_block], cut out by matching:
      [cb_lit] (send_code(s, lc, ltree), the literal case), [cb_lsend] (send_code(s, code + LITERALS + 1,
      ltree)), [cb_lextra] (if (extra != 0) { lc -= base_length[code]; send_bits(s, lc, extra); }),
      [cb_dsend] (send_code(s, code, dtree)), [cb_dextra] (if (extra != 0) { dist -= base_dist[code];
      send_bits(s, dist, extra); }), [cb_end] (send_code(s, END_BLOCK, ltree));
    - their common pre/postconditions ([cb_base] locals, [cb_sep] resources: the trees in their Code/Len
      members, [SendKit.tree_codes]);
    - ranges of the trees.c tables ([rd_*_range]);
    - [cb_apply]: use a part lemma at a goal whose first statement is the part. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TSpec.
Require Import Zlib.proof.trees.SendKit2.
Require Import Zlib.trees.code.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

(** ** Model helpers *)

Lemma cb_rd_inv l i x : rd l i = Some x -> 0 <= i < Zlength l /\ x = Znth i l.
Proof.
  unfold rd, in_range. destruct (andb (0 <=? i) (i <? Zlength l)) eqn:E; [|discriminate].
  apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  intros H; inversion H; auto.
Qed.

Lemma cb_rd_forall (P : Z -> Prop) l i x : Forall P l -> rd l i = Some x -> P x.
Proof.
  intros HF H. apply cb_rd_inv in H. destruct H as [Hi ->].
  rewrite Forall_forall in HF. apply HF. apply Znth_In. exact Hi.
Qed.

Lemma cb_forallb_range lo hi l :
  forallb (fun x => andb (lo <=? x) (x <=? hi)) l = true -> Forall (fun x => lo <= x <= hi) l.
Proof.
  intros H. rewrite forallb_forall in H. rewrite Forall_forall. intros x Hx.
  specialize (H x Hx). apply andb_prop in H. destruct H. lia.
Qed.

Lemma rd_length_code_range i x : rd length_code_tab i = Some x -> 0 <= x <= 28.
Proof. apply (cb_rd_forall (fun x => _ <= x <= _)). apply cb_forallb_range. vm_compute. reflexivity. Qed.
Lemma rd_dist_code_range i x : rd dist_code_tab i = Some x -> 0 <= x <= 29.
Proof. apply (cb_rd_forall (fun x => _ <= x <= _)). apply cb_forallb_range. vm_compute. reflexivity. Qed.
Lemma rd_extra_lbits_range i x : rd extra_lbits i = Some x -> 0 <= x <= 5.
Proof. apply (cb_rd_forall (fun x => _ <= x <= _)). apply cb_forallb_range. vm_compute. reflexivity. Qed.
Lemma rd_extra_dbits_range i x : rd extra_dbits i = Some x -> 0 <= x <= 13.
Proof. apply (cb_rd_forall (fun x => _ <= x <= _)). apply cb_forallb_range. vm_compute. reflexivity. Qed.
Lemma rd_base_length_range i x : rd base_length_tab i = Some x -> 0 <= x <= 224.
Proof. apply (cb_rd_forall (fun x => _ <= x <= _)). apply cb_forallb_range. vm_compute. reflexivity. Qed.
Lemma rd_base_dist_range i x : rd base_dist_tab i = Some x -> 0 <= x <= 24576.
Proof. apply (cb_rd_forall (fun x => _ <= x <= _)). apply cb_forallb_range. vm_compute. reflexivity. Qed.

Lemma Zlength_length_code_tab : Zlength length_code_tab = 256. Proof. reflexivity. Qed.
Lemma Zlength_dist_code_tab : Zlength dist_code_tab = 512. Proof. reflexivity. Qed.
Lemma Zlength_extra_lbits : Zlength extra_lbits = 29. Proof. reflexivity. Qed.
Lemma Zlength_extra_dbits : Zlength extra_dbits = 30. Proof. reflexivity. Qed.
Lemma Zlength_base_length_tab : Zlength base_length_tab = 29. Proof. reflexivity. Qed.
Lemma Zlength_base_dist_tab : Zlength base_dist_tab = 30. Proof. reflexivity. Qed.

(** ** The statements *)

Definition cb_body : statement := Eval cbv [f_compress_block fn_body] in fn_body f_compress_block.

(** The literal case: [send_code(s, lc, ltree)]. *)
Definition cb_lit : statement := ltac:(
  let b := eval cbv [cb_body] in cb_body in
  lazymatch b with
  | context [Sifthenelse (Ebinop Oeq (Etempvar _dist tuint) (Econst_int (Int.repr 0) tint) tint) ?a _] => exact a
  end).

(** The match case: [code = _length_code[lc]; L1; extra = extra_lbits[code]; L2; dist--; D0; D1;
    extra = extra_dbits[code]; D2]. *)
Definition cb_match : statement := ltac:(
  let b := eval cbv [cb_body] in cb_body in
  lazymatch b with
  | context [Sifthenelse (Ebinop Oeq (Etempvar _dist tuint) (Econst_int (Int.repr 0) tint) tint) _ ?a] => exact a
  end).

(** [send_code(s, code + LITERALS + 1, ltree)]. *)
Definition cb_lsend : statement := ltac:(
  let b := eval cbv [cb_match] in cb_match in
  lazymatch b with Ssequence _ (Ssequence ?a _) => exact a end).

(** [if (extra != 0) { lc -= base_length[code]; send_bits(s, lc, extra); }]. *)
Definition cb_lextra : statement := ltac:(
  let b := eval cbv [cb_match] in cb_match in
  lazymatch b with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence ?a _))) => exact a end).

(** [code = d_code(dist)] (after [dist--]). *)
Definition cb_dcode : statement := ltac:(
  let b := eval cbv [cb_match] in cb_match in
  lazymatch b with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence ?a _))))) =>
    exact a end).

(** [send_code(s, code, dtree)]. *)
Definition cb_dsend : statement := ltac:(
  let b := eval cbv [cb_match] in cb_match in
  lazymatch b with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _
    (Ssequence ?a _)))))) => exact a end).

(** [if (extra != 0) { dist -= base_dist[code]; send_bits(s, dist, extra); }]. *)
Definition cb_dextra : statement := ltac:(
  let b := eval cbv [cb_match] in cb_match in
  lazymatch b with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _
    (Ssequence _ (Ssequence _ ?a))))))) => exact a end).

(** [send_code(s, END_BLOCK, ltree)] after the loop. *)
Definition cb_end : statement := ltac:(
  let b := eval cbv [cb_body] in cb_body in
  lazymatch b with Ssequence _ (Ssequence _ ?a) => exact a end).

Definition Delta_cb : tycontext := func_tycontext f_compress_block Vprog Gprog_compress_block nil.

(** ** Pre/postconditions *)

(** The locals that every part keeps. *)
Definition cb_base (sx : Z) (sp ltp dtp : val) (gv : globals) : list localdef :=
  [temp _sx (vi sx); temp _s sp; temp _ltree ltp; temp _dtree dtp; gvars gv].

(** The resources: the output fields, the symbol fields, the two trees (Code/Len presentation), the tables. *)
Definition cb_sep (om : cout) (sp pbp : val) (ts : tstate) (lsh : share) (ln : Z) (lt : tree) (ltp : val)
    (dsh : share) (dn : Z) (dt : tree) (dtp : val) (gv : globals) : list mpred :=
  [out_at (fst om) (snd om) sp pbp; sym_at ts sp pbp; tree_codes lsh ln lt ltp; tree_codes dsh dn dt dtp;
   trees_tables gv].

Definition cb_assert (L : list localdef) (om : cout) (sp pbp : val) (ts : tstate) (lsh : share) (ln : Z)
    (lt : tree) (ltp : val) (dsh : share) (dn : Z) (dt : tree) (dtp : val) (gv : globals) : environ -> mpred :=
  PROPx [] (LOCALx L (SEPx (cb_sep om sp pbp ts lsh ln lt ltp dsh dn dt dtp gv))).

(** The hypotheses shared by all parts. *)
Definition cb_ok (lsh : share) (ln : Z) (lt : tree) (dsh : share) (dn : Z) (dt : tree) : Prop :=
  readable_share lsh /\ readable_share dsh /\ tree_ok lt ln /\ tree_ok dt dn.

(** ** The part lemmas (statements) *)

(** [send_code(s, lc, ltree)]: [lc] is the literal byte. *)
Definition cb_lit_stmt : Prop :=
  forall {Espec : OracleKind} (sx lc : Z) (sp pbp ltp dtp : val) (gv : globals) (ts : tstate)
    (lsh : share) (ln : Z) (lt : tree) (dsh : share) (dn : Z) (dt : tree) (om r : cout),
  cb_ok lsh ln lt dsh dn dt -> 0 <= lc < 256 ->
  c_send_code om lc (fc lt) (dl lt) = Some r ->
  semax Delta_cb (cb_assert (temp _lc (vi lc) :: cb_base sx sp ltp dtp gv) om sp pbp ts lsh ln lt ltp dsh dn dt dtp gv)
    cb_lit
    (normal_ret_assert (cb_assert (cb_base sx sp ltp dtp gv) r sp pbp ts lsh ln lt ltp dsh dn dt dtp gv)).

(** [send_code(s, code + LITERALS + 1, ltree)]: [code] is the length code. *)
Definition cb_lsend_stmt : Prop :=
  forall {Espec : OracleKind} (sx lc dist code : Z) (sp pbp ltp dtp : val) (gv : globals) (ts : tstate)
    (lsh : share) (ln : Z) (lt : tree) (dsh : share) (dn : Z) (dt : tree) (om r : cout),
  cb_ok lsh ln lt dsh dn dt -> 0 <= code <= 28 ->
  c_send_code om (code + LITERALS + 1) (fc lt) (dl lt) = Some r ->
  semax Delta_cb
    (cb_assert (temp _code (vi code) :: temp _lc (vi lc) :: temp _dist (vi dist) :: cb_base sx sp ltp dtp gv)
       om sp pbp ts lsh ln lt ltp dsh dn dt dtp gv)
    cb_lsend
    (normal_ret_assert
      (cb_assert (temp _code (vi code) :: temp _lc (vi lc) :: temp _dist (vi dist) :: cb_base sx sp ltp dtp gv)
         r sp pbp ts lsh ln lt ltp dsh dn dt dtp gv)).

(** [if (extra != 0) { lc -= base_length[code]; send_bits(s, lc, extra); }]. *)
Definition cb_lextra_stmt : Prop :=
  forall {Espec : OracleKind} (sx lc dist code extra : Z) (sp pbp ltp dtp : val) (gv : globals) (ts : tstate)
    (lsh : share) (ln : Z) (lt : tree) (dsh : share) (dn : Z) (dt : tree) (om r : cout),
  cb_ok lsh ln lt dsh dn dt -> 0 <= lc < 256 -> 0 <= code <= 28 ->
  rd extra_lbits code = Some extra ->
  (if negb (extra =? 0) then let* bl := rd base_length_tab code in c_send_bits om (lc - bl) extra
   else Some om) = Some r ->
  semax Delta_cb
    (cb_assert (temp _extra (vi extra) :: temp _code (vi code) :: temp _lc (vi lc) :: temp _dist (vi dist) ::
                cb_base sx sp ltp dtp gv) om sp pbp ts lsh ln lt ltp dsh dn dt dtp gv)
    cb_lextra
    (normal_ret_assert
      (cb_assert (temp _dist (vi dist) :: cb_base sx sp ltp dtp gv) r sp pbp ts lsh ln lt ltp dsh dn dt dtp gv)).

(** [send_code(s, code, dtree)]: [code] is the distance code. *)
Definition cb_dsend_stmt : Prop :=
  forall {Espec : OracleKind} (sx dist code : Z) (sp pbp ltp dtp : val) (gv : globals) (ts : tstate)
    (lsh : share) (ln : Z) (lt : tree) (dsh : share) (dn : Z) (dt : tree) (om r : cout),
  cb_ok lsh ln lt dsh dn dt -> 0 <= code <= 29 ->
  c_send_code om code (fc dt) (dl dt) = Some r ->
  semax Delta_cb
    (cb_assert (temp _code (vi code) :: temp _dist (vi dist) :: cb_base sx sp ltp dtp gv)
       om sp pbp ts lsh ln lt ltp dsh dn dt dtp gv)
    cb_dsend
    (normal_ret_assert
      (cb_assert (temp _code (vi code) :: temp _dist (vi dist) :: cb_base sx sp ltp dtp gv)
         r sp pbp ts lsh ln lt ltp dsh dn dt dtp gv)).

(** [if (extra != 0) { dist -= base_dist[code]; send_bits(s, dist, extra); }]: [dist] is the distance - 1. *)
Definition cb_dextra_stmt : Prop :=
  forall {Espec : OracleKind} (sx dist code extra : Z) (sp pbp ltp dtp : val) (gv : globals) (ts : tstate)
    (lsh : share) (ln : Z) (lt : tree) (dsh : share) (dn : Z) (dt : tree) (om r : cout),
  cb_ok lsh ln lt dsh dn dt -> 0 <= dist < 65536 -> 0 <= code <= 29 ->
  rd extra_dbits code = Some extra ->
  (if negb (extra =? 0) then let* bd := rd base_dist_tab code in c_send_bits om (dist - bd) extra
   else Some om) = Some r ->
  semax Delta_cb
    (cb_assert (temp _extra (vi extra) :: temp _code (vi code) :: temp _dist (vi dist) ::
                cb_base sx sp ltp dtp gv) om sp pbp ts lsh ln lt ltp dsh dn dt dtp gv)
    cb_dextra
    (normal_ret_assert (cb_assert (cb_base sx sp ltp dtp gv) r sp pbp ts lsh ln lt ltp dsh dn dt dtp gv)).

(** [send_code(s, END_BLOCK, ltree)]: the last statement of the function (no [_sx] needed). *)
Definition cb_end_stmt : Prop :=
  forall {Espec : OracleKind} (sp pbp ltp dtp : val) (gv : globals) (ts : tstate)
    (lsh : share) (ln : Z) (lt : tree) (dsh : share) (dn : Z) (dt : tree) (om r : cout),
  cb_ok lsh ln lt dsh dn dt ->
  c_send_code om END_BLOCK (fc lt) (dl lt) = Some r ->
  semax Delta_cb
    (cb_assert [temp _s sp; temp _ltree ltp; temp _dtree dtp; gvars gv] om sp pbp ts lsh ln lt ltp dsh dn dt dtp gv)
    cb_end
    (normal_ret_assert
      (cb_assert [temp _s sp; temp _ltree ltp; temp _dtree dtp; gvars gv] r sp pbp ts lsh ln lt ltp dsh dn dt dtp gv)).

(** ** Using a part lemma *)

Lemma cb_apply {Espec : OracleKind} Delta (P P' : environ -> mpred) c (Q : environ -> mpred) R :
  ENTAIL Delta, P |-- P' ->
  semax Delta P' c (normal_ret_assert Q) -> semax Delta P c (overridePost Q R).
Proof.
  intros HP H. eapply semax_pre; [exact HP|].
  eapply semax_post; [| | | | exact H]; destruct R; simpl.
  - intros x. apply andp_left2, derives_refl.
  - intros x. apply andp_left2. apply prop_left. intros [].
  - intros x. apply andp_left2. apply prop_left. intros [].
  - intros vl x. apply andp_left2. apply prop_left. intros [].
Qed.

Lemma cb_apply_seq {Espec : OracleKind} Delta (P P' Q : environ -> mpred) c1 c2 R :
  ENTAIL Delta, P |-- P' ->
  semax Delta P' c1 (normal_ret_assert Q) -> semax Delta Q c2 R -> semax Delta P (Ssequence c1 c2) R.
Proof.
  intros HP H1 H2. eapply semax_seq; [|exact H2].
  apply (cb_apply Delta P P' c1 Q); assumption.
Qed.
