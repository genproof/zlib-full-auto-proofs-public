(** * Kit for the body proof of deflate() (Body_deflate.v): the context, the body split into stages, the model
    split the same way, the shape of a stage triple, and call lemmas for flush_pending / putShortMSB on [dfull].

    The body of deflate() is a right-nested chain of 23 statements e0 .. e22 (see [nth_stmt]):
      e0  if (deflateStateCheck(strm) || flush > Z_BLOCK || flush < 0) return Z_STREAM_ERROR;
      e1  s = strm->state;
      e2  if (strm->next_out == Z_NULL || (avail_in != 0 && next_in == Z_NULL) || (FINISH && flush != Z_FINISH)) ERR_RETURN
      e3  if (strm->avail_out == 0) ERR_RETURN(strm, Z_BUF_ERROR);
      e4  old_flush = s->last_flush;     e5  s->last_flush = flush;
      e6  if (s->pending != 0) { flush_pending ... } else if (avail_in == 0 && RANK ...) ERR_RETURN
      e7  if (s->status == FINISH_STATE && strm->avail_in != 0) ERR_RETURN(strm, Z_BUF_ERROR);
      e8  if (s->status == INIT_STATE && s->wrap == 0) s->status = BUSY_STATE;
      e9  if (s->status == INIT_STATE) { zlib header }                  [S_zlib,    model c_zlib2]
      e10 if (s->status == GZIP_STATE) { gzip header }                  [S_gzip,    c_deflate_gzip_header]
      e11 if (s->status == EXTRA_STATE) { ... }                         [S_extra,   c_deflate_extra]
      e12 if (s->status == NAME_STATE) { ... }                          [S_name,    c_deflate_name]
      e13 if (s->status == COMMENT_STATE) { ... }                       [S_comment, c_deflate_comment]
      e14 if (s->status == HCRC_STATE) { ... }                          [S_hcrc,    c_deflate_hcrc]
      e15 if (strm->avail_in != 0 || ...) { bstate = ...; ... }         [S_compress, c_deflate_compress]
      e16 .. e22  if (flush != Z_FINISH) return Z_OK; ... the trailer; return   [S_trailer, c_deflate_trailer]

    A stage triple ([stage_pre], [stage_post]): from the whole stream [dfull s z ...] with output space [R],
    the read-only globals, and an extra resource [X] (the user's gz_header and the validity witnesses for the
    gzip stages, [emp] otherwise), the stage statement ends normally in [dfull s' z' ...] with output space
    [rest_after z z' R] when the model's stage gives [(s', z', None)], and returns [rc] in that state when it
    gives [(s', z', Some rc)]. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Export Zlib.proof.deflate.DSpec.
Require Export Zlib.proof.trees.TLemmas.
Require Export Zlib.proof.deflate.Obligations.
Require Export Zlib.deflate.code.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

(** ** The context of the body *)
Definition Delta_df : tycontext := func_tycontext f_deflate Vprog Gprog_deflate nil.

(** ** Sub-statements *)

(** The k-th statement of a right-nested chain of [Ssequence]s (the last one is the chain's tail). *)
Fixpoint nth_stmt (s : statement) (k : nat) {struct k} : statement :=
  match k, s with
  | O, Ssequence a _ => a
  | S k', Ssequence _ b => nth_stmt b k'
  | O, _ => s
  | S _, _ => Sskip
  end.

(** The chain from its k-th statement on. *)
Fixpoint chain_from (s : statement) (k : nat) {struct k} : statement :=
  match k, s with
  | O, _ => s
  | S k', Ssequence _ b => chain_from b k'
  | S _, _ => Sskip
  end.

Lemma chain_from_S s k : (exists a b, chain_from s k = Ssequence a b) ->
  chain_from s k = Ssequence (nth_stmt s k) (chain_from s (S k)).
Proof.
  revert s; induction k; intros s [a [b E]]; destruct s; cbn in *; try discriminate.
  - inversion E; subst; reflexivity.
  - apply IHk. eauto.
Qed.

Definition df_body : statement := fn_body f_deflate.

Definition S_zlib : statement := nth_stmt df_body 9.
Definition S_gzip : statement := nth_stmt df_body 10.
Definition S_extra : statement := nth_stmt df_body 11.
Definition S_name : statement := nth_stmt df_body 12.
Definition S_comment : statement := nth_stmt df_body 13.
Definition S_hcrc : statement := nth_stmt df_body 14.
Definition S_compress : statement := nth_stmt df_body 15.
Definition S_trailer : statement := chain_from df_body 16.

(** Show a stage's statement concretely. *)
Ltac show_stmt :=
  cbv [S_zlib S_gzip S_extra S_name S_comment S_hcrc S_compress S_trailer nth_stmt chain_from df_body
       f_deflate fn_body].

(** ** The model, split like the body *)

(** The zlib header stage after e8 (the adjustment [INIT && wrap == 0 -> BUSY]). *)
Definition c_zlib2 (s : dstate) (z : strm) : option dres :=
  if d_status s =? INIT_STATE then
    let* s := c_putShortMSB s (zlib_header s) in
    let* s := (if d_strstart s =? 0 then Some s else
                 let* s := c_putShortMSB s (u32 (Z.shiftr (z_adler z) 16)) in
                 c_putShortMSB s (u32 (Z.land (z_adler z) 65535))) in
    let z := set_z_adler z 1 in
    let s := set_d_status s BUSY_STATE in
    c_flush_or_return s z
  else Some (s, z, None).

Definition init_busy (s : dstate) : dstate :=
  if ((d_status s =? INIT_STATE) && (d_wrap s =? 0))%bool then set_d_status s BUSY_STATE else s.

Lemma c_deflate_zlib_header_eq s z : c_deflate_zlib_header s z = c_zlib2 (init_busy s) z.
Proof. reflexivity. Qed.

(** The trailer stage as a [dres] (it always returns). *)
Definition c_trailer2 (s : dstate) (z : strm) (flush : Z) : option dres :=
  let* (s, z, r) := c_deflate_trailer s z flush in Some (s, z, Some r).

(** ** The user's gzip header and the validity of its pointers *)

(** The gz_header of the state ([d_gzhead s]) in memory. *)
Definition hdr_res (o : option gzh) (ghp : val) (hx : share * val * val * val) : mpred :=
  match o with
  | Some h => let '(hsh, xp, np, cp) := hx in gzh_at hsh h ghp xp np cp
  | None => emp
  end.

(** What the gzip stages need besides [hdr_res]: [s->gzhead] is NULL exactly without header; the header's share
    is readable; the extra / name / comment pointers that are not NULL can be compared with NULL (a witness [W],
    e.g. a malloc token of an empty object, gives their weak validity). *)
Definition gz_ok (o : option gzh) (ghp : val) (hx : share * val * val * val) (W : mpred) : Prop :=
  match o with
  | None => ghp = nullval
  | Some h =>
    let '(hsh, xp, np, cp) := hx in
    readable_share hsh /\
    (gz_extra h <> None -> gzh_at hsh h ghp xp np cp * W |-- weak_valid_pointer xp) /\
    (gz_name h <> None -> gzh_at hsh h ghp xp np cp * W |-- weak_valid_pointer np) /\
    (gz_comment h <> None -> gzh_at hsh h ghp xp np cp * W |-- weak_valid_pointer cp)
  end.

(** ** The shape of a stage triple *)

(** The locals every stage relies on. *)
Definition df_locals (p : dptrs) (flush : Z) (gv : globals) : list localdef :=
  [temp _strm (p_strm p); temp _s (p_s p); temp _flush (vi flush); gvars gv].

Definition stage_pre (p : dptrs) (pin pout : val) (ish : share) (R : list val) (msgv : val) (gv : globals)
    (flush : Z) (s : dstate) (z : strm) (X : mpred) : environ -> mpred :=
  PROPx [] (LOCALx (df_locals p flush gv)
  (SEPx [dfull s z p pin pout ish R msgv gv; deflate_globals gv; X])).

Definition stage_post (p : dptrs) (pin pout : val) (ish : share) (R : list val) (gv : globals)
    (flush : Z) (z : strm) (X : mpred) (res : dres) : ret_assert :=
  let '(s', z', o) := res in
  {| RA_normal :=
       match o with
       | None =>
         EX msgv' : val,
         PROPx [] (LOCALx (df_locals p flush gv)
         (SEPx [dfull s' z' p pin pout ish (rest_after z z' R) msgv' gv; deflate_globals gv; X]))
       | Some _ => FF
       end;
     RA_break := FF;
     RA_continue := FF;
     RA_return := fun vl =>
       match o with
       | Some rc =>
         EX msgv' : val,
         PROP (vl = Some (vi rc)) LOCAL ()
         SEP (dfull s' z' p pin pout ish (rest_after z z' R) msgv' gv; deflate_globals gv; X)
       | None => FF
       end |}.

(** A stage: for every run of its model ([c flush s z]), the triple, for any frame [X]. *)
Definition stage_ok (S : statement) (c : Z -> dstate -> strm -> option dres) : Prop :=
  forall (Espec : OracleKind) p pin pout ish R msgv gv flush s z X res,
  0 <= flush <= 5 -> c flush s z = Some res ->
  @semax DCS.CS Espec Delta_df (stage_pre p pin pout ish R msgv gv flush s z X) S
    (stage_post p pin pout ish R gv flush z X res).

(** A gzip header stage: the frame is the user's gz_header of the state and a validity witness [W]. *)
Definition stage_ok_gz (S : statement) (c : dstate -> strm -> option dres) : Prop :=
  forall (Espec : OracleKind) p pin pout ish R msgv gv flush s z hx W res,
  0 <= flush <= 5 -> c s z = Some res -> gz_ok (d_gzhead s) (p_gzhead p) hx W ->
  @semax DCS.CS Espec Delta_df
    (stage_pre p pin pout ish R msgv gv flush s z (hdr_res (d_gzhead s) (p_gzhead p) hx * W))%logic S
    (stage_post p pin pout ish R gv flush z (hdr_res (d_gzhead s) (p_gzhead p) hx * W)%logic res).

(** ** Tactics on model equations *)
Ltac case_if H := match type of H with context [if ?b then _ else _] => destruct b eqn:? end.
Ltac case_if_as H E := match type of H with context [if ?b then _ else _] => destruct b eqn:E end.

(** ** Unsigned arithmetic *)
Lemma repr_u32 x : Int.repr (u32 x) = Int.repr x.
Proof.
  unfold u32. apply Int.eqm_samerepr. apply Int.eqm_sym. unfold Int.eqm.
  apply Zbits.eqmod_mod. reflexivity.
Qed.

Lemma repr_u64 x : Int64.repr (u64 x) = Int64.repr x.
Proof.
  unfold u64. apply Int64.eqm_samerepr. apply Int64.eqm_sym. unfold Int64.eqm.
  apply Zbits.eqmod_mod. reflexivity.
Qed.

Lemma u32_range x : 0 <= u32 x <= Int.max_unsigned.
Proof. unfold u32. pose proof (Z.mod_pos_bound x 4294967296). rep_lia. Qed.

Lemma u64_range x : 0 <= u64 x <= Int64.max_unsigned.
Proof. unfold u64. pose proof (Z.mod_pos_bound x 18446744073709551616). rep_lia. Qed.

Lemma u32_small x : 0 <= x <= Int.max_unsigned -> u32 x = x.
Proof. intros. unfold u32. apply Z.mod_small. rep_lia. Qed.

Lemma u64_small x : 0 <= x <= Int64.max_unsigned -> u64 x = x.
Proof. intros. unfold u64. apply Z.mod_small. rep_lia. Qed.

(** ** The output space *)
Definition out_grow (z z' : strm) : Prop :=
  exists d, z_out z' = z_out z ++ d /\ z_avail_out z' = z_avail_out z - Zlength d.

Lemma out_grow_refl z : out_grow z z.
Proof. exists []. rewrite app_nil_r. split; auto. rewrite Zlength_nil. lia. Qed.

Lemma out_grow_same z z' : z_out z' = z_out z -> z_avail_out z' = z_avail_out z -> out_grow z z'.
Proof. intros E1 E2. exists []. rewrite app_nil_r, Zlength_nil. split; [auto | lia]. Qed.

Lemma out_grow_trans z1 z2 z3 : out_grow z1 z2 -> out_grow z2 z3 -> out_grow z1 z3.
Proof.
  intros [d1 [E1 F1]] [d2 [E2 F2]]. exists (d1 ++ d2). rewrite E2, E1, app_assoc, Zlength_app.
  split; [auto | lia].
Qed.

Lemma rest_after_refl z rest : rest_after z z rest = rest.
Proof. unfold rest_after. rewrite Z.sub_diag, sublist_same; auto. Qed.

Lemma rest_after_trans z z' z2 rest :
  Zlength rest = z_avail_out z -> 0 <= z_avail_out z2 -> out_grow z z' -> out_grow z' z2 ->
  rest_after z' z2 (rest_after z z' rest) = rest_after z z2 rest.
Proof.
  intros Hr H2 [d1 [E1 F1]] [d2 [E2 F2]]. unfold rest_after.
  rewrite E2, E1, !Zlength_app.
  assert (0 <= Zlength d1) by apply Zlength_nonneg. assert (0 <= Zlength d2) by apply Zlength_nonneg.
  rewrite Zlength_sublist by lia.
  rewrite sublist_sublist by lia. f_equal; lia.
Qed.

Lemma rest_after_same z z' rest : z_out z' = z_out z -> rest_after z z' rest = rest.
Proof. intros E. unfold rest_after. rewrite E, Z.sub_diag, sublist_same; auto. Qed.

Lemma mb_read_length b lo len l : mb_read b lo len = Some l -> Zlength l = len.
Proof.
  unfold mb_read, mb_definedb. intros H.
  case_if_as H E; [|discriminate]. inversion H; subst.
  repeat rewrite andb_true_iff in E. destruct E as [E1 [[E2 E3] E4]].
  apply Z.leb_le in E1. apply Z.leb_le in E2. apply Z.leb_le in E3.
  rewrite Zlength_sublist by lia. lia.
Qed.

(** The bytes read by [mb_read] from a buffer whose defined entries are bytes are bytes. *)
Lemma mb_read_bytes b lo len l : mb_ok b -> mb_read b lo len = Some l -> Forall (fun x => 0 <= x < 256) l.
Proof.
  unfold mb_read, mb_definedb. intros [Hl Hb] H.
  case_if_as H E; [|discriminate]. inversion H; subst.
  repeat rewrite andb_true_iff in E. destruct E as [E1 [[E2 E3] E4]].
  apply Z.leb_le in E1. apply Z.leb_le in E2. apply Z.leb_le in E3.
  apply Forall_Znth. intros i Hi. rewrite Zlength_sublist in Hi by lia.
  rewrite Znth_sublist by lia. apply Hb; [lia|].
  rewrite forallb_forall in E4. apply E4. apply in_map_iff. exists (Z.to_nat i). split; [lia|].
  apply in_seq. lia.
Qed.

(** ** flush_pending: what it changes, ranges, growth *)
Lemma set_d_out_out s o1 o2 : set_d_out (set_d_out s o1) o2 = set_d_out s o2.
Proof. destruct s as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? t ?]. destruct t. reflexivity. Qed.

Lemma set_d_out_po s o x : set_d_out (set_d_po s x) o = set_d_po (set_d_out s o) x.
Proof. reflexivity. Qed.

Lemma set_d_po_po s x y : set_d_po (set_d_po s x) y = set_d_po s y.
Proof. reflexivity. Qed.

Lemma flush_out_ranges z b lo len bytes z1 : strm_ranges z -> mb_ok b -> mb_read b lo len = Some bytes ->
  out_put z bytes = Some z1 -> 0 <= len <= z_avail_out z ->
  strm_ranges (set_z_avail_out (set_z_total_out z1 (u64 (z_total_out z1 + len))) (z_avail_out z1 - len)) /\
  out_grow z (set_z_avail_out (set_z_total_out z1 (u64 (z_total_out z1 + len))) (z_avail_out z1 - len)).
Proof.
  intros Hz Hb Hrd Hput Hl.
  pose proof (mb_read_length _ _ _ _ Hrd) as Hlen. pose proof (mb_read_bytes _ _ _ _ Hb Hrd) as Hby.
  unfold out_put in Hput. case_if Hput; [|discriminate]. inversion Hput; subst; clear Hput.
  pose proof (u64_range (z_total_out z + Zlength bytes)).
  split; [|exists bytes; cbn; split; auto].
  destruct Hz as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12).
  unfold u32_ok, u64_ok in *.
  unfold strm_ranges, u32_ok, u64_ok. cbn - [Z.max]. rewrite Zlength_app.
  repeat match goal with |- _ /\ _ => split end; try rep_lia; auto.
  apply Forall_app; auto.
Qed.

Lemma flush_len_range pend aout : 0 <= aout <= Int.max_unsigned ->
  0 <= pend - (if pend >? aout then aout else u32 pend) ->
  0 <= (if pend >? aout then aout else u32 pend) <= aout.
Proof.
  intros Ha Hp. destruct (pend >? aout) eqn:E; [lia|].
  pose proof (u32_range pend). rewrite Z.gtb_ltb, Z.ltb_ge in E.
  rewrite u32_small in * by lia. lia.
Qed.

Lemma c_flush_pending_inv s z s' z' : strm_ranges z -> c_flush_pending s z = Some (s', z') ->
  exists o po, s' = set_d_po (set_d_out s o) po /\ (0 <= d_po s -> 0 <= po) /\
  (out_ok (fst o) (snd o) -> strm_ranges z' /\ out_grow z z').
Proof.
  unfold c_flush_pending. intros Hz0 H. inv_bind H. rename x into o1.
  case_if H.
  - inversion H; subst; clear H. exists o1, (d_po s). split; [destruct s; reflexivity|].
    split; [auto|]. intros. split; [auto | apply out_grow_refl].
  - inv_bind H. rename x into bytes, Ha0 into Hrd. inv_bind H. rename x into z1, Ha0 into Hput.
    inversion H; subst; clear H.
    set (len := if d_pending (set_d_out s o1) >? z_avail_out z then z_avail_out z
                else u32 (d_pending (set_d_out s o1))) in *.
    assert (Hlen : 0 <= d_po s -> 0 <= len -> 0 <= d_po s + len) by lia.
    assert (Hcommon : out_ok (mkOut (o_buf (fst o1)) (o_pending (fst o1) - len) (o_bi_buf (fst o1))
                                         (o_bi_valid (fst o1)) (o_bi_used (fst o1))) (snd o1) ->
              strm_ranges (set_z_avail_out (set_z_total_out z1 (u64 (z_total_out z1 + len))) (z_avail_out z1 - len)) /\
              out_grow z (set_z_avail_out (set_z_total_out z1 (u64 (z_total_out z1 + len))) (z_avail_out z1 - len))).
    { intros Hok. pose proof Hz0 as Hz. destruct Hok as [Hmb [_ [Hp _]]]. cbn in Hmb, Hp.
      assert (Hl : 0 <= len <= z_avail_out z).
      { apply flush_len_range; [destruct Hz as (_ & _ & _ & _ & _ & _ & H7 & _); exact H7|].
        destruct o1 as [o1 m1]. cbn [fst snd] in Hp.
        assert (E : d_pending (set_d_out s (o1, m1)) = o_pending o1) by reflexivity.
        unfold len in Hp |- *. rewrite E in *. lia. }
      eapply flush_out_ranges; eauto. }
    match goal with |- context [if ?b then _ else _] => destruct b eqn:Ep end.
    + eexists; exists 0. split; [rewrite set_d_out_po, set_d_out_out, set_d_po_po; reflexivity|].
      split; [lia|]. exact Hcommon.
    + eexists; eexists. split; [rewrite set_d_out_po, set_d_out_out; reflexivity|].
      split; [|exact Hcommon]. intros Hpo. apply Hlen; auto.
      (* 0 <= len *)
      unfold len. destruct (_ >? _); [|apply u32_range].
      destruct Hz0 as (_ & _ & _ & _ & _ & _ & H7 & _). unfold u32_ok in H7. lia.
Qed.

(** ** Opening the representation without its foreign globals
    (trees.c's static descriptors and zutil.c's zcalloc / zcfree are not in deflate.c's type context). *)
Definition trees_rest (t : tstate) (sp strmp : val) (gv : globals) : mpred :=
  (bltree_at (tr_bltree t) sp *
   ldesc_at (field_address t_ds (DOT Zlib.trees.code._dyn_ltree) sp) (tr_lmax t) (gv Zlib.trees.code._static_l_desc) sp *
   ddesc_at (field_address t_ds (DOT Zlib.trees.code._dyn_dtree) sp) (tr_dmax t) (gv Zlib.trees.code._static_d_desc) sp *
   bldesc_at (field_address t_ds (DOT Zlib.trees.code._bl_tree) sp) (tr_blmax t) (gv Zlib.trees.code._static_bl_desc) sp *
   work_at (tr_wk t) sp)%logic.

Lemma trees_at_open cs sp pbp strmp gv :
  trees_at cs sp pbp strmp gv =
  (ltree_at (tr_ltree (fst cs)) sp * dtree_at (tr_dtree (fst cs)) sp * out_at (tr_out (fst cs)) (snd cs) sp pbp *
   sym_at (fst cs) sp pbp * dtype_at (fst cs) sp strmp * lvl_at (fst cs) sp * trees_rest (fst cs) sp strmp gv)%logic.
Proof. unfold trees_at, trees_rest. apply pred_ext; cancel. Qed.

Definition strm_zfuncs (strmp : val) (gv : globals) : mpred :=
  (@field_at DCS.CS Ews t_strm (DOT _zalloc) (gv _zcalloc) strmp *
   @field_at DCS.CS Ews t_strm (DOT _zfree) (gv _zcfree) strmp)%logic.

Lemma strm_at_open z sp strmp pin pout msgv gv :
  strm_at z sp strmp pin pout msgv gv =
  (@field_at DCS.CS Ews t_strm (DOT _next_in) (offset_val (z_next_in z) pin) strmp *
   @field_at DCS.CS Ews t_strm (DOT _avail_in) (vi (z_avail_in z)) strmp *
   @field_at DCS.CS Ews t_strm (DOT _total_in) (vl (z_total_in z)) strmp *
   @field_at DCS.CS Ews t_strm (DOT _next_out) (offset_val (Zlength (z_out z)) pout) strmp *
   @field_at DCS.CS Ews t_strm (DOT _avail_out) (vi (z_avail_out z)) strmp *
   @field_at DCS.CS Ews t_strm (DOT _total_out) (vl (z_total_out z)) strmp *
   @field_at DCS.CS Ews t_strm (DOT _msg) msgv strmp *
   @field_at DCS.CS Ews t_strm (DOT _state) sp strmp *
   strm_zfuncs strmp gv *
   @field_at DCS.CS Ews t_strm (DOT _opaque) nullval strmp *
   @field_at DCS.CS Ews t_strm (DOT _adler) (vl (z_adler z)) strmp *
   @field_at_ DCS.CS Ews t_strm (DOT _reserved) strmp)%logic.
Proof. unfold strm_at, strm_zfuncs. apply pred_ext; cancel. Qed.

Lemma dfull_fold s z p pin pout ish rest msgv gv :
  strm_ranges z -> msg_ok (z_msg z) msgv -> readable_share ish -> dstate_ranges s ->
  trees_at (d_trm s) (p_s p) (p_pbuf p) (p_strm p) gv * win_at s p * hash_at s p * match_at s p * cfg_at s p *
  stat_at s p * strm_at z (p_s p) (p_strm p) pin pout msgv gv * in_obj ish z pin * out_space z pout rest
  |-- dfull s z p pin pout ish rest msgv gv.
Proof. intros. unfold dfull, dstate_at. entailer!. Qed.

(** ** The call [flush_pending(strm)] on the whole stream: [sep_apply dfull_flush_open], [forward_call],
    [sep_apply dfull_flush_close]. *)
Lemma c_flush_pending_same s z s' z' : c_flush_pending s z = Some (s', z') ->
  z_in z' = z_in z /\ z_msg z' = z_msg z /\ z_next_in z' = z_next_in z /\ z_avail_in z' = z_avail_in z /\
  z_total_in z' = z_total_in z /\ z_adler z' = z_adler z.
Proof.
  unfold c_flush_pending. intros H. inv_bind H. case_if H; [inversion H; subst; repeat split|].
  inv_bind H. inv_bind H. inversion H; subst; clear H.
  unfold out_put in Ha1. case_if Ha1; [|discriminate]. inversion Ha1; subst. cbn. repeat split.
Qed.

Lemma c_flush_pending_grow s z r : c_flush_pending s z = Some r -> out_grow z (snd r).
Proof.
  unfold c_flush_pending. intros H. inv_bind H.
  case_if H; [inversion H; subst; apply out_grow_refl|].
  inv_bind H. inv_bind H. inversion H; subst; clear H. cbn.
  unfold out_put in Ha1. case_if Ha1; [|discriminate]. inversion Ha1; subst.
  apply mb_read_length in Ha0.
  exists x0. cbn. split; [auto | lia].
Qed.

(** What flush_pending does not touch. *)
Definition flush_frame (s : dstate) (z : strm) (p : dptrs) (pin : val) (ish : share) (gv : globals) : mpred :=
  (!! (dstate_ranges s /\ readable_share ish) &&
   (ltree_at (tr_ltree (d_tr s)) (p_s p) * dtree_at (tr_dtree (d_tr s)) (p_s p) *
    sym_at (d_tr s) (p_s p) (p_pbuf p) * dtype_at (d_tr s) (p_s p) (p_strm p) * lvl_at (d_tr s) (p_s p) *
    trees_rest (d_tr s) (p_s p) (p_strm p) gv *
    win_at s p * hash_at s p * match_at s p * cfg_at s p *
    @field_at DCS.CS Ews t_ds (DOT _status) (vi (d_status s)) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _pending_buf_size) (vl (d_pending_buf_size s)) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _wrap) (vi (d_wrap s)) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _gzhead) (p_gzhead p) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _gzindex) (vl (d_gzindex s)) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _method) (vi (d_method s)) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _last_flush) (vi (d_last_flush s)) (p_s p) *
    in_obj ish z pin))%logic.

Lemma dstate_ranges_flush s o po : dstate_ranges s -> 0 <= po -> dstate_ranges (set_d_po (set_d_out s o) po).
Proof. intros H Hpo. destruct s. unfold dstate_ranges in *. cbn in *. tauto. Qed.

Section FlushSame.
Variables (s : dstate) (o : cout) (po : Z) (p : dptrs) (gv : globals).
Let s' := set_d_po (set_d_out s o) po.
Lemma fs_win : win_at s' p = win_at s p. Proof. reflexivity. Qed.
Lemma fs_hash : hash_at s' p = hash_at s p. Proof. reflexivity. Qed.
Lemma fs_match : match_at s' p = match_at s p. Proof. reflexivity. Qed.
Lemma fs_cfg : cfg_at s' p = cfg_at s p. Proof. reflexivity. Qed.
Lemma fs_ltree : tr_ltree (d_tr s') = tr_ltree (d_tr s). Proof. reflexivity. Qed.
Lemma fs_dtree : tr_dtree (d_tr s') = tr_dtree (d_tr s). Proof. reflexivity. Qed.
Lemma fs_sym : sym_at (d_tr s') = sym_at (d_tr s). Proof. reflexivity. Qed.
Lemma fs_dtype : dtype_at (d_tr s') = dtype_at (d_tr s). Proof. reflexivity. Qed.
Lemma fs_rest : trees_rest (d_tr s') = trees_rest (d_tr s). Proof. reflexivity. Qed.
Lemma fs_lvl : lvl_at (d_tr s') = lvl_at (d_tr s). Proof. reflexivity. Qed.
End FlushSame.

Lemma dfull_flush_open s z p pin pout ish R msgv gv :
  dfull s z p pin pout ish R msgv gv |--
  (!! (strm_ranges z /\ msg_ok (z_msg z) msgv /\ dstate_ranges s) &&
   (strm_at z (p_s p) (p_strm p) pin pout msgv gv * out_space z pout R *
    @field_at DCS.CS Ews t_ds (DOT _pending_out) (offset_val (d_po s) (p_pbuf p)) (p_s p) *
    out_at (tr_out (d_tr s)) (d_pbm s) (p_s p) (p_pbuf p) * flush_frame s z p pin ish gv))%logic.
Proof.
  unfold dfull, dstate_at, flush_frame, stat_at. rewrite trees_at_open. unfold d_trm. cbn [fst snd].
  Intros. entailer!.
Qed.

Lemma dfull_flush_close s z s' z' p pin pout ish R' msgv gv :
  strm_ranges z -> msg_ok (z_msg z) msgv -> c_flush_pending s z = Some (s', z') ->
  strm_at z' (p_s p) (p_strm p) pin pout msgv gv * out_space z' pout R' *
  @field_at DCS.CS Ews t_ds (DOT _pending_out) (offset_val (d_po s') (p_pbuf p)) (p_s p) *
  out_at (tr_out (d_tr s')) (d_pbm s') (p_s p) (p_pbuf p) * flush_frame s z p pin ish gv
  |-- dfull s' z' p pin pout ish R' msgv gv.
Proof.
  intros Hz Hm H.
  destruct (c_flush_pending_same _ _ _ _ H) as (Ein & Emsg & _).
  destruct (c_flush_pending_inv _ _ _ _ Hz H) as (o & po & -> & Hpo & Hr).
  unfold dfull, dstate_at, flush_frame, stat_at. rewrite trees_at_open. unfold d_trm. cbn [fst snd].
  unfold out_at at 1. Intros.
  assert (Hz' : strm_ranges z') by (apply Hr; destruct o; auto).
  assert (Hd : dstate_ranges (set_d_po (set_d_out s o) po)).
  { match goal with H : dstate_ranges s |- _ => apply dstate_ranges_flush; auto; apply Hpo; destruct H as (_ & _ & Hp & _); exact Hp end. }
  unfold in_obj. rewrite Ein.
  rewrite fs_win, fs_hash, fs_match, fs_cfg, fs_ltree, fs_dtree, fs_sym, fs_dtype, fs_rest, fs_lvl.
  unfold out_at. entailer!.
Qed.


(** The same opening for any change of the bit output / pending_buf ([set_d_out]), pending_out ([set_d_po]) and
    the stream [z] (same input object, same msg): [sep_apply dfull_flush_open], change, [sep_apply dfull_out_close]. *)
Lemma dfull_out_close s z0 z ob m po p pin pout ish R msgv gv :
  strm_ranges z -> msg_ok (z_msg z) msgv -> z_in z = z_in z0 -> 0 <= po ->
  strm_at z (p_s p) (p_strm p) pin pout msgv gv * out_space z pout R *
  @field_at DCS.CS Ews t_ds (DOT _pending_out) (offset_val po (p_pbuf p)) (p_s p) *
  out_at ob m (p_s p) (p_pbuf p) * flush_frame s z0 p pin ish gv
  |-- dfull (set_d_po (set_d_out s (ob, m)) po) z p pin pout ish R msgv gv.
Proof.
  intros Hz Hm Ein Hpo.
  unfold dfull, dstate_at, flush_frame, stat_at. rewrite trees_at_open. unfold d_trm. cbn [fst snd].
  Intros.
  assert (Hd : dstate_ranges (set_d_po (set_d_out s (ob, m)) po)) by (apply dstate_ranges_flush; auto).
  unfold in_obj. rewrite Ein.
  rewrite fs_win, fs_hash, fs_match, fs_cfg, fs_ltree, fs_dtree, fs_sym, fs_dtype, fs_rest, fs_lvl.
  change (tr_out (d_tr (set_d_po (set_d_out s (ob, m)) po))) with ob.
  change (d_pbm (set_d_po (set_d_out s (ob, m)) po)) with m.
  change (d_po (set_d_po (set_d_out s (ob, m)) po)) with po.
  entailer!.
Qed.



Lemma set_d_po_same s o : set_d_po (set_d_out s o) (d_po s) = set_d_out s o.
Proof. destruct s; reflexivity. Qed.

(** [putShortMSB(s, b)] on the whole stream. *)
Lemma c_putShortMSB_eq s b : c_putShortMSB s b =
  let* om := c_putShortMSB_o (d_out s) b in Some (set_d_out s om).
Proof.
  unfold c_putShortMSB, c_putShortMSB_o, c_dput_byte.
  destruct (c_put_byte (d_out s) (Z.shiftr b 8)) as [o1|]; [|reflexivity]. cbn [bind].
  replace (d_out (set_d_out s o1)) with o1 by (destruct s as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? t ?]; destruct t, o1; reflexivity).
  destruct (c_put_byte o1 (Z.land b 255)); cbn [bind]; [rewrite set_d_out_out|]; reflexivity.
Qed.

Lemma set_d_out_self s : set_d_out s (d_out s) = s.
Proof. destruct s as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? t ?]; destruct t; reflexivity. Qed.

(** All the range facts of a [dstate_ranges] / [strm_ranges] hypothesis, as separate hypotheses. *)
Ltac open_dranges H :=
  let Hc := fresh "Hc" in pose proof H as Hc;
  unfold dstate_ranges, u32_ok, u64_ok, s32_ok, s64_ok in Hc; decompose [and] Hc; clear Hc.
Ltac open_zranges H :=
  let Hc := fresh "Hc" in pose proof H as Hc;
  unfold strm_ranges, u32_ok, u64_ok in Hc; decompose [and] Hc; clear Hc.

(** [forward_if] whose join point adds [temp id v] to the current precondition. *)
Ltac forward_if_temp id v :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp id v :: Q) (SEPx R)))
  end.

(** Back to [dfull] with nothing changed. *)
Lemma dfull_flush_back s z p pin pout ish R msgv gv :
  strm_ranges z -> msg_ok (z_msg z) msgv -> dstate_ranges s ->
  strm_at z (p_s p) (p_strm p) pin pout msgv gv * out_space z pout R *
  @field_at DCS.CS Ews t_ds (DOT _pending_out) (offset_val (d_po s) (p_pbuf p)) (p_s p) *
  out_at (tr_out (d_tr s)) (d_pbm s) (p_s p) (p_pbuf p) * flush_frame s z p pin ish gv
  |-- dfull s z p pin pout ish R msgv gv.
Proof.
  intros Hz Hm Hd.
  eapply derives_trans; [apply (dfull_out_close s z z (tr_out (d_tr s)) (d_pbm s) (d_po s)); auto|].
  { destruct Hd as (_ & _ & Hp & _). exact Hp. }
  change (tr_out (d_tr s), d_pbm s) with (d_out s). rewrite set_d_po_same, set_d_out_self. auto.
Qed.

(** The items of [flush_frame], opened, folded back. *)
Lemma flush_frame_fold s z p pin ish gv :
  dstate_ranges s -> readable_share ish ->
  ltree_at (tr_ltree (d_tr s)) (p_s p) * dtree_at (tr_dtree (d_tr s)) (p_s p) *
  sym_at (d_tr s) (p_s p) (p_pbuf p) * dtype_at (d_tr s) (p_s p) (p_strm p) * lvl_at (d_tr s) (p_s p) *
  trees_rest (d_tr s) (p_s p) (p_strm p) gv *
  win_at s p * hash_at s p * match_at s p * cfg_at s p *
  @field_at DCS.CS Ews t_ds (DOT _status) (vi (d_status s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf_size) (vl (d_pending_buf_size s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _wrap) (vi (d_wrap s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _gzhead) (p_gzhead p) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _gzindex) (vl (d_gzindex s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _method) (vi (d_method s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _last_flush) (vi (d_last_flush s)) (p_s p) *
  in_obj ish z pin
  |-- flush_frame s z p pin ish gv.
Proof. intros. unfold flush_frame. entailer!. Qed.

Lemma d_out_set_d_out s o : d_out (set_d_out s o) = o.
Proof. destruct s as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? t ?]; destruct t, o; reflexivity. Qed.

(** ** Tactics *)

(** Close a goal on [Z] comparisons: case on every comparison in the goal. *)
Ltac zfin :=
  rewrite ?Z.geb_leb, ?Z.gtb_ltb;
  repeat (match goal with
          | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b)
          | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b)
          | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
          | |- context [zlt ?a ?b] => destruct (zlt a b)
          | |- context [zeq ?a ?b] => destruct (zeq a b)
          end; try lia); try reflexivity.

Ltac drop_temp id Q :=
  match Q with
  | nil => constr:(@nil localdef)
  | temp id _ :: ?Q' => drop_temp id Q'
  | ?a :: ?Q' => let r := drop_temp id Q' in constr:(a :: r)
  end.

(** [forward_if] whose join point sets [temp id v] (replacing an earlier value of [id]). *)
Ltac forward_if_set id v :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    let Q' := drop_temp id Q in
    forward_if (PROPx P (LOCALx (temp id v :: Q') (SEPx R)))
  end.

Ltac subst_sep old new R :=
  match R with
  | nil => constr:(@nil mpred)
  | old :: ?R' => constr:(new :: R')
  | ?a :: ?R' => let r := subst_sep old new R' in constr:(a :: r)
  end.

(** [forward_if] whose join point is the current precondition with the SEP item [old] replaced by [new]. *)
Ltac forward_if_sep old new :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    let R' := subst_sep old new R in
    forward_if (PROPx P (LOCALx Q (SEPx R')))
  end.

(** Simplification of the projections of updated states (as in CompressKit). *)
Tactic Notation "dsimpl" :=
  cbn [set_d_status set_d_po set_d_wrap set_d_gzhead set_d_gzindex set_d_method set_d_last_flush set_d_w_size
       set_d_w_bits set_d_w_mask set_d_window set_d_window_size set_d_prev set_d_head set_d_ins_h set_d_hash_size
       set_d_hash_bits set_d_hash_mask set_d_hash_shift set_d_block_start set_d_match_length set_d_prev_match
       set_d_match_available set_d_strstart set_d_match_start set_d_lookahead set_d_prev_length
       set_d_max_chain_length set_d_max_lazy_match set_d_good_match set_d_nice_match set_d_insert set_d_high_water
       set_d_slid set_d_pending_buf_size set_d_tr set_d_pbm d_trm set_d_trm d_level d_strategy d_pending
       d_status d_po d_wrap d_gzhead d_gzindex d_method d_last_flush d_w_size d_w_bits d_w_mask d_window
       d_window_size d_prev d_head d_ins_h d_hash_size d_hash_bits d_hash_mask d_hash_shift d_block_start
       d_match_length d_prev_match d_match_available d_strstart d_match_start d_lookahead d_prev_length
       d_max_chain_length d_max_lazy_match d_good_match d_nice_match d_insert d_high_water d_slid
       d_pending_buf_size d_tr d_pbm set_d_out d_out
       o_buf o_pending o_bi_buf o_bi_valid o_bi_used tr_ltree tr_dtree tr_bltree tr_lmax tr_dmax tr_blmax tr_wk
       tr_out tr_sym_next tr_sym_end tr_matches tr_lit_bufsize tr_level tr_strategy tr_data_type
       set_ltree set_dtree set_bltree set_lmax set_dmax set_blmax set_wk set_out set_sym_next set_matches
       set_data_type fst snd].
Tactic Notation "dsimpl" "in" hyp(H) :=
  cbn [set_d_status set_d_po set_d_wrap set_d_gzhead set_d_gzindex set_d_method set_d_last_flush set_d_w_size
       set_d_w_bits set_d_w_mask set_d_window set_d_window_size set_d_prev set_d_head set_d_ins_h set_d_hash_size
       set_d_hash_bits set_d_hash_mask set_d_hash_shift set_d_block_start set_d_match_length set_d_prev_match
       set_d_match_available set_d_strstart set_d_match_start set_d_lookahead set_d_prev_length
       set_d_max_chain_length set_d_max_lazy_match set_d_good_match set_d_nice_match set_d_insert set_d_high_water
       set_d_slid set_d_pending_buf_size set_d_tr set_d_pbm d_trm set_d_trm d_level d_strategy d_pending
       d_status d_po d_wrap d_gzhead d_gzindex d_method d_last_flush d_w_size d_w_bits d_w_mask d_window
       d_window_size d_prev d_head d_ins_h d_hash_size d_hash_bits d_hash_mask d_hash_shift d_block_start
       d_match_length d_prev_match d_match_available d_strstart d_match_start d_lookahead d_prev_length
       d_max_chain_length d_max_lazy_match d_good_match d_nice_match d_insert d_high_water d_slid
       d_pending_buf_size d_tr d_pbm set_d_out d_out
       o_buf o_pending o_bi_buf o_bi_valid o_bi_used tr_ltree tr_dtree tr_bltree tr_lmax tr_dmax tr_blmax tr_wk
       tr_out tr_sym_next tr_sym_end tr_matches tr_lit_bufsize tr_level tr_strategy tr_data_type
       set_ltree set_dtree set_bltree set_lmax set_dmax set_blmax set_wk set_out set_sym_next set_matches
       set_data_type fst snd] in H.

(** ** Folding opened groups back *)
Lemma win_at_fold s p :
  @field_at DCS.CS Ews t_ds (DOT _window) (p_window p) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _window_size) (vl (d_window_size s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _w_size) (vi (d_w_size s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _w_bits) (vi (d_w_bits s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _w_mask) (vi (d_w_mask s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _high_water) (vl (d_high_water s)) (p_s p) *
  @data_at DCS.CS Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) (p_window p)
  |-- win_at s p.
Proof. unfold win_at. cancel. Qed.

Lemma match_at_fold s p :
  @field_at DCS.CS Ews t_ds (DOT _block_start) (vl (d_block_start s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _match_length) (vi (d_match_length s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _prev_match) (vi (d_prev_match s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _match_available) (vi (d_match_available s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _strstart) (vi (d_strstart s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _match_start) (vi (d_match_start s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _lookahead) (vi (d_lookahead s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _prev_length) (vi (d_prev_length s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _insert) (vi (d_insert s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _slid) (vi (d_slid s)) (p_s p)
  |-- match_at s p.
Proof. unfold match_at. cancel. Qed.

Lemma lvl_at_fold t sp :
  Int.min_signed <= tr_level t <= Int.max_signed -> Int.min_signed <= tr_strategy t <= Int.max_signed ->
  @field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._level) (vi (tr_level t)) sp *
  @field_at DCS.CS Ews t_ds (DOT Zlib.deflate.code._strategy) (vi (tr_strategy t)) sp
  |-- lvl_at t sp.
Proof. intros. unfold lvl_at. entailer!. Qed.

(** The z_stream with a new adler (strm->adler = a), folded. *)
Lemma strm_at_set_adler z a sp strmp pin pout msgv gv :
  @field_at DCS.CS Ews t_strm (DOT _next_in) (offset_val (z_next_in z) pin) strmp *
  @field_at DCS.CS Ews t_strm (DOT _avail_in) (vi (z_avail_in z)) strmp *
  @field_at DCS.CS Ews t_strm (DOT _total_in) (vl (z_total_in z)) strmp *
  @field_at DCS.CS Ews t_strm (DOT _next_out) (offset_val (Zlength (z_out z)) pout) strmp *
  @field_at DCS.CS Ews t_strm (DOT _avail_out) (vi (z_avail_out z)) strmp *
  @field_at DCS.CS Ews t_strm (DOT _total_out) (vl (z_total_out z)) strmp *
  @field_at DCS.CS Ews t_strm (DOT _msg) msgv strmp *
  @field_at DCS.CS Ews t_strm (DOT _state) sp strmp *
  strm_zfuncs strmp gv *
  @field_at DCS.CS Ews t_strm (DOT _opaque) nullval strmp *
  @field_at DCS.CS Ews t_strm (DOT _adler) (vl a) strmp *
  @field_at_ DCS.CS Ews t_strm (DOT _reserved) strmp
  |-- strm_at (set_z_adler z a) sp strmp pin pout msgv gv.
Proof. rewrite strm_at_open. cbn [z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler set_z_adler]. cancel. Qed.

Lemma strm_ranges_set_adler z a : strm_ranges z -> 0 <= a <= Int64.max_unsigned -> strm_ranges (set_z_adler z a).
Proof. unfold strm_ranges, u32_ok, u64_ok. cbn. tauto. Qed.

(** ** The entry stage (v2): statements e2 .. e8 as one statement, after [s = strm->state]
    (the checks and ERR_RETURNs, last_flush, the flush of pending output, and e8 [INIT && wrap == 0 -> BUSY]).
    The main proof turns the chain e2; (e3; ...) into [Ssequence S_entry (chain_from df_body 9)]. *)
Definition S_entry : statement :=
  Ssequence (nth_stmt df_body 2) (Ssequence (nth_stmt df_body 3) (Ssequence (nth_stmt df_body 4)
  (Ssequence (nth_stmt df_body 5) (Ssequence (nth_stmt df_body 6) (Ssequence (nth_stmt df_body 7)
  (nth_stmt df_body 8)))))).

(** Its model: the entry checks of [c_deflate_entry], then [init_busy] (the first line of
    [c_deflate_zlib_header]). *)
Definition c_entry2 (flush : Z) (s : dstate) (z : strm) : option dres :=
  then_stage (c_deflate_entry s z flush) (fun s z => Some (init_busy s, z, None)).

(** The entry stage: at the start of the call nothing is written yet ([z_out z = []], next_out = pout), and the
    caller's witness [W] gives the weak validity of [pout] for [strm->next_out == Z_NULL] when there is no output
    space. *)
Definition stage_ok_entry : Prop :=
  forall (Espec : OracleKind) p pin pout ish R msgv gv flush s z W X res,
  0 <= flush <= 5 -> z_out z = [] -> (Zlength R = 0 -> wv_ok W) -> c_entry2 flush s z = Some res ->
  @semax DCS.CS Espec Delta_df (stage_pre p pin pout ish R msgv gv flush s z (X * wv_at W pout))%logic S_entry
    (stage_post p pin pout ish R gv flush z (X * wv_at W pout)%logic res).

(** ** What every stage keeps of the state (the gz_header and the sizes of the allocations, [dtokens]; v4: the
    buffer lengths agree with the size fields, [DSpec.dsizes]). *)
Definition dkeep (s s' : dstate) : Prop :=
  d_gzhead s' = d_gzhead s /\ d_w_size s' = d_w_size s /\ d_hash_size s' = d_hash_size s /\
  tr_lit_bufsize (d_tr s') = tr_lit_bufsize (d_tr s) /\ (dsizes s -> dsizes s').

Lemma dkeep_refl s : dkeep s s.
Proof. unfold dkeep. split; [|split; [|split; [|split]]]; auto. Qed.

Lemma dkeep_trans s1 s2 s3 : dkeep s1 s2 -> dkeep s2 s3 -> dkeep s1 s3.
Proof. unfold dkeep. intros (A & B & C & D & I) (E & F & G & H & J). split; [|split; [|split; [|split]]]; auto; congruence. Qed.

(** A stage's model only appends to the output and keeps [dkeep]. *)
Definition stage_facts (c : Z -> dstate -> strm -> option dres) : Prop :=
  forall f s z s' z' o, c f s z = Some (s', z', o) -> out_grow z z' /\ dkeep s s'.
