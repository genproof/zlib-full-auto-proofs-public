(* Law inflate_reset, main (IRMain.v): the kit shared by the segment lemmas of main's proof (as inflate_codes'
   MainKit.v / MainHelp.v / MainInfKit.v).
   - Gmain_k (= IRMain.Gmain), Delta_m (main's type context), POST_m (main's postcondition after start_function);
   - the segments of f_main's body: seg_loop (the loop body after its leading Sskip), seg_tail (after the loop),
     seg_ph2 (the then-branch of `if (phase == 2)`: b's inflate() call and the asserts), seg_rst (the then-branch
     of `if (stop == 0)` after `if (phase == 2) break;`: the reset of a and inflateInit2(&b, w2));
   - the assertions: inv_at / loop_inv (the loop invariant, phase 1 or 2), brk_inv (after the loop, phase 2),
     ph2_pre / ph2_post, rst_pre;
   - the statements of the parts (loop_stmt, ph2_stmt, rst_stmt), proved in IRMainLoop.v, IRMainPh2.v,
     IRMainRst.v, assembled in IRMainTop.v / IRMain.v;
   - moves of byte arrays, malloc tokens and struct z_stream between the units' compspecs and the law's;
     the stream at the law's compspecs (ir_tup); the message literals' pointers. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_reset.IRLawCS Zlib.proof.harness.inflate_reset.IRGlobals
               Zlib.proof.harness.inflate_reset.IRFacts.
Require Import Zlib.harness.x_inflate_reset.code.
Require Import Zlib.proof.crc32.Spec.
Local Open Scope logic.

Definition Gmain_k : funspecs :=
  [inflateInit2__spec; inflate_spec; inflateEnd_spec; inflateReset_spec; inflateReset2_spec; zcalloc_i; zcfree_i;
   bytes_same_spec; exact_copy_spec; exact_space_spec; inflate_wbits_ok_spec; stream_defaults_spec;
   (_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   nondet_u32_spec; nondet_u8_spec; nondet_bytes_spec; gp_assert_spec; gp_assume_spec].

Definition Delta_m : tycontext := func_tycontext f_main (QPvarspecs p) Gmain_k nil.

(* main's postcondition after start_function (main_core_spec) *)
Definition POST_m : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* ---------------------------------------------------------------------------------------------- *)
(* The segments of f_main's body                                                                 *)

(* a sub-statement by its path (0: first component, other: second) *)
Fixpoint sub_stmt (path: list nat) (s: statement) : statement :=
  match path, s with
  | nil, _ => s
  | O :: pth, Ssequence a _ => sub_stmt pth a
  | S _ :: pth, Ssequence _ b => sub_stmt pth b
  | O :: pth, Sifthenelse _ a _ => sub_stmt pth a
  | S _ :: pth, Sifthenelse _ _ b => sub_stmt pth b
  | O :: pth, Sloop a _ => sub_stmt pth a
  | S _ :: pth, Sloop _ b => sub_stmt pth b
  | _, _ => Sskip
  end.

Definition opt_or {A} (x y: option A) : option A := match x with Some _ => x | None => y end.
Definition opt_cons {A} (k: A) (x: option (list A)) : option (list A) :=
  match x with Some l => Some (k :: l) | None => None end.

(* the path of the first `Ssequence (Sloop _ _) _` *)
Fixpoint find_loop (s: statement) : option (list nat) :=
  match s with
  | Ssequence (Sloop _ _) _ => Some nil
  | Ssequence a b => opt_or (opt_cons O (find_loop a)) (opt_cons 1%nat (find_loop b))
  | Sifthenelse _ a b => opt_or (opt_cons O (find_loop a)) (opt_cons 1%nat (find_loop b))
  | Sloop a b => opt_or (opt_cons O (find_loop a)) (opt_cons 1%nat (find_loop b))
  | _ => None
  end.

(* the path of the first `Sifthenelse (Ebinop _ (Etempvar x _) _ _) _ _` *)
Fixpoint find_if (x: ident) (s: statement) : option (list nat) :=
  match s with
  | Sifthenelse (Ebinop _ (Etempvar y _) _ _) a b =>
      if Pos.eqb x y then Some nil
      else opt_or (opt_cons O (find_if x a)) (opt_cons 1%nat (find_if x b))
  | Sifthenelse _ a b => opt_or (opt_cons O (find_if x a)) (opt_cons 1%nat (find_if x b))
  | Ssequence a b => opt_or (opt_cons O (find_if x a)) (opt_cons 1%nat (find_if x b))
  | Sloop a b => opt_or (opt_cons O (find_if x a)) (opt_cons 1%nat (find_if x b))
  | _ => None
  end.

Ltac get_seg pth sfx :=
  let p := eval vm_compute in (match pth with Some l => l ++ sfx | None => nil end) in
  let x := eval cbv beta iota zeta delta [sub_stmt f_main fn_body] in (sub_stmt p (fn_body f_main)) in
  exact x.

(* the loop body (after its leading Sskip) and the statements after the loop *)
Definition seg_loop : statement := ltac:(get_seg (find_loop (fn_body f_main)) [0; 0; 1]%nat).
Definition seg_tail : statement := ltac:(get_seg (find_loop (fn_body f_main)) [1]%nat).
(* the then-branch of `if (phase == 2)` (the first test of phase: b's call and the asserts) *)
Definition seg_ph2 : statement := ltac:(get_seg (find_if _phase (fn_body f_main)) [0]%nat).
(* the then-branch of `if (stop == 0)` after `if (phase == 2) break;` *)
Definition seg_rst : statement := ltac:(get_seg (find_if _stop (fn_body f_main)) [0; 1]%nat).

(* ---------------------------------------------------------------------------------------------- *)
(* Compspecs moves (the specs are at the units' CS, main at the law's CS)                          *)

Lemma bytes_inflate_cs sh n (v: list val) q:
  @data_at Zlib.units.Inflate.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.
Lemma bytes_adler_cs sh n (v: list val) q:
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.
Lemma tok_inflate_cs sh n q:
  @malloc_token Zlib.units.Inflate.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_inflate). reflexivity. Qed.
Lemma tok_adler_cs sh n q:
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_adler32). reflexivity. Qed.
Lemma ptr_adler_cs_ sh q:
  @data_at_ Zlib.units.Adler32.CS sh (tptr tuchar) q = @data_at_ CS sh (tptr tuchar) q.
Proof. unfold data_at_. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.
Lemma ptr_adler_cs sh (v: val) q:
  @data_at Zlib.units.Adler32.CS sh (tptr tuchar) v q = @data_at CS sh (tptr tuchar) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.

(* the stream struct *)
Definition t_z : type := Tstruct _z_stream_s noattr.

Definition strm_tuple : Type :=
  (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * val)))))))))))))%type.

Lemma strm_cs sh (v: strm_tuple) q:
  @data_at Zlib.units.Inflate.CS sh Rep.t_strm v q = @data_at CS sh t_z v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.

Definition strm_undef : strm_tuple :=
  (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef,
   (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, Vundef))))))))))))).

Lemma strm_undef_cs sh q:
  @data_at_ CS sh t_z q = @data_at Zlib.units.Inflate.CS sh Rep.t_strm strm_undef q.
Proof. unfold data_at_. rewrite strm_cs. reflexivity. Qed.

(* any stream contents (at the inflate unit's CS) give back the local variable's memory *)
Lemma strm_to_undef sh (v: strm_tuple) q:
  @data_at Zlib.units.Inflate.CS sh Rep.t_strm v q |-- @data_at_ CS sh t_z q.
Proof. rewrite strm_undef_cs. apply (@data_at_data_at_ Zlib.units.Inflate.CS). Qed.

(* a stream (live or not) gives back the local variable's memory *)
Lemma istream_to_undef gv vs z st:
  istream gv Tsh vs z st |-- @data_at_ CS Tsh t_z vs * TT.
Proof.
  unfold istream, zstrm_at, strm_rep. destruct st as [L | ]; Intros.
  - sep_apply strm_to_undef. cancel.
  - sep_apply strm_to_undef. cancel.
Qed.

(* the stream at the law's compspecs: its 14 fields *)
Definition ir_tup (gv: globals) (z: zfields) (sp: val) : strm_tuple :=
  (zf_ni z, (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), (zf_no z, (Vint (Int.repr (zf_ao z)),
   (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (sp, (gv Zlib.inflate.code._zcalloc,
   (gv Zlib.inflate.code._zcfree, (nullval, (Vint (Int.repr (zf_dt z)), (Vlong (Int64.repr (zf_adler z)),
   zf_res z))))))))))))).

Lemma ir_istream_unfold gv shs vs z L:
  istream gv shs vs z (Some L) =
  !! (zf_ok z /\ writable_share shs /\ live_ok L) &&
  (@data_at CS shs t_z (ir_tup gv z (l_sp L)) vs * state_mem gv vs L).
Proof.
  unfold istream, zstrm_at, strm_rep.
  rewrite strm_cs.
  apply pred_ext; entailer!.
Qed.

Lemma ir_istream_fold gv shs vs z L:
  zf_ok z -> writable_share shs -> live_ok L ->
  @data_at CS shs t_z (ir_tup gv z (l_sp L)) vs * state_mem gv vs L |-- istream gv shs vs z (Some L).
Proof. intros. rewrite ir_istream_unfold. entailer!. Qed.

Lemma ir_istream_opt gv shs (vs: val) z st: isptr vs -> istream_opt gv shs vs z st = istream gv shs vs z st.
Proof. intros P. unfold istream_opt. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma ir_is_live (vs: val) st: isptr vs -> is_live vs st = st.
Proof. intros P. unfold is_live. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

(* the 4 stores before an inflate() call (IRFacts.ir_call) *)
Lemma ir_tup_call gv z sp ni ai no ao:
  ir_tup gv (ir_call z ni ai no ao) sp =
  (ni, (Vint (Int.repr ai), (fst (snd (snd (ir_tup gv z sp))), (no, (Vint (Int.repr ao),
   snd (snd (snd (snd (snd (ir_tup gv z sp)))))))))).
Proof. reflexivity. Qed.

(* the call's input and output objects (non-null, the whole object, with their malloc tokens) *)
Definition ir_ib (p: val) (n: Z) (c: list val) : inbuf := InBuf Ews p 0 n c.
Definition ir_ob (p: val) (n: Z) (c: list val) : outbuf := OutBuf Ews p 0 n c.

Lemma ir_in_ptr p n c: isptr p -> in_ptr (ir_ib p n c) 0 = p.
Proof. intros P. destruct p; try contradiction. simpl. rewrite Ptrofs.add_zero. reflexivity. Qed.
Lemma ir_out_ptr p n c: isptr p -> out_ptr (ir_ob p n c) 0 = p.
Proof. intros P. destruct p; try contradiction. simpl. rewrite Ptrofs.add_zero. reflexivity. Qed.

(* the output object after a call that wrote ow (out_rep at offset 0) *)
Definition out_after (c: list val) (ow: list Z) (n: Z) : list val :=
  sublist 0 0 c ++ byte_vals ow ++ sublist (0 + Zlength ow) n c.

Lemma ir_bufs_pre L ip op ain aout (ci co: list val):
  Zlength co = aout ->
  @data_at CS Ews (tarray tuchar ain) ci ip * @malloc_token CS Ews (tarray tuchar ain) ip *
  @data_at CS Ews (tarray tuchar aout) co op * @malloc_token CS Ews (tarray tuchar aout) op
  |-- bufs_opt (Some L) (ir_ib ip ain ci) (Some (ir_ob op aout co)) [] true true.
Proof.
  intros Hc. unfold bufs_opt, ir_ib, ir_ob, in_rep, out_opt, out_rep, in_tok, out_tok.
  rewrite <- (bytes_inflate_cs Ews ain ci ip), <- (tok_inflate_cs Ews ain ip),
          <- (bytes_inflate_cs Ews aout co op), <- (tok_inflate_cs Ews aout op).
  assert (Eo: sublist 0 0 co ++ byte_vals [] ++ sublist (0 + Zlength (@nil Z)) aout co = co).
  { rewrite sublist_nil. simpl. rewrite sublist_same by lia. reflexivity. }
  rewrite Eo. cancel.
Qed.

Lemma ir_bufs_post L ip op ain aout (ci co: list val) (ow: list Z):
  bufs_opt (Some L) (ir_ib ip ain ci) (Some (ir_ob op aout co)) ow true true
  |-- @data_at CS Ews (tarray tuchar ain) ci ip * @malloc_token CS Ews (tarray tuchar ain) ip *
      @data_at CS Ews (tarray tuchar aout) (out_after co ow aout) op *
      @malloc_token CS Ews (tarray tuchar aout) op.
Proof.
  unfold bufs_opt, ir_ib, ir_ob, in_rep, out_opt, out_rep, in_tok, out_tok, out_after.
  rewrite (bytes_inflate_cs Ews ain ci ip), (tok_inflate_cs Ews ain ip), (tok_inflate_cs Ews aout op),
          (bytes_inflate_cs Ews aout _ op). cancel.
Qed.

(* the message literals: a.msg / b.msg are valid pointers (or NULL) for the comparisons *)
Lemma ir_mapsto_valid sh p: readable_share sh -> mapsto_ sh tschar p |-- valid_pointer p.
Proof.
  intros Hsh. unfold mapsto_, mapsto. destruct p; try apply FF_left.
  cbv beta iota zeta delta [access_mode type_is_volatile tschar]. rewrite if_true by auto. apply orp_left.
  - apply andp_left1. apply prop_left. intros X. inversion X.
  - apply andp_left2. apply exp_left. intros v2.
    replace (Vptr b i) with (Vptr b (Ptrofs.repr (Ptrofs.unsigned i + 0)))
      by (rewrite Z.add_0_r, Ptrofs.repr_unsigned; auto).
    pose proof (valid_pointer.address_mapsto_valid_pointer Mint8signed v2 sh b (Ptrofs.unsigned i) 0
             ltac:(pose proof (Ptrofs.unsigned_range i); simpl; lia) ltac:(simpl; lia)) as X.
    constructor. exact X.
Qed.

Lemma ir_msg_valid gv m: ir_msg_lits gv |-- valid_pointer (gv (msg_ident m)).
Proof.
  unfold ir_msg_lits. pose proof (ir_all_msgs_complete m) as Hm. induction ir_all_msgs as [ | a l IH].
  - inversion Hm.
  - simpl. destruct Hm as [<- | Hm].
    + apply sepcon_valid_pointer1. apply ir_mapsto_valid. auto with share.
    + apply sepcon_valid_pointer2. auto.
Qed.

Lemma ir_msg_ptr gv m: ir_msg_lits gv |-- !! isptr (gv (msg_ident m)).
Proof.
  unfold ir_msg_lits. pose proof (ir_all_msgs_complete m) as Hm. induction ir_all_msgs as [ | a l IH].
  - inversion Hm.
  - simpl. destruct Hm as [<- | Hm].
    + sep_apply (mapsto__local_facts Ers tschar (gv (msg_ident a))). entailer!.
    + sep_apply IH. entailer!.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Stream b before inflateInit2_(&b, w2), and right after it                                      *)

(* the fields stream_defaults(&b) leaves (msg, state undefined) *)
Definition rb_of (tin tout adl dt rs: Z) : rawf :=
  RF nullval (Vint (Int.repr 0)) (Vlong (Int64.repr tin)) nullval (Vint (Int.repr 0))
     (Vlong (Int64.repr tout)) (Vint (Int.repr dt)) (Vlong (Int64.repr adl)) (Vlong (Int64.repr rs)).

Definition rb_ok (rb: rawf) : Prop :=
  exists tin tout adl dt rs,
    0 <= tin <= Int64.max_unsigned /\ 0 <= tout <= Int64.max_unsigned /\ 0 <= adl <= Int64.max_unsigned /\
    Int.min_signed <= dt <= Int.max_signed /\ 0 <= rs <= Int64.max_unsigned /\ rb = rb_of tin tout adl dt rs.

Definition braw (gv: globals) (vb: val) (rb: rawf) : mpred :=
  raw_strm gv Tsh vb rb Vundef Vundef nullval nullval nullval.

(* the stream after a successful inflateInit2_ on rb_of tin tout adl dt rs *)
Definition z_init (adl rs: Z) (L: live) : zfields :=
  ZF nullval 0 0 nullval 0 0 None 0 (if i_wrap (l_s L) =? 0 then adl else Z.land (i_wrap (l_s L)) 1)
     (Vlong (Int64.repr rs)).

Lemma init_istream gv vs tin tout adl dt rs L:
  0 <= adl <= Int64.max_unsigned ->
  istream_raw gv Tsh vs (raw_after_init (rb_of tin tout adl dt rs) (l_s L)) L
  = istream gv Tsh vs (z_init adl rs L) (Some L).
Proof.
  intros A. unfold rb_of. rewrite <- istream_raw_istream.
  - unfold raw_after_init, z_init; simpl. f_equal. f_equal. destruct (i_wrap (l_s L) =? 0); reflexivity.
  - unfold zf_ok, z_init; simpl. split; [rep_lia | ]. split; [rep_lia | ]. split; [rep_lia | ].
    split; [rep_lia | ]. split; [rep_lia | ].
    destruct (i_wrap (l_s L) =? 0); [auto | ].
    assert (M: Z.land (i_wrap (l_s L)) 1 = i_wrap (l_s L) mod 2) by (apply (Z.land_ones _ 1); lia).
    rewrite M. pose proof (Z.mod_pos_bound (i_wrap (l_s L)) 2 ltac:(lia)). rep_lia.
  - reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The loop invariant                                                                            *)

Definition I1T : Type := Z -> list Z -> Z -> zfields -> live -> Prop.
Definition I2T : Type := Z -> list Z -> Z -> zfields -> live -> zfields -> live -> Prop.

(* the facts fixed before the loop: w = wbits (accepted by inflateInit2_), src (n = Zlength src bytes at
   srcp), rb (b's fields before its inflateInit2_) *)
Definition g_facts (I1: I1T) (I2: I2T) (w: Z) (srcp: val) (src: list Z) (rb: rawf) : Prop :=
  reset_facts I1 I2 /\ wbits_ok w = true /\ Int.min_signed <= w <= Int.max_signed /\
  Zlength src <= 2 ^ 24 /\ bytes_ok src /\ isptr srcp /\ rb_ok rb.

(* phase 1: I1 for a (w2 = w; zb, Lb unused); phase 2: I2 for a and b *)
Definition ph_inv (I1: I1T) (I2: I2T) (w: Z) (src: list Z) (ph pos w2: Z) (za: zfields) (La: live)
    (zb: zfields) (Lb: live) : Prop :=
  if ph =? 1 then w2 = w /\ I1 w src pos za La else ph = 2 /\ I2 w2 src pos za La zb Lb.

(* stream b: before its inflateInit2_ (phase 1), live (phase 2) *)
Definition bmem (gv: globals) (vb: val) (ph: Z) (rb: rawf) (zb: zfields) (Lb: live) : mpred :=
  if ph =? 1 then braw gv vb rb else istream gv Tsh vb zb (Some Lb).

(* at the loop head (and after the loop: brk_inv) *)
Definition inv_at (I1: I1T) (I2: I2T) (gv: globals) (va vb vsa vsb: val) (w: Z) (srcp: val) (src: list Z)
    (rb: rawf) (ph pos w2: Z) (za: zfields) (La: live) (zb: zfields) (Lb: live) : environ -> mpred :=
  PROP (ph_inv I1 I2 w src ph pos w2 za La zb Lb; 0 <= pos <= Zlength src;
        Int.min_signed <= w2 <= Int.max_signed)
  LOCAL (temp _wbits (Vint (Int.repr w)); temp _n (Vint (Int.repr (Zlength src))); temp _src srcp;
         temp _phase (Vint (Int.repr ph)); temp _w2 (Vint (Int.repr w2)); temp _pos (Vint (Int.repr pos));
         lvar _sb (tptr tuchar) vsb; lvar _sa (tptr tuchar) vsa; lvar _b t_z vb; lvar _a t_z va; gvars gv)
  SEP (istream gv Tsh va za (Some La); bmem gv vb ph rb zb Lb; mem_mgr gv; zfuncs gv; tables_rep Ers gv;
       crc_table_at Ers gv; version_lit gv; ir_hversion_lit gv; ir_msg_lits gv;
       malloc_token Ews (tarray tuchar (Zlength src)) srcp;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) srcp;
       data_at_ Tsh (tptr tuchar) vsa; data_at_ Tsh (tptr tuchar) vsb).

Definition loop_inv (I1: I1T) (I2: I2T) (gv: globals) (va vb vsa vsb: val) (w: Z) (srcp: val) (src: list Z)
    (rb: rawf) : environ -> mpred :=
  EX ph: Z, EX pos: Z, EX w2: Z, EX za: zfields, EX La: live, EX zb: zfields, EX Lb: live,
  inv_at I1 I2 gv va vb vsa vsb w srcp src rb ph pos w2 za La zb Lb.

(* after the loop: only `if (stop == 0) { if (phase == 2) break; ...}` leaves it, in phase 2 *)
Definition brk_inv (I1: I1T) (I2: I2T) (gv: globals) (va vb vsa vsb: val) (w: Z) (srcp: val) (src: list Z)
    (rb: rawf) : environ -> mpred :=
  EX pos: Z, EX w2: Z, EX za: zfields, EX La: live, EX zb: zfields, EX Lb: live,
  inv_at I1 I2 gv va vb vsa vsb w srcp src rb 2 pos w2 za La zb Lb.

(* the loop body (IRMainLoop.v) *)
Definition loop_stmt : Prop :=
  forall {Espec: OracleKind} I1 I2 gv va vb vsa vsb w srcp src rb ph pos w2 za La zb Lb,
  g_facts I1 I2 w srcp src rb ->
  semax Delta_m (inv_at I1 I2 gv va vb vsa vsb w srcp src rb ph pos w2 za La zb Lb)
    seg_loop
    (loop_nocontinue_ret_assert (loop_inv I1 I2 gv va vb vsa vsb w srcp src rb)
       (overridePost (brk_inv I1 I2 gv va vb vsa vsb w srcp src rb) POST_m)).

(* ---------------------------------------------------------------------------------------------- *)
(* Phase 2: b's inflate() call and the asserts (seg_ph2)                                          *)

(* Ghost values: ain = nlim - pos; the input objects iap (a's) and ibp (b's) hold src[pos .. pos + ain);
   the output objects oap (a's, its bytes bsa before a's call) and obp (b's, bytes bsb); qa, qb the snapshot
   objects in sa, sb (in Fr with the rest that the segment does not touch: src, the version literals,
   the snapshot objects); a's call: from (za, La) to (za', La') writing owa, returning ra. *)
Definition ph2_facts (I1: I1T) (I2: I2T) (w: Z) (srcp: val) (src: list Z) (rb: rawf) (va vb: val)
    (w2 pos aout flush stop how wsel ain: Z) (iap ibp oap obp: val) (bsa bsb: list Z)
    (za: zfields) (La: live) (zb: zfields) (Lb: live) (ra: Z) (za': zfields) (La': live) (owa: list Z) : Prop :=
  g_facts I1 I2 w srcp src rb /\
  I2 w2 src pos za La zb Lb /\ live_ok La /\ zf_ok za /\ live_ok Lb /\ zf_ok zb /\
  Int.min_signed <= w2 <= Int.max_signed /\
  0 <= pos /\ 0 <= ain /\ pos + ain <= Zlength src /\ 0 <= aout <= 2 ^ 20 /\
  Int.min_signed <= flush <= Int.max_signed /\ Int.min_signed <= wsel <= Int.max_signed /\
  0 <= stop <= 255 /\ 0 <= how <= 255 /\
  Zlength bsa = aout /\ is_bytes bsa /\ Zlength bsb = aout /\ is_bytes bsb /\
  isptr va /\ isptr vb /\ isptr iap /\ isptr ibp /\ isptr oap /\ isptr obp /\
  inflate_rel flush va
    (ir_call za (in_ptr (ir_ib iap ain (bytes_rep (sublist pos (pos + ain) src))) 0) ain
       (out_ptr (ir_ob oap aout (bytes_rep bsa)) 0) aout)
    (Some La) (ir_ib iap ain (bytes_rep (sublist pos (pos + ain) src))) (sublist pos (pos + ain) src)
    (Some (ir_ob oap aout (bytes_rep bsa))) ra za' (Some La') owa /\
  ra <> Z_MEM_ERROR.

Definition ph2_pre (gv: globals) (va vb vsa vsb: val) (w: Z) (srcp: val) (src: list Z)
    (w2 pos aout flush stop how wsel ain: Z) (iap ibp oap obp qa qb: val) (bsa bsb: list Z)
    (zb: zfields) (Lb: live) (ra: Z) (za': zfields) (La': live) (owa: list Z) (Fr: mpred)
    : environ -> mpred :=
  PROP ()
  LOCAL (temp _ra (Vint (Int.repr ra));
         temp _wbits (Vint (Int.repr w)); temp _n (Vint (Int.repr (Zlength src))); temp _src srcp;
         temp _phase (Vint (Int.repr 2)); temp _w2 (Vint (Int.repr w2)); temp _pos (Vint (Int.repr pos));
         temp _aout (Vint (Int.repr aout)); temp _flush (Vint (Int.repr flush));
         temp _wsel (Vint (Int.repr wsel)); temp _stop (Vint (Int.repr stop)); temp _how (Vint (Int.repr how));
         temp _ain (Vint (Int.repr ain)); temp _ia iap; temp _ib ibp; temp _oa oap; temp _ob obp;
         lvar _sb (tptr tuchar) vsb; lvar _sa (tptr tuchar) vsa; lvar _b t_z vb; lvar _a t_z va; gvars gv)
  SEP (istream gv Tsh va za' (Some La'); head_mem La'; istream gv Tsh vb zb (Some Lb);
       mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv; ir_msg_lits gv;
       data_at Ews (tarray tuchar ain) (bytes_rep (sublist pos (pos + ain) src)) iap;
       malloc_token Ews (tarray tuchar ain) iap;
       data_at Ews (tarray tuchar ain) (bytes_rep (sublist pos (pos + ain) src)) ibp;
       malloc_token Ews (tarray tuchar ain) ibp;
       data_at Ews (tarray tuchar aout) (out_after (bytes_rep bsa) owa aout) oap;
       malloc_token Ews (tarray tuchar aout) oap;
       data_at Ews (tarray tuchar aout) (bytes_rep bsb) obp; malloc_token Ews (tarray tuchar aout) obp;
       data_at Tsh (tptr tuchar) qa vsa; data_at Tsh (tptr tuchar) qb vsb; Fr).

(* after it: both streams after the call, I2 at the new position (pos + bytes consumed), the output objects
   any contents *)
Definition ph2_post (I2: I2T) (gv: globals) (va vb vsa vsb: val) (w: Z) (srcp: val) (src: list Z)
    (w2 pos aout flush stop how wsel ain: Z) (iap ibp oap obp qa qb: val)
    (za': zfields) (La': live) (Fr: mpred) : environ -> mpred :=
  EX zb': zfields, EX Lb': live, EX ca: list val, EX cb: list val,
  PROP (I2 w2 src (pos + (ain - zf_ai za'))%Z za' La' zb' Lb'; 0 <= zf_ai za' <= ain)
  LOCAL (temp _wbits (Vint (Int.repr w)); temp _n (Vint (Int.repr (Zlength src))); temp _src srcp;
         temp _phase (Vint (Int.repr 2)); temp _w2 (Vint (Int.repr w2)); temp _pos (Vint (Int.repr pos));
         temp _aout (Vint (Int.repr aout)); temp _flush (Vint (Int.repr flush));
         temp _wsel (Vint (Int.repr wsel)); temp _stop (Vint (Int.repr stop)); temp _how (Vint (Int.repr how));
         temp _ain (Vint (Int.repr ain)); temp _ia iap; temp _ib ibp; temp _oa oap; temp _ob obp;
         lvar _sb (tptr tuchar) vsb; lvar _sa (tptr tuchar) vsa; lvar _b t_z vb; lvar _a t_z va; gvars gv)
  SEP (istream gv Tsh va za' (Some La'); istream gv Tsh vb zb' (Some Lb');
       mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv; ir_msg_lits gv;
       data_at Ews (tarray tuchar ain) (bytes_rep (sublist pos (pos + ain) src)) iap;
       malloc_token Ews (tarray tuchar ain) iap;
       data_at Ews (tarray tuchar ain) (bytes_rep (sublist pos (pos + ain) src)) ibp;
       malloc_token Ews (tarray tuchar ain) ibp;
       data_at Ews (tarray tuchar aout) ca oap; malloc_token Ews (tarray tuchar aout) oap;
       data_at Ews (tarray tuchar aout) cb obp; malloc_token Ews (tarray tuchar aout) obp;
       data_at Tsh (tptr tuchar) qa vsa; data_at Tsh (tptr tuchar) qb vsb; Fr).

(* IRMainPh2.v *)
Definition ph2_stmt : Prop :=
  forall {Espec: OracleKind} I1 I2 gv va vb vsa vsb w srcp src rb w2 pos aout flush stop how wsel ain
         iap ibp oap obp qa qb bsa bsb za La zb Lb ra za' La' owa Fr,
  ph2_facts I1 I2 w srcp src rb va vb w2 pos aout flush stop how wsel ain iap ibp oap obp bsa bsb
    za La zb Lb ra za' La' owa ->
  semax Delta_m
    (ph2_pre gv va vb vsa vsb w srcp src w2 pos aout flush stop how wsel ain iap ibp oap obp qa qb bsa bsb
       zb Lb ra za' La' owa Fr)
    seg_ph2
    (overridePost
       (ph2_post I2 gv va vb vsa vsb w srcp src w2 pos aout flush stop how wsel ain iap ibp oap obp qa qb
          za' La' Fr)
       POST_m).

(* ---------------------------------------------------------------------------------------------- *)
(* The reset of a and the new stream b (seg_rst), from phase 1 to phase 2                         *)

Definition rst_pre (gv: globals) (va vb vsa vsb: val) (w: Z) (srcp: val) (src: list Z) (rb: rawf)
    (pos wsel how: Z) (za: zfields) (La: live) : environ -> mpred :=
  PROP ()
  LOCAL (temp _wbits (Vint (Int.repr w)); temp _n (Vint (Int.repr (Zlength src))); temp _src srcp;
         temp _phase (Vint (Int.repr 1)); temp _w2 (Vint (Int.repr w)); temp _pos (Vint (Int.repr pos));
         temp _wsel (Vint (Int.repr wsel)); temp _how (Vint (Int.repr how));
         lvar _sb (tptr tuchar) vsb; lvar _sa (tptr tuchar) vsa; lvar _b t_z vb; lvar _a t_z va; gvars gv)
  SEP (istream gv Tsh va za (Some La); braw gv vb rb; mem_mgr gv; zfuncs gv; tables_rep Ers gv;
       crc_table_at Ers gv; version_lit gv; ir_hversion_lit gv; ir_msg_lits gv;
       malloc_token Ews (tarray tuchar (Zlength src)) srcp;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) srcp;
       data_at_ Tsh (tptr tuchar) vsa; data_at_ Tsh (tptr tuchar) vsb).

(* IRMainRst.v *)
Definition rst_stmt : Prop :=
  forall {Espec: OracleKind} I1 I2 gv va vb vsa vsb w srcp src rb pos wsel how za La,
  g_facts I1 I2 w srcp src rb -> I1 w src pos za La -> 0 <= pos <= Zlength src ->
  Int.min_signed <= wsel <= Int.max_signed -> 0 <= how <= 255 -> isptr va -> isptr vb ->
  semax Delta_m (rst_pre gv va vb vsa vsb w srcp src rb pos wsel how za La)
    seg_rst
    (overridePost (loop_inv I1 I2 gv va vb vsa vsb w srcp src rb) POST_m).
