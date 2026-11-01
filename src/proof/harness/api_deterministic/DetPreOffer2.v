(* Law api_deterministic (data of any length): the loop body from the NULL test of the four objects to the
   nondet_u8 test when no object is NULL (DetKit2.det_pre_stmt's last part): offer the piece and the output space
   on both streams.  [M_at] is main's state before the NULL test; DetPreNull2.v and DetPreNullOut2.v prove the NULL
   cases, DetPre2.v the body up to the NULL test.  The body is cut into four files to keep each file's check short. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.deflate.DetFacts2.
Require Zlib.proof.deflate.DModel5.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_deterministic.DetCS2.
Require Import Zlib.proof.harness.api_deterministic.DetMainStmt2.
Require Import Zlib.proof.harness.api_deterministic.DetKit2.
Require Import Zlib.harness.api_deterministic.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.


(* VST's after_forward_call simplifies [remove_localdef_temp i L] with [simpl], which takes minutes when the
   identifiers are built by $"name" (here out_second); the same list built syntactically, comparing the
   identifiers by vm_compute *)
Ltac rlt_list i L :=
  lazymatch L with
  | temp ?j ?v :: ?L' =>
      let r := rlt_list i L' in
      let b := eval vm_compute in (Pos.eqb i j) in
      lazymatch b with true => r | false => constr:(temp j v :: r) end
  | ?d :: ?L' => let r := rlt_list i L' in constr:(d :: r)
  | nil => constr:(@nil localdef)
  end.
Local Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u' := rlt_list i L in change (remove_localdef_temp i L) with u' end.


(* a branch of an if whose condition is known: its hypothesis is false *)
Ltac det_false :=
  first [ contradiction | discriminate
        | match goal with H : _ <> _ |- _ => contradiction H; reflexivity end ].

(* A stream between iterations as offer's precondition (the whole z_stream at the compress unit's compspecs),
   the rest of its state kept as a wand, and the other half of main's local *)
Lemma det_offer_open (p : val) (s : dstate) (sp : val) (tin tout : Z) (msgv : val) (adler : Z) (gv : globals) :
  shead p s sp tin tout msgv adler gv |--
  EX nin : val, EX ain : Z, EX nout : val, EX aout : Z,
    !! (u64_ok tin /\ u64_ok tout /\ u64_ok adler) &&
    (@data_at Zlib.units.Compress.CS Ews t_zs
       (zs_val nin (vi ain) (vl tin) nout (vi aout) (vl tout) msgv sp (gv DC._zcalloc) (gv DC._zcfree) nullval
          (det_dt s) (vl adler) Vundef) p *
     (strm_own_live p sp gv s -* dstream_sp 2 (Some s) p nullval sp gv) *
     data_at_ BoundKit.Ecomp t_strm p).
Proof.
  unfold shead, strm_at. Intros nin ain nout aout. Exists nin ain nout aout.
  sep_apply (det_dstream_open s p nullval sp gv). unfold api_fields. Intros.
  rewrite prop_true_andp by (unfold u32_ok, u64_ok in *; tauto).
  eapply derives_trans;
    [| apply sepcon_derives;
       [apply sepcon_derives;
          [apply (det_offer_pre p nin (vi ain) (vl tin) nout (vi aout) (vl tout) msgv (vl adler) sp
                    (gv DC._zcalloc) (gv DC._zcfree) nullval (det_dt s)) | apply derives_refl] |
        apply derives_refl]].
  unfold reset_fields, strm_own_live. cancel.
Qed.

(* offer's postcondition back to a live stream with the offered buffers ([za], [zf]: the allocator's
   function pointers, named so that entailer does not meet [gv] applied to them) *)
Lemma det_offer_close (p : val) (s : dstate) (sp nin : val) (ain tin : Z) (nout : val) (aout tout : Z)
    (msgv : val) (adler : Z) (gv : globals) (za zf : val) :
  za = gv DC._zcalloc -> zf = gv DC._zcfree ->
  u32_ok ain -> u64_ok tin -> u32_ok aout -> u64_ok tout -> u64_ok adler ->
  @data_at Zlib.units.Compress.CS Ews t_zs
    (zs_val nin (vi ain) (vl tin) nout (vi aout) (vl tout) msgv sp za zf nullval
       (det_dt s) (vl adler) Vundef) p *
  (strm_own_live p sp gv s -* dstream_sp 2 (Some s) p nullval sp gv) * data_at_ BoundKit.Ecomp t_strm p
  |-- strm_at p s sp nin ain tin nout aout tout msgv adler gv.
Proof.
  intros -> -> **. sep_apply (det_offer_post p nin ain nout aout tin tout adler msgv sp (gv DC._zcalloc) (gv DC._zcfree)
                       nullval (det_dt s)); auto.
  fold (strm_own_live p sp gv s).
  unfold strm_at. sep_apply (det_dstream_close s p nullval sp gv). cancel.
Qed.

(* malloc's new object of [room] bytes is an output space with nothing written *)
Lemma det_out0 (room : Z) (q : val) :
  0 <= room -> data_at_ Ews (tarray tuchar room) q = data_at Ews (tarray tuchar room) (out_vals room []) q.
Proof. intros. unfold data_at_, out_vals. simpl. rewrite Z.sub_0_r. reflexivity. Qed.

(* (tbool) (p == NULL) is 0 for a malloc'd p *)
Ltac det_nonnull :=
  match goal with |- context [sem_cmp_pp Ceq ?p _] =>
    destruct p; try contradiction;
    match goal with H : malloc_compatible _ _ |- _ => simpl in H; try contradiction end;
    reflexivity
  end.

(* return 0 after a failed allocation: both streams back to main's locals, everything else dropped *)
Ltac det_ret :=
  forward; Exists (Int.repr 0); entailer!;
  repeat match goal with |- context [shead ?p ?s ?sp ?ti ?to ?m ?a ?g] =>
    sep_apply (det_shead_back p s sp ti to m a g) end;
  cancel.


(* main's state after the two copies of the piece and the two calls of malloc: the next [offered] and flush,
   take = clip(offered - read), the output space [room], the four objects of malloc (each maybe NULL) *)
Definition M_at (J : det_inv) (n : Z) (data : list Z) (datap v1 v2 sp1 sp2 : val) (gv : globals) (ls : lstate)
    (off fl room : Z) (in1 in2 out1 out2 : val) : environ -> mpred :=
  PROP (J_ok J n data datap ls; ls_read ls <= off <= n; 0 <= fl <= 5;
        fl = 4 -> off = n /\ n - ls_read ls <= 4294967295; ls_fin ls <> None -> fl = 4; 0 <= room <= 4294967295)
  LOCAL (temp _data datap; temp _data_len (vl n); temp _offered (vl off); temp _read (vl (ls_read ls));
         temp _flush (vi fl); temp _take (vl (Z.min (off - ls_read ls) 4294967295)); temp _room (vl room);
         temp _in_first in1; temp _in_second in2; temp _out_first out1; temp _out_second out2;
         lvar _first t_strm v1; lvar _second t_strm v2; gvars gv)
  SEP (mem_mgr gv; deflate_globals gv; data_at Ews (tarray tuchar n) (map vi data) datap;
       if eq_dec in1 nullval then emp
       else malloc_token Ews (tarray tuchar (Z.min (off - ls_read ls) 4294967295)) in1 *
            data_at Ews (tarray tuchar (Z.min (off - ls_read ls) 4294967295))
              (bytes_rep (sublist (ls_read ls) (ls_read ls + Z.min (off - ls_read ls) 4294967295) data)) in1;
       if eq_dec in2 nullval then emp
       else malloc_token Ews (tarray tuchar (Z.min (off - ls_read ls) 4294967295)) in2 *
            data_at Ews (tarray tuchar (Z.min (off - ls_read ls) 4294967295))
              (bytes_rep (sublist (ls_read ls) (ls_read ls + Z.min (off - ls_read ls) 4294967295) data)) in2;
       if eq_dec out1 nullval then emp
       else malloc_token Ews (tarray tuchar room) out1 * data_at_ Ews (tarray tuchar room) out1;
       if eq_dec out2 nullval then emp
       else malloc_token Ews (tarray tuchar room) out2 * data_at_ Ews (tarray tuchar room) out2;
       shead v1 (ls_s ls) sp1 (ls_read ls) (ls_tout ls) (ls_msgv1 ls) (ls_adler ls) gv;
       shead v2 (ls_s ls) sp2 (ls_read ls) (ls_tout ls) (ls_msgv2 ls) (ls_adler ls) gv; TT).

(* the loop body from the NULL test on (statement 7, DetKit2.v) *)
Definition lsuf7 : statement := ltac:(get_lsuf 7%nat).

(* no object is NULL: the test falls through and the two offers lead to [C_at] *)
Lemma det_pre_ok {Espec : OracleKind} J n data datap v1 v2 sp1 sp2 gv ls off fl room in1 in2 out1 out2 :
  in1 <> nullval -> in2 <> nullval -> out1 <> nullval -> out2 <> nullval ->
  (forall ci, semax Delta_m (C_at J n data datap v1 v2 sp1 sp2 gv ls ci (c0 ls)) lsuf10
                (Rbody J n data datap v1 v2 sp1 sp2 gv)) ->
  semax Delta_m (M_at J n data datap v1 v2 sp1 sp2 gv ls off fl room in1 in2 out1 out2) lsuf7
    (Rbody J n data datap v1 v2 sp1 sp2 gv).
Proof.
  intros E1 E2 E3 E4 HC.
  unfold M_at, J_ok, setup_ok. Intros.
  unfold lsuf7, Rbody, loop1_ret_assert, POST_m, overridePost, frame_ret_assert. cbv beta iota.
  set (tk := Z.min (off - ls_read ls) 4294967295) in *.
  assert (Htk0 : 0 <= tk <= 4294967295) by (unfold tk; rep_lia).
  abbreviate_semax.
  (* the NULL test needs only the four objects: the rest is frozen *)
  freeze FR := (mem_mgr gv) (deflate_globals gv) (data_at Ews _ _ datap) (shead v1 _ _ _ _ _ _ _)
                 (shead v2 _ _ _ _ _ _ _) TT.
  destruct (eq_dec in1 nullval); [contradiction | ]. destruct (eq_dec in2 nullval); [contradiction | ].
  destruct (eq_dec out1 nullval); [contradiction | ]. destruct (eq_dec out2 nullval); [contradiction | ].
  Intros.
  forward_if (temp _t'21 (vi 0)); [ det_false | | ]. { forward. entailer!. det_nonnull. }
  forward_if (temp _t'22 (vi 0)); [ det_false | | ]. { forward. entailer!. det_nonnull. }
  forward_if (temp _t'23 (vi 0)); [ det_false | | ]. { forward. entailer!. det_nonnull. }
  match goal with |- semax _ ?P _ _ => apply semax_seq with (Q := P) end.
  { forward_if; [ det_false | ]. forward. entailer!. }
  thaw FR.
  (* the two offers lead to C_at; the rest of the body is the hypothesis *)
  unfold abbreviate in MORE_COMMANDS; subst MORE_COMMANDS.
  rewrite seq_assoc.
  eapply semax_seq'; [| apply (HC (mkCI off fl room in1 in2 out1 out2)) ].
  abbreviate_semax.
  sep_apply (det_offer_open v1 (ls_s ls) sp1 (ls_read ls) (ls_tout ls) (ls_msgv1 ls) (ls_adler ls) gv).
  Intros nin1 ain1 nout1 aout1.
  remember (gv DC._zcalloc) as zca. remember (gv DC._zcfree) as zcf.
  sep_apply (det_offer_open v2 (ls_s ls) sp2 (ls_read ls) (ls_tout ls) (ls_msgv2 ls) (ls_adler ls) gv).
  Intros nin2 ain2 nout2 aout2. rewrite <- Heqzca, <- Heqzcf.
  forward_call (v1, Ews, in1, tk, out1, room, nin1, vi ain1, vl (ls_read ls), nout1, vi aout1,
                vl (ls_tout ls), ls_msgv1 ls, sp1, zca, zcf, nullval, det_dt (ls_s ls),
                vl (ls_adler ls), Vundef).
  forward_call (v2, Ews, in2, tk, out2, room, nin2, vi ain2, vl (ls_read ls), nout2, vi aout2,
                vl (ls_tout ls), ls_msgv2 ls, sp2, zca, zcf, nullval, det_dt (ls_s ls),
                vl (ls_adler ls), Vundef).
  assert (Hut : u32_ok tk) by (unfold u32_ok; rep_lia).
  assert (Hur : u32_ok room) by (unfold u32_ok; rep_lia).
  sep_apply (det_offer_close v1 (ls_s ls) sp1 in1 tk (ls_read ls) out1 room (ls_tout ls)
               (ls_msgv1 ls) (ls_adler ls) gv zca zcf Heqzca Heqzcf Hut ltac:(assumption) Hur ltac:(assumption)
               ltac:(assumption)).
  sep_apply (det_offer_close v2 (ls_s ls) sp2 in2 tk (ls_read ls) out2 room (ls_tout ls)
               (ls_msgv2 ls) (ls_adler ls) gv zca zcf Heqzca Heqzcf Hut ltac:(assumption) Hur ltac:(assumption)
               ltac:(assumption)).
  assert_PROP (isptr in1 /\ isptr in2 /\ isptr out1 /\ isptr out2) as Hptr.
  { entailer!. }
  destruct Hptr as [Pi1 [Pi2 [Po1 Po2]]].
  unfold C_at, C_sep, B_loc, c0, ci_inb, ci_take, out_at, BoundKit.obj.
  cbn [ci_offered ci_flush ci_room ci_in1 ci_in2 ci_out1 ci_out2 cs_s cs_fin cs_nin cs_out cs_tout cs_adler cs_msg
       cs_msgv1 cs_msgv2].
  change (Z.min (off - ls_read ls) 4294967295) with tk.
  rewrite !isptr_offset_val_zero by auto. rewrite Zlength_nil, !Z.sub_0_r, !Z.add_0_r.
  rewrite <- !det_out0 by lia.
  rewrite Zlength_sublist by (unfold tk in *; lia). rewrite Z.add_simpl_l.
  change (bytes_rep (sublist (ls_read ls) (ls_read ls + tk) data))
    with (map vi (sublist (ls_read ls) (ls_read ls + tk) data)).
  entailer!.
  set (tk := Z.min (off - ls_read ls) 4294967295) in *.
  split; [| split].
  - unfold J_ok, setup_ok. tauto.
  - unfold ci_ok. cbn. repeat split; auto; lia.
  - unfold cs_ok, ci_take, ci_inb. cbn. change (Z.min (off - ls_read ls) 4294967295) with tk. rewrite Z.add_0_r.
    split; [exact H3 |]. split; [exact H4 |]. split; [lia |]. split; [simpl; lia |].
    split; [constructor |]. split; [| tauto].
    (* after Z_FINISH the piece is the whole rest of the data *)
    intros R HR. rewrite HR in H8. destruct H8 as [Hf [Ho [HRe Hr]]].
    assert (Hfl : fl = 4) by (apply H15; congruence).
    destruct (H14 Hfl) as [Hoff _]. split; [exact Hfl |].
    unfold ci_take; cbn [ci_offered]. change (Z.min (off - ls_read ls) 4294967295) with tk.
    assert (Etk' : ls_read ls + tk = Zlength data) by (unfold tk; rep_lia).
    rewrite Etk', HRe. symmetry; apply firstn_all2. rewrite <- ZtoNat_Zlength, Zlength_sublist by lia. lia.
Qed.
