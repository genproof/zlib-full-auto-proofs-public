(* Law rt_session (harness/rt_session.c), main's statements 24-46 (SMKit.segA2_stmt, proved in SMSegA2.v): the kit
   of the proof, as rt_gzip_header's G2MS1Kit.v (the same statements on head and got, other temporaries).

   Every store into head or got and every load from them costs seconds at the law's compspecs, so the segment is
   cut into groups of statements, each proved in its own file (SMA2*.v) from one named state to the next:
     statements 24-30  the copies dict_copy, extra_copy, name_copy, comment_copy, expected (copy_of), compressed
                       and out (malloc)                                         A24 u -> QC u ..
     statements 31-38  head's fields                                            QC -> QH h -> .. -> QH (hvals u)
     statements 39-44  got's buffers (malloc) and sizes                         QG w objs -> .. -> NS u' []
     statement 45      `if (!dict_copy || .. || !out) return 0;`: one operand at a time (temporaries _t'41 ..
                       _t'46, each by the cases of the previous temporary and of the pointer tested), then the
                       test (return 0, or NS u' [] when f46 u' = false)
     statement 46      `if (!got.extra || !got.name || !got.comment) return 0;` (temporaries _t'47, _t'48), then
                       the test (return 0, or A47 u').
   The values main draws and the objects of A24 are the setup u; the setup u' of A47 is u with the pointers malloc
   and copy_of returned ([withp]).  Until their NULL tests the new objects are [obj0] / [new0]: NULL, or the
   object. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SDFacts.
Require Import Zlib.proof.harness.rt_session.SIFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers; each identifier comparison is decided by vm_compute instead. *)
Ltac a2_rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in a2_rlt_fix u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := a2_rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

(** ** The statements *)

Ltac a2_get e := let x := eval cbv beta iota zeta delta [take suf segA2] in e in exact x.

Definition S24 : statement := ltac:(a2_get (take 1 (suf 0 segA2))).
Definition S25 : statement := ltac:(a2_get (take 1 (suf 1 segA2))).
Definition S26 : statement := ltac:(a2_get (take 1 (suf 2 segA2))).
Definition S27 : statement := ltac:(a2_get (take 1 (suf 3 segA2))).
Definition S28 : statement := ltac:(a2_get (take 1 (suf 4 segA2))).
Definition S29 : statement := ltac:(a2_get (take 1 (suf 5 segA2))).
Definition S30 : statement := ltac:(a2_get (take 1 (suf 6 segA2))).
Definition S31 : statement := ltac:(a2_get (take 1 (suf 7 segA2))).
Definition S32 : statement := ltac:(a2_get (take 1 (suf 8 segA2))).
Definition S33 : statement := ltac:(a2_get (take 1 (suf 9 segA2))).
Definition S34 : statement := ltac:(a2_get (take 1 (suf 10 segA2))).
Definition S35 : statement := ltac:(a2_get (take 1 (suf 11 segA2))).
Definition S36 : statement := ltac:(a2_get (take 1 (suf 12 segA2))).
Definition S37 : statement := ltac:(a2_get (take 1 (suf 13 segA2))).
Definition S38 : statement := ltac:(a2_get (take 1 (suf 14 segA2))).
Definition S39 : statement := ltac:(a2_get (take 1 (suf 15 segA2))).
Definition S40 : statement := ltac:(a2_get (take 1 (suf 16 segA2))).
Definition S41 : statement := ltac:(a2_get (take 1 (suf 17 segA2))).
Definition S42 : statement := ltac:(a2_get (take 1 (suf 18 segA2))).
Definition S43 : statement := ltac:(a2_get (take 1 (suf 19 segA2))).
Definition S44 : statement := ltac:(a2_get (take 1 (suf 20 segA2))).
Definition S45 : statement := ltac:(a2_get (take 1 (suf 21 segA2))).
Definition S46 : statement := ltac:(a2_get (suf 22 segA2)).

Lemma segA2_split : segA2 =
  Ssequence S24 (Ssequence S25 (Ssequence S26 (Ssequence S27 (Ssequence S28 (Ssequence S29 (Ssequence S30
  (Ssequence S31 (Ssequence S32 (Ssequence S33 (Ssequence S34 (Ssequence S35 (Ssequence S36 (Ssequence S37
  (Ssequence S38 (Ssequence S39 (Ssequence S40 (Ssequence S41 (Ssequence S42 (Ssequence S43 (Ssequence S44
  (Ssequence S45 S46))))))))))))))))))))).
Proof. reflexivity. Qed.

(* statement 45: the operands setting _t'41 .. _t'46, then the test *)
Definition I41 : statement := ltac:(let x := eval cbv [S45] in
  (match S45 with Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence a _) _) _) _) _) _ => a
   | _ => Sskip end) in exact x).
Definition I42 : statement := ltac:(let x := eval cbv [S45] in
  (match S45 with Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence _ a) _) _) _) _) _ => a
   | _ => Sskip end) in exact x).
Definition I43 : statement := ltac:(let x := eval cbv [S45] in
  (match S45 with Ssequence (Ssequence (Ssequence (Ssequence (Ssequence _ a) _) _) _) _ => a
   | _ => Sskip end) in exact x).
Definition I44 : statement := ltac:(let x := eval cbv [S45] in
  (match S45 with Ssequence (Ssequence (Ssequence (Ssequence _ a) _) _) _ => a | _ => Sskip end) in exact x).
Definition I45 : statement := ltac:(let x := eval cbv [S45] in
  (match S45 with Ssequence (Ssequence (Ssequence _ a) _) _ => a | _ => Sskip end) in exact x).
Definition I46 : statement := ltac:(let x := eval cbv [S45] in
  (match S45 with Ssequence (Ssequence _ a) _ => a | _ => Sskip end) in exact x).
Definition Iret : statement := ltac:(let x := eval cbv [S45] in
  (match S45 with Ssequence _ a => a | _ => Sskip end) in exact x).

Lemma S45_split : S45 =
  Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence I41 I42) I43) I44) I45) I46) Iret.
Proof. reflexivity. Qed.

(* statement 46: the operands setting _t'47 and _t'48, then the test *)
Definition J47 : statement := ltac:(let x := eval cbv [S46] in
  (match S46 with Ssequence (Ssequence a _) _ => a | _ => Sskip end) in exact x).
Definition J48 : statement := ltac:(let x := eval cbv [S46] in
  (match S46 with Ssequence (Ssequence _ a) _ => a | _ => Sskip end) in exact x).
Definition Jret : statement := ltac:(let x := eval cbv [S46] in
  (match S46 with Ssequence _ a => a | _ => Sskip end) in exact x).

Lemma S46_split : S46 = Ssequence (Ssequence J47 J48) Jret.
Proof. reflexivity. Qed.

(** ** Head, got and the new objects *)

(* head or got with the fields text, time, os, extra, extra_len, name, comment, hcrc (head's stores) *)
Definition hv (t tm os xp xl np cp hc : val) : reptype t_g :=
  (t, (tm, (Vundef, (os, (xp, (xl, (Vundef, (np, (Vundef, (cp, (Vundef, (hc, Vundef)))))))))))).
(* got with its buffers and their sizes *)
Definition gw (gxp gxm gnp gnm gcp gcm : val) : reptype t_g :=
  (Vundef, (Vundef, (Vundef, (Vundef, (gxp, (Vundef, (gxm, (gnp, (gnm, (gcp, (gcm, (Vundef, Vundef)))))))))))).

Definition U : val := Vundef.
(* head or got before any store *)
Definition h00 : reptype t_g := gw U U U U U U.

Lemma data_at_g p : data_at_ Tsh t_g p = data_at Tsh t_g h00 p.
Proof. reflexivity. Qed.

(* head after its scalar fields (statements 31-34) *)
Definition h2 (u : setup) : reptype t_g :=
  hv (vi (su_text u)) (vl (su_time u)) (vi (su_os u)) U U U U (vi (su_hcrc u)).

Lemma hvals_hv u : hvals u = hv (vi (su_text u)) (vl (su_time u)) (vi (su_os u)) (selp u 2 (su_xp u))
  (vi (Zlength (su_xf u))) (selp u 4 (su_np u)) (selp u 8 (su_cmp u)) (vi (su_hcrc u)).
Proof. reflexivity. Qed.

Lemma gval_gw u : gval u = gw (su_gxp u) (vi (Zlength (su_xf u))) (su_gnp u) (vi (Zlength (su_nm u) + 1))
  (su_gcp u) (vi (Zlength (su_cm u) + 1)).
Proof. reflexivity. Qed.

(* the object copy_of gives (NULL, or the bytes l); the object malloc gives (NULL, or n bytes never written) *)
Definition obj0 (q : val) (l : list Z) : mpred := if eq_dec q nullval then emp else bobj q l.
Definition new0 (q : val) (n : Z) : mpred := if eq_dec q nullval then emp else cnew q n.

(* u with the pointers of statements 24-44 *)
Definition withp (u : setup) (dcp xcp ncp ccp ep cp op gxp gnp gcp : val) : setup :=
  mkSU (su_level u) (su_wbits u) (su_mem u) (su_strategy u) (su_choice u) (su_dict u) (su_xf u) (su_nm u)
    (su_cm u) (su_data u) (su_cap u) (su_text u) (su_time u) (su_os u) (su_hcrc u) (su_dictp u) (su_xp u)
    (su_np u) (su_cmp u) (su_dp u) dcp xcp ncp ccp ep cp op gxp gnp gcp.

(* withp changes only pointers: the facts of the draws, head, with_dict and with_head are u's *)
Lemma su_dok_withp u dcp xcp ncp ccp ep cp op gxp gnp gcp :
  su_dok (withp u dcp xcp ncp ccp ep cp op gxp gnp gcp) = su_dok u.
Proof. reflexivity. Qed.

Lemma hvals_withp u dcp xcp ncp ccp ep cp op gxp gnp gcp :
  hvals (mkSU (su_level u) (su_wbits u) (su_mem u) (su_strategy u) (su_choice u) (su_dict u) (su_xf u) (su_nm u)
    (su_cm u) (su_data u) (su_cap u) (su_text u) (su_time u) (su_os u) (su_hcrc u) (su_dictp u) (su_xp u)
    (su_np u) (su_cmp u) (su_dp u) dcp xcp ncp ccp ep cp op gxp gnp gcp) = hvals u.
Proof. reflexivity. Qed.

Lemma with_dict_withp u dcp xcp ncp ccp ep cp op gxp gnp gcp :
  with_dict (mkSU (su_level u) (su_wbits u) (su_mem u) (su_strategy u) (su_choice u) (su_dict u) (su_xf u)
    (su_nm u) (su_cm u) (su_data u) (su_cap u) (su_text u) (su_time u) (su_os u) (su_hcrc u) (su_dictp u) (su_xp u)
    (su_np u) (su_cmp u) (su_dp u) dcp xcp ncp ccp ep cp op gxp gnp gcp) = with_dict u.
Proof. reflexivity. Qed.

Lemma with_head_withp u dcp xcp ncp ccp ep cp op gxp gnp gcp :
  with_head (mkSU (su_level u) (su_wbits u) (su_mem u) (su_strategy u) (su_choice u) (su_dict u) (su_xf u)
    (su_nm u) (su_cm u) (su_data u) (su_cap u) (su_text u) (su_time u) (su_os u) (su_hcrc u) (su_dictp u) (su_xp u)
    (su_np u) (su_cmp u) (su_dp u) dcp xcp ncp ccp ep cp op gxp gnp gcp) = with_head u.
Proof. reflexivity. Qed.

(* the value of a test: 1 when b, else 0; [nb q]: q is NULL *)
Definition vb (b : bool) : val := Vint (if b then Int.one else Int.zero).
Definition nb (q : val) : bool := if eq_dec q nullval then true else false.

(* the temporaries _t'41 .. _t'46 of statement 45: one of the first two, three, .. seven objects tested is NULL *)
Definition f41 (u : setup) : bool := nb (su_dcp u) || nb (su_xcp u).
Definition f42 (u : setup) : bool := f41 u || nb (su_ncp u).
Definition f43 (u : setup) : bool := f42 u || nb (su_ccp u).
Definition f44 (u : setup) : bool := f43 u || nb (su_ep u).
Definition f45 (u : setup) : bool := f44 u || nb (su_cp u).
Definition f46 (u : setup) : bool := f45 u || nb (su_op u).
(* the temporaries _t'47, _t'48 of statement 46: one of got's first two, three buffers is NULL *)
Definition f47 (u : setup) : bool := nb (su_gxp u) || nb (su_gnp u).
Definition f48 (u : setup) : bool := f47 u || nb (su_gcp u).

Section States.
Context (gv : globals) (vh vg vc va vd : val).

(* the five locals and A24's objects *)
Definition base (u : setup) : list mpred :=
  [data_at_ Tsh t_z vc; data_at_ Tsh t_z vd; data_at_ Tsh t_p va; mem_mgr gv; Rm gv; dictobj u;
   bobj (su_xp u) (su_xf u); bobj (su_np u) (su_nm u ++ [0]); bobj (su_cmp u) (su_cm u ++ [0]); datobj u].

(* main's state with the setup u, the temporaries L, head h, got w and the new objects objs *)
Definition Qs (u : setup) (L : list localdef) (h w : reptype t_g) (objs : list mpred) : environ -> mpred :=
  PROPx [su_dok u]
  (LOCALx (L ++ o_locals u ++ d_locals u (su_wbits u) ++ lvs gv vh vg vc va vd)
  (SEPx (data_at Tsh t_g h vh :: data_at Tsh t_g w vg :: base u ++ objs))).

(* the temporaries of statements 24-30 *)
Definition ctemps (dcp xcp ncp ccp ep cp op : val) : list localdef :=
  [temp _dict_copy dcp; temp _extra_copy xcp; temp _name_copy ncp; temp _comment_copy ccp; temp _expected ep;
   temp _compressed cp; temp _out op].

(* the objects of statements 24-30 *)
Definition cobjs (u : setup) (dcp xcp ncp ccp ep cp op : val) : list mpred :=
  [obj0 dcp (su_dict u); obj0 xcp (su_xf u); obj0 ncp (su_nm u ++ [0]); obj0 ccp (su_cm u ++ [0]);
   obj0 ep (su_data u); new0 cp (su_cap u); new0 op (Zlength (su_data u))].

(* statements 31-38: the objects of statements 24-30, head h *)
Definition QH (u : setup) (dcp xcp ncp ccp ep cp op : val) (h : reptype t_g) : environ -> mpred :=
  Qs u (ctemps dcp xcp ncp ccp ep cp op) h h00 (cobjs u dcp xcp ncp ccp ep cp op).

(* statements 39-44: head's fields stored, got w, malloc's objects objs *)
Definition QG (u : setup) (dcp xcp ncp ccp ep cp op : val) (w : reptype t_g) (objs : list mpred)
    : environ -> mpred :=
  Qs u (ctemps dcp xcp ncp ccp ep cp op) (hvals u) w (cobjs u dcp xcp ncp ccp ep cp op ++ objs).

(* after statement 44: every pointer in u (the ten new ones possibly NULL), the temporaries L of statements 45
   and 46 *)
Definition NS (u : setup) (L : list localdef) : environ -> mpred :=
  PROPx [su_dok u]
  (LOCALx (L ++ c_locals u ++ o_locals u ++ d_locals u (su_wbits u) ++ lvs gv vh vg vc va vd)
  (SEPx (data_at Tsh t_g (hvals u) vh :: data_at Tsh t_g (gval u) vg :: base u ++
         cobjs u (su_dcp u) (su_xcp u) (su_ncp u) (su_ccp u) (su_ep u) (su_cp u) (su_op u) ++
         [new0 (su_gxp u) (Zlength (su_xf u)); new0 (su_gnp u) (Zlength (su_nm u) + 1);
          new0 (su_gcp u) (Zlength (su_cm u) + 1)]))).
End States.

(** ** The objects *)

Lemma bobj_isptr q l : bobj q l |-- !! isptr q.
Proof.
  unfold bobj. entailer!;
    match goal with Hf : field_compatible _ _ _ |- _ => exact (field_compatible_isptr _ _ _ Hf) end.
Qed.

Lemma cnew_isptr q n : cnew q n |-- !! isptr q.
Proof.
  unfold cnew. entailer!;
    match goal with Hf : field_compatible _ _ _ |- _ => exact (field_compatible_isptr _ _ _ Hf) end.
Qed.

Lemma obj0_bobj q l : q <> nullval -> obj0 q l = bobj q l.
Proof. intros Hq. unfold obj0. rewrite if_false by exact Hq. reflexivity. Qed.

Lemma new0_cnew q n : q <> nullval -> new0 q n = cnew q n.
Proof. intros Hq. unfold new0. rewrite if_false by exact Hq. reflexivity. Qed.

Lemma obj0_null l : obj0 nullval l = emp.
Proof. reflexivity. Qed.

Lemma new0_null n : new0 nullval n = emp.
Proof. reflexivity. Qed.

Lemma nb_false q : nb q = false -> q <> nullval.
Proof. unfold nb. destruct (eq_dec q nullval); congruence. Qed.

(* a malloc'ed object (any size, also 0) can be compared with NULL *)
Lemma bobj_test_eq P q l : P |-- bobj q l * TT -> P |-- denote_tc_test_eq q (Vlong Int64.zero).
Proof.
  intros HP. apply (malloc_test_eq P (Zlength l) q ltac:(apply Zlength_nonneg)).
  eapply derives_trans; [exact HP | ]. unfold bobj. cancel.
Qed.

Lemma cnew_test_eq P n q : 0 <= n -> P |-- cnew q n * TT -> P |-- denote_tc_test_eq q (Vlong Int64.zero).
Proof.
  intros Hn HP. apply (malloc_test_eq P n q Hn).
  eapply derives_trans; [exact HP | ]. unfold cnew. cancel.
Qed.

(* copy_of gives its object at the compspecs of laws_common.h *)
Lemma a2_bytes_cs sh n (v : list val) q :
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at SCS.CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.

Lemma a2_tok_cs sh n q :
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) q = @malloc_token SCS.CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_adler32). reflexivity. Qed.

Lemma bobj_cs q l n : Zlength l = n ->
  bobj q l = @malloc_token Zlib.units.Adler32.CS Ews (tarray tuchar n) q *
             @data_at Zlib.units.Adler32.CS Ews (tarray tuchar n) (map vi l) q.
Proof. intros <-. unfold bobj. rewrite a2_bytes_cs, a2_tok_cs. reflexivity. Qed.

(* copy_of's result is obj0 *)
Lemma obj0_of_copy q l n : Zlength l = n ->
  (if eq_dec q nullval then emp
   else @malloc_token Zlib.units.Adler32.CS Ews (tarray tuchar n) q *
        @data_at Zlib.units.Adler32.CS Ews (tarray tuchar n) (bytes_rep l) q) = obj0 q l.
Proof.
  intros Hn. unfold obj0. destruct (eq_dec q nullval); [reflexivity |].
  rewrite (bobj_cs q l n Hn). reflexivity.
Qed.

(* the source of copy_of: an object of the n bytes l, from its start *)
Lemma bobj_cbuf q l n : isptr q -> is_bytes l -> Zlength l = n ->
  cbuf_ok false q Ews q 0 n n (map vi l) l.
Proof.
  intros Hq Hb <-. unfold cbuf_ok. rewrite isptr_offset_val_zero by exact Hq.
  rewrite sublist_same by (rewrite ?Zlength_map; lia).
  repeat split; auto; try lia.
Qed.

Lemma rbytes_is_bytes l : RTDIface.rbytes l -> is_bytes l.
Proof. intros H. unfold is_bytes. eapply Forall_impl; [ | exact H]. cbv beta. intros; rep_lia. Qed.

(* a name or a comment with its zero byte *)
Lemma nz_is_bytes l : nzbytes l -> is_bytes (l ++ [0]).
Proof.
  intros H. unfold is_bytes. apply Forall_app. split.
  - eapply Forall_impl; [ | exact H]. cbv beta. intros; rep_lia.
  - repeat constructor; rep_lia.
Qed.

Lemma Zlength_z0 l : Zlength (l ++ [0]) = Zlength l + 1.
Proof. rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. Qed.

(* compressed and out before any write: cobj u [] and oobj u [] *)
Lemma cnew_cbytes q n : 0 <= n ->
  cnew q n = malloc_token Ews (tarray tuchar n) q * data_at Ews (tarray tuchar n) (cbytes n []) q.
Proof.
  intros Hn. unfold cnew, cbytes, data_at_. simpl map. rewrite app_nil_l, Z.sub_0_r. reflexivity.
Qed.

(** ** The tests of choice *)

(* choice & m, for choice a byte and m a mask below 256 *)
Lemma a2_and (ch m : Z) :
  0 <= ch <= 255 -> 0 <= m <= 255 ->
  Int.and (Int.repr ch) (Int.repr m) = Int.repr (Z.land ch m) /\ 0 <= Z.land ch m <= 255.
Proof.
  intros Hp Hm. split.
  - unfold Int.and. rewrite !Int.unsigned_repr by rep_lia. reflexivity.
  - replace ch with (Z.land ch (Z.ones 8)) by (rewrite Z.land_ones by lia; apply Z.mod_small; simpl; lia).
    rewrite <- Z.land_assoc, (Z.land_comm (Z.ones 8)), Z.land_assoc, Z.land_ones by lia.
    pose proof (Z.mod_pos_bound (Z.land ch m) (2 ^ 8)). simpl in *. lia.
Qed.

(* the test (choice & m) decides selp *)
Lemma selp_zero u m q :
  0 <= su_choice u <= 255 -> 0 <= m <= 255 -> Int.and (Int.repr (su_choice u)) (Int.repr m) = Int.zero ->
  selp u m q = nullval.
Proof.
  intros Hp Hm E. destruct (a2_and _ _ Hp Hm) as [E' B]. rewrite E' in E.
  unfold selp, has. replace (Z.land (su_choice u) m) with 0; [reflexivity |].
  apply (f_equal Int.unsigned) in E. rewrite Int.unsigned_repr in E by rep_lia. rewrite E. reflexivity.
Qed.

Lemma selp_nz u m q :
  0 <= su_choice u <= 255 -> 0 <= m <= 255 -> Int.and (Int.repr (su_choice u)) (Int.repr m) <> Int.zero ->
  selp u m q = q.
Proof.
  intros Hp Hm E. destruct (a2_and _ _ Hp Hm) as [E' B]. rewrite E' in E.
  unfold selp, has. destruct (Z.eqb_spec (Z.land (su_choice u) m) 0) as [Z0 | Z0]; [| reflexivity].
  rewrite Z0 in E. contradiction.
Qed.

(** ** Tactics *)

(* the tc goal of `!q` for an object q *)
Ltac a2_tceq_obj := match goal with |- ?P |-- denote_tc_test_eq ?q _ =>
  match P with
  | context [bobj q ?l] => apply (bobj_test_eq _ q l); cancel
  | context [cnew q ?n] => apply (cnew_test_eq _ n q); [rep_lia | cancel]
  end end.
Ltac a2_tceq := match goal with
  | |- _ |-- denote_tc_test_eq _ _ => a2_tceq_obj
  | |- ENTAIL _, _ |-- tc_expr _ _ => go_lower; unfold tc_expr; simpl typecheck_expr; cbv beta iota; a2_tceq_obj
  end.

(* a branch excluded by the value of its test *)
Ltac a2_nob := exfalso; first [ congruence | exact (Int.one_not_zero ltac:(assumption)) | contradiction ].

(* an object's pointer is a concrete pointer *)
Ltac a2_mkptr P b o :=
  let Ip := fresh in
  assert_PROP (isptr P) as Ip by
    (match goal with
     | |- context [bobj P ?l] => sep_apply (bobj_isptr P l)
     | |- context [cnew P ?n] => sep_apply (cnew_isptr P n)
     end; entailer!);
  destruct P as [ | | | | | b o]; try contradiction; clear Ip.

(* the ifs of eq_dec a destruct decided *)
Ltac a2_if_simpl :=
  repeat match goal with
  | |- context [if @left ?A ?B ?h then ?x else ?y] => change (if @left A B h then x else y) with x
  | |- context [if @right ?A ?B ?h then ?x else ?y] => change (if @right A B h then x else y) with y
  end.

(* a setup into its components (so that its pointers can be cut by cases) *)
Ltac a2_destr u :=
  destruct u as [lv wv mv sv ch dict xf nm cm data cap text time os hcrc dictp xp np cmp dp dcp xcp ncp ccp ep cp op
                 gxp gnp gcp];
  cbn [su_level su_wbits su_mem su_strategy su_choice su_dict su_xf su_nm su_cm su_data su_cap su_text su_time su_os
       su_hcrc su_dictp su_xp su_np su_cmp su_dp su_dcp su_xcp su_ncp su_ccp su_ep su_cp su_op su_gxp su_gnp su_gcp]
    in *.

(* the facts of su_dok as hypotheses (su_dok itself kept) *)
Ltac a2_facts :=
  match goal with H : su_dok _ |- _ => let H' := fresh "Hd" in pose proof H as H'; unfold su_dok in H' end;
  repeat match goal with H : _ /\ _ |- _ => destruct H end.

(* the objects tested, in the postcondition of an operand *)
Ltac a2_objs :=
  rewrite ?obj0_null, ?new0_null;
  repeat match goal with
  | |- context [obj0 (Vptr ?b ?o) ?l] => rewrite (obj0_bobj (Vptr b o) l) by (intros ?; discriminate)
  | |- context [new0 (Vptr ?b ?o) ?n] => rewrite (new0_cnew (Vptr b o) n) by (intros ?; discriminate)
  end.

(* the end of an operand of statement 45 or 46: the state NS with its temporary *)
Ltac a2_end :=
  destruct POST_s as [r1 r2 r3 r4]; cbn [tycontext.RA_normal];
  repeat match goal with E : ?f = ?b |- context [?f] => match b with true => rewrite E | false => rewrite E end end;
  a2_if_simpl; unfold vb; cbn [orb]; a2_objs; entailer!.

(* the start of an operand: the state unfolded, the setup cut into its components *)
Ltac a2_tstart u :=
  unfold NS, base, cobjs, c_locals, lvs, lv_locals, o_locals, d_locals, nb, dictobj, datobj, hvals, gval;
  cbn [app];
  unfold Delta_s; simplify_func_tycontext; abbreviate_semax;
  Intros; a2_facts; a2_destr u.
