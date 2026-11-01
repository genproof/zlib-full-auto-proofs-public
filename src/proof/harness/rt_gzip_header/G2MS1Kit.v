(* Law rt_gzip_header, main's body, segment 1 (G2MainKit.seg1_stmt), statements 0-33: the kit of the proof (the
   statements one by one, the states between them, the lemmas on the objects and on the tests of present).

   Every store into head or got and every load from them costs seconds at main's compspecs (VST evaluates the
   struct update through the whole composite environment), so the segment is cut into groups of statements, each
   proved in its own file from one named state to the next, with at most one store or load per file (two for a
   load in both cases of a pointer test):
     G2MS1S00.v  statements 0-7    the draws of the lengths, present and the locals text, time, os, hcrc
                                                                                       PRE0 -> Q1
     G2MS1S08.v  statements 8-10   extra (alloc_any_bytes), name, comment (any_string) Q1 -> QO
     G2MS1S11a.v .. G2MS1S11c.v    `if (!extra || !name || !comment) return 0` (statement 11), by the cases of
                                   the three pointers (a: extra or name NULL, b: comment NULL, c: none)   QO -> QP
     G2MS1S12.v  statements 12-14  the three copies (copy_of)                          QP -> QH (head h00)
     G2MS1S15.v .. G2MS1S18.v      head.text, head.time, head.os, head.hcrc            QH -> QH (head h2)
     G2MS1S19.v  statement 19      head.extra = (present & 1) ? extra : Z_NULL         QH -> QH
     G2MS1S20.v  statement 20      head.extra_len                                      QH -> QH
     G2MS1S21.v  statement 21      head.name = (present & 2) ? name : Z_NULL           QH -> QH
     G2MS1S22.v  statement 22      head.comment = (present & 4) ? comment : Z_NULL     QH -> QH (head hfin)
     G2MS1S23.v  statements 23-26  level, window_bits, mem_level, strategy             QH -> QG
     G2MS1S27.v  statement 27      got.extra (malloc)                                  QG -> QG
     G2MS1S28.v  statement 28      got.extra_max                                       QG -> QG
     G2MS1S29.v  statement 29      got.name (malloc)                                   QG -> QG
     G2MS1S30.v  statement 30      got.name_max                                        QG -> QG
     G2MS1S31.v  statement 31      got.comment (malloc)                                QG -> QG
     G2MS1S32.v  statement 32      got.comm_max; the values drawn and the objects as a gsetup g   QG -> NS g []
   statement 33, `if (!extra_copy || !name_copy || !comment_copy || !got.extra || !got.name || !got.comment)
   return 0;`, one operand at a time (NS g [] -> NS g [_t'27] -> .. -> NS g [_t'31]), each by cases:
     G2MS1O27a.v, G2MS1O27b.v, G2MS1O27c.v   _t'27 = !extra_copy || !name_copy: extra_copy NULL; extra_copy not
                                             NULL and name_copy NULL or not
     G2MS1OT1.v, G2MS1OT2.v                  _t'28 .. _t'31 when the previous temporary is 1
     G2MS1O28.v                              _t'28 = _t'27 || !comment_copy when _t'27 is 0
     G2MS1O29n.v, G2MS1O29p.v                _t'29 = _t'28 || !got.extra when _t'28 is 0, got.extra NULL or not
     G2MS1O30n.v, G2MS1O30p.v                _t'30 = _t'29 || !got.name likewise
     G2MS1O31n.v, G2MS1O31p.v                _t'31 = _t'30 || !got.comment likewise
     G2MS1Ret.v                              the test of _t'31: return 0 (the objects leak), or A26 g
   and chained in G2MainSeg1.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_gzip_header.CS.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainDefs.
Require Import Zlib.proof.roundtrip.RTDIface.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainKit.
Require Import Zlib.harness.rt_gzip_header.code.
#[local] Existing Instance Zlib.proof.harness.rt_gzip_header.CS.CS.
Local Open Scope logic.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers (_extra and _extra_len, ...); each identifier comparison is decided by vm_compute instead. *)
Ltac g1_rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in g1_rlt_fix u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := g1_rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

(** ** The statements *)

Definition S0 : statement := ltac:(let x := eval cbv [take suf seg1] in (take 1 (suf 0 seg1)) in exact x).
Definition S1 : statement := ltac:(let x := eval cbv [take suf seg1] in (take 1 (suf 1 seg1)) in exact x).
Definition S2 : statement := ltac:(let x := eval cbv [take suf seg1] in (take 1 (suf 2 seg1)) in exact x).
Definition S3 : statement := ltac:(let x := eval cbv [take suf seg1] in (take 1 (suf 3 seg1)) in exact x).
Definition S4 : statement := ltac:(let x := eval cbv [take suf seg1] in (take 1 (suf 4 seg1)) in exact x).
Definition S5 : statement := ltac:(let x := eval cbv [take suf seg1] in (take 1 (suf 5 seg1)) in exact x).
Definition S6 : statement := ltac:(let x := eval cbv [take suf seg1] in (take 1 (suf 6 seg1)) in exact x).
Definition S7 : statement := ltac:(let x := eval cbv [take suf seg1] in (take 1 (suf 7 seg1)) in exact x).
Definition S8 : statement := ltac:(let x := eval cbv [take suf seg1] in (take 1 (suf 8 seg1)) in exact x).
Definition S9 : statement := ltac:(let x := eval cbv [take suf seg1] in (take 1 (suf 9 seg1)) in exact x).
Definition S10 : statement := ltac:(let x := eval cbv [take suf seg1] in (take 1 (suf 10 seg1)) in exact x).
Definition S11 : statement := ltac:(let x := eval cbv [take suf seg1] in (take 1 (suf 11 seg1)) in exact x).
Definition S12 : statement := ltac:(let x := eval cbv [take suf seg1] in (take 1 (suf 12 seg1)) in exact x).
Definition S13 : statement := ltac:(let x := eval cbv [take suf seg1] in (take 1 (suf 13 seg1)) in exact x).
Definition S14 : statement := ltac:(let x := eval cbv [take suf seg1] in (take 1 (suf 14 seg1)) in exact x).
Definition S15 : statement := ltac:(let x := eval cbv [take suf seg1] in (take 1 (suf 15 seg1)) in exact x).
Definition S16 : statement := ltac:(let x := eval cbv [take suf seg1] in (take 1 (suf 16 seg1)) in exact x).
Definition S17 : statement := ltac:(let x := eval cbv [take suf seg1] in (take 1 (suf 17 seg1)) in exact x).
Definition S18 : statement := ltac:(let x := eval cbv [take suf seg1] in (take 1 (suf 18 seg1)) in exact x).
Definition S19 : statement := ltac:(let x := eval cbv [take suf seg1] in (take 1 (suf 19 seg1)) in exact x).
Definition S20 : statement := ltac:(let x := eval cbv [take suf seg1] in (take 1 (suf 20 seg1)) in exact x).
Definition S21 : statement := ltac:(let x := eval cbv [take suf seg1] in (take 1 (suf 21 seg1)) in exact x).
Definition S22 : statement := ltac:(let x := eval cbv [take suf seg1] in (take 1 (suf 22 seg1)) in exact x).
Definition S23 : statement := ltac:(let x := eval cbv [take suf seg1] in (take 1 (suf 23 seg1)) in exact x).
Definition S24 : statement := ltac:(let x := eval cbv [take suf seg1] in (take 1 (suf 24 seg1)) in exact x).
Definition S25 : statement := ltac:(let x := eval cbv [take suf seg1] in (take 1 (suf 25 seg1)) in exact x).
Definition S26 : statement := ltac:(let x := eval cbv [take suf seg1] in (take 1 (suf 26 seg1)) in exact x).
Definition S27 : statement := ltac:(let x := eval cbv [take suf seg1] in (take 1 (suf 27 seg1)) in exact x).
Definition S28 : statement := ltac:(let x := eval cbv [take suf seg1] in (take 1 (suf 28 seg1)) in exact x).
Definition S29 : statement := ltac:(let x := eval cbv [take suf seg1] in (take 1 (suf 29 seg1)) in exact x).
Definition S30 : statement := ltac:(let x := eval cbv [take suf seg1] in (take 1 (suf 30 seg1)) in exact x).
Definition S31 : statement := ltac:(let x := eval cbv [take suf seg1] in (take 1 (suf 31 seg1)) in exact x).
Definition S32 : statement := ltac:(let x := eval cbv [take suf seg1] in (take 1 (suf 32 seg1)) in exact x).
Definition S33 : statement := ltac:(let x := eval cbv [take suf seg1] in (suf 33 seg1) in exact x).

Lemma seg1_split : seg1 =
  (Ssequence S0 (Ssequence S1 (Ssequence S2 (Ssequence S3 (Ssequence S4 (Ssequence S5 (Ssequence S6 (Ssequence S7
  (Ssequence S8 (Ssequence S9 (Ssequence S10 (Ssequence S11 (Ssequence S12 (Ssequence S13 (Ssequence S14
  (Ssequence S15 (Ssequence S16 (Ssequence S17 (Ssequence S18 (Ssequence S19 (Ssequence S20 (Ssequence S21
  (Ssequence S22 (Ssequence S23 (Ssequence S24 (Ssequence S25 (Ssequence S26 (Ssequence S27 (Ssequence S28
  (Ssequence S29 (Ssequence S30 (Ssequence S31 (Ssequence S32 S33))))))))))))))))))))))))))))))))).
Proof. reflexivity. Qed.

(* statement 11: `if (!extra || !name || !comment) return 0;`: the operands, setting _t'12 and _t'13, then the
   test *)
Definition J12 : statement := ltac:(let x := eval cbv [S11] in
  (match S11 with Ssequence (Ssequence a _) _ => a | _ => Sskip end)
  in exact x).
Definition J13 : statement := ltac:(let x := eval cbv [S11] in
  (match S11 with Ssequence (Ssequence _ a) _ => a | _ => Sskip end)
  in exact x).
Definition Jret : statement := ltac:(let x := eval cbv [S11] in
  (match S11 with Ssequence _ a => a | _ => Sskip end)
  in exact x).

Lemma S11_split : S11 = Ssequence (Ssequence J12 J13) Jret.
Proof. reflexivity. Qed.

(* statement 33: `if (!extra_copy || !name_copy || !comment_copy || !got.extra || !got.name || !got.comment)
   return 0;`: the operands, each setting its temporary _t'27 .. _t'31, then the test *)
Definition I27 : statement := ltac:(let x := eval cbv [S33] in
  (match S33 with Ssequence (Ssequence (Ssequence (Ssequence (Ssequence a _) _) _) _) _ => a | _ => Sskip end)
  in exact x).
Definition I28 : statement := ltac:(let x := eval cbv [S33] in
  (match S33 with Ssequence (Ssequence (Ssequence (Ssequence (Ssequence _ a) _) _) _) _ => a | _ => Sskip end)
  in exact x).
Definition I29 : statement := ltac:(let x := eval cbv [S33] in
  (match S33 with Ssequence (Ssequence (Ssequence (Ssequence _ a) _) _) _ => a | _ => Sskip end)
  in exact x).
Definition I30 : statement := ltac:(let x := eval cbv [S33] in
  (match S33 with Ssequence (Ssequence (Ssequence _ a) _) _ => a | _ => Sskip end)
  in exact x).
Definition I31 : statement := ltac:(let x := eval cbv [S33] in
  (match S33 with Ssequence (Ssequence _ a) _ => a | _ => Sskip end)
  in exact x).
Definition Iret : statement := ltac:(let x := eval cbv [S33] in
  (match S33 with Ssequence _ a => a | _ => Sskip end)
  in exact x).

Lemma S33_split : S33 = Ssequence (Ssequence (Ssequence (Ssequence (Ssequence I27 I28) I29) I30) I31) Iret.
Proof. reflexivity. Qed.

(* a group of statements, nested to the left as the file of each group proves it *)
Lemma seq_left {Espec : OracleKind} {cs : compspecs} Delta P s1 s2 s3 R :
  semax Delta P (Ssequence (Ssequence s1 s2) s3) R -> semax Delta P (Ssequence s1 (Ssequence s2 s3)) R.
Proof. intros H. apply seq_assoc. exact H. Qed.

(** ** The states between the groups *)

(* head with its fields text, time, os, extra, extra_len, name, comment, hcrc (the others are never written) *)
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

(* the object alloc_any_bytes, any_string or copy_of gives: NULL, or n bytes l (at the compspecs of
   laws_common.h) *)
Definition obj0 (q : val) (n : Z) (l : list Z) : mpred :=
  if eq_dec q nullval then emp
  else @malloc_token Zlib.units.Adler32.CS Ews (tarray tuchar n) q *
       @data_at Zlib.units.Adler32.CS Ews (tarray tuchar n) (bytes_rep l) q.
(* the object malloc gives: NULL, or n bytes never written *)
Definition new0 (q : val) (n : Z) : mpred :=
  if eq_dec q nullval then emp else malloc_token Ews (tarray tuchar n) q * data_at_ Ews (tarray tuchar n) q.

(* the drawn lengths and the present bits *)
Definition dr_ok (xl nl cl pr : Z) : Prop :=
  0 <= xl <= 65535 /\ 0 <= nl <= 4294967294 /\ 0 <= cl <= 4294967294 /\ 0 <= pr <= Byte.max_unsigned.
Definition u32 (u : Z) : Prop := 0 <= u <= Int.max_unsigned.
Definition dr_temps (xl nl cl pr : Z) : list localdef :=
  [temp _extra_len (vl xl); temp _name_len (vl nl); temp _comment_len (vl cl); temp _present (vi pr)].
(* the locals text, time, os and hcrc (statements 4-7) *)
Definition sc_temps (ut utm uo uh : Z) : list localdef :=
  [temp _text (vi ut); temp _time (vl utm); temp _os (vi uo); temp _hcrc (vi uh)].
Definition ob_temps (xp np cp : val) : list localdef := [temp _extra xp; temp _name np; temp _comment cp].
Definition cp_temps (xcp ncp ccp : val) : list localdef :=
  [temp _extra_copy xcp; temp _name_copy ncp; temp _comment_copy ccp].
Definition lv_temps (ul w um us : Z) : list localdef :=
  [temp _level (vi ul); temp _window_bits (vi (25 + w)); temp _mem_level (vi um); temp _strategy (vi us)].

(* head.extra, head.name, head.comment: q when bit m of present is set, else Z_NULL *)
Definition psel (pr m : Z) (q : val) : val := if Z.land pr m =? 0 then nullval else q.

Lemma selp_psel g m q : selp g m q = psel (g_pr g) m q.
Proof. unfold selp, has, psel. destruct (Z.land (g_pr g) m =? 0); reflexivity. Qed.

(* gs_ok but for the nine pointers (the copies and got's buffers may still be NULL before statement 33; the three
   objects are known not NULL from their cobj) *)
Definition gs_ok0 (g : gsetup) : Prop :=
  0 <= g_xl g <= 65535 /\ 0 <= g_nl g <= 4294967294 /\ 0 <= g_cl g <= 4294967294 /\ 0 <= g_pr g <= 255 /\
  rs32 (g_text g) /\ 0 <= g_time g <= 4294967295 /\ rs32 (g_os g) /\ rs32 (g_hcrc g) /\
  rs32 (g_level g) /\ 25 <= g_wb g <= 31 /\ rs32 (g_mem g) /\ rs32 (g_strat g) /\
  Zlength (g_xf g) = g_xl g /\ rbytes (g_xf g) /\ Zlength (g_nm g) = g_nl g /\ nzbytes (g_nm g) /\
  Zlength (g_cm g) = g_cl g /\ nzbytes (g_cm g).

Lemma gs_ok_of (g : gsetup) : gs_ok0 g ->
  isptr (g_xp g) -> isptr (g_np g) -> isptr (g_cp g) -> isptr (g_gxp g) -> isptr (g_gnp g) -> isptr (g_gcp g) ->
  isptr (g_xcp g) -> isptr (g_ncp g) -> isptr (g_ccp g) ->
  gs_ok g.
Proof. unfold gs_ok0, gs_ok. tauto. Qed.

(* the value of a test: 1 when b, else 0; [nb q]: q is NULL *)
Definition vb (b : bool) : val := Vint (if b then Int.one else Int.zero).
Definition nb (q : val) : bool := if eq_dec q nullval then true else false.

(* the temporaries _t'27 .. _t'31 of statement 33: one of the first two, three, .. six objects tested is NULL *)
Definition f27 (g : gsetup) : bool := nb (g_xcp g) || nb (g_ncp g).
Definition f28 (g : gsetup) : bool := f27 g || nb (g_ccp g).
Definition f29 (g : gsetup) : bool := f28 g || nb (g_gxp g).
Definition f30 (g : gsetup) : bool := f29 g || nb (g_gnp g).
Definition f31 (g : gsetup) : bool := f30 g || nb (g_gcp g).

(* the facts of a state's PROP as hypotheses for rep_lia *)
Ltac s1_facts := repeat match goal with
  | H : dr_ok _ _ _ _ |- _ => unfold dr_ok in H
  | H : u32 _ |- _ => unfold u32 in H
  | H : _ /\ _ |- _ => destruct H
  end.

(** ** The tests of present *)

(* present & m, for present a byte and m a mask below 256 *)
Lemma s1_and (pr m : Z) :
  0 <= pr <= 255 -> 0 <= m <= 255 ->
  Int.and (Int.repr pr) (Int.repr m) = Int.repr (Z.land pr m) /\ 0 <= Z.land pr m <= 255.
Proof.
  intros Hp Hm. split.
  - unfold Int.and. rewrite !Int.unsigned_repr by rep_lia. reflexivity.
  - replace pr with (Z.land pr (Z.ones 8)) by (rewrite Z.land_ones by lia; apply Z.mod_small; simpl; lia).
    rewrite <- Z.land_assoc, (Z.land_comm (Z.ones 8)), Z.land_assoc, Z.land_ones by lia.
    pose proof (Z.mod_pos_bound (Z.land pr m) (2 ^ 8)). simpl in *. lia.
Qed.

(* the test (present & m) decides psel *)
Lemma psel_zero (pr m : Z) (q : val) :
  0 <= pr <= 255 -> 0 <= m <= 255 -> Int.and (Int.repr pr) (Int.repr m) = Int.zero -> psel pr m q = nullval.
Proof.
  intros Hp Hm E. destruct (s1_and _ _ Hp Hm) as [E' B]. rewrite E' in E.
  unfold psel. replace (Z.land pr m) with 0; [reflexivity |].
  apply (f_equal Int.unsigned) in E. rewrite Int.unsigned_repr in E by rep_lia. rewrite E. reflexivity.
Qed.

Lemma psel_nz (pr m : Z) (q : val) :
  0 <= pr <= 255 -> 0 <= m <= 255 -> Int.and (Int.repr pr) (Int.repr m) <> Int.zero -> psel pr m q = q.
Proof.
  intros Hp Hm E. destruct (s1_and _ _ Hp Hm) as [E' B]. rewrite E' in E.
  unfold psel. destruct (Z.eqb_spec (Z.land pr m) 0) as [Z0 | Z0]; [| reflexivity].
  rewrite Z0 in E. contradiction.
Qed.

(** ** The objects and their NULL tests (statements 11 and 33) *)

(* alloc_any_bytes, any_string and copy_of give their objects at the adler32 unit's compspecs; main keeps them at its
   own *)
Lemma s1_bytes_cs sh n (v : list val) q :
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.

Lemma s1_tok_cs sh n q :
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_adler32). reflexivity. Qed.

(* a non-NULL object is G2MainKit's cobj / cnew *)
Lemma nb_false q : (if eq_dec q nullval then true else false) = false -> q <> nullval.
Proof. destruct (eq_dec q nullval); congruence. Qed.

Lemma obj0_cobj q n l : q <> nullval -> n = Zlength l -> obj0 q n l = cobj q l.
Proof.
  intros Hq ->. unfold obj0, cobj. rewrite if_false by exact Hq. rewrite s1_bytes_cs, s1_tok_cs. reflexivity.
Qed.

Lemma new0_cnew q n : q <> nullval -> new0 q n = cnew q n.
Proof. intros Hq. unfold new0, cnew. rewrite if_false by exact Hq. reflexivity. Qed.

Lemma obj0_null n l : obj0 nullval n l = emp.
Proof. reflexivity. Qed.

Lemma new0_null n : new0 nullval n = emp.
Proof. reflexivity. Qed.

Lemma cobj_isptr q l : cobj q l |-- !! isptr q.
Proof.
  unfold cobj. entailer!;
    match goal with Hf : field_compatible _ _ _ |- _ => exact (field_compatible_isptr _ _ _ Hf) end.
Qed.

Lemma cnew_isptr q n : cnew q n |-- !! isptr q.
Proof.
  unfold cnew. entailer!;
    match goal with Hf : field_compatible _ _ _ |- _ => exact (field_compatible_isptr _ _ _ Hf) end.
Qed.

(* a malloc'ed object (any size, also 0) can be compared with NULL *)
Lemma cobj_test_eq P q l : P |-- cobj q l * TT -> P |-- denote_tc_test_eq q (Vlong Int64.zero).
Proof.
  intros HP. apply (malloc_test_eq P (Zlength l) q ltac:(apply Zlength_nonneg)).
  eapply derives_trans; [exact HP | ]. unfold cobj. cancel.
Qed.

Lemma cnew_test_eq P n q : 0 <= n -> P |-- cnew q n * TT -> P |-- denote_tc_test_eq q (Vlong Int64.zero).
Proof.
  intros Hn HP. apply (malloc_test_eq P n q Hn).
  eapply derives_trans; [exact HP | ]. unfold cnew. cancel.
Qed.

(* the tc goal of `!q` (or of the expression containing it) for an object q *)
Ltac s1_tceq_obj := match goal with |- ?P |-- denote_tc_test_eq ?q _ =>
  match P with
  | context [cobj q ?l] => apply (cobj_test_eq _ q l); cancel
  | context [cnew q ?n] => apply (cnew_test_eq _ n q); [lia | cancel]
  end end.
Ltac s1_tceq := match goal with
  | |- _ |-- denote_tc_test_eq _ _ => s1_tceq_obj
  | |- ENTAIL _, _ |-- tc_expr _ _ => go_lower; unfold tc_expr; simpl typecheck_expr; cbv beta iota; s1_tceq_obj
  end.

(* a branch excluded by the value of its test *)
Ltac s1_nob := exfalso; first [ congruence | exact (Int.one_not_zero ltac:(assumption)) | contradiction ].

(* an object's pointer is a concrete pointer *)
Ltac s1_mkptr P b o :=
  let Ip := fresh in
  assert_PROP (isptr P) as Ip by
    (match goal with
     | |- context [cobj P ?l] => sep_apply (cobj_isptr P l)
     | |- context [cnew P ?n] => sep_apply (cnew_isptr P n)
     end; entailer!);
  destruct P as [ | | | | | b o]; try contradiction; clear Ip.

(* the ifs of eq_dec a destruct decided *)
Ltac s1_if_simpl :=
  repeat match goal with
  | |- context [if @left ?A ?B ?h then ?x else ?y] => change (if @left A B h then x else y) with x
  | |- context [if @right ?A ?B ?h then ?x else ?y] => change (if @right A B h then x else y) with y
  end.

(* the end of a branch of statement 33: the state of NS with its temporary *)
Ltac s1_objs :=
  rewrite ?obj0_null, ?new0_null;
  repeat match goal with
  | |- context [obj0 (Vptr ?b ?o) ?n ?l] =>
      rewrite (obj0_cobj (Vptr b o) n l) by
        (first [intros ?; discriminate | rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; lia])
  | |- context [new0 (Vptr ?b ?o) ?n] => rewrite (new0_cnew (Vptr b o) n) by (intros ?; discriminate)
  end.
Ltac s1_end :=
  destruct POST_m as [r1 r2 r3 r4]; cbn [tycontext.RA_normal];
  repeat match goal with E : ?f = ?b |- context [?f] => match b with true => rewrite E | false => rewrite E end end;
  s1_if_simpl; unfold vb; cbn [orb]; s1_objs; entailer!.

(* copy_of takes its source at the compspecs of laws_common.h *)
Lemma cobj_cs q l n : Zlength l = n ->
  cobj q l = @malloc_token Zlib.units.Adler32.CS Ews (tarray tuchar n) q *
             @data_at Zlib.units.Adler32.CS Ews (tarray tuchar n) (map vi l) q.
Proof. intros <-. unfold cobj. rewrite s1_bytes_cs, s1_tok_cs. reflexivity. Qed.

(* the source of copy_of: an object of the n bytes l, from its start *)
Lemma cobj_cbuf q l n : isptr q -> is_bytes l -> Zlength l = n ->
  cbuf_ok false q Ews q 0 n n (map vi l) l.
Proof.
  intros Hq Hb <-. unfold cbuf_ok. rewrite isptr_offset_val_zero by exact Hq.
  rewrite sublist_same by (rewrite ?Zlength_map; lia).
  repeat split; auto; try lia.
Qed.

(* a name or a comment with its zero byte *)
Lemma nz_is_bytes l : nzbytes l -> is_bytes (l ++ [0]).
Proof.
  intros H. unfold is_bytes. apply Forall_app. split.
  - eapply Forall_impl; [ | exact H]. cbv beta. intros; rep_lia.
  - repeat constructor; rep_lia.
Qed.

Lemma Zlength_z0 l : Zlength (l ++ [0]) = Zlength l + 1.
Proof. rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. Qed.

(* a gsetup into its components (so that its pointers can be cut by cases) *)
Ltac s1_destr_g g :=
  destruct g as [xl nl cl pr text time os hcrc level wb mem strat xp np cp gxp gnp gcp xf nm cm xcp ncp ccp];
  cbn [g_xl g_nl g_cl g_pr g_text g_time g_os g_hcrc g_level g_wb g_mem g_strat g_xp g_np g_cp g_gxp g_gnp g_gcp
       g_xf g_nm g_cm g_xcp g_ncp g_ccp] in *.

Section States.
Context (gv : globals) (vh vg vc vd vr : val).

(* main's state with the facts P, the temporaries L, head h, got w, and the objects objs *)
Definition Qs (P : list Prop) (L : list localdef) (h w : reptype t_g) (objs : list mpred) : environ -> mpred :=
  PROPx P (LOCALx (L ++ lv_locals gv vh vg vc vd vr)
  (SEPx (data_at Tsh t_g h vh :: data_at Tsh t_g w vg :: data_at_ Tsh t_z vc :: data_at_ Tsh t_z vd ::
         data_at_ Tsh (tarray tuchar 1) vr :: mem_mgr gv :: R gv :: ifz gv :: objs))).

(* the facts of the draws of statements 0-7 *)
Definition fs1 (xl nl cl pr ut utm uo uh : Z) : list Prop :=
  [dr_ok xl nl cl pr; u32 ut; u32 utm; u32 uo; u32 uh].

(* after statement 7: the lengths, present and the four locals drawn *)
Definition Q1 (xl nl cl pr ut utm uo uh : Z) : environ -> mpred :=
  Qs (fs1 xl nl cl pr ut utm uo uh) (dr_temps xl nl cl pr ++ sc_temps ut utm uo uh) h00 h00 [].

(* the facts of the draws up to statement 10 *)
Definition fs2 (xl nl cl pr ut utm uo uh : Z) (xf nm cm : list Z) : list Prop :=
  [dr_ok xl nl cl pr; u32 ut; u32 utm; u32 uo; u32 uh; Zlength xf = xl /\ is_bytes xf;
   Zlength nm = nl /\ nzbytes nm; Zlength cm = cl /\ nzbytes cm].

(* the three objects of alloc_any_bytes and any_string, or the three copies (copy_of): possibly NULL *)
Definition objs3 (xl nl cl : Z) (xp : val) (xf : list Z) (np : val) (nm : list Z) (cp : val) (cm : list Z)
    : list mpred :=
  [obj0 xp xl xf; obj0 np (nl + 1) (nm ++ [0]); obj0 cp (cl + 1) (cm ++ [0])].
(* the three objects, not NULL *)
Definition cobjs3 (xp : val) (xf : list Z) (np : val) (nm : list Z) (cp : val) (cm : list Z) : list mpred :=
  [cobj xp xf; cobj np (nm ++ [0]); cobj cp (cm ++ [0])].

(* after statement 10: the three objects drawn *)
Definition QO (xl nl cl pr ut utm uo uh : Z) (xp : val) (xf : list Z) (np : val) (nm : list Z) (cp : val)
    (cm : list Z) : environ -> mpred :=
  Qs (fs2 xl nl cl pr ut utm uo uh xf nm cm) (dr_temps xl nl cl pr ++ sc_temps ut utm uo uh ++ ob_temps xp np cp)
    h00 h00 (objs3 xl nl cl xp xf np nm cp cm).

(* after statement 11: none of the three objects NULL *)
Definition QP (xl nl cl pr ut utm uo uh : Z) (xp : val) (xf : list Z) (np : val) (nm : list Z) (cp : val)
    (cm : list Z) : environ -> mpred :=
  Qs (fs2 xl nl cl pr ut utm uo uh xf nm cm) (dr_temps xl nl cl pr ++ sc_temps ut utm uo uh ++ ob_temps xp np cp)
    h00 h00 (cobjs3 xp xf np nm cp cm).

(* statements 15-22: the three objects and their copies xcp, ncp, ccp (possibly NULL), head h *)
Definition QH (xl nl cl pr ut utm uo uh : Z) (xp : val) (xf : list Z) (np : val) (nm : list Z) (cp : val)
    (cm : list Z) (xcp ncp ccp : val) (h : reptype t_g) : environ -> mpred :=
  Qs (fs2 xl nl cl pr ut utm uo uh xf nm cm)
    (dr_temps xl nl cl pr ++ sc_temps ut utm uo uh ++ ob_temps xp np cp ++ cp_temps xcp ncp ccp)
    h h00 (cobjs3 xp xf np nm cp cm ++ objs3 xl nl cl xcp xf ncp nm ccp cm).

(* head after statement 18 (its scalar fields) and after statement 22 (its pointers as present selects them) *)
Definition h2 (ut utm uo uh : Z) : reptype t_g := hv (vi ut) (vl utm) (vi uo) U U U U (vi uh).
Definition hfin (xl pr ut utm uo uh : Z) (xp np cp : val) : reptype t_g :=
  hv (vi ut) (vl utm) (vi uo) (psel pr 1 xp) (vi xl) (psel pr 2 np) (psel pr 4 cp) (vi uh).

(* statements 27-32: head complete, level, window_bits (25 + w), mem_level and strategy drawn; got wg with the
   objects objs malloc gave so far *)
Definition QG (xl nl cl pr ut utm uo uh : Z) (xp : val) (xf : list Z) (np : val) (nm : list Z) (cp : val)
    (cm : list Z) (xcp ncp ccp : val) (ul w um us : Z) (wg : reptype t_g) (objs : list mpred) : environ -> mpred :=
  Qs (fs2 xl nl cl pr ut utm uo uh xf nm cm ++ [u32 ul; 0 <= w <= 6; u32 um; u32 us])
    (dr_temps xl nl cl pr ++ sc_temps ut utm uo uh ++ ob_temps xp np cp ++ cp_temps xcp ncp ccp ++
     lv_temps ul w um us)
    (hfin xl pr ut utm uo uh xp np cp) wg
    (cobjs3 xp xf np nm cp cm ++ objs3 xl nl cl xcp xf ncp nm ccp cm ++ objs).

(* after statement 32, every value drawn and stored, as a gsetup g (the copies and got's buffers possibly NULL),
   with the temporaries L of statement 33 *)
Definition NS (g : gsetup) (L : list localdef) : environ -> mpred :=
  PROPx [gs_ok0 g]
  (LOCALx (L ++ gp_locals g ++ gs_locals g ++ lv_locals gv vh vg vc vd vr)
  (SEPx [data_at Tsh t_g (hvals g) vh; data_at Tsh t_g (gval g) vg; data_at_ Tsh t_z vc; data_at_ Tsh t_z vd;
         data_at_ Tsh (tarray tuchar 1) vr; mem_mgr gv; R gv; ifz gv;
         cobj (g_xp g) (g_xf g); cobj (g_np g) (g_nm g ++ [0]); cobj (g_cp g) (g_cm g ++ [0]);
         obj0 (g_xcp g) (g_xl g) (g_xf g); obj0 (g_ncp g) (g_nl g + 1) (g_nm g ++ [0]);
         obj0 (g_ccp g) (g_cl g + 1) (g_cm g ++ [0]); new0 (g_gxp g) (g_xl g); new0 (g_gnp g) (g_nl g + 1);
         new0 (g_gcp g) (g_cl g + 1)])).
End States.

(* the states' definitions, unfolded *)
Ltac s1_unfold :=
  unfold QH, QG, Qs, fs2, objs3, cobjs3, h2, hfin, hv, gw, h00, U, dr_temps, sc_temps, ob_temps, cp_temps, lv_temps,
    lv_locals.

(* statement 11: cut at the operand setting temporary i to v (the state before it, with i = v) *)
Ltac s11_cut i v :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
    apply semax_seq with (Q := PROPx P (LOCALx (temp i v :: L) (SEPx S))); [rewrite ?overridePost_overridePost | ]
  end.

(* the return: the objects leak, head and got are main's locals *)
Ltac s11_ret :=
  forward; Exists (Int.repr 0); apply andp_right; [apply prop_right; reflexivity |];
  rewrite <- !data_at_g; cancel.

(* the end of an operand *)
Ltac s11_end := destruct POST_m as [r1 r2 r3 r4]; cbn [tycontext.RA_normal]; unfold dr_ok, u32; entailer!.

(* the start: the state unfolded, the statement cut into its three parts *)
Ltac s11_start :=
  unfold QO, QP, Qs, fs2, objs3, cobjs3, dr_temps, sc_temps, ob_temps, lv_locals; cbn [app];
  rewrite S11_split; unfold Delta_m; simplify_func_tycontext;
  Intros; s1_facts.
