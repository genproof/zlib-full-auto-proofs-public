(* Law rfc_level0_blocks (data of any length, deflate() in whole-block pieces), main (L0B2Main.v): the kit shared
   by the segment lemmas of main's proof, at DCS.CS (the compspecs of main's body).  Up to the end of the
   deflate loop main is rfc_level0_size's (rfc_level0_size/L0S2Kit.v; its temporaries renamed), and the
   assertions carry in addition the temporaries blocks and head_len (and after the loop data_len, the range of
   the data's length and of room) that the check of the stored blocks reads.
   - Delta_l0 (main's type context), POST_l0 (main's postcondition after start_function), POST_B (the
     postcondition of every suffix of main's chain of statements: each ends by a return);
   - the segments: main's body is `chain; return 0`, the chain s1; (s2; (s3; ...)); l0_seg k is the suffix of the
     chain from its k-th statement (1-based);
   - the assertions at the cuts and the segment statements (CPS: each segment is proved from the proof of the
     next one).
   Main's statements: 1-4 data_len = upto(PTRDIFF_MAX), window_bits, mem_level, strategy (nondet_u32),
   5-11 blocks, head_len, trailer_len and size, 12 room = size + upto(SIZE_MAX - size), 13 data =
   alloc_any_bytes(data_len), 14 `return 0` if it is NULL, 15 expected = copy_of(data, data_len),
   16 compressed = malloc(room), 17 `return 0` if either is NULL, 18 new_stream(&strm), 19 deflateInit2 and
   `return 0` unless Z_OK, 20-21 next_in = data, next_out = compressed, 22 the do-while of deflate() calls,
   23 `if (code != Z_STREAM_END) return 0`, 24-27 the check of the stored blocks against the copy (L0B2Blocks.v,
   L0B2Loop.v) and return 0.
   The cuts: l0_A0 (after start_function), l0_A18 (the inputs drawn, the three objects made: the data, its copy
   and the output object), l0_LI (the head of the do-while: Level0Calls' invariant J), l0_LB (after the
   do-while: the last code, and with Z_STREAM_END total_out = size and the stored stream).  The copy is not
   touched by deflate(): every assertion from l0_A18 on holds it, at ep, with the data's bytes. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.LawFacts.
Require Import Zlib.proof.deflate.GlobalsInit.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.deflate.Level0Calls Zlib.proof.deflate.DeflateCodes.
Require Import Zlib.proof.harness.rfc_level0_blocks.L0B2MainStmt.
Require Import Zlib.harness.rfc_level0_blocks.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

Definition Delta_l0 : tycontext :=
  func_tycontext f_main (QPvarspecs Zlib.contracts.rfc_level0_blocks.whole_prog) Gmain nil.

(* main's postcondition after start_function (main_core_spec) *)
Definition POST_l0 : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* the postcondition of every suffix of the chain: it never ends normally *)
Definition POST_B : ret_assert := overridePost FF POST_l0.

(* ---------------------------------------------------------------------------------------------- *)
(* The segments of f_main's body                                                                 *)

Fixpoint l0_drop (n : nat) (s : statement) : statement :=
  match n, s with
  | O, _ => s
  | S n', Ssequence _ b => l0_drop n' b
  | _, _ => Sskip
  end.

Definition l0_chain (s : statement) : statement := match s with Ssequence a _ => a | _ => Sskip end.

Ltac l0_get_seg k :=
  let n := eval compute in (k - 1)%nat in
  let x := eval cbv beta iota zeta delta [l0_drop l0_chain f_main fn_body] in
    (l0_drop n (l0_chain (fn_body f_main))) in
  exact x.

Definition l0_seg1 : statement := ltac:(l0_get_seg 1%nat).
Definition l0_seg18 : statement := ltac:(l0_get_seg 18%nat).
Definition l0_seg22 : statement := ltac:(l0_get_seg 22%nat).
Definition l0_seg23 : statement := ltac:(l0_get_seg 23%nat).

Lemma l0_body_eq : fn_body f_main = Ssequence l0_seg1 (Sreturn (Some (Econst_int (Int.repr 0) tint))).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The assertions                                                                                *)

Definition t_zsl : type := Tstruct _z_stream_s noattr.

(* the rest of the local strm while the deflate API holds its fields: the complement of Ews (the
   specifications' share) and the Ews share of the struct's padding *)
Definition l0_srest (vs : val) : mpred := data_at_ BoundKit.Ecomp t_zsl vs * BoundKit.strm_pad vs.

(* the output object of room bytes (malloc(room)) after O was produced into it *)
Definition l0_comp (room : Z) (O : list Z) (cp : val) : mpred :=
  malloc_token Ews (tarray tuchar room) cp *
  data_at Ews (tarray tuchar room) (map vi O ++ Zrepeat Vundef (room - Zlength O)) cp.

(* the data object of n bytes (also its copy) *)
Definition l0_data (n : Z) (D : list Z) (dp : val) : mpred :=
  malloc_token Ews (tarray tuchar n) dp * data_at Ews (tarray tuchar n) (map vi D) dp.

(* the choices after statement 17: the data D (n bytes) in dp, the output object cp of room bytes, room at
   least the size main computed *)
Definition l0_cf (n : Z) (D : list Z) (dp cp : val) (wbits mem strategy room : Z) : Prop :=
  0 <= n <= l0_max_size /\ Zlength D = n /\ bytes D /\ isptr dp /\ isptr cp /\
  s32_ok wbits /\ s32_ok mem /\ s32_ok strategy /\ l0_size wbits n <= room <= l0_max_u64.

(* the stored stream of the data D with the wrapper of wbits *)
Definition l0_final (wbits : Z) (D O : list Z) : Prop :=
  exists H T, O = H ++ stored_blocks D ++ T /\ Zlength H = l0_hlen wbits /\ Zlength T = l0_tlen wbits.

Section Assertions.
Context (gv : globals) (vs : val).

(* after start_function *)
Definition l0_A0 : environ -> mpred :=
  PROP ()
  LOCAL (lvar _strm t_zsl vs; gvars gv)
  SEP (data_at_ Tsh t_zsl vs; mem_mgr gv; R gv).

(* before statement 18 (new_stream(&strm)): the copy of the data at ep *)
Definition l0_A18 (n : Z) (D : list Z) (dp ep cp : val) (wbits mem strategy room : Z) : environ -> mpred :=
  PROP (l0_cf n D dp cp wbits mem strategy room; isptr ep)
  LOCAL (temp _data_len (Vlong (Int64.repr n)); temp _window_bits (Vint (Int.repr wbits));
         temp _mem_level (Vint (Int.repr mem)); temp _strategy (Vint (Int.repr strategy));
         temp _blocks (Vlong (Int64.repr (l0_blocks n))); temp _head_len (Vlong (Int64.repr (l0_hlen wbits)));
         temp _size (Vlong (Int64.repr (l0_size wbits n))); temp _room (Vlong (Int64.repr room));
         temp _data dp; temp _expected ep; temp _compressed cp; lvar _strm t_zsl vs; gvars gv)
  SEP (data_at_ Tsh t_zsl vs; mem_mgr gv; R gv; l0_data n D dp;
       malloc_token Ews (tarray tuchar room) cp; data_at_ Ews (tarray tuchar room) cp; l0_data n D ep).

(* the invariant of the do-while (statement 22) at the head of its body: pos bytes of the data consumed
   (next_in = data + pos), O produced (next_out = compressed + |O|), avail_in / avail_out as the previous call
   left them (ai, ao), J of the state and the fields *)
Definition l0_LI (J : Z -> list Z -> Z -> Z -> list Z -> dstate -> Z -> Z -> Z -> Prop) (n : Z) (D : list Z)
    (dp ep cp : val) (wbits room : Z) : environ -> mpred :=
  EX pos : Z, EX O : list Z, EX s : dstate, EX tin : Z, EX tout : Z, EX adler : Z, EX ai : Z, EX ao : Z,
  EX msg : option Z, EX msgv : val,
  PROP (Zlength D = n; isptr dp; isptr ep; isptr cp; J wbits D room pos O s tin tout adler; msg_ok msg msgv;
        0 < room)
  LOCAL (temp _data_len (Vlong (Int64.repr n)); temp _blocks (Vlong (Int64.repr (l0_blocks n)));
         temp _head_len (Vlong (Int64.repr (l0_hlen wbits))); temp _size (Vlong (Int64.repr (l0_size wbits n)));
         temp _room (Vlong (Int64.repr room)); temp _data dp; temp _expected ep; temp _compressed cp;
         lvar _strm t_zsl vs; gvars gv)
  SEP (dstream 2 (Some s) vs nullval gv;
       api_fields vs (offset_val pos dp) ai tin (offset_val (Zlength O) cp) ao tout msgv adler; l0_srest vs;
       mem_mgr gv; R gv; l0_data n D dp; l0_comp room O cp; l0_data n D ep).

(* after the do-while (before statement 23): the last call returned a code other than Z_OK, one of deflate's
   (DeflateCodes.code4); with Z_STREAM_END, total_out = size and O is the stored stream of the data; the data
   are bytes, at most PTRDIFF_MAX of them, and room is a size_t (Level0Calls' lf_range) *)
Definition l0_LB (n : Z) (D : list Z) (dp ep cp : val) (wbits room : Z) : environ -> mpred :=
  EX code : Z, EX O : list Z, EX os : option dstate, EX nin : val, EX ai : Z, EX tin : Z, EX ao : Z, EX tout : Z,
  EX adler : Z, EX msgv : val,
  PROP (Zlength D = n; isptr dp; isptr ep; isptr cp; 0 <= Zlength O <= room; bytes O; code4 code; code <> Z_OK;
        code = Z_STREAM_END -> tout = l0_size wbits n /\ l0_final wbits D O;
        0 <= n <= l0_max_size; room <= l0_max_u64; bytes D)
  LOCAL (temp _code (Vint (Int.repr code)); temp _data_len (Vlong (Int64.repr n));
         temp _blocks (Vlong (Int64.repr (l0_blocks n))); temp _head_len (Vlong (Int64.repr (l0_hlen wbits)));
         temp _size (Vlong (Int64.repr (l0_size wbits n)));
         temp _data dp; temp _expected ep; temp _compressed cp; lvar _strm t_zsl vs; gvars gv)
  SEP (dstream 2 os vs nullval gv;
       api_fields vs nin ai tin (offset_val (Zlength O) cp) ao tout msgv adler; l0_srest vs;
       mem_mgr gv; R gv; l0_data n D dp; l0_comp room O cp; l0_data n D ep).

End Assertions.

(* ---------------------------------------------------------------------------------------------- *)
(* Tactic support                                                                                *)

(* Floyd's simplify_remove_localdef_temp (simpl on rlt_ident_eq of the large $"..." identifiers) takes minutes
   after a call that stores into a temp: remove the temp by rewriting instead *)
Lemma l0_rlt_nil i: remove_localdef_temp i [] = [].
Proof. reflexivity. Qed.
Lemma l0_rlt_gvars i g l: remove_localdef_temp i (gvars g :: l) = gvars g :: remove_localdef_temp i l.
Proof. reflexivity. Qed.
Lemma l0_rlt_lvar i j t v l: remove_localdef_temp i (lvar j t v :: l) = lvar j t v :: remove_localdef_temp i l.
Proof. reflexivity. Qed.
Lemma l0_rlt_same i v l: remove_localdef_temp i (temp i v :: l) = remove_localdef_temp i l.
Proof. simpl. unfold rlt_ident_eq. rewrite if_true by auto. reflexivity. Qed.
Lemma l0_rlt_cons i j v l: i <> j -> remove_localdef_temp i (temp j v :: l) = temp j v :: remove_localdef_temp i l.
Proof. intros. simpl. unfold rlt_ident_eq. rewrite if_false by auto. reflexivity. Qed.

Ltac l0_rlt :=
  repeat first [ rewrite l0_rlt_nil | rewrite l0_rlt_gvars | rewrite l0_rlt_lvar | rewrite l0_rlt_same
               | rewrite l0_rlt_cons by (let X := fresh in intro X; discriminate X) ].

(* a branch the test excludes *)
Ltac l0_bad := first [ contradiction
  | match goal with H: Int.repr _ = Int.zero |- _ =>
      apply (f_equal Int.unsigned) in H; rewrite Int.unsigned_repr in H by rep_lia; discriminate H end ].

(* ---------------------------------------------------------------------------------------------- *)
(* The segment statements                                                                        *)

(* statements 1-17 *)
Definition seg_inputs_stmt : Prop :=
  forall {Espec : OracleKind} gv vs,
  (forall n D dp ep cp wbits mem strategy room,
     semax Delta_l0 (l0_A18 gv vs n D dp ep cp wbits mem strategy room) l0_seg18 POST_B) ->
  semax Delta_l0 (l0_A0 gv vs) l0_seg1 POST_B.

(* statements 18-21 *)
Definition seg_init_stmt : Prop :=
  forall {Espec : OracleKind} J gv vs n D dp ep cp wbits mem strategy room,
  l0_facts J ->
  semax Delta_l0 (l0_LI gv vs J n D dp ep cp wbits room) l0_seg22 POST_B ->
  semax Delta_l0 (l0_A18 gv vs n D dp ep cp wbits mem strategy room) l0_seg18 POST_B.

(* statement 22 *)
Definition seg_loop_stmt : Prop :=
  forall {Espec : OracleKind} J gv vs n D dp ep cp wbits room,
  l0_facts J ->
  semax Delta_l0 (l0_LB gv vs n D dp ep cp wbits room) l0_seg23 POST_B ->
  semax Delta_l0 (l0_LI gv vs J n D dp ep cp wbits room) l0_seg22 POST_B.

(* statements 23-27 *)
Definition seg_end_stmt : Prop :=
  forall {Espec : OracleKind} gv vs n D dp ep cp wbits room,
  semax Delta_l0 (l0_LB gv vs n D dp ep cp wbits room) l0_seg23 POST_B.
