(* Law api_short_output (data of any length), main (WMain.v): the kit of main's proof and its second segment.
   - the moves of byte arrays, unsigned longs and malloc tokens between the units' compspecs and the law's, the
     globals as uncompress2 takes them, the output space as uncompress2's destination and bytes_eq's argument;
   - Delta_w (main's type context), POST_w (main's postcondition after start_function), w_tail (main's statements
     from `decompressed_len = decompressed_size` to the end: the call of uncompress2 and the checks) with its
     precondition w_tail_pre (compress2 returned Z_OK with the zlib stream of the data, the source holds that
     stream and any bytes after it);
   - w_tail_ok: that segment, from UTheoryW.uw_theory_stmt.
   main's proof is cut there to keep each file's check short. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.compress.CSpec.
Require Import Zlib.proof.roundtrip.RTCSpec Zlib.proof.roundtrip.RTCSpecW.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.uncompr.USpecW.
Require Import Zlib.proof.harness.laws_common.Spec Zlib.proof.harness.laws_common.BytesEqNull.
Require Import Zlib.proof.roundtrip.RTC2W Zlib.proof.roundtrip.RTC2WFinal Zlib.proof.uncompr.UTheoryW.
Require Zlib.proof.roundtrip.RTCLFacts.
Require Import Zlib.proof.harness.api_short_output.WLawCS Zlib.proof.harness.api_short_output.WMainDefs.
Require Import Zlib.harness.api_short_output.code.
#[local] Existing Instance Zlib.proof.harness.api_short_output.WLawCS.CS.
Local Open Scope logic.

(* Moves of byte arrays, unsigned longs and malloc tokens between the units' compspecs (compress.c, uncompr.c,
   and adler32's, where the laws_common.h helpers are specified) and the law's. *)
Lemma asw_bytes_compress sh n (v: list val) q:
  @data_at Zlib.units.Compress.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_compress); [apply JMeq_refl | reflexivity]. Qed.
Lemma asw_ulong_compress sh (v: val) q:
  @data_at Zlib.units.Compress.CS sh tulong v q = @data_at CS sh tulong v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_compress); [apply JMeq_refl | reflexivity]. Qed.
Lemma asw_bytes_uncompr sh n (v: list val) q:
  @data_at Zlib.units.Uncompr.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_uncompr); [apply JMeq_refl | reflexivity]. Qed.
Lemma asw_tok_uncompr sh n q:
  @malloc_token Zlib.units.Uncompr.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_uncompr). reflexivity. Qed.
Lemma asw_ulong_uncompr sh (v: val) q:
  @data_at Zlib.units.Uncompr.CS sh tulong v q = @data_at CS sh tulong v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_uncompr); [apply JMeq_refl | reflexivity]. Qed.
Lemma asw_bytes_adler sh n (v: list val) q:
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.
Lemma asw_tok_adler sh n q:
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_adler32). reflexivity. Qed.

Ltac asw_law := repeat first [ rewrite asw_bytes_compress | rewrite asw_ulong_compress | rewrite asw_bytes_uncompr
                             | rewrite asw_tok_uncompr | rewrite asw_ulong_uncompr | rewrite asw_bytes_adler
                             | rewrite asw_tok_adler ].

(* deflate_globals without crc32's table (which uncompress2's inflate_globals takes, at share Ers) *)
Definition asw_dgr (gv : globals) : mpred :=
  trees_globals gv * errmsg_at gv *
  @data_at Zlib.proof.deflate.DCS.CS Ers (tarray t_config 10) (config_vals gv) (gv Zlib.deflate.code._configuration_table) *
  @data_at Zlib.proof.deflate.DCS.CS Ers (tarray tschar 6) (map vi [49; 46; 51; 46; 50; 0]) (gv Zlib.deflate.code._my_version).

Lemma asw_ig_to gv :
  deflate_globals gv * tables_rep Ers gv * version_lit gv * Zlib.proof.inflate.Callees.zfuncs gv |--
  inflate_globals Ers Ers gv * asw_dgr gv.
Proof. unfold deflate_globals, asw_dgr, inflate_globals. cancel. Qed.

Lemma asw_ig_from gv :
  inflate_globals Ers Ers gv * asw_dgr gv |--
  deflate_globals gv * tables_rep Ers gv * version_lit gv * Zlib.proof.inflate.Callees.zfuncs gv.
Proof. unfold deflate_globals, asw_dgr, inflate_globals. cancel. Qed.

(* The output space as any_bytes returns it, Z_NULL or not, under the flag dnull (Z_NULL) *)
Lemma asw_if_null {A} (dnull: bool) (q: val) (a b: A) :
  (if dnull then q = nullval else q <> nullval) -> (if eq_dec q nullval then a else b) = (if dnull then a else b).
Proof. destruct dnull; intros H; [rewrite if_true | rewrite if_false]; auto. Qed.

(* ... is uncompress2's destination (USpecN.dest_rep), with its malloc token when it is an object *)
Lemma asw_dest_in (dnull: bool) (q: val) (cap: Z) (bs: list Z) :
  (if dnull then emp else malloc_token Ews (tarray tuchar cap) q * data_at Ews (tarray tuchar cap) (bytes_rep bs) q) =
  dest_rep dnull Ews q cap (if dnull then [] else bytes_rep bs) (negb dnull).
Proof.
  unfold dest_rep. destruct dnull; [reflexivity | ]. simpl.
  rewrite asw_bytes_uncompr, asw_tok_uncompr. apply sepcon_comm.
Qed.

(* ... and is given back to bytes_eq (BytesEqNull.bytes_eq_spec_n) with the token aside *)
Lemma asw_dest_out (dnull: bool) (q: val) (cap: Z) (dc: list val) :
  dest_rep dnull Ews q cap dc (negb dnull) =
  (if dnull then emp else @data_at Zlib.units.Adler32.CS Ews (tarray tuchar cap) dc q) *
  (if dnull then emp else malloc_token Ews (tarray tuchar cap) q).
Proof.
  unfold dest_rep. destruct dnull; simpl.
  - rewrite sepcon_emp. reflexivity.
  - rewrite asw_bytes_adler, asw_bytes_uncompr, asw_tok_uncompr. reflexivity.
Qed.

(* forward_call's frame when the spec's SEP list is a definition [d] (RTCSpec.c2_sep_pre) *)
Ltac asw_sep_cancel d :=
  unfold d;
  repeat (eapply syntactic_cancel_cons_succeed;
          [find_nth ecancel_local_tac | cbv iota; unfold delete_nth; cbv zeta iota ]);
  apply syntactic_cancel_nil.

(* Floyd's simplify_remove_localdef_temp (simpl on rlt_ident_eq of the large $"..." identifiers) takes minutes
   after a call that stores into a temp: remove the temp by rewriting instead *)
Lemma asw_rlt_nil i: remove_localdef_temp i [] = [].
Proof. reflexivity. Qed.
Lemma asw_rlt_gvars i g l: remove_localdef_temp i (gvars g :: l) = gvars g :: remove_localdef_temp i l.
Proof. reflexivity. Qed.
Lemma asw_rlt_lvar i j t v l: remove_localdef_temp i (lvar j t v :: l) = lvar j t v :: remove_localdef_temp i l.
Proof. reflexivity. Qed.
Lemma asw_rlt_same i v l: remove_localdef_temp i (temp i v :: l) = remove_localdef_temp i l.
Proof. simpl. unfold rlt_ident_eq. rewrite if_true by auto. reflexivity. Qed.
Lemma asw_rlt_cons i j v l: i <> j -> remove_localdef_temp i (temp j v :: l) = temp j v :: remove_localdef_temp i l.
Proof. intros. simpl. unfold rlt_ident_eq. rewrite if_false by auto. reflexivity. Qed.

Ltac simplify_remove_localdef_temp ::=
  repeat first [ rewrite asw_rlt_nil | rewrite asw_rlt_gvars | rewrite asw_rlt_lvar | rewrite asw_rlt_same
               | rewrite asw_rlt_cons by (let X := fresh in intro X; discriminate X) ].

(* a branch the test excludes *)
Ltac asw_bad := first [ contradiction
  | match goal with H: Int.repr _ = Int.zero |- _ =>
      apply (f_equal Int.unsigned) in H; rewrite Int.unsigned_repr in H by rep_lia; discriminate H end
  | match goal with H: ?x <> ?x |- _ => contradiction H; reflexivity end ].

(* (tbool) (p == NULL) for a pointer p *)
Ltac asw_cmp := try match goal with |- context [sem_cmp_pp Ceq ?p _] =>
  let Hp := fresh in assert (Hp: isptr p) by (first [eapply field_compatible_isptr; eassumption | auto]);
  destruct p; try contradiction Hp; reflexivity end.

Definition Delta_w : tycontext := func_tycontext f_main (QPvarspecs p) Gmain nil.

(* main's postcondition after start_function (main_core_spec), and that of a suffix of main's statements that
   always returns *)
Definition POST_w : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).
Definition POST_wB : ret_assert := overridePost FF POST_w.

(* main's body is `chain; return 0` with the chain s1; (s2; (s3; ...)); w_drop k drops its first k statements *)
Fixpoint w_drop (n : nat) (s : statement) : statement :=
  match n, s with
  | O, _ => s
  | S n', Ssequence _ b => w_drop n' b
  | _, _ => Sskip
  end.
Definition w_chain (s : statement) : statement := match s with Ssequence a _ => a | _ => Sskip end.

(* the statements from `decompressed_len = decompressed_size` *)
Definition w_tail : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [w_drop w_chain f_main fn_body] in
          (w_drop 21 (w_chain (fn_body f_main))) in exact x).

(* before `decompressed_len = decompressed_size`: compress2 returned Z_OK, its output out is the zlib stream of the
   data bs and the object source holds out followed by the bytes tl (suffix_len = |tl|); original_copy holds the copy
   of the data made before compress2; the output space outp of cap bytes, Z_NULL (dnull) only when cap = 0 *)
Definition w_tail_pre (gv : globals) (vcl vol vul : val) (bs : list Z) (cap : Z) (outp expp inp : val)
    (ob : list Z) (dnull : bool) (out tl : list Z) : environ -> mpred :=
  PROP (Zlib.proof.roundtrip.RTFinal.dfinal [] 1 15 None bs out; is_bytes bs;
        1 <= Zlength bs <= 9223372036854775807; 0 <= cap <= Zlength bs - 1; Zlength ob = cap;
        if dnull then outp = nullval else outp <> nullval; dnull = true -> cap = 0; dnull = false -> isptr outp;
        is_bytes tl; Zlength out + Zlength tl <= Int64.max_unsigned; isptr expp; isptr inp)
  LOCAL (temp _decompressed outp; temp _original_copy expp; temp _source inp; temp _suffix_len (Vlong (Int64.repr (Zlength tl)));
         temp _decompressed_size (Vlong (Int64.repr cap));
         lvar _source_consumed_len tulong vul; lvar _decompressed_len tulong vol; lvar _compressed_len tulong vcl; gvars gv)
  SEP (data_at Ews (tarray tuchar (Zlength out + Zlength tl)) (bytes_rep (out ++ tl)) inp;
       malloc_token Ews (tarray tuchar (Zlength out + Zlength tl)) inp;
       data_at Ews (tarray tuchar (Zlength bs)) (bytes_rep bs) expp;
       data_at Tsh tulong (vl (Zlength out)) vcl;
       cversion_lit gv; deflate_globals gv; mem_mgr gv; TT;
       if dnull then emp
       else malloc_token Ews (tarray tuchar cap) outp * data_at Ews (tarray tuchar cap) (bytes_rep ob) outp;
       Zlib.proof.inflate.Callees.zfuncs gv; data_at_ Tsh tulong vul; data_at_ Tsh tulong vol;
       tables_rep Ers gv; version_lit gv; uversion_lit gv).

Lemma w_tail_ok {Espec : OracleKind} (UF : uw_theory_stmt) gv vcl vol vul bs cap outp expp inp ob dnull out tl :
  semax Delta_w (w_tail_pre gv vcl vol vul bs cap outp expp inp ob dnull out tl) w_tail POST_wB.
Proof.
  unfold w_tail, w_tail_pre, POST_wB, POST_w. abbreviate_semax.
  Intros.
  rename H into Hok, H0 into Hbs, H1 into Hn, H2 into Hcap, H3 into Hob, H4 into Hdn, H5 into Hd0, H6 into Po,
    H7 into Htl, H8 into Hsl, Pexpp into Pe, Pinp into Pi.
  assert (Hrb: rbytes bs) by (eapply Forall_impl; [ | exact Hbs]; simpl; intros; rep_lia).
  assert (Hob': bytes_ok out) by exact (Zlib.proof.roundtrip.RTCLFacts.rtcl_dfinal_bytes _ _ Hok).
  (* decompressed_len = decompressed_size; source_consumed_len = compressed_len + suffix_len *)
  unfold vl. forward. forward. forward.
  rewrite add64_repr, <- (Zlength_app _ out tl).
  assert (Hsrc: bytes_ok (out ++ tl)) by (apply Forall_app; split; [exact Hob' | exact Htl]).
  rewrite <- (Zlength_app _ out tl) in Hsl.
  (* code = uncompress2(decompressed, &decompressed_len, source, &source_consumed_len) *)
  rewrite (asw_dest_in dnull outp cap ob).
  rewrite <- (asw_bytes_uncompr Ews (Zlength (out ++ tl)) _ inp), <- (asw_tok_uncompr Ews _ inp),
    <- (asw_ulong_uncompr Tsh _ vol), <- (asw_ulong_uncompr Tsh _ vul).
  sep_apply (asw_ig_to gv).
  forward_call (gv, dnull, Ews, outp, cap, (if dnull then [] else bytes_rep ob), cap, vol, negb dnull, false,
                true, Ews, inp, Zlength (out ++ tl), bytes_rep (out ++ tl), out ++ tl, vul, Ers, Ers).
  { rewrite src_rep_obj. cancel. }
  { split.
    - unfold dest_ok_w. destruct dnull; simpl.
      + rewrite (Hd0 eq_refl). repeat split; auto.
      + unfold bytes_rep. split; [auto | ]. split; [exact (Po eq_refl) | ]. split; [lia | ].
        split; [discriminate | ]. split; [list_solve | rep_lia].
    - unfold src_ok_w, bytes_rep, byte_vals. split; [auto | ]. split; [discriminate | ].
      split; [list_solve | ]. split; [list_solve | ]. split; [rep_lia | ].
      rewrite sublist_same by list_solve. reflexivity. }
  Intros vret. destruct vret as [[[r2 slen2] dlen2] out2]. simpl fst in *; simpl snd in *.
  rewrite src_rep_obj. flatten_sepcon_in_SEP.
  asw_law.
  match goal with H: uncompressw_rel _ _ _ _ _ _ |- _ => rename H into Hu end.
  (* uncompress2 of the stream and the bytes after it into cap < |data| bytes: Z_MEM_ERROR, or Z_BUF_ERROR with
     the first cap bytes of the data and fewer bytes read than the stream has (Z_OK would have written all the
     data) *)
  destruct (UF bs out (out ++ tl) cap r2 slen2 dlen2 out2 Hok Hrb ltac:(lia)
              ltac:(list_solve) ltac:(list_solve)
              Hsrc ltac:(rep_lia) ltac:(rep_lia) Hu)
    as [Hm | [(Hr2 & Hfit & _) | (Hr2 & Hlt & Hd2 & Ho2 & Hs2)]].
  { subst r2. forward_if. { ret0. } { asw_bad. } }
  { lia. }
  subst r2 dlen2 out2.
  sep_apply (asw_ig_from gv).
  forward_if.
  { discriminate. }
  assert (Hda: dest_after (if dnull then [] else bytes_rep ob) cap (sublist 0 cap bs) = map vi (sublist 0 cap bs)).
  { unfold dest_after, byte_vals, vi. destruct dnull.
    - rewrite (Hd0 eq_refl). rewrite sublist_nil'; auto.
    - unfold bytes_rep. list_solve. }
  rewrite Hda, asw_dest_out. Intros.
  (* gp_assert(code == Z_BUF_ERROR && decompressed_len == decompressed_size &&
               bytes_eq(decompressed, original_copy, decompressed_size)) *)
  ifpost _t'17 (Int.repr 1).
  { forward. forward. entailer!. }
  { asw_bad. }
  ifpost _t'18 (Int.repr 1).
  { rewrite <- (asw_bytes_adler Ews (Zlength bs) _ expp).
    forward_call (dnull, outp, Ews, outp, 0, cap, map vi (sublist 0 cap bs), sublist 0 cap bs,
                  false, expp, Ews, expp, 0, Zlength bs, bytes_rep bs, sublist 0 cap bs, cap).
    { split.
      - destruct dnull.
        + rewrite (Hd0 eq_refl). repeat split; auto.
        + unfold cbuf_ok. rewrite isptr_offset_val_zero by auto. unfold bytes_rep, is_bytes.
          repeat split; auto; try rep_lia; try list_solve. apply Forall_sublist. exact Hbs.
      - unfold cbuf_ok. rewrite isptr_offset_val_zero by auto. unfold bytes_rep, is_bytes.
        repeat split; auto; try rep_lia; try list_solve. apply Forall_sublist. exact Hbs. }
    destruct (list_eq_dec Z.eq_dec (sublist 0 cap bs) (sublist 0 cap bs)); [ | contradiction].
    forward. entailer!. }
  { asw_bad. }
  forward_call (Int.repr 1).
  (* gp_assert(source_consumed_len < compressed_len) *)
  assert (Hol: Zlength out <= Int64.max_unsigned)
    by (rewrite Zlength_app in Hsl; pose proof (Zlength_nonneg tl); lia).
  forward. forward.
  forward_call (Int.repr 1).
  { entailer!. simpl. unfold Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
    destruct (zlt _ _); [reflexivity | lia]. }
  ret0.
Qed.
