(* Law rt_roundtrip (data of any length), main (WMain.v): the kit of main's proof and its last segment.
   - the moves of byte arrays, unsigned longs and malloc tokens between the units' compspecs and the law's, the
     globals as uncompress2 takes them;
   - the buffers that may be Z_NULL: a flag per buffer (true: Z_NULL, no object), the output space as uncompress2
     takes it (USpecN.dest_rep);
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
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.roundtrip.RTC2W Zlib.proof.roundtrip.RTC2WFinal Zlib.proof.uncompr.UTheoryW.
Require Zlib.proof.roundtrip.RTCLFacts.
Require Import Zlib.proof.harness.rt_roundtrip.WCS Zlib.proof.harness.rt_roundtrip.WMainDefs.
Require Import Zlib.harness.rt_roundtrip.code.
#[local] Existing Instance Zlib.proof.harness.rt_roundtrip.WCS.CS.
Local Open Scope logic.

(* Moves of byte arrays, unsigned longs and malloc tokens between the units' compspecs (compress.c, uncompr.c,
   and adler32's, where the laws_common.h helpers are specified) and the law's. *)
Lemma rtw_bytes_compress sh n (v: list val) q:
  @data_at Zlib.units.Compress.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_compress); [apply JMeq_refl | reflexivity]. Qed.
Lemma rtw_ulong_compress sh (v: val) q:
  @data_at Zlib.units.Compress.CS sh tulong v q = @data_at CS sh tulong v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_compress); [apply JMeq_refl | reflexivity]. Qed.
Lemma rtw_bytes_uncompr sh n (v: list val) q:
  @data_at Zlib.units.Uncompr.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_uncompr); [apply JMeq_refl | reflexivity]. Qed.
Lemma rtw_tok_uncompr sh n q:
  @malloc_token Zlib.units.Uncompr.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_uncompr). reflexivity. Qed.
Lemma rtw_ulong_uncompr sh (v: val) q:
  @data_at Zlib.units.Uncompr.CS sh tulong v q = @data_at CS sh tulong v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_uncompr); [apply JMeq_refl | reflexivity]. Qed.
Lemma rtw_bytes_adler sh n (v: list val) q:
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.
Lemma rtw_tok_adler sh n q:
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_adler32). reflexivity. Qed.

Ltac rtw_law := repeat first [ rewrite rtw_bytes_compress | rewrite rtw_ulong_compress | rewrite rtw_bytes_uncompr
                             | rewrite rtw_tok_uncompr | rewrite rtw_ulong_uncompr | rewrite rtw_bytes_adler
                             | rewrite rtw_tok_adler ].

(* deflate_globals without crc32's table (which uncompress2's inflate_globals takes, at share Ers) *)
Definition rtw_dgr (gv : globals) : mpred :=
  trees_globals gv * errmsg_at gv *
  @data_at Zlib.proof.deflate.DCS.CS Ers (tarray t_config 10) (config_vals gv) (gv Zlib.deflate.code._configuration_table) *
  @data_at Zlib.proof.deflate.DCS.CS Ers (tarray tschar 6) (map vi [49; 46; 51; 46; 50; 0]) (gv Zlib.deflate.code._my_version).

Lemma rtw_ig_to gv :
  deflate_globals gv * tables_rep Ers gv * version_lit gv * Zlib.proof.inflate.Callees.zfuncs gv |--
  inflate_globals Ers Ers gv * rtw_dgr gv.
Proof. unfold deflate_globals, rtw_dgr, inflate_globals. cancel. Qed.

Lemma rtw_ig_from gv :
  inflate_globals Ers Ers gv * rtw_dgr gv |--
  deflate_globals gv * tables_rep Ers gv * version_lit gv * Zlib.proof.inflate.Callees.zfuncs gv.
Proof. unfold deflate_globals, rtw_dgr, inflate_globals. cancel. Qed.

(* forward_call's frame when the spec's SEP list is a definition [d] (RTCSpec.c2_sep_pre) *)
Ltac rtw_sep_cancel d :=
  unfold d;
  repeat (eapply syntactic_cancel_cons_succeed;
          [find_nth ecancel_local_tac | cbv iota; unfold delete_nth; cbv zeta iota ]);
  apply syntactic_cancel_nil.

(* Floyd's simplify_remove_localdef_temp (simpl on rlt_ident_eq of the large $"..." identifiers) takes minutes
   after a call that stores into a temp: remove the temp by rewriting instead *)
Lemma rtw_rlt_nil i: remove_localdef_temp i [] = [].
Proof. reflexivity. Qed.
Lemma rtw_rlt_gvars i g l: remove_localdef_temp i (gvars g :: l) = gvars g :: remove_localdef_temp i l.
Proof. reflexivity. Qed.
Lemma rtw_rlt_lvar i j t v l: remove_localdef_temp i (lvar j t v :: l) = lvar j t v :: remove_localdef_temp i l.
Proof. reflexivity. Qed.
Lemma rtw_rlt_same i v l: remove_localdef_temp i (temp i v :: l) = remove_localdef_temp i l.
Proof. simpl. unfold rlt_ident_eq. rewrite if_true by auto. reflexivity. Qed.
Lemma rtw_rlt_cons i j v l: i <> j -> remove_localdef_temp i (temp j v :: l) = temp j v :: remove_localdef_temp i l.
Proof. intros. simpl. unfold rlt_ident_eq. rewrite if_false by auto. reflexivity. Qed.

Ltac simplify_remove_localdef_temp ::=
  repeat first [ rewrite rtw_rlt_nil | rewrite rtw_rlt_gvars | rewrite rtw_rlt_lvar | rewrite rtw_rlt_same
               | rewrite rtw_rlt_cons by (let X := fresh in intro X; discriminate X) ].

(* a branch the test excludes *)
Ltac rtw_bad := first [ contradiction
  | match goal with H: Int.repr _ = Int.zero |- _ =>
      apply (f_equal Int.unsigned) in H; rewrite Int.unsigned_repr in H by rep_lia; discriminate H end
  | match goal with H: ?x <> ?x |- _ => contradiction H; reflexivity end ].

(* (tbool) (p == NULL) for a pointer p *)
Ltac rtw_cmp := try match goal with |- context [sem_cmp_pp Ceq ?p _] =>
  let Hp := fresh in assert (Hp: isptr p) by (first [eapply field_compatible_isptr; eassumption | auto]);
  destruct p; try contradiction Hp; reflexivity end.

Definition Delta_w : tycontext := func_tycontext f_main (QPvarspecs p) Gmain nil.

(* A result of alloc_any_bytes or copy_of, Z_NULL or not, under a flag (true: Z_NULL) *)
Lemma rtw_if_null {A} (b: bool) (q: val) (x y: A) :
  (if b then q = nullval else q <> nullval) -> (if eq_dec q nullval then x else y) = (if b then x else y).
Proof. destruct b; intros H; [rewrite if_true | rewrite if_false]; auto. Qed.

Lemma rtw_if_split (b: bool) (P Q: mpred) :
  (if b then emp else P * Q) = (if b then emp else P) * (if b then emp else Q).
Proof. destruct b; [rewrite emp_sepcon | ]; reflexivity. Qed.

(* the output space as uncompress2 takes it (USpecN.dest_rep, with its malloc token), and back *)
Lemma rtw_dest_in (dn: bool) (q: val) (cap: Z) (dc: list val) :
  (if dn then emp else malloc_token Ews (tarray tuchar cap) q) *
  (if dn then emp else data_at Ews (tarray tuchar cap) dc q) =
  dest_rep dn Ews q cap dc (negb dn).
Proof.
  unfold dest_rep. destruct dn; simpl; [apply emp_sepcon | ].
  rewrite rtw_bytes_uncompr, rtw_tok_uncompr. apply sepcon_comm.
Qed.

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
          (w_drop 24 (w_chain (fn_body f_main))) in exact x).

(* before `decompressed_len = decompressed_size`: compress2 returned Z_OK, its output out is the zlib stream of the
   data bs and the object source holds out followed by the bytes tl (suffix_len = |tl|); original_copy holds the
   copy of the data made before compress2 (Z_NULL only for no data: flag en); the output space decompressed and its
   copy decompressed_copy hold the bytes ob, at least as many as the data (each Z_NULL only when ob is empty:
   flags dn, bn) *)
Definition w_tail_pre (gv : globals) (vcl vol vul : val) (bs : list Z) (en dn bn : bool) (outp expp q inp : val)
    (ob out tl : list Z) : environ -> mpred :=
  PROP (Zlib.proof.roundtrip.RTFinal.dfinal [] 1 15 None bs out; is_bytes bs;
        Zlength bs <= Zlength ob <= 9223372036854775807; is_bytes ob; is_bytes tl;
        Zlength out + Zlength tl <= Int64.max_unsigned; isptr inp;
        if en then expp = nullval /\ bs = [] else isptr expp;
        if dn then outp = nullval /\ ob = [] else isptr outp;
        if bn then q = nullval /\ ob = [] else isptr q)
  LOCAL (temp _decompressed_copy q; temp _decompressed outp; temp _original_copy expp; temp _source inp;
         temp _suffix_len (Vlong (Int64.repr (Zlength tl)));
         temp _decompressed_size (Vlong (Int64.repr (Zlength ob)));
         temp _original_len (Vlong (Int64.repr (Zlength bs)));
         lvar _source_consumed_len tulong vul; lvar _decompressed_len tulong vol; lvar _compressed_len tulong vcl;
         gvars gv)
  SEP (data_at Ews (tarray tuchar (Zlength out + Zlength tl)) (bytes_rep (out ++ tl)) inp;
       malloc_token Ews (tarray tuchar (Zlength out + Zlength tl)) inp;
       if en then emp else data_at Ews (tarray tuchar (Zlength bs)) (bytes_rep bs) expp;
       if bn then emp else data_at Ews (tarray tuchar (Zlength ob)) (bytes_rep ob) q;
       data_at Tsh tulong (vl (Zlength out)) vcl;
       cversion_lit gv; deflate_globals gv; mem_mgr gv; TT;
       if dn then emp else malloc_token Ews (tarray tuchar (Zlength ob)) outp;
       if dn then emp else data_at Ews (tarray tuchar (Zlength ob)) (bytes_rep ob) outp;
       Zlib.proof.inflate.Callees.zfuncs gv; data_at_ Tsh tulong vul; data_at_ Tsh tulong vol;
       tables_rep Ers gv; version_lit gv; uversion_lit gv).

Lemma w_tail_ok {Espec : OracleKind} (UF : uw_theory_stmt) gv vcl vol vul bs en dn bn outp expp q inp ob out tl :
  semax Delta_w (w_tail_pre gv vcl vol vul bs en dn bn outp expp q inp ob out tl) w_tail POST_wB.
Proof.
  unfold w_tail, w_tail_pre, POST_wB, POST_w. abbreviate_semax.
  Intros.
  rename H into Hok, H0 into Hbs, H1 into Hcap, H2 into Hobb, H3 into Htl, H4 into Hst,
    H5 into Fen, H6 into Fdn, H7 into Fbn.
  pose proof (Zlength_nonneg bs). pose proof (Zlength_nonneg out). pose proof (Zlength_nonneg tl).
  assert (Hrb: rbytes bs) by (eapply Forall_impl; [ | exact Hbs]; simpl; intros; rep_lia).
  assert (Hob: bytes_ok out) by exact (Zlib.proof.roundtrip.RTCLFacts.rtcl_dfinal_bytes _ _ Hok).
  (* decompressed_len = decompressed_size; source_consumed_len = compressed_len + suffix_len;
     code = uncompress2(decompressed, &decompressed_len, source, &source_consumed_len) *)
  forward. forward. forward.
  rewrite Int64.add_unsigned, !Int64.unsigned_repr by rep_lia.
  assert (Hsl: Zlength (out ++ tl) = Zlength out + Zlength tl) by apply Zlength_app.
  assert (Hsb: bytes_ok (out ++ tl)) by (apply Forall_app; split; auto).
  gather_SEP (if dn then emp else malloc_token _ _ outp) (if dn then emp else data_at _ _ _ outp).
  rewrite (rtw_dest_in dn outp).
  rewrite <- (rtw_bytes_uncompr Ews (Zlength out + Zlength tl) _ inp),
    <- (rtw_tok_uncompr Ews (Zlength out + Zlength tl) inp),
    <- (rtw_ulong_uncompr Tsh _ vol), <- (rtw_ulong_uncompr Tsh _ vul).
  sep_apply (rtw_ig_to gv).
  forward_call (gv, dn, Ews, outp, Zlength ob, bytes_rep ob, Zlength ob, vol, negb dn, false,
                true, Ews, inp, Zlength out + Zlength tl, bytes_rep (out ++ tl), out ++ tl, vul, Ers, Ers).
  { rewrite Hsl. rewrite src_rep_obj. cancel. }
  { unfold dest_ok_w, src_ok_w, bytes_rep, byte_vals. split.
    - destruct dn.
      + destruct Fdn as (-> & ->). repeat split; reflexivity.
      + split; [auto | ]. split; [exact Fdn | ]. split; [pose proof (Zlength_nonneg ob); lia | ].
        split; [discriminate | ]. split; [list_solve | rep_lia].
    - split; [auto | ]. split; [discriminate | ]. split; [list_solve | ]. split; [list_solve | ].
      split; [rep_lia | ]. rewrite sublist_same by list_solve. reflexivity. }
  Intros vret. destruct vret as [[[r2 slen2] dlen2] out2]. simpl fst in *; simpl snd in *.
  rewrite src_rep_obj. flatten_sepcon_in_SEP.
  rtw_law.
  match goal with H: uncompressw_rel _ _ _ _ _ _ |- _ => rename H into Hu end.
  (* uncompress2 of the stream and the bytes after it into at least |data| bytes: Z_MEM_ERROR, or Z_OK with the
     data back and exactly the stream read *)
  destruct (UF bs out (out ++ tl) (Zlength ob) r2 slen2 dlen2 out2 Hok Hrb ltac:(lia)
              ltac:(rewrite sublist_app1, sublist_same by list_solve; reflexivity)
              ltac:(rewrite Hsl; list_solve) Hsb ltac:(rep_lia) ltac:(rep_lia) Hu)
    as [Hm | [(Hr2 & _ & Hd2 & Ho2 & Hs2) | (Hr2 & Hlt & _)]].
  { subst r2. forward_if. { ret0. } { rtw_bad. } }
  2: { lia. }
  subst r2 dlen2 out2 slen2.
  sep_apply (rtw_ig_from gv).
  forward_if.
  { discriminate. }
  rewrite <- (rtw_dest_in dn outp). Intros.
  (* gp_assert(code == Z_OK && decompressed_len == original_len && source_consumed_len == compressed_len) *)
  ifpost _t'22 (Int.repr 1).
  { forward. forward. entailer!. }
  { rtw_bad. }
  ifpost _t'23 (Int.repr 1).
  { forward. forward. forward. entailer!. }
  { rtw_bad. }
  forward_call (Int.repr 1).
  (* gp_assert(bytes_eq(decompressed, original_copy, original_len)): each Z_NULL only for no data *)
  assert (Hda: sublist 0 (Zlength bs) (dest_after (bytes_rep ob) (Zlength ob) bs) = bytes_rep bs)
    by (unfold dest_after, byte_vals, bytes_rep; list_solve).
  rewrite <- (rtw_bytes_adler Ews (Zlength ob) _ outp), <- (rtw_bytes_adler Ews (Zlength bs) _ expp).
  forward_call (dn, outp, Ews, outp, 0, Zlength ob, dest_after (bytes_rep ob) (Zlength ob) bs, bs,
                en, expp, Ews, expp, 0, Zlength bs, bytes_rep bs, bs, Zlength bs).
  { split.
    - destruct dn.
      + destruct Fdn as (-> & ->). rewrite Zlength_nil in Hcap.
        assert (bs = []) as -> by (apply Zlength_nil_inv; pose proof (Zlength_nonneg bs); lia). auto.
      + unfold cbuf_ok. rewrite isptr_offset_val_zero by auto.
        repeat split; auto; try rep_lia.
    - destruct en.
      + destruct Fen as (-> & ->). auto.
      + unfold cbuf_ok. rewrite isptr_offset_val_zero by auto. unfold bytes_rep.
        rewrite sublist_same by list_solve. repeat split; auto; try rep_lia. }
  destruct (list_eq_dec Z.eq_dec bs bs); [ | contradiction].
  forward_call (Int.repr 1).
  rtw_law.
  (* if (decompressed_size > original_len) gp_assert(bytes_eq(decompressed + original_len,
                                                    decompressed_copy + original_len, ...)) *)
  ifsame.
  { match goal with H: Zlength bs < Zlength ob |- _ => rename H into Hgt end.
    (* the output space is larger than the data: decompressed and decompressed_copy are objects *)
    destruct dn; [destruct Fdn as (_ & ->); rewrite Zlength_nil in Hgt; pose proof (Zlength_nonneg bs); lia | ].
    destruct bn; [destruct Fbn as (_ & ->); rewrite Zlength_nil in Hgt; pose proof (Zlength_nonneg bs); lia | ].
    rewrite <- (rtw_bytes_adler Ews (Zlength ob) (dest_after (bytes_rep ob) (Zlength ob) bs) outp),
            <- (rtw_bytes_adler Ews (Zlength ob) (bytes_rep ob) q).
    forward_call (false, offset_val (Zlength bs) outp, Ews, outp, Zlength bs, Zlength ob,
                  dest_after (bytes_rep ob) (Zlength ob) bs, sublist (Zlength bs) (Zlength ob) ob,
                  false, offset_val (Zlength bs) q, Ews, q, Zlength bs, Zlength ob, bytes_rep ob,
                  sublist (Zlength bs) (Zlength ob) ob, Zlength ob - Zlength bs).
    { assert (is_bytes (sublist (Zlength bs) (Zlength ob) ob)) by (apply Forall_sublist; auto).
      unfold cbuf_ok. replace (Zlength bs + (Zlength ob - Zlength bs)) with (Zlength ob) by lia.
      unfold dest_after, byte_vals, bytes_rep.
      repeat split; auto with share; try rep_lia; try (rewrite Zlength_sublist by rep_lia; lia); list_solve. }
    destruct (list_eq_dec Z.eq_dec (sublist (Zlength bs) (Zlength ob) ob) (sublist (Zlength bs) (Zlength ob) ob));
      [ | contradiction].
    forward_call (Int.repr 1).
    rtw_law. entailer!. }
  { forward. entailer!. }
  ret0.
Qed.
