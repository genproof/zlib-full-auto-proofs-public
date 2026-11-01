(* Law rt_roundtrip (data of any length), main (WMain.v): the segment of the test `if ((original_copy == NULL &&
   original_len > 0) || compressed == NULL || (decompressed == NULL && decompressed_size > 0)) return 0`, of
   `decompressed_copy = copy_of(decompressed, decompressed_size)` (CopyOfNull.copy_of_spec_n: decompressed may be
   Z_NULL when decompressed_size is 0) and of its test `if (decompressed_copy == NULL && decompressed_size > 0)
   return 0`; then WMainMid.w_mid_ok (compress2).  main's proof is cut there to keep each file's check short. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.compress.CSpec.
Require Import Zlib.proof.roundtrip.RTCSpec Zlib.proof.roundtrip.RTCSpecW.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.uncompr.USpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.laws_common.CopyOfNull.
Require Import Zlib.proof.roundtrip.RTC2W Zlib.proof.roundtrip.RTC2WFinal Zlib.proof.uncompr.UTheoryW.
Require Import Zlib.proof.harness.rt_roundtrip.WCS Zlib.proof.harness.rt_roundtrip.WMainDefs
        Zlib.proof.harness.rt_roundtrip.WMainTail
        Zlib.proof.harness.rt_roundtrip.WMainMid.
Require Import Zlib.proof.harness.rt_roundtrip.WMainCopy.
Require Import Zlib.proof.harness.rt_roundtrip.WMainInput.
Require Import Zlib.harness.rt_roundtrip.code.
#[local] Existing Instance Zlib.proof.harness.rt_roundtrip.WCS.CS.
Local Open Scope logic.

(* the tests `x > 0` on an unsigned long, and the value of an int test *)
Lemma rtw_gt0 a: 0 <= a <= Int64.max_unsigned ->
  bool2val (Int64.cmpu Cgt (Int64.repr a) (Int64.repr 0)) = Vint (Int.repr (if 0 <? a then 1 else 0)).
Proof.
  intros A. unfold Int64.cmpu, Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
  destruct (zlt 0 a), (Z.ltb_spec 0 a); try lia; reflexivity.
Qed.

Lemma rtw_true (b: bool): Int.repr (if b then 1 else 0) <> Int.zero -> b = true.
Proof. destruct b; [auto | intros H; contradiction H; reflexivity]. Qed.

Lemma rtw_false (b: bool): Int.repr (if b then 1 else 0) = Int.zero -> b = false.
Proof. destruct b; [intros H; discriminate H | auto]. Qed.

Ltac rtw_tf E := match goal with
  | H: Int.repr (if ?b then 1 else 0) <> Int.zero |- _ => apply rtw_true in H; rename H into E
  | H: Int.repr (if ?b then 1 else 0) = Int.zero |- _ => apply rtw_false in H; rename H into E
  end.

(* the statements from the test `if ((original_copy == NULL && original_len > 0) || ...)` *)
Definition w_null : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [w_drop w_chain f_main fn_body] in
          (w_drop 12 (w_chain (fn_body f_main))) in exact x).

(* before that test: the inputs drawn (original_len n, decompressed_size cap >= n, level v - 1), the data bs (Z_NULL
   only when empty: flag sn), copy_of, malloc and alloc_any_bytes returned (decompressed Z_NULL also when cap = 0
   and null_if_empty asked for it), each result Z_NULL or an object *)
Definition w_null_pre (gv : globals) (vcl vol vul : val) (n : Z) (bs : list Z) (cap v : Z) (sn : bool)
    (datap compp outp expp : val) (ob : list Z) : environ -> mpred :=
  PROP (Zlength bs = n; is_bytes bs; 0 <= n <= cap; cap <= 9223372036854775807; 0 <= v <= 10; Zlength ob = cap;
        is_bytes ob; if sn then datap = nullval /\ bs = [] else isptr datap)
  LOCAL (temp _decompressed outp; temp _compressed compp; temp _original_copy expp; temp _original datap;
         temp _compressed_bound (Vlong (Int64.repr (c_compressBound n)));
         temp _level (Vint (Int.repr (v - 1)));
         temp _decompressed_size (Vlong (Int64.repr cap));
         temp _original_len (Vlong (Int64.repr n));
         lvar _source_consumed_len tulong vul; lvar _decompressed_len tulong vol; lvar _compressed_len tulong vcl;
         gvars gv)
  SEP (mem_mgr gv;
       if eq_dec outp nullval then emp
       else malloc_token Ews (tarray tuchar cap) outp * data_at Ews (tarray tuchar cap) (bytes_rep ob) outp;
       if eq_dec compp nullval then emp
       else malloc_token Ews (tarray tuchar (c_compressBound n)) compp *
            data_at_ Ews (tarray tuchar (c_compressBound n)) compp;
       if eq_dec expp nullval then emp
       else malloc_token Ews (tarray tuchar n) expp * data_at Ews (tarray tuchar n) (bytes_rep bs) expp;
       if sn then emp else malloc_token Ews (tarray tuchar n) datap;
       if sn then emp else data_at Ews (tarray tuchar n) (bytes_rep bs) datap;
       Zlib.proof.inflate.Callees.zfuncs gv; data_at_ Tsh tulong vul; data_at_ Tsh tulong vol;
       data_at_ Tsh tulong vcl; deflate_globals gv; cversion_lit gv; tables_rep Ers gv; version_lit gv;
       uversion_lit gv).

Lemma w_null_ok {Espec : OracleKind} (CB : c2w_bound_stmt) (CF : c2w_final_stmt) (UF : uw_theory_stmt)
    gv vcl vol vul n bs cap v sn datap compp outp expp ob :
  semax Delta_w (w_null_pre gv vcl vol vul n bs cap v sn datap compp outp expp ob) w_null POST_wB.
Proof.
  unfold w_null, w_null_pre, POST_wB, POST_w. abbreviate_semax.
  Intros.
  (* Intros substituted n = |bs| and cap = |ob| *)
  match goal with H: if sn then _ else _ |- _ => rename H into Fsn end.
  try subst n. try subst cap.
  pose proof (rtw_cb_range (Zlength bs) ltac:(rep_lia)) as Hcb.
  set (cb := c_compressBound (Zlength bs)) in *.
  (* the three results: Z_NULL (flags en, cn, dn) or objects *)
  assert (He: exists en: bool, if en then expp = nullval else expp <> nullval)
    by (destruct (eq_dec expp nullval); [exists true | exists false]; auto).
  destruct He as [en He]. rewrite (rtw_if_null en expp) by exact He.
  assert (Hc: exists cn: bool, if cn then compp = nullval else compp <> nullval)
    by (destruct (eq_dec compp nullval); [exists true | exists false]; auto).
  destruct Hc as [cn Hc]. rewrite (rtw_if_null cn compp) by exact Hc.
  assert (Hd: exists dn: bool, if dn then outp = nullval else outp <> nullval)
    by (destruct (eq_dec outp nullval); [exists true | exists false]; auto).
  destruct Hd as [dn Hd]. rewrite (rtw_if_null dn outp) by exact Hd.
  rewrite !rtw_if_split. Intros.
  (* if ((original_copy == NULL && original_len > 0) || compressed == NULL ||
         (decompressed == NULL && decompressed_size > 0)) return 0; *)
  ifpost _t'12 (Int.repr (if (en && (0 <? Zlength bs))%bool then 1 else 0)).
  { destruct en.
    - rewrite He. entailer!.
    - eapply (@malloc_test_eq CS _ (Zlength bs)); [lia | ].
      sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength bs)) (bytes_rep bs) expp). cancel. }
  { destruct en; [ | congruence]. forward. entailer!. rewrite rtw_gt0 by rep_lia. reflexivity. }
  { forward. destruct en; [congruence | ]. entailer!. }
  ifpost _t'13 (Int.repr (if ((en && (0 <? Zlength bs)) || cn)%bool then 1 else 0)).
  { rtw_tf E. forward. entailer!. rewrite E. reflexivity. }
  { rtw_tf E. rewrite E. simpl orb. forward.
    { destruct cn.
      - rewrite Hc. entailer!.
      - entailer!. }
    entailer!. rewrite E. destruct cn; simpl orb.
    { rewrite Hc. split; reflexivity. }
    destruct compp; try contradiction; try (simpl in PNcompp; subst; contradiction Hc; reflexivity).
    split; reflexivity. }
  ifpost _t'14 (Int.repr (if ((en && (0 <? Zlength bs)) || cn || (dn && (0 <? Zlength ob)))%bool then 1 else 0)).
  { rtw_tf E. forward. entailer!. rewrite E. reflexivity. }
  { rtw_tf E. rewrite E. simpl orb.
    forward_if.
    { destruct dn.
      - rewrite Hd. entailer!.
      - eapply (@malloc_test_eq CS _ (Zlength ob)); [lia | ].
        sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength ob)) (bytes_rep ob) outp). cancel. }
    { destruct dn; [ | congruence]. forward. forward. entailer!. rewrite rtw_gt0 by rep_lia.
      rewrite E. simpl. destruct (0 <? Zlength ob); split; reflexivity. }
    { forward. destruct dn; [congruence | ]. entailer!. rewrite E. split; reflexivity. } }
  forward_if.
  { ret0. }
  rtw_tf E. apply orb_false_iff in E. destruct E as [E12 E3]. apply orb_false_iff in E12. destruct E12 as [E1 E2].
  subst cn.
  assert (Hen: en = true -> bs = []).
  { intros ->. simpl in E1. apply Z.ltb_ge in E1. apply Zlength_nil_inv. pose proof (Zlength_nonneg bs). lia. }
  assert (Hdn: dn = true -> ob = []).
  { intros ->. simpl in E3. apply Z.ltb_ge in E3. apply Zlength_nil_inv. pose proof (Zlength_nonneg ob). lia. }
  clear E1 E3.
  (* decompressed_copy = copy_of(decompressed, decompressed_size) *)
  assert_PROP (dn = false -> isptr outp) as Po by (destruct dn; entailer!).
  rewrite <- (rtw_bytes_adler Ews (Zlength ob) (bytes_rep ob) outp).
  forward_call (dn, outp, Ews, outp, 0, Zlength ob, bytes_rep ob, Zlength ob, ob, gv).
  { destruct dn.
    - rewrite (Hdn eq_refl). auto.
    - unfold cbuf_ok. rewrite isptr_offset_val_zero by exact (Po eq_refl).
      unfold bytes_rep. repeat split; auto; try rep_lia; try list_solve. }
  Intros q. rtw_law.
  (* if (decompressed_copy == NULL && decompressed_size > 0) return 0; *)
  assert (Hb: exists bn: bool, if bn then q = nullval else q <> nullval)
    by (destruct (eq_dec q nullval); [exists true | exists false]; auto).
  destruct Hb as [bn Hb]. rewrite (rtw_if_null bn q) by exact Hb.
  rewrite (rtw_if_split bn). Intros.
  ifpost _t'16 (Int.repr (if (bn && (0 <? Zlength ob))%bool then 1 else 0)).
  { destruct bn.
    - rewrite Hb. entailer!.
    - eapply (@malloc_test_eq CS _ (Zlength ob)); [lia | ].
      sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength ob)) (bytes_rep ob) q). cancel. }
  { destruct bn; [ | congruence]. forward. entailer!. rewrite rtw_gt0 by rep_lia. reflexivity. }
  { forward. destruct bn; [congruence | ]. entailer!. }
  forward_if.
  { ret0. }
  rtw_tf E. assert (Hbn: bn = true -> ob = []).
  { intros ->. simpl in E. apply Z.ltb_ge in E. apply Zlength_nil_inv. pose proof (Zlength_nonneg ob). lia. }
  clear E.
  (* the objects' pointers *)
  assert_PROP (isptr compp) as Pc by entailer!.
  assert_PROP (if en then expp = nullval /\ bs = [] else isptr expp) as Fen.
  { destruct en; entailer!. }
  assert_PROP (if dn then outp = nullval /\ ob = [] else isptr outp) as Fdn.
  { destruct dn; entailer!. }
  assert_PROP (if bn then q = nullval /\ ob = [] else isptr q) as Fbn.
  { destruct bn; entailer!. }
  (* the rest: w_mid_ok *)
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply (w_mid_ok CB CF UF gv vcl vol vul bs v sn en dn bn datap compp outp expp q ob)].
  unfold w_mid_pre. subst cb. entailer!.
Qed.
