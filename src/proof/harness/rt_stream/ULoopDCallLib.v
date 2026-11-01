(* Law rt_stream (data of any length), main's deflate loop: the facts the proof of its deflate() call
   (ULoopDCall.v) uses.  The objects data and compressed are cut around the call: data's bytes offered
   ([dobj_split]), compressed's output space ([out_ok]).  When no output space is offered, deflate asks for a
   witness that next_out is weakly valid: the byte before next_out once something is written, the malloc token
   of compressed when its capacity is 0, and otherwise (nothing written yet, a nonempty compressed object)
   compressed's first byte, at next_out itself (DSpecV.WVat).  The return code of deflate's model is an int
   ([cd_deflate_code]). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpecV.
Require Import Zlib.proof.harness.rt_stream.UDFacts.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream.UMainStmt.
Require Import Zlib.proof.harness.rt_stream.UMainKit.
Require Import Zlib.harness.rt_stream.code.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.

(** ** The objects data and compressed around the call *)

(* deflate.c's specifications hold the bytes at its compspecs, main at the law's *)
Lemma cd_bytes_cs sh n (v : list val) (q : val) :
  @data_at DCS.CS sh (tarray tuchar n) v q = @data_at LawCS.CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity]. Qed.

Lemma cd_byte_cs sh (v : val) (q : val) :
  @data_at DCS.CS sh tuchar v q = @data_at LawCS.CS sh tuchar v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity]. Qed.

Lemma cd_tok_cs sh n (q : val) :
  @malloc_token DCS.CS sh (tarray tuchar n) q = @malloc_token LawCS.CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_dcs). reflexivity. Qed.

Lemma cd_fc_off n i p :
  field_compatible (tarray tuchar n) [] p -> 0 <= i <= n ->
  field_address0 (Tarray tuchar n noattr) (SUB i) p = offset_val i p.
Proof.
  intros FC Hi. change (Tarray tuchar n noattr) with (tarray tuchar n).
  rewrite arr_field_address0 by (auto; lia). simpl sizeof. f_equal. lia.
Qed.

(* an array of bytes cut at a <= b *)
Lemma cd_arr3 sh n a b (v : list val) p :
  0 <= a <= b -> b <= n -> Zlength v = n ->
  data_at sh (tarray tuchar n) v p =
  !! field_compatible (tarray tuchar n) [] p &&
  (data_at sh (tarray tuchar a) (sublist 0 a v) p *
   data_at sh (tarray tuchar (b - a)) (sublist a b v) (offset_val a p) *
   data_at sh (tarray tuchar (n - b)) (sublist b n v) (offset_val b p)).
Proof.
  intros Hab Hb Hv. apply pred_ext.
  - assert_PROP (field_compatible (tarray tuchar n) [] p) as FC by entailer!.
    change (tarray tuchar n) with (Tarray tuchar n noattr).
    rewrite (split3_data_at_Tarray_tuchar sh n a b v p) by lia.
    rewrite !cd_fc_off by (auto; lia). entailer!.
  - Intros. change (tarray tuchar n) with (Tarray tuchar n noattr).
    rewrite (split3_data_at_Tarray_tuchar sh n a b v p) by lia.
    rewrite !cd_fc_off by (auto; lia). cancel.
Qed.

(* data: the bytes offered and not consumed, [a, b), cut out of the object; the copy expected *)
Definition din_rest (u : setup) (a b : Z) : mpred :=
  malloc_token Ews (tarray tuchar (Zlength (su_data u))) (su_dp u) *
  (!! field_compatible (tarray tuchar (Zlength (su_data u))) [] (su_dp u) &&
   (data_at Ews (tarray tuchar a) (map vi (sublist 0 a (su_data u))) (su_dp u) *
    data_at Ews (tarray tuchar (Zlength (su_data u) - b)) (map vi (sublist b (Zlength (su_data u)) (su_data u)))
      (offset_val b (su_dp u)))) * eobj u.

Lemma dobj_split (u : setup) (a b : Z) :
  0 <= a <= b -> b <= Zlength (su_data u) ->
  dobj u = din_rest u a b *
    @data_at DCS.CS Ews (tarray tuchar (Zlength (sublist a b (su_data u)))) (map vi (sublist a b (su_data u)))
      (offset_val a (su_dp u)).
Proof.
  intros Hab Hb. unfold dobj, din_rest. rewrite cd_bytes_cs.
  rewrite (cd_arr3 Ews (Zlength (su_data u)) a b) by (rewrite ?Zlength_map; lia).
  rewrite !sublist_map, Zlength_sublist by lia.
  apply pred_ext; entailer!.
Qed.

Lemma dobj_join (u : setup) (a b : Z) :
  0 <= a <= b -> b <= Zlength (su_data u) ->
  din_rest u a b *
    @data_at DCS.CS Ews (tarray tuchar (Zlength (sublist a b (su_data u)))) (map vi (sublist a b (su_data u)))
      (offset_val a (su_dp u))
  |-- dobj u.
Proof. intros Hab Hb. rewrite (dobj_split u a b) by lia. apply derives_refl. Qed.

(* compressed: the output space offered (avail_out bytes at next_out = compressed + |O|), its frame [Fo], and
   deflate_specV's witness [W] that next_out is weakly valid when there is no output space; after the call,
   O followed by the bytes written *)
Definition out_ok (u : setup) (O : list Z) (aout : Z) (Fo : mpred) (W : wvw2) : Prop :=
  (Zlength (Zrepeat Vundef aout) = 0 -> wv2_ok W) /\
  (cobj u O |-- Fo *
     @data_at DCS.CS Ews (tarray tuchar (Zlength (Zrepeat Vundef aout))) (Zrepeat Vundef aout)
       (offset_val (Zlength O) (su_cp u)) * wv2_at W (offset_val (Zlength O) (su_cp u))) /\
  (forall z, Zlength z <= aout ->
     Fo * @data_at DCS.CS Ews (tarray tuchar (Zlength (Zrepeat Vundef aout)))
            (map vi z ++ sublist (Zlength z) (Zlength (Zrepeat Vundef aout)) (Zrepeat Vundef aout))
            (offset_val (Zlength O) (su_cp u)) *
     wv2_at W (offset_val (Zlength O) (su_cp u))
     |-- cobj u (O ++ z)).

Lemma out_ok_ex (u : setup) (O : list Z) (aout : Z) :
  isptr (su_cp u) -> 0 <= aout -> Zlength O + aout <= su_cap u ->
  exists Fo W, out_ok u O aout Fo W.
Proof.
  intros Pc Ha Hc.
  assert (HO := Zlength_nonneg O).
  set (k := Zlength O) in *. set (c := su_cap u) in *.
  destruct (Z_lt_le_dec 0 aout) as [Ha0 | Ha0].
  - (* output space offered: no witness needed *)
    exists (malloc_token Ews (tarray tuchar c) (su_cp u) *
            (!! field_compatible (tarray tuchar c) [] (su_cp u) &&
             (data_at Ews (tarray tuchar k) (map vi O) (su_cp u) *
              data_at Ews (tarray tuchar (c - (k + aout))) (Zrepeat Vundef (c - (k + aout)))
                (offset_val (k + aout) (su_cp u))))), (WVold WVnone).
    split3.
    + rewrite Zlength_Zrepeat by lia. lia.
    + unfold cobj, cbytes. fold c.
      rewrite cd_bytes_cs. unfold wv2_at, wv_at. rewrite Zlength_Zrepeat by lia. fold k.
      rewrite (cd_arr3 Ews c k (k + aout)) by (subst k; list_solve).
      replace (sublist 0 k (map vi O ++ Zrepeat Vundef (c - k))) with (map vi O) by (subst k; list_solve).
      replace (sublist k (k + aout) (map vi O ++ Zrepeat Vundef (c - k))) with (Zrepeat Vundef aout)
        by (subst k; list_solve).
      replace (sublist (k + aout) c (map vi O ++ Zrepeat Vundef (c - k))) with (Zrepeat Vundef (c - (k + aout)))
        by (subst k; list_solve).
      replace (k + aout - k) with aout by lia.
      entailer!.
    + intros z Hz. unfold cobj, cbytes. fold c.
      rewrite cd_bytes_cs. unfold wv2_at, wv_at. rewrite Zlength_Zrepeat by lia. fold k.
      Intros. assert (Hz0 := Zlength_nonneg z).
      set (v := map vi (O ++ z) ++ Zrepeat Vundef (c - Zlength (O ++ z))).
      rewrite (cd_arr3 Ews c k (k + aout) v) by (subst v k; list_solve).
      replace (sublist 0 k v) with (map vi O) by (subst v k; list_solve).
      replace (sublist k (k + aout) v) with (map vi z ++ sublist (Zlength z) aout (Zrepeat Vundef aout))
        by (subst v k; list_solve).
      replace (sublist (k + aout) c v) with (Zrepeat Vundef (c - (k + aout))) by (subst v k; list_solve).
      replace (k + aout - k) with aout by lia.
      entailer!.
  - assert (aout = 0) by lia. subst aout.
    destruct (Z_lt_le_dec 0 k) as [Hk | Hk].
    + (* no output space after a nonempty O: the witness is O's last byte, just before next_out *)
      exists (malloc_token Ews (tarray tuchar c) (su_cp u) *
              (!! field_compatible (tarray tuchar c) [] (su_cp u) &&
               (data_at Ews (tarray tuchar (k - 1)) (map vi (sublist 0 (k - 1) O)) (su_cp u) *
                data_at Ews (tarray tuchar (c - k)) (Zrepeat Vundef (c - k)) (offset_val k (su_cp u))))),
        (WVold (WVbefore Ews (vi (Znth (k - 1) O)))).
      split3.
      * intros _. simpl. auto with share.
      * unfold cobj, cbytes. fold c.
        rewrite cd_bytes_cs. unfold wv2_at, wv_at. rewrite cd_byte_cs. fold k.
        change (Zrepeat Vundef 0) with (@nil val). rewrite Zlength_nil.
        rewrite data_at_tuchar_zero_array_eq by (rewrite isptr_offset_val; auto).
        rewrite offset_offset_val. replace (k + -1) with (k - 1) by lia.
        set (v := map vi O ++ Zrepeat Vundef (c - Zlength O)).
        rewrite (cd_arr3 Ews c (k - 1) k v) by (subst v k; list_solve).
        replace (sublist 0 (k - 1) v) with (map vi (sublist 0 (k - 1) O)) by (subst v k; list_solve).
        replace (sublist (k - 1) k v) with [vi (Znth (k - 1) O)] by (subst v k; list_solve).
        replace (sublist k c v) with (Zrepeat Vundef (c - k)) by (subst v k; list_solve).
        replace (k - (k - 1)) with 1 by lia.
        erewrite data_at_singleton_array_eq by reflexivity.
        entailer!.
      * intros z Hz. assert (z = []) by (apply Zlength_nil_inv; pose proof (Zlength_nonneg z); lia). subst z.
        unfold cobj, cbytes. rewrite (app_nil_r O). fold c.
        rewrite cd_bytes_cs. unfold wv2_at, wv_at. rewrite cd_byte_cs. fold k.
        change (Zrepeat Vundef 0) with (@nil val). change (map vi [] ++ sublist (Zlength (@nil Z)) (Zlength (@nil val)) []) with (@nil val).
        rewrite Zlength_nil.
        rewrite data_at_tuchar_zero_array_eq by (rewrite isptr_offset_val; auto).
        rewrite offset_offset_val. replace (k + -1) with (k - 1) by lia.
        Intros.
        set (v := map vi O ++ Zrepeat Vundef (c - Zlength O)).
        rewrite (cd_arr3 Ews c (k - 1) k v) by (subst v k; list_solve).
        replace (sublist 0 (k - 1) v) with (map vi (sublist 0 (k - 1) O)) by (subst v k; list_solve).
        replace (sublist (k - 1) k v) with [vi (Znth (k - 1) O)] by (subst v k; list_solve).
        replace (sublist k c v) with (Zrepeat Vundef (c - k)) by (subst v k; list_solve).
        replace (k - (k - 1)) with 1 by lia.
        erewrite data_at_singleton_array_eq by reflexivity.
        entailer!.
    + (* no output space and nothing written *)
      assert (k = 0) by lia. assert (O = []) by (apply Zlength_nil_inv; subst k; lia). subst O.
      destruct (Z_lt_le_dec 0 c) as [Hc0 | Hc0].
      * (* a nonempty compressed object: the witness is its first byte, at next_out *)
        exists (malloc_token Ews (tarray tuchar c) (su_cp u) *
                (!! field_compatible (tarray tuchar c) [] (su_cp u) &&
                 data_at Ews (tarray tuchar (c - 1)) (Zrepeat Vundef (c - 1)) (offset_val 1 (su_cp u)))),
          (WVat Ews Vundef).
        split3.
        -- intros _. simpl. auto with share.
        -- unfold cobj, cbytes, wv2_at. fold c. subst k.
           change (Zrepeat Vundef 0) with (@nil val).
           rewrite !Zlength_nil, isptr_offset_val_zero by auto.
           rewrite cd_bytes_cs, cd_byte_cs.
           set (v := map vi [] ++ Zrepeat Vundef (c - 0)).
           rewrite (cd_arr3 Ews c 0 1 v) by (subst v; list_solve).
           replace (sublist 0 0 v) with (@nil val) by (subst v; list_solve).
           replace (sublist 0 1 v) with [Vundef] by (subst v; list_solve).
           replace (sublist 1 c v) with (Zrepeat Vundef (c - 1)) by (subst v; list_solve).
           replace (1 - 0) with 1 by lia.
           erewrite data_at_singleton_array_eq by reflexivity.
           rewrite isptr_offset_val_zero by auto.
           entailer!.
        -- intros z Hz. assert (z = []) by (apply Zlength_nil_inv; pose proof (Zlength_nonneg z); lia). subst z.
           unfold cobj, cbytes, wv2_at. fold c. subst k.
           change (map vi [] ++ sublist (Zlength (@nil Z)) (Zlength (Zrepeat Vundef 0)) (Zrepeat Vundef 0))
             with (@nil val).
           change (Zrepeat Vundef 0) with (@nil val). rewrite (app_nil_r (@nil Z)).
           rewrite !Zlength_nil, isptr_offset_val_zero by auto.
           rewrite cd_bytes_cs, cd_byte_cs. Intros.
           set (v := map vi [] ++ Zrepeat Vundef (c - 0)).
           rewrite (cd_arr3 Ews c 0 1 v) by (subst v; list_solve).
           replace (sublist 0 0 v) with (@nil val) by (subst v; list_solve).
           replace (sublist 0 1 v) with [Vundef] by (subst v; list_solve).
           replace (sublist 1 c v) with (Zrepeat Vundef (c - 1)) by (subst v; list_solve).
           replace (1 - 0) with 1 by lia.
           erewrite data_at_singleton_array_eq by reflexivity.
           rewrite isptr_offset_val_zero by auto.
           entailer!.
      * (* capacity 0: the witness is compressed's malloc token *)
        assert (c = 0) by lia.
        exists (data_at Ews (tarray tuchar 0) [] (su_cp u)), (WVold (WVtok (tarray tuchar 0))).
        split3.
        -- intros _. simpl. lia.
        -- unfold cobj, cbytes, wv2_at, wv_at. fold c. rewrite H0. subst k.
           rewrite Zlength_nil, isptr_offset_val_zero by auto.
           change (map vi [] ++ Zrepeat Vundef (0 - 0)) with (@nil val). change (Zrepeat Vundef 0) with (@nil val).
           rewrite Zlength_nil, cd_bytes_cs, cd_tok_cs.
           rewrite (data_at_tuchar_zero_array_eq Ews (su_cp u) Pc) at 2. cancel.
        -- intros z Hz. assert (z = []) by (apply Zlength_nil_inv; pose proof (Zlength_nonneg z); lia). subst z.
           unfold cobj, cbytes, wv2_at, wv_at. fold c. rewrite H0. subst k.
           rewrite Zlength_nil, isptr_offset_val_zero by auto.
           change (map vi ([] ++ []) ++ Zrepeat Vundef (0 - Zlength (@nil Z ++ []))) with (@nil val).
           change (map vi [] ++ sublist (Zlength (@nil Z)) (Zlength (Zrepeat Vundef 0)) (Zrepeat Vundef 0))
             with (@nil val).
           change (Zrepeat Vundef 0) with (@nil val).
           rewrite Zlength_nil, cd_bytes_cs, cd_tok_cs.
           rewrite (data_at_tuchar_zero_array_eq Ews (su_cp u) Pc). cancel.
Qed.

(** ** The compressor around the call *)

Lemma cd_hdr (s : dstate) (hx : share * val * val * val) :
  d_gzhead s = None -> hdr_at (Some s) nullval hx = emp.
Proof. intros H. unfold hdr_at. rewrite H. apply pred_ext; entailer!. Qed.

Lemma cd_dstream_sp_fold lvl os strmp ghp sp gv :
  dstream_sp lvl os strmp ghp sp gv |-- dstream lvl os strmp ghp gv.
Proof. rewrite dstream_sp_eq. Exists sp. cancel. Qed.

(** ** The return codes of deflate's model *)
(* deflate() returns one of Z_OK, Z_STREAM_END, Z_STREAM_ERROR, Z_BUF_ERROR: an int (DK's range of code) *)
(* the model's loops have 2^40 iterations of fuel: the kernel must never unfold them *)
Local Strategy opaque [Zlib.proof.deflate.DLoop.loop Zlib.proof.deflate.DLoop.loop2 Zlib.proof.deflate.DLoop.FUEL].

Definition cd_cok (r : option dres) : Prop := forall s z c, r = Some (s, z, Some c) -> -6 <= c <= 2.

Ltac cd_code_end :=
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
  unfold Zlib.proof.deflate.DState.Z_OK, Zlib.proof.deflate.DState.Z_STREAM_END,
         Zlib.proof.deflate.DState.Z_STREAM_ERROR, Zlib.proof.deflate.DState.Z_BUF_ERROR; lia.

Ltac cd_cok_run :=
  repeat match goal with
    | E : Some _ = Some _ |- _ => injection E; clear E; intros; subst
    | E : None = Some _ |- _ => discriminate E
    | E : bind ?a _ = Some _ |- _ => let H := fresh in destruct a eqn:H; cbv beta iota zeta delta [bind] in E
    | E : (if ?b then _ else _) = Some _ |- _ => let H := fresh in destruct b eqn:H
    | E : (match ?x with _ => _ end) = Some _ |- _ => let H := fresh in destruct x eqn:H
    | E : _ = Some _ |- _ =>
        progress (cbv beta iota zeta delta [bind then_stage guard c_flush_or_return c_gzhead c_deflate_str] in E)
    end;
  try cd_code_end.

Ltac cd_cok_tac := intros ? ? ? ?; cd_cok_run.

Lemma cd_cok_then (r : option dres) (k : dstate -> strm -> option dres) :
  cd_cok r -> (forall s z, cd_cok (k s z)) -> cd_cok (then_stage r k).
Proof.
  unfold cd_cok, then_stage, bind. intros Hr Hk s z c E.
  destruct r as [[[s0 z0] [c0|]]|]; [ | eapply Hk; eauto | discriminate].
  injection E as <- <- <-. eapply Hr; reflexivity.
Qed.

Lemma cd_cok_entry s z f : cd_cok (c_deflate_entry s z f).
Proof. unfold c_deflate_entry. cd_cok_tac. Qed.
Lemma cd_cok_zlib s z : cd_cok (c_deflate_zlib_header s z).
Proof. unfold c_deflate_zlib_header. cd_cok_tac. Qed.
Lemma cd_cok_gzip s z : cd_cok (c_deflate_gzip_header s z).
Proof. unfold c_deflate_gzip_header. cd_cok_tac. Qed.
Lemma cd_cok_extra s z : cd_cok (c_deflate_extra s z).
Proof. unfold c_deflate_extra. cd_cok_tac. Qed.
Lemma cd_cok_name s z : cd_cok (c_deflate_name s z).
Proof. unfold c_deflate_name. cd_cok_tac. Qed.
Lemma cd_cok_comment s z : cd_cok (c_deflate_comment s z).
Proof. unfold c_deflate_comment. cd_cok_tac. Qed.
Lemma cd_cok_hcrc s z : cd_cok (c_deflate_hcrc s z).
Proof. unfold c_deflate_hcrc. cd_cok_tac. Qed.
Lemma cd_cok_compress s z f : cd_cok (c_deflate_compress s z f).
Proof. unfold c_deflate_compress. cd_cok_tac. Qed.

Lemma cd_trailer_code s z f s' z' c : c_deflate_trailer s z f = Some (s', z', c) -> -6 <= c <= 2.
Proof. unfold c_deflate_trailer. intros E. cd_cok_run. Qed.

Lemma cd_deflate_code s z f s' z' c : c_deflate s z f = Some (s', z', c) -> -6 <= c <= 2.
Proof.
  unfold c_deflate. intros E.
  destruct (_ || _ || _)%bool.
  { injection E; intros; subst; cd_code_end. }
  match type of E with
  | bind ?r _ = _ =>
      assert (Hr : cd_cok r)
        by (repeat (apply cd_cok_then; intros);
            first [ apply cd_cok_entry | apply cd_cok_zlib | apply cd_cok_gzip | apply cd_cok_extra
                  | apply cd_cok_name | apply cd_cok_comment | apply cd_cok_hcrc | apply cd_cok_compress ]);
      destruct r as [[[s1 z1] [r1|]]|]; cbv beta iota delta [bind] in E
  end.
  - injection E; intros; subst. eapply Hr; reflexivity.
  - eapply cd_trailer_code; exact E.
  - discriminate E.
Qed.

