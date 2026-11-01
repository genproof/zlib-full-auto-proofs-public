(* Law res_memory_deflate: the rest of an iteration of main's loop (MemKit.body_call_stmt): deflate(&strm,
   (int) nondet_u32()) on the piece offered (defined by the invariant of deflate/AnyCalls.v), the check of
   count.peak (PeakExact.check_true_exact), read += take - strm.avail_in, free(out); back to the invariant. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.za.deflate.Stmt.
Require Import Zlib.proof.deflate.AnyCalls.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.counted.Spec.
Require Import Zlib.proof.harness.counted.Kit.
Require Import Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.res_alloc_deflate.ACS.
Require Import Zlib.proof.harness.res_alloc_deflate.Specs.
Require Import Zlib.proof.harness.res_alloc_deflate.Gmain.
Require Import Zlib.proof.harness.res_alloc_deflate.InitFacts.
Require Import Zlib.proof.harness.res_alloc_deflate.StrmKit.
Require Import Zlib.proof.harness.res_alloc_deflate.MainKit.
Require Import Zlib.proof.harness.res_memory_deflate.Peak.
Require Import Zlib.proof.harness.res_memory_deflate.PeakExact.
Require Import Zlib.proof.harness.res_memory_deflate.MainStmt.
Require Import Zlib.proof.harness.res_memory_deflate.MemKit.
Require Zlib.contracts.res_memory_deflate.
Require Import Zlib.harness.res_memory_deflate.code.
Local Open Scope logic.
Local Ltac simplify_remove_localdef_temp ::= mem_simplify_rlt.


(* the data as three objects: the bytes consumed so far, the piece offered to deflate() and the rest *)
Lemma data_split3 (dp : val) (bs : list Z) (r t : Z) :
  0 <= r -> 0 <= t -> r + t <= Zlength bs -> @field_compatible DCS.CS (tarray tuchar (Zlength bs)) [] dp ->
  @data_at DCS.CS Ews (tarray tuchar (Zlength bs)) (map vi bs) dp =
  (@data_at DCS.CS Ews (tarray tuchar r) (map vi (sublist 0 r bs)) dp *
   @data_at DCS.CS Ews (tarray tuchar (Zlength (sublist r (r + t) bs))) (map vi (sublist r (r + t) bs))
     (offset_val r dp) *
   @data_at DCS.CS Ews (tarray tuchar (Zlength bs - (r + t))) (map vi (sublist (r + t) (Zlength bs) bs))
     (offset_val (r + t) dp))%logic.
Proof.
  intros H1 H2 H3 FC. unfold tarray.
  rewrite (@split3_data_at_Tarray_tuchar DCS.CS Ews (Zlength bs) r (r + t) (map vi bs) dp)
    by (rewrite ?Zlength_map; lia).
  change (Tarray tuchar (Zlength bs) noattr) with (tarray tuchar (Zlength bs)).
  rewrite arr_field_address0 by (auto; lia). rewrite arr_field_address0 by (auto; lia).
  change (sizeof tuchar) with 1. rewrite !Z.mul_1_l. rewrite !sublist_map.
  rewrite Zlength_sublist by lia. replace (r + t - r) with t by lia. reflexivity.
Qed.

(* malloc's output space, as deflate() takes it: its bytes at DCS.CS, the weak-validity witness [out_wv] (the
   token, when the space is empty), and the token kept for free() otherwise *)
Definition out_tok (room : Z) (out : val) : mpred :=
  if room =? 0 then emp else @malloc_token CSa Ews (tarray tuchar room) out.

Lemma out_open (room : Z) (out : val) :
  (@malloc_token CSa Ews (tarray tuchar room) out * @data_at_ CSa Ews (tarray tuchar room) out)%logic
  |-- (@data_at DCS.CS Ews (tarray tuchar room) (Zrepeat Vundef room) out * wv_at (out_wv room) out *
       out_tok room out)%logic.
Proof.
  rewrite (data_at__tuchar_cs CSa DCS.CS).
  unfold data_at_, field_at_.
  change (@default_val DCS.CS (tarray tuchar room)) with (Zrepeat Vundef room).
  fold (@data_at DCS.CS Ews (tarray tuchar room) (Zrepeat Vundef room) out).
  unfold out_wv, out_tok, wv_at. destruct (Z.eqb_spec room 0).
  - subst room.
    rewrite <- (@malloc_token_change_composite DCS.CS CSa CC_dcs Ews (tarray tuchar 0)) by reflexivity.
    cancel.
  - cancel.
Qed.

Lemma out_close (room : Z) (out : val) (X : list val) :
  (@data_at DCS.CS Ews (tarray tuchar room) X out * wv_at (out_wv room) out * out_tok room out)%logic
  |-- (@malloc_token CSa Ews (tarray tuchar room) out * @data_at_ CSa Ews (tarray tuchar room) out)%logic.
Proof.
  sep_apply (@data_at_data_at_ DCS.CS). rewrite (data_at__tuchar_cs DCS.CS CSa).
  unfold out_wv, out_tok, wv_at. destruct (Z.eqb_spec room 0).
  - subst room.
    rewrite <- (@malloc_token_change_composite DCS.CS CSa CC_dcs Ews (tarray tuchar 0)) by reflexivity.
    cancel.
  - cancel.
Qed.

(* the application's avail_in, as main reads it (strm.avail_in at CSa), lent by the members deflate() left *)
Lemma api_avail_open (sp nin : val) (ain tin : Z) (nout : val) (aout tout : Z) (msgv : val) (adler : Z) :
  api_fields sp nin ain tin nout aout tout msgv adler |--
  (!! (u32_ok ain) &&
   (@field_at CSa Ews (Tstruct _z_stream_s noattr) (DOT _avail_in) (Vint (Int.repr ain)) sp *
    (@field_at CSa Ews (Tstruct _z_stream_s noattr) (DOT _avail_in) (Vint (Int.repr ain)) sp -*
     api_fields sp nin ain tin nout aout tout msgv adler)))%logic.
Proof.
  assert (E : @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_in) (vi ain) sp =
              @field_at CSa Ews (Tstruct _z_stream_s noattr) (DOT _avail_in) (Vint (Int.repr ain)) sp).
  { apply (f_equal (fun f => f sp)).
    apply (@field_at_change_composite DCS.CS CSa CC_dcs); [apply JMeq_refl | reflexivity]. }
  unfold api_fields at 1. Intros. apply andp_right; [apply prop_right; tauto | ].
  rewrite E.
  apply (wand_lend _ _ _ (!! (u32_ok ain /\ u64_ok tin /\ u32_ok aout /\ u64_ok tout /\ u64_ok adler) &&
     (@field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_in) nin sp *
      @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._total_in) (vl tin) sp *
      @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_out) nout sp *
      @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_out) (vi aout) sp *
      @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._total_out) (vl tout) sp *
      @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._msg) msgv sp *
      @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._adler) (vl adler) sp))).
  - rewrite prop_true_andp by tauto. cancel.
  - unfold api_fields. Intros. rewrite prop_true_andp by tauto. rewrite E. cancel.
Qed.

(* without a gzip header (any_calls' ac_gzhead), deflate()'s hdr_at is empty *)
Lemma hdr_none (s : dstate) (hx : share * val * val * val) :
  d_gzhead s = None -> hdr_at (Some s) nullval hx = emp.
Proof. intros E. unfold hdr_at. rewrite E. rewrite prop_true_andp by auto. reflexivity. Qed.

Lemma mem_body_call : body_call_stmt.
Proof.
  intros Espec K gv cp p dp bs mem W tr spp L ci AC.
  destruct L as [s read tout adler msg msgv], ci as [take room out].
  unfold C_at, C_loc, C_sep, J_loc, lsuf5, Delta_m, strm_offered, out_obj.
  cbn [ms_s ms_read ms_tout ms_adler ms_msg ms_msgv ci_take ci_room ci_out].
  abbreviate_semax.
  Intros.
  destruct H as [[[HB [Hby [Hdp [HW [Hm Hpk]]]]] [HK [Hrd [Htout Hmsg]]]] [Ht [Hr Hout]]].
  cbn [ms_s ms_read ms_tout ms_adler ms_msg ms_msgv ci_take ci_room ci_out] in *.
  assert_PROP (@field_compatible DCS.CS (tarray tuchar (Zlength bs)) [] dp) as FCd by entailer!.
  set (inb := sublist read (read + take) bs).
  assert (Hinb : Zlength inb = take) by (unfold inb; rewrite Zlength_sublist; lia).
  assert (Hinbb : bytes inb) by (apply Forall_sublist; auto).
  rewrite (data_split3 dp bs read take) by (auto; lia). fold inb.
  sep_apply (out_open room out).
  replace (api_fields p (offset_val read dp)) with (api_fields p (offset_val 0 (offset_val read dp)))
    by (rewrite isptr_offset_val_zero by (rewrite isptr_offset_val; auto); reflexivity).
  rewrite <- seq_assoc.
  forward_call tt. Intros fl.
  rewrite (vint_signed fl).
  pose proof (Int.signed_range (Int.repr fl)) as Hfl.
  set (flush := Int.signed (Int.repr fl)) in *. clearbody flush.
  pose proof (ac_gzhead K AC _ _ _ HK) as Hgz.
  pose proof (ac_adler K AC _ _ _ HK) as Had.
  destruct (ac_deflate K AC s read adler inb room tout flush msg) as (s' & z' & code & Hrun & Hcall & HK');
    try (rewrite ?Hinb; auto; unfold s32; rep_lia).
  rewrite Hinb in Hrun.
  forward_call (mc gv cp, (Some s, p, nullval, spp, (Ews, nullval, nullval, nullval), offset_val read dp, Ews,
                inb, 0, take, read, out, Zrepeat Vundef room, out_wv room, tout, msgv, msg, adler, flush,
                (Some s', z', code), gv)).
  { rewrite Zlength_Zrepeat by lia. rewrite (hdr_none s) by auto. cancel. }
  { rewrite Zlength_Zrepeat by lia.
    split; [intros E; apply out_wv_ok; exact E | ].
    split.
    - unfold strm_ranges, zmk. cbn [z_in z_next_in z_avail_in z_total_in z_avail_out z_out z_total_out z_adler].
      rewrite Hinb. unfold u32_ok, u64_ok, u64r, bytes in *. rewrite Zlength_nil.
      repeat split; auto; try rep_lia.
    - exists (fun f => f). split; [apply ef_ok_id | ].
      unfold on_state, c_on_state. rewrite Zlib.proof.deflate.DModel5.c_deflate_g_id.
      change (zmk inb 0 take read room tout adler msg) with (zcall inb 0 take read room tout adler msg).
      rewrite Hrun. reflexivity. }
  cbn [fst snd]. Intros msgv'.
  rewrite Zlength_Zrepeat by lia. rewrite (hdr_none s) by auto. rewrite offset_offset_val.
  sep_apply (derives_refl' _ _ (eq_sym (data_split3 dp bs read take ltac:(lia) ltac:(lia) ltac:(lia) FCd))).
  fold inb.
  unfold count_at.
  forward.
  forward_call (Int.repr 1).
  { split; change (Int.unsigned Int64.iwordsize') with 64; lia. }
  { apply prop_right. simpl. rewrite (check_true_exact (snd (cnt tr)) W mem) by lia. reflexivity. }
  sep_apply api_avail_open. Intros.
  forward.
  sep_apply wand_frame_elim.
  forward.
  destruct Hcall as (Hzin & Hnx & Hav & Htin & Haout & Hzout & Htot & Hzb).
  rewrite Hinb in Hnx, Hav. rewrite Z.sub_0_r in Htin.
  assert (Er : Int64.add (Int64.repr read) (Int64.sub (Int64.repr take)
                 (Int64.repr (Int.unsigned (Int.repr (z_avail_in z'))))) = Int64.repr (read + z_next_in z')).
  { rewrite Int.unsigned_repr by rep_lia. rewrite sub64_repr, add64_repr. f_equal. lia. }
  rewrite Er. clear Er.
  sep_apply (out_close room out).
  assert (Nout : out <> nullval) by (intros E; subst out; contradiction).
  forward_call (tarray tuchar room, out, gv).
  { rewrite if_false by exact Nout. cancel. }
  unfold Rbody, loop1_ret_assert, overridePost. destruct POST_m. cbv beta iota.
  unfold J_inv.
  Exists (mkMS s' (read + z_next_in z') (z_total_out z') (z_adler z') (z_msg z') msgv').
  unfold J_at, J_ok, setup_ok, J_loc, J_sep, strm_head.
  cbn [ms_s ms_read ms_tout ms_adler ms_msg ms_msgv].
  Exists (offset_val (read + z_next_in z') dp) (z_avail_in z') (offset_val (Zlength (z_out z')) out)
    (z_avail_out z').
  rewrite Htin in HK' |- *.
  assert (Hu : u64r (z_total_out z')).
  { rewrite Htot. unfold u64r. unfold u64.
    pose proof (Z.mod_pos_bound (tout + (room - z_avail_out z')) 18446744073709551616 ltac:(lia)). lia. }
  unfold count_at.
  entailer!.
Qed.
