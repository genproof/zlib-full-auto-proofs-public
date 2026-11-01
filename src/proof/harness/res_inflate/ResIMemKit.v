(* Law res_memory_inflate: the separation facts of one iteration of main's do-while (harness/res_memory_inflate.c),
   for any allocator of inflate.c (main's is the counting one) and any adler cell:
   - a live stream with any application fields, as set_buffer() takes its struct z_stream (at the compress
     unit's compspecs), and back once the fields are defined;
   - the piece input + read of the input object (alloc_any_bytes) and the output object (malloc) as inflate()
     takes them, and back after the call, the output ready for free(). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.za.inflate_api.USpec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.counted.Spec.
Require Import Zlib.proof.harness.res_inflate.ResICS.
Require Import Zlib.proof.harness.res_inflate.ResISpecs.
Require Import Zlib.proof.harness.res_inflate.ResIKit.
Require Import QuickProof.Assembly.
Require Zlib.units.Compress.
Require Zlib.units.Inflate.
Require Zlib.units.Adler32.
Require Zlib.proof.uncompr.URunRet.
Require Zlib.proof.uncompr.URunFrame.
Local Open Scope logic.

(* main's struct z_stream at the compress unit's compspecs, at the law's and at the inflate unit's *)
Lemma zs_csi sh v p : @data_at Zlib.units.Compress.CS sh t_zs v p = @data_at CSi sh tzs v p.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_compress); [apply JMeq_refl | reflexivity]. Qed.

Lemma zs_strm sh v p : @data_at Zlib.units.Compress.CS sh t_zs v p = @data_at Zlib.units.Inflate.CS sh t_strm v p.
Proof.
  rewrite zs_csi. symmetry.
  apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity].
Qed.

(* the struct z_stream of a live stream with the fields z *)
Definition zs_of {ZA : zallocator} {ZAV : adler_cell} (gv : globals) (z : zfields) (sp : val) : reptype t_zs :=
  zs_val (zf_ni z) (Vint (Int.repr (zf_ai z))) (Vlong (Int64.repr (zf_tin z))) (zf_no z)
    (Vint (Int.repr (zf_ao z))) (Vlong (Int64.repr (zf_tout z))) (msg_val gv (zf_msg z)) sp
    za_alloc za_free za_opaque (Vint (Int.repr (zf_dt z))) (adler_val (zf_adler z)) (zf_res z).

Lemma istream_zs {ZA : zallocator} {ZAV : adler_cell} gv vs z L :
  @istream_za ZA ZAV gv Tsh vs z (Some L) =
  !! (zf_ok z /\ live_ok L) &&
  (@data_at Zlib.units.Compress.CS Tsh t_zs (@zs_of ZA ZAV gv z (l_sp L)) vs * @state_mem_za ZA gv vs L).
Proof.
  unfold istream_za, zstrm_at_za, strm_rep_za, zs_of. rewrite zs_strm.
  apply pred_ext; entailer!.
Qed.

(* the fields set_buffer(strm, in, in_len, out, out_len) writes *)
Definition set_bufz (z : zfields) (ni : val) (ai : Z) (no : val) (ao : Z) : zfields :=
  ZF ni ai (zf_tin z) no ao (zf_tout z) (zf_msg z) (zf_dt z) (zf_adler z) (zf_res z).

Lemma set_bufz_ok z ni ai no ao :
  zf_ok z -> 0 <= ai <= Int.max_unsigned -> 0 <= ao <= Int.max_unsigned -> zf_ok (set_bufz z ni ai no ao).
Proof. unfold zf_ok, set_bufz; cbn. tauto. Qed.

Lemma zs_of_set_bufz {ZA : zallocator} {ZAV : adler_cell} gv z ni ai no ao sp :
  @zs_of ZA ZAV gv (set_bufz z ni ai no ao) sp =
  zs_val ni (Vint (Int.repr ai)) (Vlong (Int64.repr (zf_tin z))) no (Vint (Int.repr ao))
    (Vlong (Int64.repr (zf_tout z))) (msg_val gv (zf_msg z)) sp
    za_alloc za_free za_opaque (Vint (Int.repr (zf_dt z))) (adler_val (zf_adler z)) (zf_res z).
Proof. reflexivity. Qed.

(* after set_buffer(): the stream with the new fields *)
Lemma set_buffer_istream {ZA : zallocator} {ZAV : adler_cell} gv vs z L ni ai no ao :
  zf_ok z -> live_ok L -> 0 <= ai <= Int.max_unsigned -> 0 <= ao <= Int.max_unsigned ->
  @data_at Zlib.units.Compress.CS Tsh t_zs
    (zs_val ni (Vint (Int.repr ai)) (Vlong (Int64.repr (zf_tin z))) no (Vint (Int.repr ao))
       (Vlong (Int64.repr (zf_tout z))) (msg_val gv (zf_msg z)) (l_sp L)
       za_alloc za_free za_opaque (Vint (Int.repr (zf_dt z))) (adler_val (zf_adler z)) (zf_res z)) vs *
  @state_mem_za ZA gv vs L
  |-- @istream_za ZA ZAV gv Tsh vs (set_bufz z ni ai no ao) (Some L).
Proof.
  intros Hz HL Ha Ho. rewrite istream_zs, zs_of_set_bufz.
  apply andp_right; [apply prop_right; split; [apply set_bufz_ok |]; auto | apply derives_refl].
Qed.

(* the piece input + read of the input object of n = |bs| bytes *)
Definition mem_ib (dp : val) (read : Z) (bs : list Z) : inbuf := InBuf Ews dp read (Zlength bs) (bytes_rep bs).

(* before inflate(): the input object (alloc_any_bytes) and the output object (malloc) *)
Lemma mem_bufs_pre L dp read bs op room :
  0 <= room ->
  (@malloc_token Zlib.units.Adler32.CS Ews (tarray tuchar (Zlength bs)) dp *
   @data_at Zlib.units.Adler32.CS Ews (tarray tuchar (Zlength bs)) (bytes_rep bs) dp *
   @malloc_token CSi Ews (tarray tuchar room) op * @data_at_ CSi Ews (tarray tuchar room) op)
  |-- bufs_opt (Some L) (mem_ib dp read bs) (Some (obuf op room)) [] true true.
Proof.
  intros Hr. eapply derives_trans; [apply (bufs_pre L dp (Zlength bs) bs op room eq_refl Hr) | ].
  unfold bufs_opt, ibuf, mem_ib, in_rep, in_tok. apply derives_refl.
Qed.

(* after inflate(): the input object unchanged, the output object as free() takes it *)
Lemma mem_bufs_post L dp read bs op room ow :
  bufs_opt (Some L) (mem_ib dp read bs) (Some (obuf op room)) ow true true
  |-- (@malloc_token Zlib.units.Adler32.CS Ews (tarray tuchar (Zlength bs)) dp *
       @data_at Zlib.units.Adler32.CS Ews (tarray tuchar (Zlength bs)) (bytes_rep bs) dp *
       @malloc_token CSi Ews (tarray tuchar room) op * @data_at_ CSi Ews (tarray tuchar room) op).
Proof.
  unfold bufs_opt, mem_ib, obuf, in_rep, out_opt, out_rep, in_tok, out_tok.
  rewrite (malloc_token_tuchar_cs Zlib.units.Adler32.CS Zlib.units.Inflate.CS).
  rewrite (malloc_token_tuchar_cs CSi Zlib.units.Inflate.CS).
  rewrite (data_at_tuchar_cs Zlib.units.Adler32.CS Zlib.units.Inflate.CS).
  rewrite (data_at__tuchar_cs CSi Zlib.units.Inflate.CS).
  sep_apply (@data_at_data_at_ Zlib.units.Inflate.CS Ews (tarray tuchar room)). cancel.
Qed.

(* the piece holds the take bytes of the input from read on *)
Lemma mem_in_ok dp read take bs :
  isptr dp -> is_bytes bs -> 0 <= read -> 0 <= take -> read + take <= Zlength bs ->
  Zlength bs <= Ptrofs.max_unsigned ->
  in_ok (mem_ib dp read bs) (sublist read (read + take) bs) /\ Zlength (sublist read (read + take) bs) = take.
Proof.
  intros Pd Hb H1 H2 H3 H4. unfold in_ok, mem_ib. rewrite Zlength_sublist by lia.
  replace (read + (read + take - read)) with (read + take) by lia.
  unfold bytes_rep, byte_vals. rewrite sublist_map.
  repeat split; auto; try lia; [apply Zlength_map | apply Forall_sublist; auto].
Qed.

(* the output object offers its room bytes *)
Lemma mem_out_ok op room : isptr op -> 0 <= room <= Int.max_unsigned -> out_ok (obuf op room) room.
Proof.
  intros Po Hr. unfold out_ok, obuf. rewrite Zlength_Zrepeat by lia.
  split; [apply writable_Ews | ]. repeat split; auto; try lia; try rep_lia.
Qed.

(* one inflate() call from a mode of the decoder proper or MEM leaves the input of the machine as it is (in MEM
   the call returns Z_MEM_ERROR at once) *)
Lemma mem_run_inp flush z L inp res :
  (i_mode (l_s L) = MEM \/ HEAD <= i_mode (l_s L) <= BAD) ->
  Zlib.proof.inflate.Model2.run2 flush lenfix_list distfix_list (m_init z L inp) res -> m_inp (r_m res) = inp.
Proof.
  intros [Hm | Hm] Hrun.
  - assert (Em : m_mode (m_init z L inp) = MEM).
    { unfold m_init, m_mode. cbv zeta. cbn [m_s]. rewrite Hm.
      change (MEM =? Zlib.proof.inflate.Model.TYPE) with false. exact Hm. }
    destruct Hrun as (o & Hl & Hr).
    assert (E : Zlib.proof.inflate.Model2.stepf2 flush lenfix_list distfix_list (m_init z L inp) =
                IRet Z_MEM_ERROR (m_init z L inp)).
    { unfold Zlib.proof.inflate.Model2.stepf2, Zlib.proof.inflate.Model2.step2. rewrite Em. reflexivity. }
    inversion Hl as [m r m' Es | m m' Es | m m' o' Es]; subst; rewrite E in Es; try discriminate Es.
    injection Es as <- <-. subst res. reflexivity.
  - assert (V : Zlib.proof.uncompr.URunFrame.vmode (i_mode (m_s (m_init z L inp)))).
    { unfold m_init, Zlib.proof.uncompr.URunFrame.vmode. cbv zeta. cbn [m_s].
      destruct (i_mode (l_s L) =? Zlib.proof.inflate.Model.TYPE); [ | exact Hm].
      destruct (l_s L); cbn. unfold HEAD, BAD, TYPEDO. lia. }
    destruct (Zlib.proof.uncompr.URunFrame.run2_frame _ _ _ _ _ V Hrun) as (E & _).
    rewrite E. reflexivity.
Qed.

(* inflate() on the live stream: the model's run, the next state, the return code (one of zlib's) and the
   input left *)
Lemma mem_rel flush vs z1 L ib inp o r z' L' ow :
  vs <> nullval -> ib <> InNull -> (i_mode (l_s L) = MEM \/ HEAD <= i_mode (l_s L) <= BAD) ->
  inflate_rel flush vs z1 (Some L) ib inp (Some o) r z' (Some L') ow ->
  exists res, Zlib.proof.inflate.Model2.run2 flush lenfix_list distfix_list (m_init z1 L inp) res /\
    l_s L' = m_s (r_m res) /\ r = r_ret res /\ -5 <= r <= 2 /\
    zf_ai z' = Zlength inp - m_snx (r_m res) /\ 0 <= m_snx (r_m res) <= Zlength inp.
Proof.
  intros Hs Hi Hm [(Hb & _) | (Hb & L1 & o1 & res & winp & E1 & E2 & Hrun & Hsnx & Er & _ & Ez & _ & Est)].
  - exfalso. unfold inflate_bad, is_live in Hb. rewrite if_false in Hb by auto.
    destruct Hb as [Hb | [Hb | [Hb _]]]; congruence.
  - injection E1 as <-. injection E2 as <-. injection Est as ->. subst r z'.
    exists res. split; [exact Hrun | ]. split; [reflexivity | ]. split; [reflexivity | ]. split.
    + eapply Zlib.proof.uncompr.URunRet.run2_ret; [ | exact Hrun]. simpl. unfold Z_OK. lia.
    + split; [ | exact Hsnx]. unfold z_after. cbn [zf_ai]. rewrite (mem_run_inp _ _ _ _ _ Hm Hrun). reflexivity.
Qed.
