(* Law res_memory_deflate: main's body after deflateInit2_ returned Z_OK (MemPrefixKit.mid_pre with a state):
   the test code != Z_OK, w = window_bits without the raw sign or the gzip 16, raised from 8 to 9, read = 0, and
   the loop invariant MemKit.J_at at the loop's entry: the state meets the invariant K of deflate/AnyCalls.v
   (ac_init), the allocator's events are deflateInit2_'s five allocations, whose peak is the harness's bound
   (PeakExact.init_peak_exact). *)
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
Require Import Zlib.proof.harness.res_memory_deflate.MemPrefixKit.
Require Zlib.contracts.res_memory_deflate.
Require Import Zlib.harness.res_memory_deflate.code.
Local Open Scope logic.
Local Ltac simplify_remove_localdef_temp ::= mem_simplify_rlt.

(* the stream's application fields as counted_stream and deflateInit2_ left them (no input, no output space,
   total_in = 0), as the loop invariant holds them *)
Lemma init_api (p : val) (tout adler : Z) (msgv : val) :
  u64_ok tout -> u64_ok adler ->
  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_in) nullval p *
  reset_fields p (vl 0) (vl tout) msgv (vl adler) *
  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_in) (Vint (Int.repr 0)) p *
  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_out) nullval p *
  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_out) (Vint (Int.repr 0)) p
  |-- api_fields p nullval 0 0 nullval 0 tout msgv adler.
Proof.
  intros Ht Ha. unfold api_fields, reset_fields.
  rewrite prop_true_andp by (unfold u32_ok, u64_ok in *; rep_lia). unfold vi. cancel.
Qed.

(* the live stream at the loop's entry, as the invariant's strm_head (read = total_in = 0) *)
Lemma init_head (gv : globals) (cp p spp : val) (s : dstate) (tout : Z) (msgv : val) (adler : Z) :
  @dstream_sp_za (kc (mc gv cp)) 2 (Some s) p nullval spp gv *
  api_fields p nullval 0 0 nullval 0 tout msgv adler * strm_pad p *
  @data_at_ Zlib.units.Compress.CS Ecomp t_zs p
  |-- strm_head gv cp p spp s 0 tout msgv adler.
Proof. unfold strm_head. Exists nullval 0 nullval 0. cancel. Qed.

Lemma mid_ok {Espec : OracleKind} (K : dstate -> Z -> Z -> Prop) (gv : globals) (cp p dp : val) (bs : list Z)
    (level wbits mem strategy : Z) (a1 a2 a3 a4 a5 : bool) (s : dstate) (z1 : strm) (tr : list zev) :
  any_calls K ->
  (forall dp bs mem W tr spp L,
     @semax CSa Espec Delta_m (J_at K gv cp p dp bs mem W tr spp L) msuf17 POST_m) ->
  0 <= Zlength bs <= 9223372036854775807 -> is_bytes bs ->
  Int.min_signed <= level <= Int.max_signed -> Int.min_signed <= wbits <= Int.max_signed ->
  Int.min_signed <= mem <= Int.max_signed -> Int.min_signed <= strategy <= Int.max_signed ->
  c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 zrst0 = Some (Some s, z1, Z_OK) ->
  tr = [] ++ dinit_events s ->
  @semax CSa Espec Delta_m (mid_pre gv cp p dp bs level wbits mem strategy (Some s) z1 Z_OK tr) msuf11 POST_m.
Proof.
  intros AC Hk H3 Hbytes H7 H8 H9 H10 HI Htr.
  unfold mid_pre, msuf11, Delta_m, POST_m. abbreviate_semax.
  destruct (init_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ HI) as (_ & Pok & HIt & Hgz & Hz1).
  destruct Hz1 as (T1 & T2 & T3 & T4).
  forward_if.
  { discriminate. }
  Intros msgv'.
  match goal with Hx : if Z_OK =? Z_VERSION_ERROR then _ else _ |- _ => rename Hx into Hmsg end.
  clear H.
  destruct (init_peak_exact _ _ _ _ _ _ _ _ _ _ _ _ _ _ HI) as (Hw & Hm & Hwb & Hpeak).
  freeze [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13] FR.
  forward.
  match goal with |- semax _ (PROPx ?P (LOCALx (temp _w _ :: ?Q) (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _w (Vint (Int.repr (if wbits <? 0 then - wbits else wbits))) :: Q) (SEPx R))) end.
  { forward.
    - entailer!. change (Int.signed Int.zero) with 0. rep_lia.
    - rewrite (proj2 (Z.ltb_lt _ _) H). rewrite Int.neg_repr. entailer!. }
  { forward. rewrite (proj2 (Z.ltb_ge wbits 0) ltac:(lia)). entailer!. }
  match goal with |- semax _ (PROPx ?P (LOCALx (temp _w _ :: ?Q) (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _w (Vint (Int.repr (wb_of wbits))) :: Q) (SEPx R))) end.
  { rewrite Int.signed_repr in H by (destruct (wbits <? 0); rep_lia).
    forward.
    - entailer!. rewrite Int.signed_repr by (destruct (wbits <? 0); rep_lia).
      change (Int.signed (Int.repr 16)) with 16. destruct (wbits <? 0); rep_lia.
    - rewrite (harness_w_eq wbits Hwb). cbv zeta.
      rewrite (proj2 (Z.gtb_lt (if wbits <? 0 then - wbits else wbits) 15) H). rewrite sub_repr. entailer!. }
  { rewrite Int.signed_repr in H by (destruct (wbits <? 0); rep_lia).
    forward. rewrite (harness_w_eq wbits Hwb). cbv zeta.
    rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge 15 (if wbits <? 0 then - wbits else wbits)) ltac:(lia)). entailer!. }
  match goal with |- semax _ (PROPx ?P (LOCALx (temp _w _ :: ?Q) (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _w (Vint (Int.repr (Z.max 9 (wb_of wbits)))) :: Q) (SEPx R))) end.
  { forward. entailer!.
    rewrite <- (harness_w9 (wb_of wbits) Hw), H. reflexivity. }
  { forward. entailer!. rewrite <- (harness_w9 (wb_of wbits) Hw).
    destruct (Z.eqb_spec (wb_of wbits) 8) as [E | E]; [rewrite E in H; contradiction | reflexivity]. }
  forward.
  thaw FR.
  sep_apply (@dstream_za_open (kc (mc gv cp)) s p nullval gv). Intros spp.
  sep_apply (wand_frame_elim (@strm_live (kc (mc gv cp)) p spp (vi (tr_data_type (d_tr s))))
                             (@dstream_sp_za (kc (mc gv cp)) 2 (Some s) p nullval spp gv)).
  assert_PROP (isptr dp) as Pdp.
  { entailer. apply prop_right.
    match goal with H : field_compatible (Tarray tuchar _ _) [] dp |- _ => destruct H; auto end. }
  cbn in Hmsg. unfold rfv. change (Z_OK =? Z_OK) with true. cbv iota. rewrite T1.
  sep_apply (init_api p (z_total_out z1) (z_adler z1) msgv' ltac:(unfold u64_ok; rep_lia)
               ltac:(unfold u64_ok; rep_lia)).
  sep_apply (init_head gv cp p spp s (z_total_out z1) msgv' (z_adler z1)).
  rewrite (data_at_tuchar_cs Zlib.units.Adler32.CS DCS.CS Ews (Zlength bs) (bytes_rep bs) dp).
  (* the loop invariant's facts: the invariant K of the state, the data's bytes, the peak of the five allocations *)
  assert (Kok : K s 0 (z_adler z1)).
  { rewrite <- T1. apply (ac_init _ AC level wbits mem strategy a1 a2 a3 a4 a5 zrst0 s z1);
      try (unfold s32; rep_lia). exact HI. }
  assert (Hb : bytes bs) by (eapply Forall_impl; [ | exact Hbytes]; intros b Hb; simpl in Hb; rep_lia).
  assert (Hc : 0 <= snd (cnt tr) <= 2 ^ (Z.max 9 (wb_of wbits) + 2) + 2 ^ (mem + 9) + 5968).
  { rewrite Htr. cbn [app]. rewrite Hpeak.
    pose proof (Z.pow_nonneg 2 (Z.max 9 (wb_of wbits) + 2)). pose proof (Z.pow_nonneg 2 (mem + 9)). lia. }
  assert (Ht : u64r (z_total_out z1)) by (unfold u64r; rewrite T2; lia).
  eapply semax_pre;
    [ | apply (Hk dp bs mem (Z.max 9 (wb_of wbits)) tr spp (mkMS s 0 (z_total_out z1) (z_adler z1) (z_msg z1) msgv'))].
  unfold J_at, J_ok, J_loc, J_sep, count_at, setup_ok. cbn [ms_s ms_read ms_tout ms_adler ms_msg ms_msgv].
  entailer!.
Qed.
