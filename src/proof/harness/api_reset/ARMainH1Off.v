(* Law api_reset, main: the do-while body in phase 1 from the test of its four objects (seg_h1t), when none of
   them is NULL: the test, offer() on both streams (ARMainKit.istreamA_zs, offer_fold), the objects as
   inflate() takes them (bufs_pre), then the two inflate() calls and the rest (ARMainH1Call.h1_call). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_reset.ARMainDefs Zlib.proof.harness.api_reset.ARMainKit.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.harness.api_reset.code.
Require Import Zlib.proof.harness.api_reset.ARMainH1Call Zlib.proof.harness.api_reset.ARMainH1Null.
Local Open Scope logic.

(* the do-while body from its 8th statement, the test of the four objects *)
Definition path_h1t : list nat := path_dbody ++ repeat 1%nat 7.
Definition seg_h1t : statement := ltac:(get_seg path_h1t).

(* after the four objects were made: the piece d = src[pos .. pos + take) in iu (used's) and ifr (fresh's),
   the output space of room bytes in ou and ofr *)
Definition h1t_pre (gv: globals) (va vb: val) (w: Z) (inp: val) (src: list Z) (pos take room flush: Z)
    (iu ifr ou ofr: val) (za: zfields) (La: live) (zb: zfields) (Lb: live) : environ -> mpred :=
  PROP ()
  LOCAL (temp _out_fresh ofr; temp _out_used ou; temp _in_fresh ifr; temp _in_used iu;
         temp _flush (Vint (Int.repr flush)); temp _room (Vlong (Int64.repr room));
         temp _take (Vlong (Int64.repr take));
         temp _window_bits (Vint (Int.repr w)); temp _phase (Vint (Int.repr 1));
         temp _input_len (Vlong (Int64.repr (Zlength src))); temp _input inp;
         temp _read (Vlong (Int64.repr pos)); lvar _used t_z va; lvar _fresh t_z vb; gvars gv)
  SEP (istreamA gv Tsh va za Vundef (Some La); istreamA gv Tsh vb zb Vundef (Some Lb);
       mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv; version_lit gv;
       hversion_at ___stringlit_api_reset_1 gv; ir_msg_lits gv;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) inp;
       malloc_token Ews (tarray tuchar (Zlength src)) inp;
       malloc_obj ofr room; malloc_obj ou room;
       copy_obj ifr take (sublist pos (pos + take) src); copy_obj iu take (sublist pos (pos + take) src); TT).

Definition h1t_facts (J0: J0T) (J1: J1T) (w: Z) (inp: val) (src: list Z) (va vb: val) (pos take room flush: Z)
    (iu ifr ou ofr: val) (za: zfields) (La: live) (zb: zfields) (Lb: live) : Prop :=
  g_facts J0 J1 w inp src va vb /\
  J1 w src pos za La zb Lb /\ swfW (l_s La) /\ swfW (l_s Lb) /\
  raw_live (Some La) = (w <? 0) /\ raw_live (Some Lb) = (w <? 0) /\
  0 <= pos /\ 0 <= take <= Int.max_unsigned /\ pos + take <= Zlength src /\ 0 <= room <= Int.max_unsigned /\
  Int.min_signed <= flush <= Int.max_signed /\
  iu <> nullval /\ ifr <> nullval /\ ou <> nullval /\ ofr <> nullval.

Lemma h1_off {Espec: OracleKind} J0 J1 gv va vb w inp src pos take room flush iu ifr ou ofr za La zb Lb:
  tail1_stmt ->
  h1t_facts J0 J1 w inp src va vb pos take room flush iu ifr ou ofr za La zb Lb ->
  semax Delta_m (h1t_pre gv va vb w inp src pos take room flush iu ifr ou ofr za La zb Lb) seg_h1t
    (dpost J0 J1 gv va vb w 1 inp src).
Proof.
  intros TAIL1 HF.
  destruct HF as (GF0 & HJ & SWa & SWb & Rwa & Rwb & Hpos & Htk & Hpt & Hroom & Hfl & N1 & N2 & N3 & N4).
  pose proof GF0 as GF. destruct GF as (AF & Wok & Hw & Hn & Hsb & Pinp & Pva & Pvb).
  unfold h1t_pre, seg_h1t, dpost, Delta_m, Gmain, POST_m. simplify_func_tycontext. abbreviate_semax.
  set (d := sublist pos (pos + take) src).
  assert (Hdl: Zlength d = take) by (unfold d; rewrite Zlength_sublist; lia).
  ifpost1 _t'14 (Vint (Int.repr 0)); [infeas1 | forward; cmpnn | ].
  ifpost1 _t'15 (Vint (Int.repr 0)); [infeas1 | forward; cmpnn | ].
  ifpost1 _t'16 (Vint (Int.repr 0)); [infeas1 | forward; cmpnn | ].
  (* the rest of the body keeps the do-while's postcondition *)
  match goal with |- semax _ ?P (Ssequence _ _) _ => apply semax_seq with P end;
    [ forward_if; [infeas1 | forward; entailer!] | ].
  unfold MORE_COMMANDS, abbreviate. abbreviate_semax.
  unfold copy_obj, malloc_obj. rewrite !if_false by auto. Intros.
  rewrite (bytes_adler_cs Ews take _ iu), (tok_adler_cs Ews take iu),
          (bytes_adler_cs Ews take _ ifr), (tok_adler_cs Ews take ifr), !malloc_bytes.
  assert_PROP (isptr iu /\ isptr ifr /\ isptr ou /\ isptr ofr) as Pobj.
  { entailer!. }
  destruct Pobj as (Piu & Pifr & Pou & Pofr).
  (* offer(&used, in_used, take, out_used, room); offer(&fresh, in_fresh, take, out_fresh, room) *)
  destruct (af_head1 _ _ AF _ _ _ _ _ _ _ HJ) as [Hha Hhb].
  sep_apply (istreamA_zs gv va za Vundef La). Intros.
  forward_call (va, Tsh, iu, take, ou, room, zf_ni za, Vint (Int.repr (zf_ai za)), Vlong (Int64.repr (zf_tin za)),
                zf_no za, Vint (Int.repr (zf_ao za)), Vlong (Int64.repr (zf_tout za)), msg_val gv (zf_msg za), l_sp La,
                gv Zlib.inflate.code._zcalloc, gv Zlib.inflate.code._zcfree, nullval, Vint (Int.repr (zf_dt za)),
                adler_v (raw_live (Some La)) za Vundef, zf_res za).
  sep_apply (istreamA_zs gv vb zb Vundef Lb). Intros.
  forward_call (vb, Tsh, ifr, take, ofr, room, zf_ni zb, Vint (Int.repr (zf_ai zb)), Vlong (Int64.repr (zf_tin zb)),
                zf_no zb, Vint (Int.repr (zf_ao zb)), Vlong (Int64.repr (zf_tout zb)), msg_val gv (zf_msg zb), l_sp Lb,
                gv Zlib.inflate.code._zcalloc, gv Zlib.inflate.code._zcfree, nullval, Vint (Int.repr (zf_dt zb)),
                adler_v (raw_live (Some Lb)) zb Vundef, zf_res zb).
  match goal with H: live_ok La |- _ => rename H into Loa end.
  match goal with H: live_ok Lb |- _ => rename H into Lob end.
  match goal with H: zf_ok za |- _ => rename H into Zoa end.
  match goal with H: zf_ok zb |- _ => rename H into Zob end.
  sep_apply (offer_fold gv va za Vundef La iu take ou room); auto; try rep_lia.
  sep_apply (offer_fold gv vb zb Vundef Lb ifr take ofr room); auto; try rep_lia.
  sep_apply (bufs_pre La iu take d ou room); [lia | ].
  sep_apply (bufs_pre Lb ifr take d ofr room); [lia | ].
  eapply semax_pre; [ | apply (h1_call J0 J1 gv va vb w inp src pos take room flush iu ifr ou ofr za La zb Lb TAIL1)].
  { unfold h1c_pre. fold d. entailer!. }
  unfold h1c_facts.
  refine (conj GF0 (conj HJ (conj SWa (conj SWb (conj Rwa (conj Rwb _)))))).
  refine (conj Hpos (conj Htk (conj Hpt (conj Hroom (conj Hfl (conj Zoa (conj Zob (conj Loa (conj Lob _))))))))).
  auto.
Qed.
