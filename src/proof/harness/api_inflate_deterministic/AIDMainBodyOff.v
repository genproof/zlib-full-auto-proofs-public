(* Law api_inflate_deterministic, main: the do-while body from the test of its four objects (seg_btest), when
   none of them is NULL: the test, set_buffer() on both streams (AIDMainKit.istreamA_zs, offer_fold), the objects
   as inflate() takes them (bufs_pre), then the two inflate() calls and the rest (AIDMainBodyCall.body_call). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDMainDefs.
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDMainKit.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.harness.api_inflate_deterministic.code.
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDMainBodyCall.
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDMainBodyNull.
Local Open Scope logic.

(* the do-while body from its 8th statement, the test of the four objects *)
Definition path_btest : list nat := path_dbody ++ repeat 1%nat 7.
Definition seg_btest : statement := ltac:(get_seg path_btest).

(* after the four objects were made: the piece d = src[pos .. pos + take) in ia (first's) and ib (second's),
   the output space of room (out_size) bytes in oa and ob *)
Definition bt_pre (gv: globals) (va vb: val) (w: Z) (inp: val) (src: list Z) (pos take room flush: Z)
    (ia ib oa ob: val) (za: zfields) (La: live) (zb: zfields) (Lb: live) : environ -> mpred :=
  PROP ()
  LOCAL (temp _out_second ob; temp _out_first oa; temp _in_second ib; temp _in_first ia;
         temp _flush (Vint (Int.repr flush)); temp _out_size (Vlong (Int64.repr room));
         temp _take (Vlong (Int64.repr take));
         temp _window_bits (Vint (Int.repr w));
         temp _input_len (Vlong (Int64.repr (Zlength src))); temp _input inp;
         temp _read (Vlong (Int64.repr pos)); lvar _first t_z va; lvar _second t_z vb; gvars gv)
  SEP (istreamA gv Tsh va za Vundef (Some La); istreamA gv Tsh vb zb Vundef (Some Lb);
       mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv; version_lit gv;
       hversion_at ___stringlit_api_inflate_deterministic_1 gv; ir_msg_lits gv;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) inp;
       malloc_token Ews (tarray tuchar (Zlength src)) inp;
       malloc_obj ob room; malloc_obj oa room;
       copy_obj ib take (sublist pos (pos + take) src); copy_obj ia take (sublist pos (pos + take) src); TT).

Definition bt_facts (J: JT) (w: Z) (inp: val) (src: list Z) (va vb: val) (pos take room flush: Z)
    (ia ib oa ob: val) (za: zfields) (La: live) (zb: zfields) (Lb: live) : Prop :=
  g_facts J w inp src va vb /\
  J w src pos za La zb Lb /\ swfW (l_s La) /\ swfW (l_s Lb) /\
  raw_live (Some La) = (w <? 0) /\ raw_live (Some Lb) = (w <? 0) /\
  0 <= pos /\ 0 <= take <= Int.max_unsigned /\ pos + take <= Zlength src /\ 0 <= room <= Int.max_unsigned /\
  Int.min_signed <= flush <= Int.max_signed /\
  ia <> nullval /\ ib <> nullval /\ oa <> nullval /\ ob <> nullval.

Lemma body_off {Espec: OracleKind} J gv va vb w inp src pos take room flush ia ib oa ob za La zb Lb:
  tail_stmt ->
  bt_facts J w inp src va vb pos take room flush ia ib oa ob za La zb Lb ->
  semax Delta_m (bt_pre gv va vb w inp src pos take room flush ia ib oa ob za La zb Lb) seg_btest
    (dpost J gv va vb w inp src).
Proof.
  intros TAIL HF.
  destruct HF as (GF0 & HJ & SWa & SWb & Rwa & Rwb & Hpos & Htk & Hpt & Hroom & Hfl & N1 & N2 & N3 & N4).
  pose proof GF0 as GF. destruct GF as (AF & Wok & Hw & Hn & Hsb & Pinp & Pva & Pvb).
  unfold bt_pre, seg_btest, dpost, Delta_m, Gmain, POST_m. simplify_func_tycontext. abbreviate_semax.
  set (d := sublist pos (pos + take) src).
  assert (Hdl: Zlength d = take) by (unfold d; rewrite Zlength_sublist; lia).
  ifpost1 _t'18 (Vint (Int.repr 0)); [infeas1 | forward; cmpnn | ].
  ifpost1 _t'19 (Vint (Int.repr 0)); [infeas1 | forward; cmpnn | ].
  ifpost1 _t'20 (Vint (Int.repr 0)); [infeas1 | forward; cmpnn | ].
  (* the rest of the body keeps the do-while's postcondition *)
  match goal with |- semax _ ?P (Ssequence _ _) _ => apply semax_seq with P end;
    [ forward_if; [infeas1 | forward; entailer!] | ].
  unfold MORE_COMMANDS, abbreviate. abbreviate_semax.
  unfold copy_obj, malloc_obj. rewrite !if_false by auto. Intros.
  rewrite (bytes_adler_cs Ews take _ ia), (tok_adler_cs Ews take ia),
          (bytes_adler_cs Ews take _ ib), (tok_adler_cs Ews take ib), !malloc_bytes.
  assert_PROP (isptr ia /\ isptr ib /\ isptr oa /\ isptr ob) as Pobj.
  { entailer!. }
  destruct Pobj as (Piu & Pifr & Pou & Pofr).
  (* set_buffer(&first, in_first, take, out_first, out_size); set_buffer(&second, in_second, take, out_second, out_size) *)
  destruct (df_head _ AF _ _ _ _ _ _ _ HJ) as [Hha Hhb].
  sep_apply (istreamA_zs gv va za Vundef La). Intros.
  forward_call (va, Tsh, ia, take, oa, room, zf_ni za, Vint (Int.repr (zf_ai za)), Vlong (Int64.repr (zf_tin za)),
                zf_no za, Vint (Int.repr (zf_ao za)), Vlong (Int64.repr (zf_tout za)), msg_val gv (zf_msg za), l_sp La,
                gv Zlib.inflate.code._zcalloc, gv Zlib.inflate.code._zcfree, nullval, Vint (Int.repr (zf_dt za)),
                adler_v (raw_live (Some La)) za Vundef, zf_res za).
  sep_apply (istreamA_zs gv vb zb Vundef Lb). Intros.
  forward_call (vb, Tsh, ib, take, ob, room, zf_ni zb, Vint (Int.repr (zf_ai zb)), Vlong (Int64.repr (zf_tin zb)),
                zf_no zb, Vint (Int.repr (zf_ao zb)), Vlong (Int64.repr (zf_tout zb)), msg_val gv (zf_msg zb), l_sp Lb,
                gv Zlib.inflate.code._zcalloc, gv Zlib.inflate.code._zcfree, nullval, Vint (Int.repr (zf_dt zb)),
                adler_v (raw_live (Some Lb)) zb Vundef, zf_res zb).
  match goal with H: live_ok La |- _ => rename H into Loa end.
  match goal with H: live_ok Lb |- _ => rename H into Lob end.
  match goal with H: zf_ok za |- _ => rename H into Zoa end.
  match goal with H: zf_ok zb |- _ => rename H into Zob end.
  sep_apply (offer_fold gv va za Vundef La ia take oa room); auto; try rep_lia.
  sep_apply (offer_fold gv vb zb Vundef Lb ib take ob room); auto; try rep_lia.
  sep_apply (bufs_pre La ia take d oa room); [lia | ].
  sep_apply (bufs_pre Lb ib take d ob room); [lia | ].
  eapply semax_pre; [ | apply (body_call J gv va vb w inp src pos take room flush ia ib oa ob za La zb Lb TAIL)].
  { unfold bc_pre. fold d. entailer!. }
  unfold bc_facts.
  refine (conj GF0 (conj HJ (conj SWa (conj SWb (conj Rwa (conj Rwb _)))))).
  refine (conj Hpos (conj Htk (conj Hpt (conj Hroom (conj Hfl (conj Zoa (conj Zob (conj Loa (conj Lob _))))))))).
  auto.
Qed.
