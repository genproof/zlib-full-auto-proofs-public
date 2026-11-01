(* Law api_inflate_deterministic, main: the asserts at the start of AIDMainKit.seg_tail, first part.
   - seg_tail is the chain of the six asserts followed by seg_rest (read += take - first.avail_in and the four
     free()s): seg_tail_eq;
   - chk_pre: mid_at with both streams opened (their struct z_stream as a tuple, the members the two calls
     left equal taken from first's fields) and the resources the asserts do not touch gathered in chk_frame;
     chk_pre_of converts mid_at to chk_pre;
   - chk_part s: s keeps chk_pre (each assert reads the structs and the output objects and changes nothing);
   - the asserts 1 and 3: code_first == code_second; the bytes written equal.
   The other asserts are in AIDMainTailChkB.v (2 and 4) and AIDMainTailChkC.v (5 and 6); AIDMainTail.v
   composes them.  (One file per assert or two: each load from a struct z_stream costs seconds.) *)
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
Local Open Scope logic.

(* the six asserts of seg_tail *)
Definition seg_c1 : statement := ltac:(get_seg (path_tail ++ [0]%nat)).
Definition seg_c2 : statement := ltac:(get_seg (path_tail ++ [1; 0]%nat)).
Definition seg_c3 : statement := ltac:(get_seg (path_tail ++ [1; 1; 0]%nat)).
Definition seg_c4 : statement := ltac:(get_seg (path_tail ++ [1; 1; 1; 0]%nat)).
Definition seg_c5 : statement := ltac:(get_seg (path_tail ++ [1; 1; 1; 1; 0]%nat)).
Definition seg_c6 : statement := ltac:(get_seg (path_tail ++ [1; 1; 1; 1; 1; 0]%nat)).
(* read += take - first.avail_in; the four free()s *)
Definition seg_rest : statement := ltac:(get_seg (path_tail ++ repeat 1%nat 6)).

Lemma seg_tail_eq :
  seg_tail = Ssequence seg_c1 (Ssequence seg_c2 (Ssequence seg_c3 (Ssequence seg_c4 (Ssequence seg_c5
               (Ssequence seg_c6 seg_rest))))).
Proof.
  reflexivity.
Qed.

(* struct z_stream of a stream whose avail_in, total_in, avail_out, total_out, msg and data_type are those of
   z, its other members those of z' *)
Definition chk_tup (gv: globals) (z z': zfields) (adv sp: val) : strm_tuple :=
  (zf_ni z', (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), (zf_no z', (Vint (Int.repr (zf_ao z)),
   (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (sp, (gv Zlib.inflate.code._zcalloc,
   (gv Zlib.inflate.code._zcfree, (nullval, (Vint (Int.repr (zf_dt z)), (adv, zf_res z'))))))))))))).

(* the resources of mid_at the asserts do not touch *)
Definition chk_frame (gv: globals) (va vb: val) (La Lb: live) (inp: val) (src: list Z) (pos take room: Z)
    (ia ib oa ob: val) : mpred :=
  state_mem gv va La * state_mem gv vb Lb *
  data_at Ews (tarray tuchar take) (bytes_rep (sublist pos (pos + take) src)) ia *
  malloc_token Ews (tarray tuchar take) ia *
  data_at Ews (tarray tuchar take) (bytes_rep (sublist pos (pos + take) src)) ib *
  malloc_token Ews (tarray tuchar take) ib *
  malloc_token Ews (tarray tuchar room) oa * malloc_token Ews (tarray tuchar room) ob *
  malloc_token Ews (tarray tuchar (Zlength src)) inp * data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) inp *
  mem_mgr gv * zfuncs gv * tables_rep Ers gv * crc_table_at Ers gv * version_lit gv *
  hversion_at ___stringlit_api_inflate_deterministic_1 gv * TT.

Definition chk_pre (gv: globals) (va vb: val) (w: Z) (inp: val) (src: list Z)
    (pos take room: Z) (ia ib oa ob: val) (ra: Z) (za: zfields) (La: live) (zb: zfields) (Lb: live)
    (ow: list Z) : environ -> mpred :=
  PROP (zf_ok za; zf_ok zb; live_ok La; live_ok Lb)
  LOCAL (temp _code_first (Vint (Int.repr ra)); temp _code_second (Vint (Int.repr ra));
         temp _window_bits (Vint (Int.repr w));
         temp _input_len (Vlong (Int64.repr (Zlength src))); temp _input inp;
         temp _read (Vlong (Int64.repr pos)); temp _take (Vlong (Int64.repr take));
         temp _out_size (Vlong (Int64.repr room));
         temp _in_first ia; temp _in_second ib; temp _out_first oa; temp _out_second ob;
         lvar _first t_z va; lvar _second t_z vb; gvars gv)
  SEP (data_at Tsh t_z (chk_tup gv za za (adler_v (w <? 0) za Vundef) (l_sp La)) va;
       data_at Tsh t_z (chk_tup gv za zb (adler_v (w <? 0) zb Vundef) (l_sp Lb)) vb;
       data_at Ews (tarray tuchar room) (out_after (Zrepeat Vundef room) ow room) oa;
       data_at Ews (tarray tuchar room) (out_after (Zrepeat Vundef room) ow room) ob;
       ir_msg_lits gv; chk_frame gv va vb La Lb inp src pos take room ia ib oa ob).

Lemma chk_pre_of J gv va vb w inp src pos take room ia ib oa ob ra za La zb Lb ow:
  mid_facts J w inp src va vb pos take room ia ib oa ob ra za La zb Lb ow ->
  ENTAIL Delta_m, mid_at J gv va vb w inp src pos take room ia ib oa ob ra za La zb Lb ow
  |-- chk_pre gv va vb w inp src pos take room ia ib oa ob ra za La zb Lb ow.
Proof.
  intros MF.
  destruct MF as (_ & _ & _ & _ & RA & RB & _ & _ & _ & _ & _ & _ & _ &
                  Eai & Eao & Etin & Etout & Edt & Emsg & _).
  unfold mid_at, chk_pre, chk_frame.
  rewrite (istreamA_unfold gv Tsh va za Vundef La), (istreamA_unfold gv Tsh vb zb Vundef Lb).
  rewrite RA, RB. unfold aid_tup, chk_tup. rewrite <- Eai, <- Eao, <- Etin, <- Etout, <- Edt, <- Emsg.
  Intros. entailer!.
Qed.

Lemma chk_post_of J gv va vb w inp src pos take room ia ib oa ob ra za La zb Lb ow:
  mid_facts J w inp src va vb pos take room ia ib oa ob ra za La zb Lb ow ->
  ENTAIL Delta_m, chk_pre gv va vb w inp src pos take room ia ib oa ob ra za La zb Lb ow
  |-- mid_at J gv va vb w inp src pos take room ia ib oa ob ra za La zb Lb ow.
Proof.
  intros MF.
  destruct MF as (_ & _ & _ & _ & RA & RB & _ & _ & _ & _ & _ & _ & _ &
                  Eai & Eao & Etin & Etout & Edt & Emsg & _).
  unfold mid_at, chk_pre, chk_frame. Intros.
  replace (chk_tup gv za za (adler_v (w <? 0) za Vundef) (l_sp La))
    with (aid_tup gv za (adler_v (raw_live (Some La)) za Vundef) (l_sp La)) by (rewrite RA; reflexivity).
  replace (chk_tup gv za zb (adler_v (w <? 0) zb Vundef) (l_sp Lb))
    with (aid_tup gv zb (adler_v (raw_live (Some Lb)) zb Vundef) (l_sp Lb))
    by (rewrite RB; unfold chk_tup, aid_tup; rewrite <- Eai, <- Eao, <- Etin, <- Etout, <- Edt, <- Emsg; reflexivity).
  sep_apply (istreamA_fold gv Tsh va za Vundef La); auto.
  sep_apply (istreamA_fold gv Tsh vb zb Vundef Lb); auto.
  entailer!.
Qed.

(* s runs from chk_pre to chk_pre *)
Definition chk_part (s: statement) : Prop :=
  forall {Espec: OracleKind} J gv va vb w inp src pos take room ia ib oa ob ra za La zb Lb ow,
  mid_facts J w inp src va vb pos take room ia ib oa ob ra za La zb Lb ow ->
  semax Delta_m (chk_pre gv va vb w inp src pos take room ia ib oa ob ra za La zb Lb ow) s
    (normal_ret_assert (chk_pre gv va vb w inp src pos take room ia ib oa ob ra za La zb Lb ow)).

(* the bytes both calls wrote at the start of an output object, as a slice for bytes_eq (the bytes normalised
   by Int.unsigned o Int.repr: the stored values are bytes, the model's list need not be) *)
Lemma chk_out_cbuf (c: list val) (ow: list Z) (n: Z) p:
  isptr p -> Zlength ow <= n -> Zlength c = n ->
  Forall (value_fits tuchar) (out_after c ow n) ->
  cbuf_ok false p Ews p 0 n (Zlength ow) (out_after c ow n) (map (fun x => Int.unsigned (Int.repr x)) ow).
Proof.
  intros Pp Hl Hc F. pose proof (Zlength_nonneg ow). unfold out_after in *. rewrite sublist_nil, app_nil_l in *.
  apply Forall_app in F. destruct F as [F _].
  unfold cbuf_ok. split; [destruct p; try contradiction; simpl; rewrite Ptrofs.add_zero; reflexivity | ].
  split; [auto with share | ]. split; [lia | ]. split; [lia | ]. split; [rewrite Zlength_map; reflexivity | ].
  split.
  - unfold is_bytes, byte_vals in *. rewrite Forall_map in F. rewrite Forall_map.
    eapply Forall_impl; [ | exact F]. intros x Hx. simpl in Hx.
    specialize (Hx ltac:(discriminate)). simpl in Hx. pose proof (Int.unsigned_range (Int.repr x)).
    cbv beta delta [Basics.compose]. lia.
  - rewrite Z.add_0_l. rewrite sublist_app1 by (rewrite ?Zlength_byte_vals; lia).
    rewrite sublist_same by (rewrite ?Zlength_byte_vals; lia).
    unfold bytes_rep, byte_vals. rewrite map_map. apply map_ext. intros x. rewrite Int.repr_unsigned. reflexivity.
Qed.

(* gp_assert(code_first == code_second) *)
Lemma chk_c1 : chk_part seg_c1.
Proof.
  intros Espec J gv va vb w inp src pos take room ia ib oa ob ra za La zb Lb ow MF.
  unfold seg_c1, chk_pre at 1, chk_tup. Intros. abbreviate_semax.
  forward_call (Int.repr 1).
  { entailer!. rewrite Int.eq_true. reflexivity. }
  unfold chk_pre, chk_tup. entailer!.
Qed.

(* gp_assert(bytes_eq(out_first, out_second, out_size - first.avail_out)): both objects hold the bytes ow the calls
   wrote, room - avail_out of them *)
Lemma chk_c3 : chk_part seg_c3.
Proof.
  intros Espec J gv va vb w inp src pos take room ia ib oa ob ra za La zb Lb ow MF.
  pose proof MF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hroom & Hao & _ & _ & _ & _ & _ & _ & _ & _ &
                    Hlow & _ & _ & Poa & Pob).
  unfold seg_c3, chk_pre at 1, chk_tup. Intros. abbreviate_semax.
  forward.
  assert_PROP (Forall (value_fits tuchar) (out_after (Zrepeat Vundef room) ow room)) as Fo by entailer!.
  pose proof (chk_out_cbuf (Zrepeat Vundef room) ow room oa Poa ltac:(lia)
                ltac:(rewrite Zlength_Zrepeat; lia) Fo) as Cu.
  pose proof (chk_out_cbuf (Zrepeat Vundef room) ow room ob Pob ltac:(lia)
                ltac:(rewrite Zlength_Zrepeat; lia) Fo) as Cf.
  rewrite Hlow in Cu, Cf.
  rewrite <- (bytes_adler_cs Ews room (out_after (Zrepeat Vundef room) ow room) oa),
          <- (bytes_adler_cs Ews room (out_after (Zrepeat Vundef room) ow room) ob).
  forward_call (oa, Ews, oa, 0, room, out_after (Zrepeat Vundef room) ow room,
                map (fun x => Int.unsigned (Int.repr x)) ow,
                ob, Ews, ob, 0, room, out_after (Zrepeat Vundef room) ow room,
                map (fun x => Int.unsigned (Int.repr x)) ow, room - zf_ao za).
  destruct (list_eq_dec Z.eq_dec (map (fun x => Int.unsigned (Int.repr x)) ow)
              (map (fun x => Int.unsigned (Int.repr x)) ow)) as [_ | NE]; [ | congruence].
  forward_call (Int.repr 1).
  rewrite (bytes_adler_cs Ews room (out_after (Zrepeat Vundef room) ow room) oa),
          (bytes_adler_cs Ews room (out_after (Zrepeat Vundef room) ow room) ob).
  unfold chk_pre, chk_tup. entailer!.
Qed.
