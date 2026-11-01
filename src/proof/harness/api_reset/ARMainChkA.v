(* Law api_reset, main: the asserts of phase 1 (ARMainKit.seg_chk), first part.
   - chk_pre: mid1_at with both streams opened (their struct z_stream as a tuple, the members the two calls
     left equal taken from used's fields) and the resources the asserts do not touch gathered in chk_frame;
     chk_pre_of / chk_post_of convert between mid1_at and chk_pre;
   - chk_part s: s keeps chk_pre (each assert reads the structs and the output objects and changes nothing);
   - the asserts 1 and 3: code_used == code_fresh; the bytes written equal.
   The other asserts are in ARMainChkB.v (2), ARMainChkC.v (4), ARMainChkD.v (5) and ARMainChk.v (6), which
   composes them into chk_proof.  (One file per assert or two: each load from a struct z_stream costs seconds.) *)
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
Local Open Scope logic.

(* the six asserts of seg_chk *)
Definition seg_c1 : statement := ltac:(get_seg (path_chk ++ [0]%nat)).
Definition seg_c2 : statement := ltac:(get_seg (path_chk ++ [1; 0]%nat)).
Definition seg_c3 : statement := ltac:(get_seg (path_chk ++ [1; 1; 0]%nat)).
Definition seg_c4 : statement := ltac:(get_seg (path_chk ++ [1; 1; 1; 0]%nat)).
Definition seg_c5 : statement := ltac:(get_seg (path_chk ++ [1; 1; 1; 1; 0]%nat)).
Definition seg_c6 : statement := ltac:(get_seg (path_chk ++ [1; 1; 1; 1; 1]%nat)).

Lemma seg_chk_eq :
  seg_chk = Ssequence seg_c1 (Ssequence seg_c2 (Ssequence seg_c3 (Ssequence seg_c4 (Ssequence seg_c5 seg_c6)))).
Proof. reflexivity. Qed.

(* struct z_stream of a stream whose avail_in, total_in, avail_out, total_out, msg and data_type are those of
   z, its other members those of z' *)
Definition chk_tup (gv: globals) (z z': zfields) (adv sp: val) : strm_tuple :=
  (zf_ni z', (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), (zf_no z', (Vint (Int.repr (zf_ao z)),
   (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (sp, (gv Zlib.inflate.code._zcalloc,
   (gv Zlib.inflate.code._zcfree, (nullval, (Vint (Int.repr (zf_dt z)), (adv, zf_res z'))))))))))))).

(* the resources of mid1_at the asserts do not touch *)
Definition chk_frame (gv: globals) (va vb: val) (La Lb: live) (inp: val) (src: list Z) (pos take room: Z)
    (iu ifr ou ofr: val) : mpred :=
  state_mem gv va La * state_mem gv vb Lb *
  data_at Ews (tarray tuchar take) (bytes_rep (sublist pos (pos + take) src)) iu *
  malloc_token Ews (tarray tuchar take) iu *
  data_at Ews (tarray tuchar take) (bytes_rep (sublist pos (pos + take) src)) ifr *
  malloc_token Ews (tarray tuchar take) ifr *
  malloc_token Ews (tarray tuchar room) ou * malloc_token Ews (tarray tuchar room) ofr *
  malloc_token Ews (tarray tuchar (Zlength src)) inp * data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) inp *
  mem_mgr gv * zfuncs gv * tables_rep Ers gv * crc_table_at Ers gv * version_lit gv *
  hversion_at ___stringlit_api_reset_1 gv * TT.

Definition chk_pre (gv: globals) (va vb: val) (w: Z) (inp: val) (src: list Z)
    (pos take room: Z) (iu ifr ou ofr: val) (ra: Z) (za: zfields) (La: live) (zb: zfields) (Lb: live)
    (ow: list Z) : environ -> mpred :=
  PROP (zf_ok za; zf_ok zb; live_ok La; live_ok Lb)
  LOCAL (temp _code_used (Vint (Int.repr ra)); temp _code_fresh (Vint (Int.repr ra));
         temp _window_bits (Vint (Int.repr w)); temp _phase (Vint (Int.repr 1));
         temp _input_len (Vlong (Int64.repr (Zlength src))); temp _input inp;
         temp _read (Vlong (Int64.repr pos)); temp _take (Vlong (Int64.repr take));
         temp _room (Vlong (Int64.repr room));
         temp _in_used iu; temp _in_fresh ifr; temp _out_used ou; temp _out_fresh ofr;
         lvar _used t_z va; lvar _fresh t_z vb; gvars gv)
  SEP (data_at Tsh t_z (chk_tup gv za za (adler_v (w <? 0) za Vundef) (l_sp La)) va;
       data_at Tsh t_z (chk_tup gv za zb (adler_v (w <? 0) zb Vundef) (l_sp Lb)) vb;
       data_at Ews (tarray tuchar room) (out_after (Zrepeat Vundef room) ow room) ou;
       data_at Ews (tarray tuchar room) (out_after (Zrepeat Vundef room) ow room) ofr;
       ir_msg_lits gv; chk_frame gv va vb La Lb inp src pos take room iu ifr ou ofr).

Lemma chk_pre_of J0 J1 gv va vb w inp src pos take room iu ifr ou ofr ra za La zb Lb ow:
  mid1_facts J0 J1 w inp src va vb pos take room iu ifr ou ofr ra za La zb Lb ow ->
  ENTAIL Delta_m, mid1_at J0 J1 gv va vb w inp src pos take room iu ifr ou ofr ra za La zb Lb ow
  |-- chk_pre gv va vb w inp src pos take room iu ifr ou ofr ra za La zb Lb ow.
Proof.
  intros MF.
  destruct MF as (_ & _ & _ & _ & RA & RB & _ & _ & _ & _ & _ & _ & _ &
                  Eai & Eao & Etin & Etout & Edt & Emsg & _).
  unfold mid1_at, chk_pre, chk_frame.
  rewrite (istreamA_unfold gv Tsh va za Vundef La), (istreamA_unfold gv Tsh vb zb Vundef Lb).
  rewrite RA, RB. unfold ar_tup, chk_tup. rewrite <- Eai, <- Eao, <- Etin, <- Etout, <- Edt, <- Emsg.
  Intros. entailer!.
Qed.

Lemma chk_post_of J0 J1 gv va vb w inp src pos take room iu ifr ou ofr ra za La zb Lb ow:
  mid1_facts J0 J1 w inp src va vb pos take room iu ifr ou ofr ra za La zb Lb ow ->
  ENTAIL Delta_m, chk_pre gv va vb w inp src pos take room iu ifr ou ofr ra za La zb Lb ow
  |-- mid1_at J0 J1 gv va vb w inp src pos take room iu ifr ou ofr ra za La zb Lb ow.
Proof.
  intros MF.
  destruct MF as (_ & _ & _ & _ & RA & RB & _ & _ & _ & _ & _ & _ & _ &
                  Eai & Eao & Etin & Etout & Edt & Emsg & _).
  unfold mid1_at, chk_pre, chk_frame. Intros.
  replace (chk_tup gv za za (adler_v (w <? 0) za Vundef) (l_sp La))
    with (ar_tup gv za (adler_v (raw_live (Some La)) za Vundef) (l_sp La)) by (rewrite RA; reflexivity).
  replace (chk_tup gv za zb (adler_v (w <? 0) zb Vundef) (l_sp Lb))
    with (ar_tup gv zb (adler_v (raw_live (Some Lb)) zb Vundef) (l_sp Lb))
    by (rewrite RB; unfold chk_tup, ar_tup; rewrite <- Eai, <- Eao, <- Etin, <- Etout, <- Edt, <- Emsg; reflexivity).
  sep_apply (istreamA_fold gv Tsh va za Vundef La); auto.
  sep_apply (istreamA_fold gv Tsh vb zb Vundef Lb); auto.
  entailer!.
Qed.

(* s runs from chk_pre to chk_pre *)
Definition chk_part (s: statement) : Prop :=
  forall {Espec: OracleKind} J0 J1 gv va vb w inp src pos take room iu ifr ou ofr ra za La zb Lb ow,
  mid1_facts J0 J1 w inp src va vb pos take room iu ifr ou ofr ra za La zb Lb ow ->
  semax Delta_m (chk_pre gv va vb w inp src pos take room iu ifr ou ofr ra za La zb Lb ow) s
    (normal_ret_assert (chk_pre gv va vb w inp src pos take room iu ifr ou ofr ra za La zb Lb ow)).

Lemma chk_part_seq s1 s2: chk_part s1 -> chk_part s2 -> chk_part (Ssequence s1 s2).
Proof.
  intros H1 H2 Espec J0 J1 gv va vb w inp src pos take room iu ifr ou ofr ra za La zb Lb ow MF.
  eapply semax_seq'.
  - exact (H1 Espec J0 J1 gv va vb w inp src pos take room iu ifr ou ofr ra za La zb Lb ow MF).
  - exact (H2 Espec J0 J1 gv va vb w inp src pos take room iu ifr ou ofr ra za La zb Lb ow MF).
Qed.

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

(* gp_assert(code_used == code_fresh) *)
Lemma chk_c1 : chk_part seg_c1.
Proof.
  intros Espec J0 J1 gv va vb w inp src pos take room iu ifr ou ofr ra za La zb Lb ow MF.
  unfold seg_c1, chk_pre at 1, chk_tup. Intros. abbreviate_semax.
  forward_call (Int.repr 1).
  { entailer!. rewrite Int.eq_true. reflexivity. }
  unfold chk_pre, chk_tup. entailer!.
Qed.

(* gp_assert(bytes_eq(out_used, out_fresh, room - used.avail_out)): both objects hold the bytes ow the calls
   wrote, room - avail_out of them *)
Lemma chk_c3 : chk_part seg_c3.
Proof.
  intros Espec J0 J1 gv va vb w inp src pos take room iu ifr ou ofr ra za La zb Lb ow MF.
  pose proof MF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hroom & Hao & _ & _ & _ & _ & _ & _ & _ & _ &
                    Hlow & _ & _ & Pou & Pofr).
  unfold seg_c3, chk_pre at 1, chk_tup. Intros. abbreviate_semax.
  forward.
  assert_PROP (Forall (value_fits tuchar) (out_after (Zrepeat Vundef room) ow room)) as Fo by entailer!.
  pose proof (chk_out_cbuf (Zrepeat Vundef room) ow room ou Pou ltac:(lia)
                ltac:(rewrite Zlength_Zrepeat; lia) Fo) as Cu.
  pose proof (chk_out_cbuf (Zrepeat Vundef room) ow room ofr Pofr ltac:(lia)
                ltac:(rewrite Zlength_Zrepeat; lia) Fo) as Cf.
  rewrite Hlow in Cu, Cf.
  rewrite <- (bytes_adler_cs Ews room (out_after (Zrepeat Vundef room) ow room) ou),
          <- (bytes_adler_cs Ews room (out_after (Zrepeat Vundef room) ow room) ofr).
  forward_call (ou, Ews, ou, 0, room, out_after (Zrepeat Vundef room) ow room,
                map (fun x => Int.unsigned (Int.repr x)) ow,
                ofr, Ews, ofr, 0, room, out_after (Zrepeat Vundef room) ow room,
                map (fun x => Int.unsigned (Int.repr x)) ow, room - zf_ao za).
  destruct (list_eq_dec Z.eq_dec (map (fun x => Int.unsigned (Int.repr x)) ow)
              (map (fun x => Int.unsigned (Int.repr x)) ow)) as [_ | NE]; [ | congruence].
  forward_call (Int.repr 1).
  rewrite (bytes_adler_cs Ews room (out_after (Zrepeat Vundef room) ow room) ou),
          (bytes_adler_cs Ews room (out_after (Zrepeat Vundef room) ow room) ofr).
  unfold chk_pre, chk_tup. entailer!.
Qed.
