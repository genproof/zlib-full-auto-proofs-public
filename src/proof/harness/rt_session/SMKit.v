(* Law rt_session (harness/rt_session.c): the kit of main's body proof ([SMainStmt.ses_main_stmt], SMain.v).

   The harness is rt_stream_trailing's with, in addition, a choice (nondet_u8) between nothing, a dictionary (raw or
   zlib wrapper: bit 0 of choice and window_bits <= 15) and a gzip header (bit 0 and window_bits > 15; bits 1, 2, 3:
   extra, name, comment present), the draws of the dictionary, the header's fields and their copies, the gz_header
   head given to deflateSetHeader and the gz_header got given to inflateGetHeader (buffers of the fields' sizes),
   deflateSetDictionary / deflateSetHeader after deflateInit2, inflateGetHeader / a raw inflateSetDictionary after
   inflateInit2, the Z_NEED_DICT branch of the inflate loop (inflateSetDictionary, flag asked) and the header checks
   at the end.

   main's body is [Ssequence b0 (return 0)]; b0 is a right-nested sequence of 85 statements, 0-based:
     0-7    level, window_bits, mem_level, strategy, gp_assume(deflate_params_ok(..)), choice, with_dict, with_head,
     8-17   dict_len, extra_len, name_len, comment_len, data_len, out_size (upto), text, time, os, hcrc (nondet_u32),
     18-22  dict, extra = alloc_any_bytes, name, comment = any_string, data = alloc_any_bytes,   23  their NULL test,
     24-30  dict_copy, extra_copy, name_copy, comment_copy, expected (copy_of), compressed, out (malloc),
     31-38  head's fields,   39-44  got's buffers (malloc) and sizes,   45-46  the NULL tests of the copies,
            compressed, out and got's buffers,
     47     new_stream(&compressor),  48  code = deflateInit2_(..),  49  Z_MEM_ERROR: return,  50  gp_assert(Z_OK),
     51     with_dict: deflateSetDictionary,  52  with_head: deflateSetHeader,  53-56  next_in, next_out, offered, flush,
     57     the deflate loop (rt_stream_trailing's),
     58-62  compressed_len, after, input = alloc_any_bytes, its NULL test, the copy loop,
     63     new_stream(&decompressor),  64  window_bits 8 -> 9,  65  inflateInit2_,  66  Z_MEM_ERROR: return,
     67     gp_assert(Z_OK),  68  with_head: inflateGetHeader,  69  with_dict and window_bits < 0: inflateSetDictionary,
     70     asked = 0,  71-72  next_in, next_out,
     73     the inflate loop (rt_stream_trailing's, with the Z_NEED_DICT branch),
     74-76  the checks of asked, next_in, next_out and the bytes,  77  !with_head: return 0,
     78-83  the header checks (as rt_gzip_header's),  84  return 0.
   The parts, as Hoare triples between the assertions below (a return inside a part goes to main's
   postcondition POST_s):
     segA1   (0-23)    PRE0 -> A24             the draws and the five objects
     segA2   (24-46)   A24 -> A47              the copies, the malloc'ed objects, head and got
     segA3   (47-56)   A47 -> DI               deflateInit2_, the dictionary or the header, the loop's start
     loopD   (57)      DI (its invariant) -> DE
     segB    (58-62)   DE -> DB                the input object: O, then any bytes
     segC    (63-72)   DB -> II_W (no header: with_head = 0) or II_9 (a header)
     loopI   (73)      II_W -> IE_W in the context Delta_W (SMainStmt.Gmain_W: inflate's SpecW specification),
                       II_9 -> IE_9 in the context Delta_9 (SMainStmt.Gmain_9: RTH9Spec's)
     segE    (74-84)   IE_W -> return, IE_9 -> return.
   SMain.v moves the two inflate loops into main's context (semax_Delta_subsumption: only inflate()'s entry
   differs, SMainStmt.inflate_ses_sub).

   The values main draws and its objects are a record [setup]; the session the inflate side sees is
   [scase_of u] (SIFacts.scase: deflate's windowBits, the dictionary when one is set, the header when one is set,
   got as inflateGetHeader receives it).  Memory (as rt_stream's UMainKit.v and rt_gzip_header's G2MainKit.v): the
   local z_stream compressor split into Ews (the deflate specifications' share) and its complement ([srest]); the
   decompressor an istreamA (SpecW) without a header, an istream8 (RTH8Spec) with one; the struct position at any
   bytes between the parts.  While the compressor holds head (from deflateSetHeader on), the header part of the
   state [hdr_at] and a rest [Hr] give head back ([hclose]); without a header [Hr] is head itself. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Zlib.proof.roundtrip.RTH8Spec Zlib.proof.roundtrip.RTH9Spec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SDFacts.
Require Import Zlib.proof.harness.rt_session.SIFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

Module IR := Zlib.proof.inflate.Records.

Definition t_z : type := Tstruct _z_stream_s noattr.
Definition t_p : type := Tstruct _position noattr.
Definition t_g : type := Tstruct _gz_header_s noattr.

(** ** Cutting main's body into its parts *)

(* b0: main's body without the final return *)
Definition body0 : statement := match fn_body f_main with Ssequence b _ => b | s => s end.

(* the statements of a right-nested sequence from position k on, its first k statements, its first statement *)
Fixpoint suf (k : nat) (s : statement) : statement :=
  match k, s with
  | O, _ => s
  | S k', Ssequence _ b => suf k' b
  | _, _ => Sskip
  end.

Fixpoint take (k : nat) (s : statement) : statement :=
  match k, s with
  | S (S k'), Ssequence a b => Ssequence a (take (S k') b)
  | S O, Ssequence a _ => a
  | _, _ => Sskip
  end.

Definition first (s : statement) : statement := match s with Ssequence a _ => a | _ => s end.

Ltac get_stmt e :=
  let x := eval cbv beta iota zeta delta [take suf first body0 f_main fn_body] in e in
  exact x.

Definition segA1 : statement := ltac:(get_stmt (take 24 body0)).
Definition segA2 : statement := ltac:(get_stmt (take 23 (suf 24 body0))).
Definition segA3 : statement := ltac:(get_stmt (take 10 (suf 47 body0))).
Definition loopD : statement := ltac:(get_stmt (first (suf 57 body0))).
Definition segB : statement := ltac:(get_stmt (take 5 (suf 58 body0))).
Definition segC : statement := ltac:(get_stmt (take 10 (suf 63 body0))).
Definition loopI : statement := ltac:(get_stmt (first (suf 73 body0))).
Definition segE : statement := ltac:(get_stmt (suf 74 body0)).

(* main's body and its parts in sequence are the same statements up to the association of the sequences *)
Definition body_of_parts : statement :=
  Ssequence
    (Ssequence segA1 (Ssequence segA2 (Ssequence segA3 (Ssequence loopD (Ssequence segB
       (Ssequence segC (Ssequence loopI segE)))))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint))).

Lemma body_parts : unfold_Ssequence body_of_parts = unfold_Ssequence (fn_body f_main).
Proof. reflexivity. Qed.

(** ** Type contexts and postcondition of main's body *)
Definition Delta_s : tycontext := func_tycontext f_main (QPvarspecs p) Gmain nil.
(* inflate() with SpecW's specification (the sessions without a header), with RTH9Spec's (with one) *)
Definition Delta_W : tycontext := func_tycontext f_main (QPvarspecs p) Gmain_W nil.
Definition Delta_9 : tycontext := func_tycontext f_main (QPvarspecs p) Gmain_9 nil.

Definition POST_s : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(** ** The values main draws and its objects *)
Record setup := mkSU {
  su_level : Z; su_wbits : Z; su_mem : Z; su_strategy : Z;   (* deflateInit2's parameters *)
  su_choice : Z;                                             (* choice *)
  su_dict : list Z;                                          (* the dictionary's bytes (dict_len of them) *)
  su_xf : list Z; su_nm : list Z; su_cm : list Z;            (* extra's bytes, name's and comment's without the 0 *)
  su_data : list Z; su_cap : Z;                              (* the data, out_size *)
  su_text : Z; su_time : Z; su_os : Z; su_hcrc : Z;          (* the header's scalar fields *)
  su_dictp : val; su_xp : val; su_np : val; su_cmp : val;    (* the objects dict, extra, name, comment *)
  su_dp : val;                                               (* data *)
  su_dcp : val; su_xcp : val; su_ncp : val; su_ccp : val;    (* dict_copy, extra_copy, name_copy, comment_copy *)
  su_ep : val; su_cp : val; su_op : val;                     (* expected, compressed, out *)
  su_gxp : val; su_gnp : val; su_gcp : val }.                (* got's buffers extra, name, comment *)

Definition nzbytes (l : list Z) : Prop := Forall (fun b => 0 < b < 256) l.

(* the draws and the first five objects (statements 0-23) *)
Definition su_dok (u : setup) : Prop :=
  rs32 (su_level u) /\ rs32 (su_wbits u) /\ rs32 (su_mem u) /\ rs32 (su_strategy u) /\
  rparams_ok (su_level u) 8 (su_wbits u) (su_mem u) (su_strategy u) = true /\
  0 <= su_choice u <= 255 /\
  1 <= Zlength (su_dict u) <= 4294967295 /\ rbytes (su_dict u) /\
  Zlength (su_xf u) <= 65535 /\ rbytes (su_xf u) /\
  Zlength (su_nm u) <= 4294967294 /\ nzbytes (su_nm u) /\
  Zlength (su_cm u) <= 4294967294 /\ nzbytes (su_cm u) /\
  Zlength (su_data u) <= max_size /\ rbytes (su_data u) /\ 0 <= su_cap u <= max_size /\
  rs32 (su_text u) /\ 0 <= su_time u <= 4294967295 /\ rs32 (su_os u) /\ rs32 (su_hcrc u) /\
  isptr (su_dictp u) /\ isptr (su_xp u) /\ isptr (su_np u) /\ isptr (su_cmp u) /\ isptr (su_dp u).

(* and the other objects (statements 24-46) *)
Definition su_ok (u : setup) : Prop :=
  su_dok u /\
  isptr (su_dcp u) /\ isptr (su_xcp u) /\ isptr (su_ncp u) /\ isptr (su_ccp u) /\
  isptr (su_ep u) /\ isptr (su_cp u) /\ isptr (su_op u) /\
  isptr (su_gxp u) /\ isptr (su_gnp u) /\ isptr (su_gcp u).

(* with_dict, with_head *)
Definition with_dict (u : setup) : bool := (su_wbits u <=? 15) && Z.odd (su_choice u).
Definition with_head (u : setup) : bool := (15 <? su_wbits u) && Z.odd (su_choice u).

(* bit m of choice is set; head.extra, head.name, head.comment: the object when its bit is set, else Z_NULL *)
Definition has (u : setup) (m : Z) : bool := negb (Z.land (su_choice u) m =? 0).
Definition selp (u : setup) (m : Z) (q : val) : val := if has u m then q else nullval.
Definition selo (u : setup) (m : Z) (l : list Z) : option (list Z) := if has u m then Some l else None.

(* the gzip header head (given to deflateSetHeader with a header) *)
Definition gh_of (u : setup) : DS7.gzh :=
  DS7.mkGZ (su_text u) (su_time u) (su_os u) (selo u 2 (su_xf u)) (Zlength (su_xf u))
    (selo u 4 (su_nm u ++ [0])) (selo u 8 (su_cm u ++ [0])) (su_hcrc u).

(* got as inflateGetHeader receives it: buffers of extra_len, name_len + 1, comment_len + 1 bytes *)
Definition h0 (u : setup) : IR.hstate :=
  IR.HS 0 0 0 0 true 0 (Zlength (su_xf u)) (Zrepeat 0 (Zlength (su_xf u)))
    true (Zlength (su_nm u) + 1) (Zrepeat 0 (Zlength (su_nm u) + 1))
    true (Zlength (su_cm u) + 1) (Zrepeat 0 (Zlength (su_cm u) + 1)) 0 0.

(* the session of the inflate side: the dictionary when one is set ([] otherwise), the header when one is set *)
Definition sdict (u : setup) : list Z := if with_dict u then su_dict u else [].
Definition sgh (u : setup) : option DS7.gzh := if with_head u then Some (gh_of u) else None.
Definition scase_of (u : setup) : scase := SC (su_wbits u) (sdict u) (sgh u) (h0 u).

(* the temporaries: the drawn values with [w] the value of window_bits (su_wbits, then rts_iw su_wbits once main
   changed 8 into 9), dict and data; the other objects; extra, name and comment (until head holds them) *)
Definition d_locals (u : setup) (w : Z) : list localdef :=
  [temp _level (vi (su_level u)); temp _window_bits (vi w); temp _mem_level (vi (su_mem u));
   temp _strategy (vi (su_strategy u)); temp _choice (vi (su_choice u));
   temp _with_dict (vi (Z.b2z (with_dict u))); temp _with_head (vi (Z.b2z (with_head u)));
   temp _dict_len (vl (Zlength (su_dict u))); temp _extra_len (vl (Zlength (su_xf u)));
   temp _name_len (vl (Zlength (su_nm u))); temp _comment_len (vl (Zlength (su_cm u)));
   temp _data_len (vl (Zlength (su_data u))); temp _out_size (vl (su_cap u));
   temp _text (vi (su_text u)); temp _time (vl (su_time u)); temp _os (vi (su_os u)); temp _hcrc (vi (su_hcrc u));
   temp _dict (su_dictp u); temp _data (su_dp u)].
Definition c_locals (u : setup) : list localdef :=
  [temp _dict_copy (su_dcp u); temp _extra_copy (su_xcp u); temp _name_copy (su_ncp u);
   temp _comment_copy (su_ccp u); temp _expected (su_ep u); temp _compressed (su_cp u); temp _out (su_op u)].
Definition o_locals (u : setup) : list localdef :=
  [temp _extra (su_xp u); temp _name (su_np u); temp _comment (su_cmp u)].

Definition lv_locals (gv : globals) (vh vg vc va vd : val) : list localdef :=
  [lvar _decompressor t_z vd; lvar _at t_p va; lvar _compressor t_z vc; lvar _got t_g vg; lvar _head t_g vh;
   gvars gv].

(* a malloc'ed object of exactly the bytes l; a malloc'ed object of n bytes never written *)
Definition bobj (q : val) (l : list Z) : mpred :=
  malloc_token Ews (tarray tuchar (Zlength l)) q * data_at Ews (tarray tuchar (Zlength l)) (map vi l) q.
Definition cnew (q : val) (n : Z) : mpred :=
  malloc_token Ews (tarray tuchar n) q * data_at_ Ews (tarray tuchar n) q.

(* an object of n bytes holding the bytes l first, undefined bytes after *)
Definition cbytes (n : Z) (l : list Z) : list val := map vi l ++ Zrepeat Vundef (n - Zlength l).

(* data, expected (dobj); compressed: the deflate output O so far; out: the inflate output so far *)
Definition datobj (u : setup) : mpred := bobj (su_dp u) (su_data u).
Definition eobj (u : setup) : mpred := bobj (su_ep u) (su_data u).
Definition dobj (u : setup) : mpred := datobj u * eobj u.
Definition cobj (u : setup) (O : list Z) : mpred :=
  malloc_token Ews (tarray tuchar (su_cap u)) (su_cp u) *
  data_at Ews (tarray tuchar (su_cap u)) (cbytes (su_cap u) O) (su_cp u).
Definition oobj (u : setup) (ob : list Z) : mpred :=
  malloc_token Ews (tarray tuchar (Zlength (su_data u))) (su_op u) *
  data_at Ews (tarray tuchar (Zlength (su_data u))) (cbytes (Zlength (su_data u)) ob) (su_op u).

(* the dictionary and its copy *)
Definition dictobj (u : setup) : mpred := bobj (su_dictp u) (su_dict u).
Definition dcopy (u : setup) : mpred := bobj (su_dcp u) (su_dict u).

(* extra, name, comment (with their zero byte) and their copies *)
Definition hcopies (u : setup) : mpred :=
  bobj (su_xcp u) (su_xf u) * bobj (su_ncp u) (su_nm u ++ [0]) * bobj (su_ccp u) (su_cm u ++ [0]).
Definition hobjs (u : setup) : mpred :=
  bobj (su_xp u) (su_xf u) * bobj (su_np u) (su_nm u ++ [0]) * bobj (su_cmp u) (su_cm u ++ [0]) * hcopies u.

(* head with its fields stored (statements 31-38); xflags, extra_max, name_max, comm_max and done never written *)
Definition hvals (u : setup) : reptype t_g :=
  (vi (su_text u), (vl (su_time u), (Vundef, (vi (su_os u), (selp u 2 (su_xp u), (vi (Zlength (su_xf u)),
   (Vundef, (selp u 4 (su_np u), (Vundef, (selp u 8 (su_cmp u), (Vundef, (vi (su_hcrc u), Vundef)))))))))))).

(* got before inflateGetHeader: its buffers and their sizes (statements 39-44); everything else never written *)
Definition gval (u : setup) : reptype t_g :=
  (Vundef, (Vundef, (Vundef, (Vundef, (su_gxp u, (Vundef, (vi (Zlength (su_xf u)), (su_gnp u,
   (vi (Zlength (su_nm u) + 1), (su_gcp u, (vi (Zlength (su_cm u) + 1), (Vundef, Vundef)))))))))))).
Definition gbufs (u : setup) : mpred :=
  cnew (su_gxp u) (Zlength (su_xf u)) * cnew (su_gnp u) (Zlength (su_nm u) + 1) *
  cnew (su_gcp u) (Zlength (su_cm u) + 1).

(* the malloc tokens of got's buffers of non-zero size, once inflate holds got (a zero-size one is in
   head_mem8's / head_mem9's btok) *)
Definition nbtok (q : val) (n : Z) : mpred := if zeq n 0 then emp else malloc_token Ews (tarray tuchar n) q.
Definition gtoks (u : setup) : mpred :=
  nbtok (su_gxp u) (Zlength (su_xf u)) * nbtok (su_gnp u) (Zlength (su_nm u) + 1) *
  nbtok (su_gcp u) (Zlength (su_cm u) + 1).

(** ** The compressor between deflate() calls *)
(* the deflate state and the caller's fields of the z_stream *)
Record cst := mkCS {
  cs_s : dstate; cs_ni : val; cs_ain : Z; cs_tin : Z; cs_no : val; cs_aout : Z; cs_tout : Z;
  cs_msgv : val; cs_adler : Z }.

(* the rest of the local compressor after the split of its Tsh into Ews and its complement: the complement,
   and the Ews share of the struct's padding *)
Definition srest (vc : val) : mpred := data_at_ BoundKit.Ecomp t_z vc * BoundKit.strm_pad vc.

(* [ghp]: the stream's gzhead pointer (&head with a header, Z_NULL otherwise) *)
Definition cstream (gv : globals) (vc ghp : val) (c : cst) : mpred :=
  dstream 2 (Some (cs_s c)) vc ghp gv *
  api_fields vc (cs_ni c) (cs_ain c) (cs_tin c) (cs_no c) (cs_aout c) (cs_tout c) (cs_msgv c) (cs_adler c) *
  srest vc.

(* the state of the deflate loop at its head (rt_stream's): the data consumed D (next_in = data + |D|), the output
   O (next_out = compressed + |O|), fin (Some R once Z_FINISH was given, R the data not consumed since), the bytes
   offered so far, the flush of the last draw, the model's strm->msg, the compressor *)
Record dls := mkDL {
  dl_D : list Z; dl_O : list Z; dl_fin : option (list Z); dl_off : Z; dl_flush : Z; dl_msg : option Z;
  dl_c : cst }.

Definition dl_ok (J : ses_dinv) (u : setup) (l : dls) : Prop :=
  let n := Zlength (su_data u) in
  J (su_wbits u) (sdict u) (sgh u) (dl_D l) (dl_O l) (dl_fin l) (cs_s (dl_c l)) (cs_tin (dl_c l))
    (cs_tout (dl_c l)) (cs_adler (dl_c l)) /\
  dl_D l = sublist 0 (Zlength (dl_D l)) (su_data u) /\ Zlength (dl_D l) <= dl_off l <= n /\
  0 <= dl_flush l <= 5 /\ (dl_flush l = Z_FINISH -> dl_off l = n /\ n - Zlength (dl_D l) <= 4294967295) /\
  (forall R, dl_fin l = Some R -> dl_flush l = Z_FINISH /\ R = sublist (Zlength (dl_D l)) n (su_data u)) /\
  Zlength (dl_O l) <= su_cap u /\ rbytes (dl_O l) /\ msg_ok (dl_msg l) (cs_msgv (dl_c l)) /\
  cs_ni (dl_c l) = offset_val (Zlength (dl_D l)) (su_dp u) /\
  cs_no (dl_c l) = offset_val (Zlength (dl_O l)) (su_cp u).

(** ** The input object of inflate: O, then any bytes *)
Definition iobj (src : list Z) (ip : val) : mpred :=
  malloc_token Ews (tarray tuchar (Zlength src)) ip * data_at Ews (tarray tuchar (Zlength src)) (map vi src) ip.

(** ** The decompressor between inflate() calls *)
(* the bytes of src consumed (next_in = input + pos), the bytes produced (next_out = out + |out|), the flag asked,
   the live state and the fields of the stream *)
Record ils := mkIL { il_pos : Z; il_out : list Z; il_asked : bool; il_L : live; il_z : zfields }.

Definition il_ok (P : ses_iinv) (u : setup) (O src : list Z) (ip : val) (l : ils) : Prop :=
  P (scase_of u) (su_data u) O src (il_pos l) (il_out l) (il_asked l) (il_L l) (zf_tout (il_z l)) /\
  swfW (l_s (il_L l)) /\
  0 <= il_pos l <= Zlength src /\ (exists rest, su_data u = il_out l ++ rest) /\
  zf_ni (il_z l) = offset_val (il_pos l) ip /\
  zf_no (il_z l) = offset_val (Zlength (il_out l)) (su_op u).

(* got attached to the stream: the live state's header pointers are got and its buffers *)
Definition got_at (u : setup) (vg : val) (L : live) : Prop :=
  l_headp L = vg /\ l_hsh L = Tsh /\ l_xb L = su_gxp u /\ l_nb L = su_gnp u /\ l_cb L = su_gcp u.

(** ** The assertions *)
Section Assertions.
Context (gv : globals) (vh vg vc va vd : val).

Definition lvs : list localdef := lv_locals gv vh vg vc va vd.

(* the gzhead pointer of the compressor *)
Definition ghp (u : setup) : val := if with_head u then vh else nullval.

(* head with its objects and their copies; got with its buffers, before inflateGetHeader *)
Definition hobj (u : setup) : mpred := data_at Tsh t_g (hvals u) vh * hobjs u.
Definition graw (u : setup) : mpred := data_at Tsh t_g (gval u) vg * gbufs u.

(* while the compressor may hold head: the header part of the state and the rest [Hr] give head back, whatever the
   state, as long as its gzhead is unchanged *)
Definition hclose (u : setup) (s : dstate) (hx : share * val * val * val) (Hr : mpred) : Prop :=
  forall s', d_gzhead s' = d_gzhead s -> hdr_at (Some s') (ghp u) hx * Hr |-- hobj u.

(* after start_function *)
Definition PRE0 : environ -> mpred :=
  PROPx [] (LOCALx lvs
  (SEPx [data_at_ Tsh t_z vd; data_at_ Tsh t_p va; data_at_ Tsh t_z vc; data_at_ Tsh t_g vg; data_at_ Tsh t_g vh;
         mem_mgr gv; Rm gv])).

(* A24 (statement 24): everything drawn; dict, extra, name, comment and data allocated, none NULL *)
Definition A24 (u : setup) : environ -> mpred :=
  PROPx [su_dok u]
  (LOCALx (o_locals u ++ d_locals u (su_wbits u) ++ lvs)
  (SEPx [data_at_ Tsh t_z vd; data_at_ Tsh t_p va; data_at_ Tsh t_z vc; data_at_ Tsh t_g vg; data_at_ Tsh t_g vh;
         mem_mgr gv; Rm gv; dictobj u; bobj (su_xp u) (su_xf u); bobj (su_np u) (su_nm u ++ [0]);
         bobj (su_cmp u) (su_cm u ++ [0]); datobj u])).

(* A47 (statement 47): the copies made, compressed, out and got's buffers allocated, none NULL; head's and got's
   fields stored *)
Definition A47 (u : setup) : environ -> mpred :=
  PROPx [su_ok u]
  (LOCALx (c_locals u ++ d_locals u (su_wbits u) ++ lvs)
  (SEPx [data_at_ Tsh t_z vc; data_at_ Tsh t_z vd; mem_mgr gv; Rm gv; dobj u; cobj u []; oobj u [];
         data_at_ Tsh t_p va; hobj u; graw u; dictobj u; dcopy u])).

(* DI: the deflate loop's head (rt_stream's DI): the invariant J of the session's dictionary and header *)
Definition DI (J : ses_dinv) (u : setup) (l : dls) (hx : share * val * val * val) (Hr : mpred)
    : environ -> mpred :=
  PROPx [su_ok u; dl_ok J u l; hclose u (cs_s (dl_c l)) hx Hr]
  (LOCALx (temp _offered (vl (dl_off l)) :: temp _flush (vi (dl_flush l)) ::
           c_locals u ++ d_locals u (su_wbits u) ++ lvs)
  (SEPx [cstream gv vc (ghp u) (dl_c l); data_at_ Tsh t_z vd; mem_mgr gv; Rm gv;
         dobj u; cobj u (dl_O l); oobj u []; data_at_ Tsh t_p va;
         hdr_at (Some (cs_s (dl_c l))) (ghp u) hx; Hr; graw u; dictobj u; dcopy u])).

(* DE: deflate returned Z_STREAM_END: O is a finished stream of the data with the session's dictionary and header;
   head is given back *)
Definition DE (u : setup) (O : list Z) (c : cst) : environ -> mpred :=
  PROPx [su_ok u; dfinal (sdict u) (rwrap_of (su_wbits u)) (rwbe (su_wbits u)) (sgh u) (su_data u) O;
         Zlength O <= su_cap u; rbytes O; cs_no c = offset_val (Zlength O) (su_cp u)]
  (LOCALx (c_locals u ++ d_locals u (su_wbits u) ++ lvs)
  (SEPx [cstream gv vc (ghp u) c; data_at_ Tsh t_z vd; mem_mgr gv; Rm gv; dobj u; cobj u O; oobj u [];
         data_at_ Tsh t_p va; hobj u; graw u; dictobj u; dcopy u])).

(* DB: the input object [ip] holds src = O followed by any bytes; the session is one SIFacts.sc_ok accepts *)
Definition DB (u : setup) (O : list Z) (c : cst) (src : list Z) (ip : val) : environ -> mpred :=
  PROPx [su_ok u; sc_ok (scase_of u) (su_data u) O;
         Zlength O <= su_cap u; rbytes O; cs_no c = offset_val (Zlength O) (su_cp u);
         SIFacts.src_ok O src; isptr ip]
  (LOCALx (temp _compressed_len (vl (Zlength O)) :: temp _after (vl (Zlength src - Zlength O)) ::
           temp _input ip :: c_locals u ++ d_locals u (su_wbits u) ++ lvs)
  (SEPx [cstream gv vc (ghp u) c; data_at_ Tsh t_z vd; mem_mgr gv; Rm gv; dobj u; cobj u O; oobj u [];
         data_at_ Tsh t_p va; iobj src ip; hobj u; graw u; dictobj u; dcopy u])).

(* II_W: the inflate loop's head without a header (istreamA, SpecW) *)
Definition II_W (P : ses_iinv) (u : setup) (O : list Z) (c : cst) (src : list Z) (ip : val) (l : ils)
    : environ -> mpred :=
  PROPx [su_ok u; with_head u = false; sc_ok (scase_of u) (su_data u) O; Zlength O <= su_cap u; rbytes O;
         il_ok P u O src ip l; SIFacts.src_ok O src; isptr ip]
  (LOCALx (temp _asked (vi (Z.b2z (il_asked l))) ::
           temp _compressed_len (vl (Zlength O)) :: temp _after (vl (Zlength src - Zlength O)) ::
           temp _input ip :: c_locals u ++ d_locals u (rts_iw (su_wbits u)) ++ lvs)
  (SEPx [istreamA gv Tsh vd (il_z l) Vundef (Some (il_L l)); head_opt (Some (il_L l));
         cstream gv vc (ghp u) c; mem_mgr gv; zfuncs gv; Rm gv; dobj u; cobj u O; oobj u (il_out l);
         data_at_ Tsh t_p va; iobj src ip; hobj u; graw u; dictobj u; dcopy u])).

(* II_9: the inflate loop's head with a header (istream8, got attached: RTH9Spec.head_mem9) *)
Definition II_9 (P : ses_iinv) (u : setup) (O : list Z) (c : cst) (src : list Z) (ip : val) (l : ils)
    : environ -> mpred :=
  PROPx [su_ok u; with_head u = true; sc_ok (scase_of u) (su_data u) O; Zlength O <= su_cap u; rbytes O;
         il_ok P u O src ip l; got_at u vg (il_L l); SIFacts.src_ok O src; isptr ip]
  (LOCALx (temp _asked (vi (Z.b2z (il_asked l))) ::
           temp _compressed_len (vl (Zlength O)) :: temp _after (vl (Zlength src - Zlength O)) ::
           temp _input ip :: c_locals u ++ d_locals u (rts_iw (su_wbits u)) ++ lvs)
  (SEPx [Zlib.proof.roundtrip.RTH8Spec.istream8 gv Tsh vd (il_z l) (Some (il_L l));
         Zlib.proof.roundtrip.RTH9Spec.head_mem9 (il_L l); gtoks u;
         cstream gv vc (ghp u) c; mem_mgr gv; zfuncs gv; Rm gv; dobj u; cobj u O; oobj u (il_out l);
         data_at_ Tsh t_p va; iobj src ip; hobj u; dictobj u; dcopy u])).

(* IE_W: without a header, inflate returned Z_STREAM_END having read exactly O, produced exactly the data, asked
   for the dictionary exactly when one was set with the zlib wrapper *)
Definition IE_W (u : setup) (O : list Z) (c : cst) (src : list Z) (ip : val) (z : zfields) (L : live)
    : environ -> mpred :=
  PROPx [su_ok u; with_head u = false; Zlength O <= su_cap u;
         zf_ni z = offset_val (Zlength O) ip; zf_no z = offset_val (Zlength (su_data u)) (su_op u);
         SIFacts.src_ok O src; isptr ip]
  (LOCALx (temp _asked (vi (Z.b2z (with_dict u && (0 <? su_wbits u)))) ::
           temp _compressed_len (vl (Zlength O)) :: temp _after (vl (Zlength src - Zlength O)) ::
           temp _input ip :: c_locals u ++ d_locals u (rts_iw (su_wbits u)) ++ lvs)
  (SEPx [istreamA gv Tsh vd z Vundef (Some L); head_opt (Some L);
         cstream gv vc (ghp u) c; mem_mgr gv; zfuncs gv; Rm gv; dobj u; cobj u O; oobj u (su_data u);
         data_at_ Tsh t_p va; iobj src ip; hobj u; graw u; dictobj u; dcopy u])).

(* IE_9: with a header, the same, and got holds every field of head (G2IFacts.g2_hdr_out; RTH8Spec.head_mem8, as
   rt_gzip_header's A40) *)
Definition IE_9 (u : setup) (O : list Z) (c : cst) (src : list Z) (ip : val) (z : zfields) (L : live)
    : environ -> mpred :=
  PROPx [su_ok u; with_head u = true; Zlength O <= su_cap u;
         zf_ni z = offset_val (Zlength O) ip; zf_no z = offset_val (Zlength (su_data u)) (su_op u);
         SIFacts.src_ok O src; isptr ip;
         g2_hdr_out (gh_of u) (h0 u) (l_s L) (l_h L); IR.i_head (l_s L) = true; got_at u vg L]
  (LOCALx (temp _asked (vi (Z.b2z (with_dict u && (0 <? su_wbits u)))) ::
           temp _compressed_len (vl (Zlength O)) :: temp _after (vl (Zlength src - Zlength O)) ::
           temp _input ip :: c_locals u ++ d_locals u (rts_iw (su_wbits u)) ++ lvs)
  (SEPx [Zlib.proof.roundtrip.RTH8Spec.istream8 gv Tsh vd z (Some L);
         Zlib.proof.roundtrip.RTH8Spec.head_mem8 L; gtoks u;
         cstream gv vc (ghp u) c; mem_mgr gv; zfuncs gv; Rm gv; dobj u; cobj u O; oobj u (su_data u);
         data_at_ Tsh t_p va; iobj src ip; hobj u; dictobj u; dcopy u])).

End Assertions.

(** ** The parts *)

Definition segA1_stmt : Prop :=
  forall {Espec : OracleKind} gv vh vg vc va vd,
  semax Delta_s (PRE0 gv vh vg vc va vd) segA1 (overridePost (EX u : setup, A24 gv vh vg vc va vd u) POST_s).

Definition segA2_stmt : Prop :=
  forall {Espec : OracleKind} gv vh vg vc va vd u,
  semax Delta_s (A24 gv vh vg vc va vd u) segA2
    (overridePost (EX u' : setup, A47 gv vh vg vc va vd u') POST_s).

Definition segA3_stmt : Prop :=
  forall {Espec : OracleKind} J gv vh vg vc va vd u, ses_dfacts J ->
  semax Delta_s (A47 gv vh vg vc va vd u) segA3
    (overridePost (EX l : dls, EX hx : share * val * val * val, EX Hr : mpred,
                     DI gv vh vg vc va vd J u l hx Hr) POST_s).

(* the do-while loop (Clight: Sloop body (if (code != Z_STREAM_END) skip else break)) from its invariant *)
Definition loopD_stmt : Prop :=
  forall {Espec : OracleKind} J gv vh vg vc va vd u hx Hr, ses_dfacts J ->
  semax Delta_s (EX l : dls, DI gv vh vg vc va vd J u l hx Hr) loopD
    (overridePost (EX O : list Z, EX c : cst, DE gv vh vg vc va vd u O c) POST_s).

Definition segB_stmt : Prop :=
  forall {Espec : OracleKind} gv vh vg vc va vd u O c,
  semax Delta_s (DE gv vh vg vc va vd u O c) segB
    (overridePost (EX src : list Z, EX ip : val, DB gv vh vg vc va vd u O c src ip) POST_s).

Definition segC_W_stmt : Prop :=
  forall {Espec : OracleKind} P PN gv vh vg vc va vd u O c src ip,
  ses_ifacts (fun _ => True) P PN -> with_head u = false ->
  semax Delta_s (DB gv vh vg vc va vd u O c src ip) segC
    (overridePost (EX l : ils, II_W gv vh vg vc va vd P u O c src ip l) POST_s).

Definition segC_9_stmt : Prop :=
  forall {Espec : OracleKind} P PN gv vh vg vc va vd u O c src ip,
  ses_ifacts (fun _ => True) P PN -> with_head u = true ->
  semax Delta_s (DB gv vh vg vc va vd u O c src ip) segC
    (overridePost (EX l : ils, II_9 gv vh vg vc va vd P u O c src ip l) POST_s).

Definition loopI_W_stmt : Prop :=
  forall {Espec : OracleKind} P PN gv vh vg vc va vd u O c src ip,
  ses_ifacts (fun _ => True) P PN ->
  semax Delta_W (EX l : ils, II_W gv vh vg vc va vd P u O c src ip l) loopI
    (overridePost (EX z : zfields, EX L : live, IE_W gv vh vg vc va vd u O c src ip z L) POST_s).

Definition loopI_9_stmt : Prop :=
  forall {Espec : OracleKind} P PN gv vh vg vc va vd u O c src ip,
  ses_ifacts (fun _ => True) P PN ->
  semax Delta_9 (EX l : ils, II_9 gv vh vg vc va vd P u O c src ip l) loopI
    (overridePost (EX z : zfields, EX L : live, IE_9 gv vh vg vc va vd u O c src ip z L) POST_s).

Definition segE_W_stmt : Prop :=
  forall {Espec : OracleKind} gv vh vg vc va vd u O c src ip z L,
  semax Delta_s (IE_W gv vh vg vc va vd u O c src ip z L) segE POST_s.

Definition segE_9_stmt : Prop :=
  forall {Espec : OracleKind} gv vh vg vc va vd u O c src ip z L,
  semax Delta_s (IE_9 gv vh vg vc va vd u O c src ip z L) segE POST_s.
