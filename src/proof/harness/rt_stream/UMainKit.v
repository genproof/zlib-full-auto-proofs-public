(* Law rt_stream (harness/rt_stream.c, data of any length): the kit of main's body proof.

   Round 1's MainKit.v for the harness of data of any length: the same cut of main's body (the deflate loop and
   the inflate loop cut their pieces with clip() and draw them with upto()), the same assertions, with the sizes
   of the harness (data and out_size up to PTRDIFF_MAX), the model facts of UDFacts.v / UIFacts.v and the context
   Gmain_u (MainStmt.Gmain, clip() and copy_of()).  Before compressing, main copies the data (copy_of) into the
   object [expected]; the output is compared with that copy.

   main's body is [Ssequence b0 (return 0)]; b0 is a right-nested sequence of statements, 0-based:
     0-3   the draws of level, window_bits, mem_level, strategy,  4  gp_assume(deflate_params_ok(...)),
     5-7   the draws of data_len, out_size, data,  8  the NULL test of data,  9  expected = copy_of(data,
           data_len),  10-11  compressed, out,  12  the NULL test of expected, compressed, out;
     13    new_stream(&compressor),  14  code = deflateInit2_(...),  15  Z_MEM_ERROR: return,
     16    gp_assert(code == Z_OK),  17-20  next_in, next_out, offered, flush;
     21    the deflate loop (do { read; if (flush != Z_FINISH) { offered, flush drawn; Z_FINISH only when the rest
           fits in one call }; avail_in = clip(offered - read); avail_out = clip(upto(room)); position_of(&compressor,
           &at); deflate(&compressor, flush); no output space offered: gp_assert(code == Z_BUF_ERROR &&
           unmoved(&compressor, &at)); out of room: return } while (code != Z_STREAM_END));
     22    compressed_len,  23  new_stream(&decompressor),  24  window_bits 8 -> 9,
     25    code = inflateInit2_(...),  26  Z_MEM_ERROR: return,  27  gp_assert(code == Z_OK),  28-29  next_in, next_out;
     30    the inflate loop (do { avail_in = clip(upto(rest)); avail_out = clip(upto(room)); position_of(&decompressor,
           &at); inflate(&decompressor, any flush); ...; neither input nor output space offered:
           gp_assert(code != Z_OK && unmoved(&decompressor, &at)) } while (code != Z_STREAM_END));
     31... the final checks and return 0.
   The parts, as Hoare triples between the assertions below (a return inside a part goes to main's
   postcondition POST_m):
     segA  (0-20)                 PRE0 -> DI
     loopD (21, the deflate loop) DI (its invariant) -> DE (after deflate returned Z_STREAM_END)
     segC  (22-29)                DE -> II
     loopI (30, the inflate loop) II (its invariant) -> IE (after inflate returned Z_STREAM_END)
     segE  (31...)                IE -> return
   The invariants use only the fields of the abstract model facts (UDFacts.urts_dfacts J, UIFacts.urts_ifacts P).

   Memory: the local z_stream compressor is split into Ews (the deflate specifications' share) and its
   complement (BoundKit.Ecomp, kept with the struct's padding as [srest] until a return); the decompressor
   is an istreamA (SpecW) once inflateInit2_ returned Z_OK.  The objects data, compressed and out are
   malloc'ed: data and expected hold the data's bytes; compressed holds the deflate output O so far, then undefined bytes
   ([cbytes]); out holds the bytes inflate produced so far, then undefined bytes.  The local struct position at
   (laws_session.h), written by position_of before each call and read after it, is any bytes ([data_at_]) at the
   heads of the loops and between the parts. *)
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
Require Import Zlib.proof.harness.rt_stream.UDFacts.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.rt_stream.UIFacts.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream.UMainStmt.
Require Import Zlib.harness.rt_stream.code.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.

Definition t_z : type := Tstruct _z_stream_s noattr.
Definition t_p : type := Tstruct _position noattr.

(** ** Cutting main's body into its parts *)

(* b0: main's body without the final return *)
Definition body0 : statement := match fn_body f_main with Ssequence b _ => b | s => s end.

(* the statements of a right-nested sequence from position k on, and its first k statements *)
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

(* the first statement of a sequence *)
Definition first (s : statement) : statement := match s with Ssequence a _ => a | _ => s end.

Ltac get_stmt e :=
  let x := eval cbv beta iota zeta delta [take suf first body0 f_main fn_body] in e in
  exact x.

Definition segA : statement := ltac:(get_stmt (take 21 body0)).
Definition loopD : statement := ltac:(get_stmt (first (suf 21 body0))).
Definition segC : statement := ltac:(get_stmt (take 8 (suf 22 body0))).
Definition loopI : statement := ltac:(get_stmt (first (suf 30 body0))).
Definition segE : statement := ltac:(get_stmt (suf 31 body0)).

(* main's body and its parts in sequence are the same statements up to the association of the sequences *)
Definition body_of_parts : statement :=
  Ssequence (Ssequence segA (Ssequence loopD (Ssequence segC (Ssequence loopI segE))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint))).

Lemma body_parts : unfold_Ssequence body_of_parts = unfold_Ssequence (fn_body f_main).
Proof. reflexivity. Qed.

(** ** Type context and postcondition of main's body *)
Definition Delta_m : tycontext := func_tycontext f_main (QPvarspecs p) Gmain_u nil.

Definition POST_m : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(** ** The values main draws and its objects *)
Record setup := mkSU {
  su_level : Z; su_wbits : Z; su_mem : Z; su_strategy : Z;   (* deflateInit2's parameters *)
  su_data : list Z; su_cap : Z;                              (* the data, out_size *)
  su_dp : val; su_ep : val; su_cp : val; su_op : val }.      (* the objects data, expected, compressed, out *)

Definition su_ok (u : setup) : Prop :=
  rs32 (su_level u) /\ rs32 (su_wbits u) /\ rs32 (su_mem u) /\ rs32 (su_strategy u) /\
  Zlength (su_data u) <= max_size /\ rbytes (su_data u) /\ 0 <= su_cap u <= max_size /\
  isptr (su_dp u) /\ isptr (su_cp u) /\ isptr (su_op u).

(* the temporaries of the drawn values; [w] the value of window_bits (su_wbits, then rts_iw su_wbits once
   main changed 8 into 9) *)
Definition su_locals (u : setup) (w : Z) : list localdef :=
  [temp _level (vi (su_level u)); temp _window_bits (vi w); temp _mem_level (vi (su_mem u));
   temp _strategy (vi (su_strategy u)); temp _data_len (vl (Zlength (su_data u))); temp _out_size (vl (su_cap u));
   temp _data (su_dp u); temp _expected (su_ep u); temp _compressed (su_cp u); temp _out (su_op u)].

Definition lv_locals (gv : globals) (vc vd va : val) : list localdef :=
  [lvar _decompressor t_z vd; lvar _at t_p va; lvar _compressor t_z vc; gvars gv].

(* an object of n bytes holding the bytes l first, undefined bytes after *)
Definition cbytes (n : Z) (l : list Z) : list val := map vi l ++ Zrepeat Vundef (n - Zlength l).

(* data and expected: the data's bytes; compressed: the deflate output O so far; out: the inflate output so far *)
Definition eobj (u : setup) : mpred :=
  malloc_token Ews (tarray tuchar (Zlength (su_data u))) (su_ep u) *
  data_at Ews (tarray tuchar (Zlength (su_data u))) (map vi (su_data u)) (su_ep u).
Definition dobj (u : setup) : mpred :=
  malloc_token Ews (tarray tuchar (Zlength (su_data u))) (su_dp u) *
  data_at Ews (tarray tuchar (Zlength (su_data u))) (map vi (su_data u)) (su_dp u) * eobj u.
Definition cobj (u : setup) (O : list Z) : mpred :=
  malloc_token Ews (tarray tuchar (su_cap u)) (su_cp u) *
  data_at Ews (tarray tuchar (su_cap u)) (cbytes (su_cap u) O) (su_cp u).
Definition oobj (u : setup) (ob : list Z) : mpred :=
  malloc_token Ews (tarray tuchar (Zlength (su_data u))) (su_op u) *
  data_at Ews (tarray tuchar (Zlength (su_data u))) (cbytes (Zlength (su_data u)) ob) (su_op u).

(** ** The compressor between deflate() calls *)
(* the deflate state and the caller's fields of the z_stream *)
Record cst := mkCS {
  cs_s : dstate; cs_ni : val; cs_ain : Z; cs_tin : Z; cs_no : val; cs_aout : Z; cs_tout : Z;
  cs_msgv : val; cs_adler : Z }.

(* the rest of the local compressor after the split of its Tsh into Ews and its complement: the complement,
   and the Ews share of the struct's padding *)
Definition srest (vc : val) : mpred := data_at_ BoundKit.Ecomp t_z vc * BoundKit.strm_pad vc.

Definition cstream (gv : globals) (vc : val) (c : cst) : mpred :=
  dstream 2 (Some (cs_s c)) vc nullval gv *
  api_fields vc (cs_ni c) (cs_ain c) (cs_tin c) (cs_no c) (cs_aout c) (cs_tout c) (cs_msgv c) (cs_adler c) *
  srest vc.

(* the state of the deflate loop at its head: the data consumed D (next_in = data + |D|), the output O
   (next_out = compressed + |O|), fin (Some R once Z_FINISH was given, R the data not consumed since), the bytes
   offered so far, the flush of the last draw, the model's strm->msg, the compressor *)
Record dls := mkDL {
  dl_D : list Z; dl_O : list Z; dl_fin : option (list Z); dl_off : Z; dl_flush : Z; dl_msg : option Z;
  dl_c : cst }.

Definition dl_ok (J : urts_dinv) (u : setup) (l : dls) : Prop :=
  let n := Zlength (su_data u) in
  J (su_wbits u) (dl_D l) (dl_O l) (dl_fin l) (cs_s (dl_c l)) (cs_tin (dl_c l)) (cs_tout (dl_c l))
    (cs_adler (dl_c l)) /\
  dl_D l = sublist 0 (Zlength (dl_D l)) (su_data u) /\ Zlength (dl_D l) <= dl_off l <= n /\
  0 <= dl_flush l <= 5 /\ (dl_flush l = Z_FINISH -> dl_off l = n /\ n - Zlength (dl_D l) <= 4294967295) /\
  (forall R, dl_fin l = Some R -> dl_flush l = Z_FINISH /\ R = sublist (Zlength (dl_D l)) n (su_data u)) /\
  Zlength (dl_O l) <= su_cap u /\ rbytes (dl_O l) /\ msg_ok (dl_msg l) (cs_msgv (dl_c l)) /\
  cs_ni (dl_c l) = offset_val (Zlength (dl_D l)) (su_dp u) /\
  cs_no (dl_c l) = offset_val (Zlength (dl_O l)) (su_cp u).

(** ** The decompressor between inflate() calls *)
(* the bytes of O consumed (next_in = compressed + pos), the bytes produced (next_out = out + |out|), the
   live state and the fields of the stream *)
Record ils := mkIL { il_pos : Z; il_out : list Z; il_L : live; il_z : zfields }.

Definition il_ok (P : rts_iinv) (u : setup) (O : list Z) (l : ils) : Prop :=
  P (su_data u) O (il_pos l) (il_out l) (l_s (il_L l)) (zf_tout (il_z l)) /\ swfW (l_s (il_L l)) /\
  0 <= il_pos l <= Zlength O /\ (exists rest, su_data u = il_out l ++ rest) /\
  zf_ni (il_z l) = offset_val (il_pos l) (su_cp u) /\
  zf_no (il_z l) = offset_val (Zlength (il_out l)) (su_op u).

(** ** The assertions *)
Section Assertions.
Context (gv : globals) (vc vd va : val).

(* after start_function *)
Definition PRE0 : environ -> mpred :=
  PROPx [] (LOCALx (lv_locals gv vc vd va)
  (SEPx [data_at_ Tsh t_z vd; data_at_ Tsh t_p va; data_at_ Tsh t_z vc; mem_mgr gv; Rm gv])).

(* DI: the deflate loop's head *)
Definition DI (J : urts_dinv) (u : setup) (l : dls) : environ -> mpred :=
  PROPx [su_ok u; rparams_ok (su_level u) 8 (su_wbits u) (su_mem u) (su_strategy u) = true; dl_ok J u l]
  (LOCALx (temp _offered (vl (dl_off l)) :: temp _flush (vi (dl_flush l)) ::
          su_locals u (su_wbits u) ++ lv_locals gv vc vd va)
  (SEPx [cstream gv vc (dl_c l); data_at_ Tsh t_z vd; mem_mgr gv; Rm gv;
        dobj u; cobj u (dl_O l); oobj u []; data_at_ Tsh t_p va])).

(* DE: deflate returned Z_STREAM_END: O is a finished stream of the data *)
Definition DE (u : setup) (O : list Z) (c : cst) : environ -> mpred :=
  PROPx [su_ok u; rparams_ok (su_level u) 8 (su_wbits u) (su_mem u) (su_strategy u) = true;
        dfinal [] (rwrap_of (su_wbits u)) (rwbe (su_wbits u)) None (su_data u) O;
        Zlength O <= su_cap u; rbytes O; cs_no c = offset_val (Zlength O) (su_cp u)]
  (LOCALx (su_locals u (su_wbits u) ++ lv_locals gv vc vd va)
  (SEPx [cstream gv vc c; data_at_ Tsh t_z vd; mem_mgr gv; Rm gv; dobj u; cobj u O; oobj u []; data_at_ Tsh t_p va])).

(* II: the inflate loop's head *)
Definition II (P : rts_iinv) (u : setup) (O : list Z) (c : cst) (l : ils) : environ -> mpred :=
  PROPx [su_ok u; Zlength O <= su_cap u; rbytes O; il_ok P u O l]
  (LOCALx (temp _compressed_len (vl (Zlength O)) :: su_locals u (rts_iw (su_wbits u)) ++ lv_locals gv vc vd va)
  (SEPx [istreamA gv Tsh vd (il_z l) Vundef (Some (il_L l)); head_opt (Some (il_L l));
        cstream gv vc c; mem_mgr gv; zfuncs gv; Rm gv; dobj u; cobj u O; oobj u (il_out l); data_at_ Tsh t_p va])).

(* IE: inflate returned Z_STREAM_END having read exactly O and produced exactly the data *)
Definition IE (u : setup) (O : list Z) (c : cst) (z : zfields) (L : live) : environ -> mpred :=
  PROPx [su_ok u; Zlength O <= su_cap u;
        zf_ni z = offset_val (Zlength O) (su_cp u);
        zf_no z = offset_val (Zlength (su_data u)) (su_op u)]
  (LOCALx (temp _compressed_len (vl (Zlength O)) :: su_locals u (rts_iw (su_wbits u)) ++ lv_locals gv vc vd va)
  (SEPx [istreamA gv Tsh vd z Vundef (Some L); head_opt (Some L);
        cstream gv vc c; mem_mgr gv; zfuncs gv; Rm gv; dobj u; cobj u O; oobj u (su_data u); data_at_ Tsh t_p va])).

End Assertions.

(** ** The parts *)

Definition segA_stmt : Prop :=
  forall {Espec : OracleKind} J gv vc vd va, urts_dfacts J ->
  semax Delta_m (PRE0 gv vc vd va) segA (overridePost (EX u : setup, EX l : dls, DI gv vc vd va J u l) POST_m).

(* the do-while loop (Clight: Sloop body (if (code != Z_STREAM_END) skip else break)) from its invariant *)
Definition loopD_stmt : Prop :=
  forall {Espec : OracleKind} J gv vc vd va u, urts_dfacts J ->
  semax Delta_m (EX l : dls, DI gv vc vd va J u l) loopD
    (overridePost (EX O : list Z, EX c : cst, DE gv vc vd va u O c) POST_m).

Definition segC_stmt : Prop :=
  forall {Espec : OracleKind} P gv vc vd va u O c, urts_ifacts P ->
  semax Delta_m (DE gv vc vd va u O c) segC
    (overridePost (EX l : ils, II gv vc vd va P u O c l) POST_m).

Definition loopI_stmt : Prop :=
  forall {Espec : OracleKind} P gv vc vd va u O c, urts_ifacts P ->
  semax Delta_m (EX l : ils, II gv vc vd va P u O c l) loopI
    (overridePost (EX z : zfields, EX L : live, IE gv vc vd va u O c z L) POST_m).

Definition segE_stmt : Prop :=
  forall {Espec : OracleKind} gv vc vd va u O c z L,
  semax Delta_m (IE gv vc vd va u O c z L) segE POST_m.
