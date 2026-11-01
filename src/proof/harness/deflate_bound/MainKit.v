(* Law deflate_bound, main (harness/deflate_bound.c): the kit of main's body proof, under DCS.CS (deflate.c +
   trees.c's composites, which include z_stream_s and gz_header_s; the body moves to the law's compspecs by
   entry_shared).

   main's body is [Ssequence b0 (return 0)], b0 a sequence of 56 statements; [msuf k] is statement k of b0 and
   everything after it (then the return).  The part lemmas (Main*.v) are in continuation-passing style: each
   proves the suffix at its first cut from the hypothesis that the suffix at its next cut is proved from the
   assertion there:
     part_pre   (MainPre.v):   msuf 0  (PRE0, after start_function)     -> msuf 34 (stream_defaults), A1
     part_init  (MainInit.v):  msuf 34 (A1)                              -> msuf 37 (dict_set = 0), A2
     part_dict  (MainDict.v):  msuf 37 (A2)                              -> msuf 39 (if (hsel == 0 ...)), A2b
     part_head  (MainHead.v):  msuf 39 (A2b)                             -> msuf 40 (deflateBound), A3
     part_bound (MainBnd.v):   msuf 40 (A3)                              -> msuf 45 (s.next_in = data), A4
     part_run   (MainRun.v):   msuf 45 (A4)                              -> the end
   Main.v assembles them (body_main). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Zlib.proof.compress.CSpec.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.deflate.Obligations.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.harness.x_deflate_bound.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

(** ** main's callees and the resources of the globals *)
Definition Gmain : funspecs :=
  [deflateInit2__spec_v9; deflateSetDictionary_spec; deflateSetHeader_spec; deflateBound_spec; deflate_spec;
   deflateEnd_spec; CSpec.compressBound_spec;
   stream_defaults_spec; deflate_params_ok_spec; draw_nonzero_bytes_spec;
   (_quickproof_malloc, @malloc_spec' DCS.CS); nondet_u32_spec; nondet_u8_spec; @nondet_bytes_spec DCS.CS;
   gp_assert_spec; gp_assume_spec].

Definition vlit : ident := ___stringlit_x_deflate_bound_1.

(* the globals main gets (GlobalsInit.globals_ok, second component) *)
Definition R (gv : globals) : mpred := deflate_globals gv * version_at gv vlit.

Definition Delta_m : tycontext := func_tycontext f_main (QPvarspecs Zlib.contracts.x_deflate_bound.whole_prog) Gmain nil.

(* main's postcondition after start_function (main_core_spec) *)
Definition POST_m : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(** ** Suffixes of main's body *)
Fixpoint suf (k : nat) (s : statement) : statement :=
  match k, s with
  | O, _ => s
  | S k', Ssequence _ b => suf k' b
  | _, _ => Sskip
  end.

Ltac get_msuf k :=
  let x := eval cbv beta iota zeta delta [suf f_main fn_body] in
    (match fn_body f_main with Ssequence b r => Ssequence (suf k b) r | s => s end) in exact x.

Definition msuf0 : statement := ltac:(get_msuf 0%nat).
Definition msuf34 : statement := ltac:(get_msuf 34%nat).
Definition msuf37 : statement := ltac:(get_msuf 37%nat).
Definition msuf39 : statement := ltac:(get_msuf 39%nat).
Definition msuf40 : statement := ltac:(get_msuf 40%nat).
Definition msuf45 : statement := ltac:(get_msuf 45%nat).

Lemma msuf0_body : msuf0 = fn_body f_main.
Proof. reflexivity. Qed.

(** ** The values main draws, and its objects *)
Record bsetup := mkBS {
  b_level : Z; b_wbits : Z; b_mem : Z; b_strategy : Z;
  b_n : Z; b_dlen : Z; b_xlen : Z; b_nl : Z; b_cl : Z; b_mtime : Z;
  b_dsel : Z; b_hsel : Z; b_text : Z; b_os : Z; b_hcrc : Z; b_xsel : Z; b_nsel : Z; b_csel : Z;
  b_datap : val; b_dictp : val; b_xfp : val; b_nfp : val; b_cfp : val;
  (* the contents: data (n bytes), dictionary (dlen), extra field (xlen), name and comment (nl, cl non-zero
     bytes; their objects hold them and a zero byte) *)
  b_data : list Z; b_dict : list Z; b_xf : list Z; b_nm : list Z; b_cm : list Z }.

Definition byte8 (x : Z) : Prop := 0 <= x < 256.
Definition nzbytes (l : list Z) : Prop := Forall (fun b => 0 < b < 256) l.

Definition bs_ok (bs : bsetup) : Prop :=
  s32 (b_level bs) /\ s32 (b_wbits bs) /\ s32 (b_mem bs) /\ s32 (b_strategy bs) /\
  params_ok (b_level bs) 8 (b_wbits bs) (b_mem bs) (b_strategy bs) = true /\
  0 <= b_n bs <= 1048576 /\ 0 <= b_dlen bs <= 32768 /\
  0 <= b_xlen bs <= 4096 /\ 0 <= b_nl bs <= 4096 /\ 0 <= b_cl bs <= 4096 /\ u32r (b_mtime bs) /\
  byte8 (b_dsel bs) /\ byte8 (b_hsel bs) /\ byte8 (b_text bs) /\ byte8 (b_os bs) /\ byte8 (b_hcrc bs) /\
  byte8 (b_xsel bs) /\ byte8 (b_nsel bs) /\ byte8 (b_csel bs) /\
  Zlength (b_data bs) = b_n bs /\ bytes (b_data bs) /\ Zlength (b_dict bs) = b_dlen bs /\ bytes (b_dict bs) /\
  Zlength (b_xf bs) = b_xlen bs /\ bytes (b_xf bs) /\ Zlength (b_nm bs) = b_nl bs /\ nzbytes (b_nm bs) /\
  Zlength (b_cm bs) = b_cl bs /\ nzbytes (b_cm bs) /\
  isptr (b_datap bs) /\ isptr (b_dictp bs) /\ isptr (b_xfp bs) /\ isptr (b_nfp bs) /\ isptr (b_cfp bs).

(* an object of main: malloc'ed, exactly its bytes *)
Definition obj (p : val) (l : list Z) : mpred :=
  @malloc_token DCS.CS Ews (tarray tuchar (Zlength l)) p * @data_at DCS.CS Ews (tarray tuchar (Zlength l)) (map vi l) p.

Definition objs (bs : bsetup) : mpred :=
  obj (b_datap bs) (b_data bs) * obj (b_dictp bs) (b_dict bs) * obj (b_xfp bs) (b_xf bs) *
  obj (b_nfp bs) (b_nm bs ++ [0]) * obj (b_cfp bs) (b_cm bs ++ [0]).

(* the temps of the drawn values and the objects *)
Definition bs_locals (bs : bsetup) : list localdef :=
  [temp _level (vi (b_level bs)); temp _wbits (vi (b_wbits bs)); temp _mem (vi (b_mem bs));
   temp _strategy (vi (b_strategy bs)); temp _n (vi (b_n bs)); temp _dlen (vi (b_dlen bs));
   temp _xlen (vi (b_xlen bs)); temp _nl (vi (b_nl bs)); temp _cl (vi (b_cl bs));
   temp _mtime (vl (b_mtime bs)); temp _dsel (vi (b_dsel bs)); temp _hsel (vi (b_hsel bs));
   temp _text (vi (b_text bs)); temp _os (vi (b_os bs)); temp _hcrc (vi (b_hcrc bs));
   temp _xsel (vi (b_xsel bs)); temp _nsel (vi (b_nsel bs)); temp _csel (vi (b_csel bs));
   temp _data (b_datap bs); temp _dict (b_dictp bs); temp _xf (b_xfp bs); temp _nf (b_nfp bs);
   temp _cf (b_cfp bs)].

(* a dictionary was set: dsel == 0 && wbits <= 15 *)
Definition ds_of (bs : bsetup) : bool := (b_dsel bs =? 0) && (b_wbits bs <=? 15).
(* a header was set: hsel == 0 && wbits > 15 *)
Definition hs_of (bs : bsetup) : bool := (b_hsel bs =? 0) && (15 <? b_wbits bs).

(** ** The stream between the calls: the state and the caller's z_stream fields (next_in and next_out are
    Z_NULL until main sets them for deflate) *)
Record bstrm := mkSt {
  st_s : dstate; st_tin : Z; st_tout : Z; st_adler : Z; st_ain : Z; st_aout : Z;
  st_msg : option Z; st_msgv : val }.

Definition st_fields (vs : val) (st : bstrm) : mpred :=
  api_fields vs nullval (st_ain st) (st_tin st) nullval (st_aout st) (st_tout st) (st_msgv st) (st_adler st).

Section Kit.
Context (Bpre : bpre_inv) (Brun : brun_inv).
Context (gv : globals) (vs vh : val).

(* the rest of the local z_stream s, after the split of its Tsh into Ews (the specs' share) and its complement:
   the complement, and the Ews share of the struct's padding (which the field-wise predicates do not hold) *)
Definition srest : mpred := @data_at_ DCS.CS (Share.comp Ews) t_strm vs * BoundKit.strm_pad vs.

(* the entry (after start_function) *)
Definition PRE0 : environ -> mpred :=
  PROP ()
  LOCAL (lvar _h t_gzh vh; lvar _s t_strm vs; gvars gv)
  SEP (data_at_ Tsh t_gzh vh; data_at_ Tsh t_strm vs; mem_mgr gv; R gv).

(* A1 (msuf 34, before stream_defaults(&s)): everything drawn and allocated *)
Definition A1 (bs : bsetup) : environ -> mpred :=
  PROPx [bs_ok bs]
  (LOCALx (bs_locals bs ++ [lvar _h t_gzh vh; lvar _s t_strm vs; gvars gv])
  (SEPx [data_at_ Tsh t_gzh vh; data_at_ Tsh t_strm vs; mem_mgr gv; deflate_globals gv; version_at gv vlit;
         objs bs])).

(* A2 (msuf 37, before dict_set = 0): deflateInit2 returned Z_OK *)
Definition A2 (bs : bsetup) (st : bstrm) : environ -> mpred :=
  PROPx [bs_ok bs; bound_facts Bpre Brun;
         Bpre (b_level bs) (b_wbits bs) (b_mem bs) (b_strategy bs) false (st_s st) (st_tin st) (st_tout st)
           (st_adler st);
         d_gzhead (st_s st) = None; msg_ok (st_msg st) (st_msgv st)]
  (LOCALx (bs_locals bs ++ [lvar _h t_gzh vh; lvar _s t_strm vs; gvars gv])
  (SEPx [dstream 2 (Some (st_s st)) vs nullval gv; st_fields vs st; srest; data_at_ Tsh t_gzh vh;
         mem_mgr gv; deflate_globals gv; objs bs; TT])).

(* A2b (msuf 39, before if (hsel == 0 && wbits > 15)): the dictionary set when ds_of bs *)
Definition A2b (bs : bsetup) (st : bstrm) : environ -> mpred :=
  PROPx [bs_ok bs; bound_facts Bpre Brun;
         Bpre (b_level bs) (b_wbits bs) (b_mem bs) (b_strategy bs) (ds_of bs) (st_s st) (st_tin st) (st_tout st)
           (st_adler st);
         d_gzhead (st_s st) = None; msg_ok (st_msg st) (st_msgv st)]
  (LOCALx (temp _dict_set (vi (if ds_of bs then 1 else 0)) :: bs_locals bs ++
           [lvar _h t_gzh vh; lvar _s t_strm vs; gvars gv])
  (SEPx [dstream 2 (Some (st_s st)) vs nullval gv; st_fields vs st; srest; data_at_ Tsh t_gzh vh;
         mem_mgr gv; deflate_globals gv; objs bs; TT])).

(* the header part at the end: whatever the state's gzhead [hdr_at] and the rest [Hr] of the local h and of the
   objects hold, with the state's gzhead unchanged they give back h's memory *)
Definition hclose (s : dstate) (ghp : val) (hx : share * val * val * val) (Hr : mpred) : Prop :=
  forall s', d_gzhead s' = d_gzhead s -> hdr_at (Some s') ghp hx * Hr |-- data_at_ Tsh t_gzh vh * TT.

(* A3 (msuf 40, before bound = deflateBound(&s, n)): the header set when hs_of bs *)
Definition A3 (bs : bsetup) (st : bstrm) (ghp : val) (hx : share * val * val * val) (Hr : mpred)
    : environ -> mpred :=
  PROPx [bs_ok bs; bound_facts Bpre Brun;
         Bpre (b_level bs) (b_wbits bs) (b_mem bs) (b_strategy bs) (ds_of bs) (st_s st) (st_tin st) (st_tout st)
           (st_adler st);
         msg_ok (st_msg st) (st_msgv st); hclose (st_s st) ghp hx Hr]
  (LOCALx (temp _dict_set (vi (if ds_of bs then 1 else 0)) :: bs_locals bs ++
           [lvar _h t_gzh vh; lvar _s t_strm vs; gvars gv])
  (SEPx [dstream 2 (Some (st_s st)) vs ghp gv; st_fields vs st; srest; hdr_at (Some (st_s st)) ghp hx; Hr;
         mem_mgr gv; deflate_globals gv; obj (b_datap bs) (b_data bs); TT])).

(* A4 (msuf 45, before s.next_in = data): b = deflateBound(&s, n), ob = malloc(b) not NULL *)
Definition A4 (bs : bsetup) (st : bstrm) (ghp : val) (hx : share * val * val * val) (Hr : mpred) (b : Z)
    (obp : val) : environ -> mpred :=
  PROPx [bs_ok bs; bound_facts Bpre Brun; Brun (b_n bs) b 0 false (st_s st) (st_tin st) (st_tout st) (st_adler st);
         0 <= b <= 4294967295; isptr obp; msg_ok (st_msg st) (st_msgv st); hclose (st_s st) ghp hx Hr]
  (LOCALx [temp _bound (vl b); temp _ob obp; temp _data (b_datap bs); temp _n (vi (b_n bs));
           lvar _h t_gzh vh; lvar _s t_strm vs; gvars gv]
  (SEPx [dstream 2 (Some (st_s st)) vs ghp gv; st_fields vs st; srest; hdr_at (Some (st_s st)) ghp hx; Hr;
         mem_mgr gv; deflate_globals gv; obj (b_datap bs) (b_data bs);
         @malloc_token DCS.CS Ews (tarray tuchar b) obp; @data_at_ DCS.CS Ews (tarray tuchar b) obp; TT])).

End Kit.
