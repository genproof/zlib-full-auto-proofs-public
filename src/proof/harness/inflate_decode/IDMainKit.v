(* Law inflate_decode, main (IDMain.v): the kit shared by the segment lemmas of main's proof.
   - Gmain_k (= IDMain.Gmain), Delta_id (main's type context), POST_id (main's postcondition after
     start_function);
   - the segments of f_main's body, by path (id_sub);
   - the abstract state of the encoder (the blocks written so far, the bits of the bit writer) and of the
     decoder (the decode theory's dinv), and the assertions at the segments' boundaries. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.HarnessRef
               Zlib.proof.adler32.MainLib.
Require Zlib.proof.crc32.HarnessRef.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_common.DRefSpec.
Require Import Zlib.proof.rfc1951.Decode.
Require Import Zlib.proof.harness.inflate_decode.IDLawCS Zlib.proof.harness.inflate_decode.IDGlobals.
Require Import Zlib.harness.x_inflate_decode.code.
Require Import Zlib.proof.crc32.Spec.

Definition Gmain_k : funspecs :=
  [inflateInit2__spec; inflate_spec; inflateEnd_spec; zcalloc_i; zcfree_i;
   ref_adler32_spec; Zlib.proof.crc32.HarnessRef.ref_crc32_spec; bytes_copy_spec; bytes_same_spec;
   exact_copy_spec; exact_space_spec; stream_defaults_spec;
   bw_byte_spec; bw_bits_spec; bw_code_spec; bw_align_spec; bw_fixed_spec;
   len_code_spec id_tabs; dist_code_spec id_tabs; bw_fixed_match_spec id_tabs; dyn_header_spec;
   (_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   nondet_u32_spec; nondet_u8_spec; nondet_bytes_spec; gp_assert_spec; gp_assume_spec].

Definition Delta_id : tycontext := func_tycontext f_main (QPvarspecs p) Gmain_k nil.

(* main's postcondition after start_function (main_core_spec) *)
Definition POST_id : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* ---------------------------------------------------------------------------------------------- *)
(* The segments of f_main's body, by path (0: first component, other: second)                    *)

Fixpoint id_sub (path: list nat) (s: statement) : statement :=
  match path, s with
  | nil, _ => s
  | O :: pth, Ssequence a _ => id_sub pth a
  | S _ :: pth, Ssequence _ b => id_sub pth b
  | O :: pth, Sifthenelse _ a _ => id_sub pth a
  | S _ :: pth, Sifthenelse _ _ b => id_sub pth b
  | O :: pth, Sloop a _ => id_sub pth a
  | S _ :: pth, Sloop _ b => id_sub pth b
  | _, _ => Sskip
  end.

Definition ones (k: nat) : list nat := repeat 1%nat k.

Ltac get_sub pth :=
  let p := eval vm_compute in pth in
  let x := eval cbv beta iota zeta delta [id_sub f_main fn_body] in (id_sub p (fn_body f_main)) in
  exact x.

(* main's body before the final `return 0` *)
Definition S_body : statement := ltac:(get_sub [0%nat]).
(* the block loop and everything after it *)
Definition Q_blk : list nat := 0%nat :: ones 18.
Definition S_blk : statement := ltac:(get_sub Q_blk).
(* the body of the block loop (after its leading skip) *)
Definition seg_blk : statement := ltac:(get_sub (Q_blk ++ [0; 0; 1])%nat).
(* `if (bt == 0) {stored} else {Huffman}` and the rest of the block loop body *)
Definition Q_bif : list nat := (Q_blk ++ [0; 0; 1] ++ ones 7)%nat.
Definition seg_stored : statement := ltac:(get_sub (Q_bif ++ [0; 0])%nat).
Definition Q_huff : list nat := (Q_bif ++ [0; 1])%nat.
Definition S_huff : statement := ltac:(get_sub Q_huff).
(* `isb[n] = 1; if (last) break;` *)
Definition seg_btail : statement := ltac:(get_sub (Q_bif ++ [1])%nat).
(* the symbol loop and the end-of-block code *)
Definition Q_sym : list nat := (Q_huff ++ ones 4)%nat.
Definition S_sym : statement := ltac:(get_sub Q_sym).
Definition seg_symb : statement := ltac:(get_sub (Q_sym ++ [0; 0; 1])%nat).
Definition seg_lit : statement := ltac:(get_sub (Q_sym ++ [0; 0; 1; 1; 1; 1; 0])%nat).
Definition seg_ref : statement := ltac:(get_sub (Q_sym ++ [0; 0; 1; 1; 1; 1; 1])%nat).
Definition seg_eob : statement := ltac:(get_sub (Q_sym ++ [1])%nat).
(* after the block loop: the trailer, up to `int iw` *)
Definition S_trl : statement := ltac:(get_sub (0%nat :: ones 19)).
(* from `int iw` (iw, stream_defaults, inflateInit2) to the decode loop *)
Definition S_mid : statement := ltac:(get_sub (0%nat :: ones 27)).
(* the decode loop and the final checks *)
Definition Q_dec : list nat := 0%nat :: ones 34.
Definition S_dec : statement := ltac:(get_sub Q_dec).
Definition seg_decb : statement := ltac:(get_sub (Q_dec ++ [0; 0; 1])%nat).
Definition seg_tail : statement := ltac:(get_sub (Q_dec ++ [1])%nat).

Lemma S_blk_eq : S_blk = Ssequence (Sloop (Ssequence Sskip seg_blk) Sskip) S_trl.
Proof. reflexivity. Qed.
Lemma S_sym_eq : S_sym = Ssequence (Sloop (Ssequence Sskip seg_symb) Sskip) seg_eob.
Proof. reflexivity. Qed.
Lemma S_dec_eq : S_dec = Ssequence (Sloop (Ssequence Sskip seg_decb) Sskip) seg_tail.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The encoder's abstract state                                                                   *)

(* the drawn parameters: wrap (0 raw, 1 zlib, 2 gzip, other raw), wb, flevel, isel *)
Definition par_ok (wrap wb flevel isel: Z) : Prop :=
  0 <= wrap <= 255 /\ 8 <= wb <= 15 /\ 0 <= flevel <= 255 /\ 0 <= isel <= 255.

Definition id_wrapper (wrap wb flevel: Z) : wrapper :=
  if wrap =? 1 then WZlib wb (Z.land flevel 3) None else if wrap =? 2 then WGzip gz_min else WRaw.

(* inflateInit2's windowBits *)
Definition id_iw (wrap wb isel: Z) : Z :=
  if wrap =? 1 then (if isel <? 85 then wb else if isel <? 170 then 0 else 32 + wb)
  else if wrap =? 2 then (if isel <? 128 then 16 + wb else 32 + wb)
  else - wb.

(* the blocks bs, none of them final, from the bit position p of the deflate stream *)
Fixpoint enc_nf (p: Z) (bs: list block) : list bool :=
  match bs with
  | [] => []
  | b :: r => let e := enc_block p false b in e ++ enc_nf (p + Zlength e) r
  end.

(* the bits of the bit writer at the head of the block loop: the wrapper's header, the blocks so far *)
Definition enc_bits (W: wrapper) (bs: list block) : list bool := bytes_bits (hdr_bytes W) ++ enc_nf 0 bs.

(* the object data[0 .. 2^18): the data D, then anything *)
Definition data_ok (dcont: list val) (D: list Z) : Prop :=
  Zlength dcont = 262144 /\ Zlength D <= 262144 /\ is_bytes D /\ sublist 0 (Zlength D) dcont = bytes_rep D.

(* the object isb[0 .. 2^18]: non-zero at every block boundary of bs *)
Definition isb_ok (bs: list block) (isbz: list Z) : Prop :=
  Zlength isbz = 262145 /\ is_bytes isbz /\
  forall k, 0 <= k <= Zlength bs -> Znth (Zlength (expand [] (firstn (Z.to_nat k) bs))) isbz <> 0.

(* the local arrays ll[316], lcodes[286], dcodes[30] *)
Definition codes_ok (llc lcc dcc: list val) : Prop := Zlength llc = 316 /\ Zlength lcc = 286 /\ Zlength dcc = 30.

(* the resources of the decode phase the encoder carries *)
Definition dres (gv: globals) : mpred :=
  (zfuncs gv * tables_rep Ers gv * crc_table_at Ers gv * version_lit gv * id_hversion_lit gv)%logic.

(* a Huffman block's kind: fixed, or dynamic with its header *)
Inductive hkind := HFix | HDyn (nlen ndist: Z) (clsent: list Z) (toks: list cltok).

Definition hk_ll (hk: hkind) : list Z :=
  match hk with HFix => fixed_ll | HDyn nlen _ _ toks => dyn_ll nlen toks end.
Definition hk_dl (hk: hkind) : list Z :=
  match hk with HFix => fixed_dl | HDyn nlen ndist _ toks => dyn_dl nlen ndist toks end.
Definition hk_block (hk: hkind) (syms: list sym) : block :=
  match hk with HFix => Fixed syms | HDyn nlen ndist cl toks => Dynamic nlen ndist cl toks syms end.
(* the bits after BFINAL: BTYPE and the dynamic header *)
Definition hk_bits (hk: hkind) : list bool :=
  match hk with HFix => [true; false] | HDyn nlen ndist cl toks => [false; true] ++ dyn_hdr_bits nlen ndist cl toks end.
Definition hk_ok (hk: hkind) : Prop :=
  match hk with
  | HFix => True
  | HDyn nlen ndist cl toks => 257 <= nlen <= 286 /\ 1 <= ndist <= 30 /\ dyn_hdr_ok nlen ndist cl toks
  end.
(* main's temporaries dyn, nlen, ndist *)
Definition hk_dyn (hk: hkind) : Z := match hk with HFix => 0 | HDyn _ _ _ _ => 1 end.
Definition hk_nlen (hk: hkind) : Z := match hk with HFix => 0 | HDyn nlen _ _ _ => nlen end.
Definition hk_ndist (hk: hkind) : Z := match hk with HFix => 0 | HDyn _ ndist _ _ => ndist end.
(* a dynamic block's code lengths and codes in ll, lcodes, dcodes (as dyn_header leaves them) *)
Definition hk_arrays_ok (hk: hkind) (llc lcc dcc: list val) : Prop :=
  codes_ok llc lcc dcc /\
  match hk with
  | HFix => True
  | HDyn nlen ndist cl toks =>
      sublist 0 (nlen + ndist) llc = zvals (dyn_lens toks) /\
      sublist 0 nlen lcc = zvals (canon_vals (dyn_ll nlen toks)) /\
      sublist 0 ndist dcc = zvals (canon_vals (dyn_dl nlen ndist toks))
  end.

(* the facts of the block loop's body that do not change within a block (bs: the blocks before it; ls: the
   temporary last_start; last: 1 for the final block) *)
Definition blk_hyps (wrap wb flevel isel: Z) (datap srcp isbp: val) (bs: list block) (ls: Z) (isbz: list Z)
    (last: Z) : Prop :=
  par_ok wrap wb flevel isel /\ isptr datap /\ isptr srcp /\ isptr isbp /\
  blocks_ok (2 ^ wb) [] bs /\ Zlength (expand [] bs) <= 262144 /\ isb_ok bs isbz /\
  (last = 0 \/ last = 1) /\ (last = 1 -> ls = Zlength (expand [] bs)).

(* ---------------------------------------------------------------------------------------------- *)
(* The encoder's assertions.  Ghost values: gv; the addresses of main's local variables vw (w), vll (ll),
   vlc (lcodes), vdc (dcodes), vs (s), vosn (osnap); the parameters wrap wb flevel isel; the objects datap,
   srcp, isbp; Fr: the rest of the memory (the static tables gz, the message literals). *)

(* the head of the block loop: the blocks bs written (none final) *)
Definition enc_at (gv: globals) (vw vll vlc vdc vs vosn: val) (wrap wb flevel isel: Z) (datap srcp isbp: val)
    (Fr: mpred) (bs: list block) (ls: Z) (dcont: list val) (isbz: list Z) (llc lcc dcc: list val)
    : environ -> mpred :=
  PROP (blocks_ok (2 ^ wb) [] bs; data_ok dcont (expand [] bs); isb_ok bs isbz; codes_ok llc lcc dcc)
  LOCAL (temp _wrap (Vint (Int.repr wrap)); temp _wb (Vint (Int.repr wb)); temp _flevel (Vint (Int.repr flevel));
         temp _isel (Vint (Int.repr isel)); temp _data datap; temp _src srcp; temp _isb isbp;
         temp _maxd (Vint (Int.repr (2 ^ wb))); temp _n (Vint (Int.repr (Zlength (expand [] bs))));
         temp _last_start (Vint (Int.repr ls));
         lvar _osnap (tptr tuchar) vosn; lvar _s (Tstruct _z_stream_s noattr) vs;
         lvar _dcodes (tarray tushort 30) vdc; lvar _lcodes (tarray tushort 286) vlc;
         lvar _ll (tarray tuchar 316) vll; lvar _w (Tstruct _bw noattr) vw; gvars gv)
  SEP (bw_at Tsh Ews (enc_bits (id_wrapper wrap wb flevel) bs) 524288 srcp vw;
       data_at Ews (tarray tuchar 262144) dcont datap;
       data_at Ews (tarray tuchar 262145) (bytes_rep isbz) isbp;
       malloc_token Ews (tarray tuchar 262144) datap; malloc_token Ews (tarray tuchar 524288) srcp;
       malloc_token Ews (tarray tuchar 262145) isbp;
       data_at Tsh (tarray tuchar 316) llc vll; data_at Tsh (tarray tushort 286) lcc vlc;
       data_at Tsh (tarray tushort 30) dcc vdc;
       dref_tabs gv Ers id_tabs; data_at Ers (tarray tuchar 19) (zvals clorder) (gv _cl_order);
       data_at_ Tsh (Tstruct _z_stream_s noattr) vs; data_at_ Tsh (tptr tuchar) vosn;
       mem_mgr gv; dres gv; Fr).

Definition enc_inv (gv: globals) (vw vll vlc vdc vs vosn: val) (wrap wb flevel isel: Z) (datap srcp isbp: val)
    (Fr: mpred) : environ -> mpred :=
  EX bs: list block, EX ls: Z, EX dcont: list val, EX isbz: list Z, EX llc: list val, EX lcc: list val,
  EX dcc: list val,
  enc_at gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr bs ls dcont isbz llc lcc dcc.

(* after the block loop: the blocks al, the last one final *)
Definition enc_post (gv: globals) (vw vll vlc vdc vs vosn: val) (wrap wb flevel isel: Z) (datap srcp isbp: val)
    (Fr: mpred) : environ -> mpred :=
  EX al: list block, EX ls: Z, EX dcont: list val, EX isbz: list Z, EX llc: list val, EX lcc: list val,
  EX dcc: list val,
  PROP (al <> []; blocks_ok (2 ^ wb) [] al; data_ok dcont (expand [] al); isb_ok al isbz; codes_ok llc lcc dcc;
        ls = Zlength (expand [] (removelast al)))
  LOCAL (temp _wrap (Vint (Int.repr wrap)); temp _wb (Vint (Int.repr wb)); temp _flevel (Vint (Int.repr flevel));
         temp _isel (Vint (Int.repr isel)); temp _data datap; temp _src srcp; temp _isb isbp;
         temp _maxd (Vint (Int.repr (2 ^ wb))); temp _n (Vint (Int.repr (Zlength (expand [] al))));
         temp _last_start (Vint (Int.repr ls));
         lvar _osnap (tptr tuchar) vosn; lvar _s (Tstruct _z_stream_s noattr) vs;
         lvar _dcodes (tarray tushort 30) vdc; lvar _lcodes (tarray tushort 286) vlc;
         lvar _ll (tarray tuchar 316) vll; lvar _w (Tstruct _bw noattr) vw; gvars gv)
  SEP (bw_at Tsh Ews (bytes_bits (hdr_bytes (id_wrapper wrap wb flevel)) ++ enc_blocks 0 al) 524288 srcp vw;
       data_at Ews (tarray tuchar 262144) dcont datap;
       data_at Ews (tarray tuchar 262145) (bytes_rep isbz) isbp;
       malloc_token Ews (tarray tuchar 262144) datap; malloc_token Ews (tarray tuchar 524288) srcp;
       malloc_token Ews (tarray tuchar 262145) isbp;
       data_at Tsh (tarray tuchar 316) llc vll; data_at Tsh (tarray tushort 286) lcc vlc;
       data_at Tsh (tarray tushort 30) dcc vdc;
       dref_tabs gv Ers id_tabs; data_at Ers (tarray tuchar 19) (zvals clorder) (gv _cl_order);
       data_at_ Tsh (Tstruct _z_stream_s noattr) vs; data_at_ Tsh (tptr tuchar) vosn;
       mem_mgr gv; dres gv; Fr).

(* in the block loop's body, after `bw_bits(&w, last, 1)` (before `if (bt == 0)`): room for 8 more bytes
   (the gp_assume before BFINAL) *)
Definition blk_mid (gv: globals) (vw vll vlc vdc vs vosn: val) (wrap wb flevel isel: Z) (datap srcp isbp: val)
    (Fr: mpred) (bs: list block) (ls: Z) (dcont: list val) (isbz: list Z) (llc lcc dcc: list val)
    (last bt: Z) : environ -> mpred :=
  PROP (data_ok dcont (expand [] bs); codes_ok llc lcc dcc; 0 <= bt <= 3;
        Zlength (enc_bits (id_wrapper wrap wb flevel) bs) / 8 + 8 <= 524288)
  LOCAL (temp _wrap (Vint (Int.repr wrap)); temp _wb (Vint (Int.repr wb)); temp _flevel (Vint (Int.repr flevel));
         temp _isel (Vint (Int.repr isel)); temp _data datap; temp _src srcp; temp _isb isbp;
         temp _maxd (Vint (Int.repr (2 ^ wb))); temp _n (Vint (Int.repr (Zlength (expand [] bs))));
         temp _last_start (Vint (Int.repr ls)); temp _last (Vint (Int.repr last)); temp _bt (Vint (Int.repr bt));
         lvar _osnap (tptr tuchar) vosn; lvar _s (Tstruct _z_stream_s noattr) vs;
         lvar _dcodes (tarray tushort 30) vdc; lvar _lcodes (tarray tushort 286) vlc;
         lvar _ll (tarray tuchar 316) vll; lvar _w (Tstruct _bw noattr) vw; gvars gv)
  SEP (bw_at Tsh Ews (enc_bits (id_wrapper wrap wb flevel) bs ++ bits_le last 1) 524288 srcp vw;
       data_at Ews (tarray tuchar 262144) dcont datap;
       data_at Ews (tarray tuchar 262145) (bytes_rep isbz) isbp;
       malloc_token Ews (tarray tuchar 262144) datap; malloc_token Ews (tarray tuchar 524288) srcp;
       malloc_token Ews (tarray tuchar 262145) isbp;
       data_at Tsh (tarray tuchar 316) llc vll; data_at Tsh (tarray tushort 286) lcc vlc;
       data_at Tsh (tarray tushort 30) dcc vdc;
       dref_tabs gv Ers id_tabs; data_at Ers (tarray tuchar 19) (zvals clorder) (gv _cl_order);
       data_at_ Tsh (Tstruct _z_stream_s noattr) vs; data_at_ Tsh (tptr tuchar) vosn;
       mem_mgr gv; dres gv; Fr).

(* after `if (bt == 0) {stored} else {Huffman}`: the block b written (final when last = 1) *)
Definition blk_done (gv: globals) (vw vll vlc vdc vs vosn: val) (wrap wb flevel isel: Z) (datap srcp isbp: val)
    (Fr: mpred) (bs: list block) (ls: Z) (isbz: list Z) (last: Z) : environ -> mpred :=
  EX b: block, EX dcont: list val, EX llc: list val, EX lcc: list val, EX dcc: list val,
  PROP (block_ok (2 ^ wb) (expand [] bs) b; data_ok dcont (block_data (expand [] bs) b); codes_ok llc lcc dcc)
  LOCAL (temp _wrap (Vint (Int.repr wrap)); temp _wb (Vint (Int.repr wb)); temp _flevel (Vint (Int.repr flevel));
         temp _isel (Vint (Int.repr isel)); temp _data datap; temp _src srcp; temp _isb isbp;
         temp _maxd (Vint (Int.repr (2 ^ wb))); temp _n (Vint (Int.repr (Zlength (block_data (expand [] bs) b))));
         temp _last_start (Vint (Int.repr ls)); temp _last (Vint (Int.repr last));
         lvar _osnap (tptr tuchar) vosn; lvar _s (Tstruct _z_stream_s noattr) vs;
         lvar _dcodes (tarray tushort 30) vdc; lvar _lcodes (tarray tushort 286) vlc;
         lvar _ll (tarray tuchar 316) vll; lvar _w (Tstruct _bw noattr) vw; gvars gv)
  SEP (bw_at Tsh Ews (enc_bits (id_wrapper wrap wb flevel) bs ++
                      enc_block (Zlength (enc_nf 0 bs)) (last =? 1) b) 524288 srcp vw;
       data_at Ews (tarray tuchar 262144) dcont datap;
       data_at Ews (tarray tuchar 262145) (bytes_rep isbz) isbp;
       malloc_token Ews (tarray tuchar 262144) datap; malloc_token Ews (tarray tuchar 524288) srcp;
       malloc_token Ews (tarray tuchar 262145) isbp;
       data_at Tsh (tarray tuchar 316) llc vll; data_at Tsh (tarray tushort 286) lcc vlc;
       data_at Tsh (tarray tushort 30) dcc vdc;
       dref_tabs gv Ers id_tabs; data_at Ers (tarray tuchar 19) (zvals clorder) (gv _cl_order);
       data_at_ Tsh (Tstruct _z_stream_s noattr) vs; data_at_ Tsh (tptr tuchar) vosn;
       mem_mgr gv; dres gv; Fr).

(* the symbol loop of a Huffman block of kind hk: the symbols syms written; the arrays llc, lcc, dcc
   (hk_arrays_ok) do not change *)
Definition sym_at (gv: globals) (vw vll vlc vdc vs vosn: val) (wrap wb flevel isel: Z) (datap srcp isbp: val)
    (Fr: mpred) (bs: list block) (ls: Z) (isbz: list Z) (last: Z) (hk: hkind) (llc lcc dcc: list val)
    (syms: list sym) (dcont: list val) : environ -> mpred :=
  PROP (syms_ok (2 ^ wb) (hk_ll hk) (hk_dl hk) (expand [] bs) syms;
        data_ok dcont (syms_data (expand [] bs) syms))
  LOCAL (temp _wrap (Vint (Int.repr wrap)); temp _wb (Vint (Int.repr wb)); temp _flevel (Vint (Int.repr flevel));
         temp _isel (Vint (Int.repr isel)); temp _data datap; temp _src srcp; temp _isb isbp;
         temp _maxd (Vint (Int.repr (2 ^ wb)));
         temp _n (Vint (Int.repr (Zlength (syms_data (expand [] bs) syms))));
         temp _last_start (Vint (Int.repr ls)); temp _last (Vint (Int.repr last));
         temp _dyn (Vint (Int.repr (hk_dyn hk))); temp _nlen (Vint (Int.repr (hk_nlen hk)));
         temp _ndist (Vint (Int.repr (hk_ndist hk)));
         lvar _osnap (tptr tuchar) vosn; lvar _s (Tstruct _z_stream_s noattr) vs;
         lvar _dcodes (tarray tushort 30) vdc; lvar _lcodes (tarray tushort 286) vlc;
         lvar _ll (tarray tuchar 316) vll; lvar _w (Tstruct _bw noattr) vw; gvars gv)
  SEP (bw_at Tsh Ews (enc_bits (id_wrapper wrap wb flevel) bs ++ bits_le last 1 ++ hk_bits hk ++
                      flat_map (send_one (hk_ll hk) (hk_dl hk)) syms) 524288 srcp vw;
       data_at Ews (tarray tuchar 262144) dcont datap;
       data_at Ews (tarray tuchar 262145) (bytes_rep isbz) isbp;
       malloc_token Ews (tarray tuchar 262144) datap; malloc_token Ews (tarray tuchar 524288) srcp;
       malloc_token Ews (tarray tuchar 262145) isbp;
       data_at Tsh (tarray tuchar 316) llc vll; data_at Tsh (tarray tushort 286) lcc vlc;
       data_at Tsh (tarray tushort 30) dcc vdc;
       dref_tabs gv Ers id_tabs; data_at Ers (tarray tuchar 19) (zvals clorder) (gv _cl_order);
       data_at_ Tsh (Tstruct _z_stream_s noattr) vs; data_at_ Tsh (tptr tuchar) vosn;
       mem_mgr gv; dres gv; Fr).

(* the bits of the bit writer in the symbol loop *)
Definition sym_bits (wrap wb flevel: Z) (bs: list block) (last: Z) (hk: hkind) (syms: list sym) : list bool :=
  enc_bits (id_wrapper wrap wb flevel) bs ++ bits_le last 1 ++ hk_bits hk ++
  flat_map (send_one (hk_ll hk) (hk_dl hk)) syms.

Definition sym_inv (gv: globals) (vw vll vlc vdc vs vosn: val) (wrap wb flevel isel: Z) (datap srcp isbp: val)
    (Fr: mpred) (bs: list block) (ls: Z) (isbz: list Z) (last: Z) (hk: hkind) (llc lcc dcc: list val)
    : environ -> mpred :=
  EX syms: list sym, EX dcont: list val,
  sym_at gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr bs ls isbz last hk llc lcc dcc syms dcont.

(* after the symbol loop (kind 0): room for 8 more bytes (the gp_assume) *)
Definition sym_post (gv: globals) (vw vll vlc vdc vs vosn: val) (wrap wb flevel isel: Z) (datap srcp isbp: val)
    (Fr: mpred) (bs: list block) (ls: Z) (isbz: list Z) (last: Z) (hk: hkind) (llc lcc dcc: list val)
    : environ -> mpred :=
  EX syms: list sym, EX dcont: list val,
  PROP (syms_ok (2 ^ wb) (hk_ll hk) (hk_dl hk) (expand [] bs) syms;
        data_ok dcont (syms_data (expand [] bs) syms);
        Zlength (sym_bits wrap wb flevel bs last hk syms) / 8 + 8 <= 524288)
  LOCAL (temp _wrap (Vint (Int.repr wrap)); temp _wb (Vint (Int.repr wb)); temp _flevel (Vint (Int.repr flevel));
         temp _isel (Vint (Int.repr isel)); temp _data datap; temp _src srcp; temp _isb isbp;
         temp _maxd (Vint (Int.repr (2 ^ wb)));
         temp _n (Vint (Int.repr (Zlength (syms_data (expand [] bs) syms))));
         temp _last_start (Vint (Int.repr ls)); temp _last (Vint (Int.repr last));
         temp _dyn (Vint (Int.repr (hk_dyn hk))); temp _nlen (Vint (Int.repr (hk_nlen hk)));
         temp _ndist (Vint (Int.repr (hk_ndist hk)));
         lvar _osnap (tptr tuchar) vosn; lvar _s (Tstruct _z_stream_s noattr) vs;
         lvar _dcodes (tarray tushort 30) vdc; lvar _lcodes (tarray tushort 286) vlc;
         lvar _ll (tarray tuchar 316) vll; lvar _w (Tstruct _bw noattr) vw; gvars gv)
  SEP (bw_at Tsh Ews (enc_bits (id_wrapper wrap wb flevel) bs ++ bits_le last 1 ++ hk_bits hk ++
                      flat_map (send_one (hk_ll hk) (hk_dl hk)) syms) 524288 srcp vw;
       data_at Ews (tarray tuchar 262144) dcont datap;
       data_at Ews (tarray tuchar 262145) (bytes_rep isbz) isbp;
       malloc_token Ews (tarray tuchar 262144) datap; malloc_token Ews (tarray tuchar 524288) srcp;
       malloc_token Ews (tarray tuchar 262145) isbp;
       data_at Tsh (tarray tuchar 316) llc vll; data_at Tsh (tarray tushort 286) lcc vlc;
       data_at Tsh (tarray tushort 30) dcc vdc;
       dref_tabs gv Ers id_tabs; data_at Ers (tarray tuchar 19) (zvals clorder) (gv _cl_order);
       data_at_ Tsh (Tstruct _z_stream_s noattr) vs; data_at_ Tsh (tptr tuchar) vosn;
       mem_mgr gv; dres gv; Fr).


(* in the symbol loop's body, after `if (kind == 0) break;` *)
Definition kind_at (gv: globals) (vw vll vlc vdc vs vosn: val) (wrap wb flevel isel: Z) (datap srcp isbp: val)
    (Fr: mpred) (bs: list block) (ls: Z) (isbz: list Z) (last: Z) (hk: hkind) (llc lcc dcc: list val)
    (syms: list sym) (dcont: list val) (kind: Z) : environ -> mpred :=
  PROP (syms_ok (2 ^ wb) (hk_ll hk) (hk_dl hk) (expand [] bs) syms;
        data_ok dcont (syms_data (expand [] bs) syms);
        1 <= kind <= 255; Zlength (sym_bits wrap wb flevel bs last hk syms) / 8 + 8 <= 524288)
  LOCAL (temp _kind (Vint (Int.repr kind)); temp _wrap (Vint (Int.repr wrap)); temp _wb (Vint (Int.repr wb)); temp _flevel (Vint (Int.repr flevel));
         temp _isel (Vint (Int.repr isel)); temp _data datap; temp _src srcp; temp _isb isbp;
         temp _maxd (Vint (Int.repr (2 ^ wb)));
         temp _n (Vint (Int.repr (Zlength (syms_data (expand [] bs) syms))));
         temp _last_start (Vint (Int.repr ls)); temp _last (Vint (Int.repr last));
         temp _dyn (Vint (Int.repr (hk_dyn hk))); temp _nlen (Vint (Int.repr (hk_nlen hk)));
         temp _ndist (Vint (Int.repr (hk_ndist hk)));
         lvar _osnap (tptr tuchar) vosn; lvar _s (Tstruct _z_stream_s noattr) vs;
         lvar _dcodes (tarray tushort 30) vdc; lvar _lcodes (tarray tushort 286) vlc;
         lvar _ll (tarray tuchar 316) vll; lvar _w (Tstruct _bw noattr) vw; gvars gv)
  SEP (bw_at Tsh Ews (enc_bits (id_wrapper wrap wb flevel) bs ++ bits_le last 1 ++ hk_bits hk ++
                      flat_map (send_one (hk_ll hk) (hk_dl hk)) syms) 524288 srcp vw;
       data_at Ews (tarray tuchar 262144) dcont datap;
       data_at Ews (tarray tuchar 262145) (bytes_rep isbz) isbp;
       malloc_token Ews (tarray tuchar 262144) datap; malloc_token Ews (tarray tuchar 524288) srcp;
       malloc_token Ews (tarray tuchar 262145) isbp;
       data_at Tsh (tarray tuchar 316) llc vll; data_at Tsh (tarray tushort 286) lcc vlc;
       data_at Tsh (tarray tushort 30) dcc vdc;
       dref_tabs gv Ers id_tabs; data_at Ers (tarray tuchar 19) (zvals clorder) (gv _cl_order);
       data_at_ Tsh (Tstruct _z_stream_s noattr) vs; data_at_ Tsh (tptr tuchar) vosn;
       mem_mgr gv; dres gv; Fr).


(* ---------------------------------------------------------------------------------------------- *)
(* The trailer and the decoder's assertions                                                       *)

(* after `total = slen + glen` (al: all blocks; srcl: the stream and the garbage, src[0 .. total)) *)
Definition trl_facts (wrap wb flevel isel: Z) (datap srcp isbp: val) (al: list block) (ls: Z) (dcont: list val)
    (isbz: list Z) (srcl: list Z) (scont: list val) : Prop :=
  par_ok wrap wb flevel isel /\ isptr datap /\ isptr srcp /\ isptr isbp /\
  al <> [] /\ blocks_ok (2 ^ wb) [] al /\ data_ok dcont (expand [] al) /\ isb_ok al isbz /\
  ls = Zlength (expand [] (removelast al)) /\
  Zlength (stream_bytes (id_wrapper wrap wb flevel) [] al) <= Zlength srcl /\
  Zlength srcl <= Zlength (stream_bytes (id_wrapper wrap wb flevel) [] al) + 16 /\
  is_bytes srcl /\
  sublist 0 (Zlength (stream_bytes (id_wrapper wrap wb flevel) [] al)) srcl =
    stream_bytes (id_wrapper wrap wb flevel) [] al /\
  Zlength scont = 524288 /\ Zlength srcl <= 524288 /\ sublist 0 (Zlength srcl) scont = bytes_rep srcl.

Definition trl_mid (gv: globals) (vw vll vlc vdc vs vosn: val) (wrap wb flevel isel: Z) (datap srcp isbp: val)
    (Fr: mpred) (al: list block) (ls: Z) (dcont: list val) (isbz: list Z) (srcl: list Z) (scont: list val)
    : environ -> mpred :=
  PROP ()
  LOCAL (temp _wrap (Vint (Int.repr wrap)); temp _wb (Vint (Int.repr wb)); temp _isel (Vint (Int.repr isel));
         temp _data datap; temp _src srcp; temp _isb isbp;
         temp _n (Vint (Int.repr (Zlength (expand [] al))));
         temp _slen (Vint (Int.repr (Zlength (stream_bytes (id_wrapper wrap wb flevel) [] al))));
         temp _total (Vint (Int.repr (Zlength srcl)));
         temp _last_start (Vint (Int.repr ls));
         lvar _osnap (tptr tuchar) vosn; lvar _s (Tstruct _z_stream_s noattr) vs;
         lvar _dcodes (tarray tushort 30) vdc; lvar _lcodes (tarray tushort 286) vlc;
         lvar _ll (tarray tuchar 316) vll; lvar _w (Tstruct _bw noattr) vw; gvars gv)
  SEP (data_at Ews (tarray tuchar 262144) dcont datap; data_at Ews (tarray tuchar 524288) scont srcp;
       data_at Ews (tarray tuchar 262145) (bytes_rep isbz) isbp;
       malloc_token Ews (tarray tuchar 262144) datap; malloc_token Ews (tarray tuchar 524288) srcp;
       malloc_token Ews (tarray tuchar 262145) isbp;
       data_at_ Tsh (Tstruct _bw noattr) vw; data_at_ Tsh (tarray tuchar 316) vll;
       data_at_ Tsh (tarray tushort 286) vlc; data_at_ Tsh (tarray tushort 30) vdc;
       data_at_ Tsh (Tstruct _z_stream_s noattr) vs; data_at_ Tsh (tptr tuchar) vosn;
       dref_tabs gv Ers id_tabs; data_at Ers (tarray tuchar 19) (zvals clorder) (gv _cl_order);
       mem_mgr gv; dres gv; Fr).

(* the decode phase: the context G (Decode.v) and the objects; ls = last_start *)
Definition dec_facts (G: dctx) (datap srcp isbp: val) (dcont scont: list val) (isbz: list Z) (ls: Z) : Prop :=
  dctx_ok G /\ dc_hist G = [] /\ isptr datap /\ isptr srcp /\ isptr isbp /\
  data_ok dcont (full G) /\
  Zlength scont = 524288 /\ Zlength (dc_src G) <= 524288 /\
  sublist 0 (Zlength (dc_src G)) scont = bytes_rep (dc_src G) /\
  Zlength isbz = 262145 /\ is_bytes isbz /\
  (forall k, 0 <= k <= nblk G -> Znth (Zlength (outk G k)) isbz <> 0) /\
  ls = Zlength (outk G (nblk G - 1)).

(* the head of the decode loop: pos bytes consumed, lim offered so far, opos bytes produced, the stream (z, L) *)
Definition dec_at (gv: globals) (vw vll vlc vdc vs vosn: val) (G: dctx) (datap srcp isbp: val)
    (dcont scont: list val) (isbz: list Z) (ls: Z) (Fr: mpred) (pos lim opos: Z) (z: zfields) (L: live)
    : environ -> mpred :=
  PROP (dinv G pos (sublist 0 opos (full G)) (l_s L) (zf_tout z); 0 <= pos <= lim; lim <= Zlength (dc_src G);
        0 <= opos <= Zlength (full G))
  LOCAL (temp _n (Vint (Int.repr (Zlength (full G)))); temp _slen (Vint (Int.repr (slen G)));
         temp _total (Vint (Int.repr (Zlength (dc_src G)))); temp _last_start (Vint (Int.repr ls));
         temp _pos (Vint (Int.repr pos)); temp _lim (Vint (Int.repr lim)); temp _opos (Vint (Int.repr opos));
         temp _data datap; temp _src srcp; temp _isb isbp;
         lvar _osnap (tptr tuchar) vosn; lvar _s (Tstruct _z_stream_s noattr) vs;
         lvar _dcodes (tarray tushort 30) vdc; lvar _lcodes (tarray tushort 286) vlc;
         lvar _ll (tarray tuchar 316) vll; lvar _w (Tstruct _bw noattr) vw; gvars gv)
  SEP (istream gv Tsh vs z (Some L);
       data_at Ews (tarray tuchar 262144) dcont datap; data_at Ews (tarray tuchar 524288) scont srcp;
       data_at Ews (tarray tuchar 262145) (bytes_rep isbz) isbp;
       malloc_token Ews (tarray tuchar 262144) datap; malloc_token Ews (tarray tuchar 524288) srcp;
       malloc_token Ews (tarray tuchar 262145) isbp;
       data_at_ Tsh (Tstruct _bw noattr) vw; data_at_ Tsh (tarray tuchar 316) vll;
       data_at_ Tsh (tarray tushort 286) vlc; data_at_ Tsh (tarray tushort 30) vdc;
       data_at_ Tsh (tptr tuchar) vosn;
       mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv; Fr).

Definition dec_inv (gv: globals) (vw vll vlc vdc vs vosn: val) (G: dctx) (datap srcp isbp: val)
    (dcont scont: list val) (isbz: list Z) (ls: Z) (Fr: mpred) : environ -> mpred :=
  EX pos: Z, EX lim: Z, EX opos: Z, EX z: zfields, EX L: live,
  dec_at gv vw vll vlc vdc vs vosn G datap srcp isbp dcont scont isbz ls Fr pos lim opos z L.

(* after the decode loop (Z_STREAM_END): all the data produced, exactly the stream consumed *)
Definition dec_post (gv: globals) (vw vll vlc vdc vs vosn: val) (G: dctx) (datap srcp isbp: val)
    (dcont scont: list val) (isbz: list Z) (ls: Z) (Fr: mpred) : environ -> mpred :=
  EX lim: Z, EX z: zfields, EX L: live,
  PROP (zf_tout z = Zlength (full G))
  LOCAL (temp _n (Vint (Int.repr (Zlength (full G)))); temp _slen (Vint (Int.repr (slen G)));
         temp _total (Vint (Int.repr (Zlength (dc_src G)))); temp _last_start (Vint (Int.repr ls));
         temp _pos (Vint (Int.repr (slen G))); temp _lim (Vint (Int.repr lim));
         temp _opos (Vint (Int.repr (Zlength (full G))));
         temp _data datap; temp _src srcp; temp _isb isbp;
         lvar _osnap (tptr tuchar) vosn; lvar _s (Tstruct _z_stream_s noattr) vs;
         lvar _dcodes (tarray tushort 30) vdc; lvar _lcodes (tarray tushort 286) vlc;
         lvar _ll (tarray tuchar 316) vll; lvar _w (Tstruct _bw noattr) vw; gvars gv)
  SEP (istream gv Tsh vs z (Some L);
       data_at Ews (tarray tuchar 262144) dcont datap; data_at Ews (tarray tuchar 524288) scont srcp;
       data_at Ews (tarray tuchar 262145) (bytes_rep isbz) isbp;
       malloc_token Ews (tarray tuchar 262144) datap; malloc_token Ews (tarray tuchar 524288) srcp;
       malloc_token Ews (tarray tuchar 262145) isbp;
       data_at_ Tsh (Tstruct _bw noattr) vw; data_at_ Tsh (tarray tuchar 316) vll;
       data_at_ Tsh (tarray tushort 286) vlc; data_at_ Tsh (tarray tushort 30) vdc;
       data_at_ Tsh (tptr tuchar) vosn;
       mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv; Fr).

(* main's precondition after start_function and `unfold R; Intros` (Fr: the rest of R and zfuncs) *)
Definition pro_pre (gv: globals) (vw vll vlc vdc vs vosn: val) (Fr: mpred) : environ -> mpred :=
  PROP ()
  LOCAL (lvar _osnap (tptr tuchar) vosn; lvar _s (Tstruct _z_stream_s noattr) vs;
         lvar _dcodes (tarray tushort 30) vdc; lvar _lcodes (tarray tushort 286) vlc;
         lvar _ll (tarray tuchar 316) vll; lvar _w (Tstruct _bw noattr) vw; gvars gv)
  SEP (data_at_ Tsh (tptr tuchar) vosn; data_at_ Tsh (Tstruct _z_stream_s noattr) vs;
       data_at_ Tsh (tarray tushort 30) vdc; data_at_ Tsh (tarray tushort 286) vlc;
       data_at_ Tsh (tarray tuchar 316) vll; data_at_ Tsh (Tstruct _bw noattr) vw; mem_mgr gv;
       dref_tabs gv Ers id_tabs; data_at Ers (tarray tuchar 19) (zvals clorder) (gv _cl_order);
       data_at Ers (tarray tuchar 10) (zvals gz_vals) (gv _gz); dres gv; Fr).
