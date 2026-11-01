(* Law inflate_header, main, positions 53 .. 74 (IHMainInit.v): the kit of its parts.
   - seg_60 (from h.extra_max = xmax: the maxima, the seven pick()s) and seg_70 (from
     r = inflateGetHeader(&s, &h) to pos = 0, then the loop);
   - ihi_s60 / ihi_s70: the assertions there (the stream after inflateInit2_ (Z_OK), the gz_header h being built,
     the header buffers of head_buf and their snapshots), ihi_f60 their facts;
   - ihi_h0: the gz_header given to inflateGetHeader. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.crc32.HarnessRef.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_header.IHLawCS Zlib.proof.harness.inflate_header.IHGlobals
               Zlib.proof.harness.inflate_header.IHHelpers Zlib.proof.harness.inflate_header.IHFacts
               Zlib.proof.harness.inflate_header.IHMainStmt.
Require Import Zlib.harness.x_inflate_header.code.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.inflate_header.IHMainKit.
Local Open Scope logic.

(* from h.extra_max = xmax *)
Definition seg_60 : statement := ltac:(ih_seg (ih_drop 60 (ih_first (fn_body f_main)))).
(* from r = inflateGetHeader(&s, &h) *)
Definition seg_70 : statement := ltac:(ih_seg (ih_drop 70 (ih_first (fn_body f_main)))).

(* the stream after a successful inflateInit2_ *)
Definition ihi_z_init (adl rs: Z) (L: live) : zfields :=
  ZF nullval 0 0 nullval 0 0 None 0 (if i_wrap (l_s L) =? 0 then adl else Z.land (i_wrap (l_s L)) 1)
     (Vlong (Int64.repr rs)).

Definition ihi_isnull (p: val) : bool := if eq_dec p nullval then true else false.

(* a header buffer of head_buf: nothing for Z_NULL, else the buffer bp and its snapshot q, both holding bs *)
Definition ihi_buf (bp q: val) (max: Z) (bs: list Z) : mpred :=
  if eq_dec bp nullval then emp
  else (malloc_token Ews (tarray tuchar max) bp * data_at Ews (tarray tuchar max) (bytes_rep bs) bp *
        malloc_token Ews (tarray tuchar max) q * data_at Ews (tarray tuchar max) (bytes_rep bs) q).

(* h after h.extra/name/comment = head_buf(...) *)
Definition ihi_h60 (xb nb cb: val) : ih_head_tuple :=
  (Vundef, (Vundef, (Vundef, (Vundef, (xb, (Vundef, (Vundef, (nb, (Vundef, (cb, (Vundef, (Vundef, Vundef)))))))))))).

(* the gz_header given to inflateGetHeader: the picked fields, the maxima, the buffers (present when nul <> 0) *)
Definition ihi_h0 (b: ihb) (xbs nbs cbs: list Z) (text time xflags os elen hcrc done: Z) : hstate :=
  HS text time xflags os (negb (b_xnul b =? 0)) elen (b_xmax b) xbs (negb (b_nnul b =? 0)) (b_nmax b) nbs
     (negb (b_cnul b =? 0)) (b_cmax b) cbs hcrc done.

(* the facts at position 60 (and 70): sp, adl, rs of inflateInit2_ and stream_defaults; H the buffers of head_buf
   (h_xb .. h_cb) and their snapshots (h_xq .. h_cq), with the contents xbs, nbs, cbs *)
Definition ihi_f60 (I: ihg -> Z -> hstate -> Z -> zfields -> live -> Prop) (g: ihg) (b: ihb) (P: ihp)
    (sp: val) (adl rs: Z) (H: ihh) (xbs nbs cbs: list Z) : Prop :=
  ih_facts I /\ ih_f53 g b P /\ wbits_ok (b_w b) = true /\ isptr sp /\
  0 <= adl <= Int64.max_unsigned /\ 0 <= rs <= Int64.max_unsigned /\
  Zlength xbs = b_xmax b /\ is_bytes xbs /\ (h_xb H = nullval -> h_xq H = nullval) /\
  (b_xnul b = 0 <-> h_xb H = nullval) /\
  Zlength nbs = b_nmax b /\ is_bytes nbs /\ (h_nb H = nullval -> h_nq H = nullval) /\
  (b_nnul b = 0 <-> h_nb H = nullval) /\
  Zlength cbs = b_cmax b /\ is_bytes cbs /\ (h_cb H = nullval -> h_cq H = nullval) /\
  (b_cnul b = 0 <-> h_cb H = nullval).

(* position 60, after the null check of the header buffers *)
Definition ihi_s60 (gv: globals) (V: ihv) (g: ihg) (b: ihb) (P: ihp) (sp: val) (adl rs: Z) (H: ihh)
    (xbs nbs cbs: list Z) : environ -> mpred :=
  PROP ()
  LOCAL (temp _r (Vint (Int.repr Z_OK));
         temp _wbits (Vint (Int.repr (b_w b))); temp _flg (Vint (Int.repr (g_flg g)));
         temp _mtime (Vlong (Int64.repr (g_mtime g))); temp _xfl (Vint (Int.repr (g_xfl g)));
         temp _os (Vint (Int.repr (g_os g))); temp _xlen (Vint (Int.repr (Zlength (g_xf g))));
         temp _nl (Vint (Int.repr (Zlength (g_nf g)))); temp _cl (Vint (Int.repr (Zlength (g_cf g))));
         temp _xmax (Vint (Int.repr (b_xmax b))); temp _nmax (Vint (Int.repr (b_nmax b)));
         temp _cmax (Vint (Int.repr (b_cmax b)));
         temp _xnul (Vint (Int.repr (b_xnul b))); temp _nnul (Vint (Int.repr (b_nnul b)));
         temp _cnul (Vint (Int.repr (b_cnul b)));
         temp _total (Vint (Int.repr (Zlength (ih_src g))));
         temp _src (p_src P); temp _xf (p_xf P); temp _nf (p_nf P); temp _cf (p_cf P);
         temp _reserved (Vint (Int.repr (b2z (ih_reserved g)))); temp _badcrc (Vint (Int.repr (b2z (ih_badcrc g))));
         lvar _s (Tstruct _z_stream_s noattr) (v_s_ V); lvar _h (Tstruct _gz_header_s noattr) (v_h_ V);
         lvar _xs (tptr tuchar) (v_xs_ V); lvar _ns (tptr tuchar) (v_ns_ V); lvar _cs (tptr tuchar) (v_cs_ V);
         lvar _osnap (tptr tuchar) (v_osn_ V); gvars gv)
  SEP (istream gv Tsh (v_s_ V) (ihi_z_init adl rs (init_live sp (b_w b))) (Some (init_live sp (b_w b)));
       mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv; version_lit gv; ih_hversion_lit gv;
       data_at Tsh (Tstruct _gz_header_s noattr) (ihi_h60 (h_xb H) (h_nb H) (h_cb H)) (v_h_ V);
       data_at Tsh (tptr tuchar) (h_xq H) (v_xs_ V); data_at Tsh (tptr tuchar) (h_nq H) (v_ns_ V);
       data_at Tsh (tptr tuchar) (h_cq H) (v_cs_ V);
       ihi_buf (h_xb H) (h_xq H) (b_xmax b) xbs; ihi_buf (h_nb H) (h_nq H) (b_nmax b) nbs;
       ihi_buf (h_cb H) (h_cq H) (b_cmax b) cbs;
       data_at_ Tsh (tptr tuchar) (v_osn_ V);
       malloc_token Ews (tarray tuchar (Zlength (ih_src g))) (p_src P);
       data_at Ews (tarray tuchar (Zlength (ih_src g))) (bytes_rep (ih_src g)) (p_src P);
       malloc_token Ews (tarray tuchar (Zlength (g_xf g))) (p_xf P);
       data_at Ews (tarray tuchar (Zlength (g_xf g))) (bytes_rep (g_xf g)) (p_xf P);
       malloc_token Ews (tarray tuchar (Zlength (g_nf g) + 1)) (p_nf P);
       data_at Ews (tarray tuchar (Zlength (g_nf g) + 1)) (bytes_rep (g_nf g ++ [0])) (p_nf P);
       malloc_token Ews (tarray tuchar (Zlength (g_cf g) + 1)) (p_cf P);
       data_at Ews (tarray tuchar (Zlength (g_cf g) + 1)) (bytes_rep (g_cf g ++ [0])) (p_cf P)).

(* position 70, before inflateGetHeader: h holds the gz_header h0 *)
Definition ihi_s70 (gv: globals) (V: ihv) (g: ihg) (b: ihb) (P: ihp) (sp: val) (adl rs: Z) (H: ihh)
    (h0: hstate) : environ -> mpred :=
  PROP ()
  LOCAL (temp _r (Vint (Int.repr Z_OK));
         temp _wbits (Vint (Int.repr (b_w b))); temp _flg (Vint (Int.repr (g_flg g)));
         temp _mtime (Vlong (Int64.repr (g_mtime g))); temp _xfl (Vint (Int.repr (g_xfl g)));
         temp _os (Vint (Int.repr (g_os g))); temp _xlen (Vint (Int.repr (Zlength (g_xf g))));
         temp _nl (Vint (Int.repr (Zlength (g_nf g)))); temp _cl (Vint (Int.repr (Zlength (g_cf g))));
         temp _xmax (Vint (Int.repr (b_xmax b))); temp _nmax (Vint (Int.repr (b_nmax b)));
         temp _cmax (Vint (Int.repr (b_cmax b)));
         temp _xnul (Vint (Int.repr (b_xnul b))); temp _nnul (Vint (Int.repr (b_nnul b)));
         temp _cnul (Vint (Int.repr (b_cnul b)));
         temp _total (Vint (Int.repr (Zlength (ih_src g))));
         temp _src (p_src P); temp _xf (p_xf P); temp _nf (p_nf P); temp _cf (p_cf P);
         temp _reserved (Vint (Int.repr (b2z (ih_reserved g)))); temp _badcrc (Vint (Int.repr (b2z (ih_badcrc g))));
         lvar _s (Tstruct _z_stream_s noattr) (v_s_ V); lvar _h (Tstruct _gz_header_s noattr) (v_h_ V);
         lvar _xs (tptr tuchar) (v_xs_ V); lvar _ns (tptr tuchar) (v_ns_ V); lvar _cs (tptr tuchar) (v_cs_ V);
         lvar _osnap (tptr tuchar) (v_osn_ V); gvars gv)
  SEP (istream gv Tsh (v_s_ V) (ihi_z_init adl rs (init_live sp (b_w b))) (Some (init_live sp (b_w b)));
       mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv; version_lit gv; ih_hversion_lit gv;
       data_at Tsh (Tstruct _gz_header_s noattr) (ih_htup (h_xb H) (h_nb H) (h_cb H) h0) (v_h_ V);
       data_at Tsh (tptr tuchar) (h_xq H) (v_xs_ V); data_at Tsh (tptr tuchar) (h_nq H) (v_ns_ V);
       data_at Tsh (tptr tuchar) (h_cq H) (v_cs_ V);
       ihi_buf (h_xb H) (h_xq H) (b_xmax b) (h_xbuf h0); ihi_buf (h_nb H) (h_nq H) (b_nmax b) (h_nbuf h0);
       ihi_buf (h_cb H) (h_cq H) (b_cmax b) (h_cbuf h0);
       data_at_ Tsh (tptr tuchar) (v_osn_ V);
       malloc_token Ews (tarray tuchar (Zlength (ih_src g))) (p_src P);
       data_at Ews (tarray tuchar (Zlength (ih_src g))) (bytes_rep (ih_src g)) (p_src P);
       malloc_token Ews (tarray tuchar (Zlength (g_xf g))) (p_xf P);
       data_at Ews (tarray tuchar (Zlength (g_xf g))) (bytes_rep (g_xf g)) (p_xf P);
       malloc_token Ews (tarray tuchar (Zlength (g_nf g) + 1)) (p_nf P);
       data_at Ews (tarray tuchar (Zlength (g_nf g) + 1)) (bytes_rep (g_nf g ++ [0])) (p_nf P);
       malloc_token Ews (tarray tuchar (Zlength (g_cf g) + 1)) (p_cf P);
       data_at Ews (tarray tuchar (Zlength (g_cf g) + 1)) (bytes_rep (g_cf g ++ [0])) (p_cf P)).
