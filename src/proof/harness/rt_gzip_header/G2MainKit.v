(* Law rt_gzip_header: the kit of main's body proof (G2Main.v), round 1's MainKit.v adapted to the harness of
   rounds 2 and 3 (inputs drawn into locals, names and comments up to 2^32 - 2 bytes, the do-while loops of
   deflate() and inflate() calls with clip()-sized pieces; round 3: the scalar header fields drawn into locals and
   copies of extra, name and comment made before compression, the checks against these).

   main's body is [Ssequence b0 ret] (b0 = [body0 f_main], a right-nested sequence ending in its own return);
   the statements of b0, 0-based:
     0-3   extra_len, name_len, comment_len = upto(..), present = nondet_u8(),
     4-7   the locals text, time, os, hcrc (nondet_u32),
     8-10  extra = alloc_any_bytes(extra_len), name, comment = any_string(..),
     11    `if (!extra || !name || !comment) return 0`,
     12-14 extra_copy, name_copy, comment_copy = copy_of(..) (the name and the comment with their zero byte),
     15-18 head.text, time, os, hcrc = the locals,
     19-22 head.extra = present & 1 ? extra : Z_NULL, head.extra_len, head.name, head.comment likewise,
     23-26 level, window_bits = 16 + 9 + upto(6), mem_level, strategy,
     27-32 got.extra, extra_max, name, name_max, comment, comm_max (malloc),
     33    the NULL test of the three copies and got's three buffers,
     34    new_stream(&compressor),                  35 deflateInit2_ and its test,
     36    deflateSetHeader and its test,            37 out_size = deflateBound_z(&compressor, 0),
     38    compressed = malloc(out_size),            39 its NULL test,
     40    compressor.next_out = compressed,         41 the do-while of deflate(Z_FINISH) calls,
     42    `if (code != Z_STREAM_END) return 0`,     43 compressed_len = next_out - compressed,
     44    new_stream(&decompressor),                45 inflateInit2_ || inflateGetHeader and the test,
     46    set_buffer(&decompressor, compressed, 0, room, 1),
     47    the do-while of inflate(Z_FINISH) calls (Z_MEM_ERROR returns),
     48-53 the six gp_assert checks (against the locals and the copies),   54 return 0.

   The segments (seg1 .. seg7) and the assertions between them (named after the statement of round 2's main they
   precede: round 3 added statements 4-7 and 11-14 of seg1, so A26 precedes statement 34, A28 36, and so on):
     seg1  0-33   PRE0 -> EX g, A26 g             the inputs, the copies and the objects
     seg2  34-35  A26 -> EX st, A28 st            deflateInit2_ (G2DFacts.gd_init: J0)
     seg3  36-39  A28 -> EX st hx Hr b cbp, A32   deflateSetHeader, deflateBound_z, malloc (gd_head, gd_bound: J)
     seg4  40-43  A32 -> EX O, A36 O              the deflate loop (gd_range, gd_call)
     seg5  44-45  A36 -> EX z sp, A38 z sp        inflateInit2_ and inflateGetHeader
     seg6  46-47  A38 -> EX L1 Fr, A40 L1 Fr      the inflate loop (G2IFacts: gi_init, gi_call)
     seg7  48-54  A40 -> POST_m                   the checks *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.rt_gzip_header.CS.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainDefs.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.DSpec9.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Zlib.proof.inflate_api.Spec5.
Require Zlib.proof.roundtrip.RTH8Spec.
Require Import Zlib.proof.harness.rt_gzip_header.G2DFacts.
Require Zlib.proof.harness.rt_gzip_header.G2IFacts.
Require Import Zlib.harness.rt_gzip_header.code.
#[local] Existing Instance Zlib.proof.harness.rt_gzip_header.CS.CS.
Local Open Scope logic.

Module DS := Zlib.proof.deflate.DState.
Module S5 := Zlib.proof.inflate_api.Spec5.
Module IR := Zlib.proof.inflate.Records.
Module AM := Zlib.proof.inflate_api.ApiModel.
Module GI := Zlib.proof.harness.rt_gzip_header.G2IFacts.

(** ** Cutting main's body into segments *)

Definition body0 (f : function) : statement :=
  match fn_body f with Ssequence b _ => b | s => s end.

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

Ltac get_stmt e :=
  let x := eval cbv beta iota zeta delta [take suf body0 f_main fn_body] in e in exact x.

Definition seg1 : statement := ltac:(get_stmt (take 34 (body0 f_main))).
Definition seg2 : statement := ltac:(get_stmt (take 2 (suf 34 (body0 f_main)))).
Definition seg3 : statement := ltac:(get_stmt (take 4 (suf 36 (body0 f_main)))).
Definition seg4 : statement := ltac:(get_stmt (take 4 (suf 40 (body0 f_main)))).
Definition seg5 : statement := ltac:(get_stmt (take 2 (suf 44 (body0 f_main)))).
Definition seg6 : statement := ltac:(get_stmt (take 2 (suf 46 (body0 f_main)))).
Definition seg7 : statement := ltac:(get_stmt (suf 48 (body0 f_main))).

(** ** Type context and postcondition *)
Definition t_z : type := Tstruct _z_stream_s noattr.
Definition t_g : type := Tstruct _gz_header_s noattr.

Definition Delta_m : tycontext := func_tycontext f_main (QPvarspecs p) Gmain nil.

(* main's postcondition after start_function (main_core_spec) *)
Definition POST_m : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(** ** The values main draws and its objects *)
Record gsetup := mkGS {
  g_xl : Z; g_nl : Z; g_cl : Z;           (* extra_len, name_len, comment_len *)
  g_pr : Z;                               (* present *)
  g_text : Z; g_time : Z; g_os : Z; g_hcrc : Z;
  g_level : Z; g_wb : Z; g_mem : Z; g_strat : Z;   (* g_wb: window_bits, 25 .. 31 *)
  g_xp : val; g_np : val; g_cp : val;     (* the extra field, the name and the comment (any_bytes, any_string) *)
  g_gxp : val; g_gnp : val; g_gcp : val;  (* got's three buffers (malloc) *)
  g_xf : list Z; g_nm : list Z; g_cm : list Z;   (* the bytes of extra, name and comment (without the 0) *)
  g_xcp : val; g_ncp : val; g_ccp : val }.  (* the copies of extra, name and comment (copy_of) *)

Definition nzbytes (l : list Z) : Prop := Forall (fun b => 0 < b < 256) l.

Definition gs_ok (g : gsetup) : Prop :=
  0 <= g_xl g <= 65535 /\ 0 <= g_nl g <= 4294967294 /\ 0 <= g_cl g <= 4294967294 /\ 0 <= g_pr g <= 255 /\
  rs32 (g_text g) /\ 0 <= g_time g <= 4294967295 /\ rs32 (g_os g) /\ rs32 (g_hcrc g) /\
  rs32 (g_level g) /\ 25 <= g_wb g <= 31 /\ rs32 (g_mem g) /\ rs32 (g_strat g) /\
  Zlength (g_xf g) = g_xl g /\ rbytes (g_xf g) /\ Zlength (g_nm g) = g_nl g /\ nzbytes (g_nm g) /\
  Zlength (g_cm g) = g_cl g /\ nzbytes (g_cm g) /\
  isptr (g_xp g) /\ isptr (g_np g) /\ isptr (g_cp g) /\ isptr (g_gxp g) /\ isptr (g_gnp g) /\ isptr (g_gcp g) /\
  isptr (g_xcp g) /\ isptr (g_ncp g) /\ isptr (g_ccp g).

(* bit m of present is set *)
Definition has (g : gsetup) (m : Z) : bool := negb (Z.land (g_pr g) m =? 0).
(* head.extra, head.name, head.comment: the object when its bit is set, else Z_NULL *)
Definition selp (g : gsetup) (m : Z) (q : val) : val := if has g m then q else nullval.
Definition selo (g : gsetup) (m : Z) (l : list Z) : option (list Z) := if has g m then Some l else None.

(* the gzip header deflateSetHeader is given *)
Definition gh_of (g : gsetup) : DS.gzh :=
  DS.mkGZ (g_text g) (g_time g) (g_os g) (selo g 1 (g_xf g)) (g_xl g) (selo g 2 (g_nm g ++ [0]))
    (selo g 4 (g_cm g ++ [0])) (g_hcrc g).

(* it is one of the headers of the law (G2Defs.g2_hdr_ok) *)
Lemma gh_of_ok2 (g : gsetup) : gs_ok g -> g2_hdr_ok (gh_of g).
Proof.
  intros (Hxl & Hnl & Hcl & _ & Htx & Htm & Hos & Hhc & _ & _ & _ & _ & Lx & Bx & Ln & Bn & Lc & Bc & _).
  assert (Cn : forall m l, Zlength l <= 4294967294 -> nzbytes l -> g2_cstr_ok (selo g m (l ++ [0]))).
  { intros m l Hl Hb l' E. unfold selo in E. destruct (has g m); inversion E; subst. eauto. }
  unfold g2_hdr_ok, gh_of, rs32 in *; cbn. repeat split; auto; try lia.
  all: try (match goal with E : selo ?gg 1 _ = Some _ |- _ =>
              unfold selo in E; destruct (has gg 1); inversion E; subst; auto end).
  all: apply Cn; [lia | auto].
Qed.

(* head with the pointers xp, np, cp; xflags, extra_max, name_max, comm_max and done are never written *)
Definition hval (g : gsetup) (xp np cp : val) : reptype t_g :=
  (vi (g_text g), (vl (g_time g), (Vundef, (vi (g_os g), (xp, (vi (g_xl g), (Vundef, (np, (Vundef,
   (cp, (Vundef, (vi (g_hcrc g), Vundef)))))))))))).
Definition hvals (g : gsetup) : reptype t_g := hval g (selp g 1 (g_xp g)) (selp g 2 (g_np g)) (selp g 4 (g_cp g)).

(* got before inflateGetHeader: its buffers and their sizes; everything else never written *)
Definition gval (g : gsetup) : reptype t_g :=
  (Vundef, (Vundef, (Vundef, (Vundef, (g_gxp g, (Vundef, (vi (g_xl g), (g_gnp g, (vi (g_nl g + 1),
   (g_gcp g, (vi (g_cl g + 1), (Vundef, Vundef)))))))))))).

(* a malloc'ed object of exactly the bytes l, at main's compspecs *)
Definition cobj (q : val) (l : list Z) : mpred :=
  malloc_token Ews (tarray tuchar (Zlength l)) q * data_at Ews (tarray tuchar (Zlength l)) (map vi l) q.
(* a malloc'ed object of n bytes never written *)
Definition cnew (q : val) (n : Z) : mpred :=
  malloc_token Ews (tarray tuchar n) q * data_at_ Ews (tarray tuchar n) q.

(* head's three objects (the name and the comment with their zero byte) with their copies, and got's three
   buffers *)
Definition hcopies (g : gsetup) : mpred :=
  cobj (g_xcp g) (g_xf g) * cobj (g_ncp g) (g_nm g ++ [0]) * cobj (g_ccp g) (g_cm g ++ [0]).
Definition hobjs (g : gsetup) : mpred :=
  cobj (g_xp g) (g_xf g) * cobj (g_np g) (g_nm g ++ [0]) * cobj (g_cp g) (g_cm g ++ [0]) * hcopies g.
Definition gbufs (g : gsetup) : mpred :=
  cnew (g_gxp g) (g_xl g) * cnew (g_gnp g) (g_nl g + 1) * cnew (g_gcp g) (g_cl g + 1).

(* the temporaries of the drawn values and of the three objects and their copies *)
Definition gs_locals (g : gsetup) : list localdef :=
  [temp _extra_len (vl (g_xl g)); temp _name_len (vl (g_nl g)); temp _comment_len (vl (g_cl g));
   temp _present (vi (g_pr g)); temp _level (vi (g_level g)); temp _window_bits (vi (g_wb g));
   temp _mem_level (vi (g_mem g)); temp _strategy (vi (g_strat g));
   temp _text (vi (g_text g)); temp _time (vl (g_time g)); temp _os (vi (g_os g)); temp _hcrc (vi (g_hcrc g))].
Definition gp_locals (g : gsetup) : list localdef :=
  [temp _extra (g_xp g); temp _name (g_np g); temp _comment (g_cp g);
   temp _extra_copy (g_xcp g); temp _name_copy (g_ncp g); temp _comment_copy (g_ccp g)].

(* the compressor between the calls: the deflate state and the caller's fields of the z_stream *)
Record dside := mkDside {
  st_s : dstate; st_tin : Z; st_tout : Z; st_adler : Z; st_msg : option Z; st_msgv : val }.

(* the compressed object: b bytes, the stream O first *)
Definition cbytes (b : Z) (O : list Z) : list val := map vi O ++ Zrepeat Vundef (b - Zlength O).

(** ** The decompressor's view *)

(* got as inflateGetHeader receives it: buffers of xl, nl + 1, cl + 1 bytes (contents anything) *)
Definition h0 (g : gsetup) : IR.hstate :=
  IR.HS 0 0 0 0 true 0 (g_xl g) (Zrepeat 0 (g_xl g)) true (g_nl g + 1) (Zrepeat 0 (g_nl g + 1))
    true (g_cl g + 1) (Zrepeat 0 (g_cl g + 1)) 0 0.

(* the live part after inflateInit2_(&decompressor, window_bits) (state sp) and inflateGetHeader(&decompressor,
   &got) *)
Definition gL (g : gsetup) (sp vg : val) : S5.live :=
  Zlib.proof.roundtrip.RTIIface.head_live (S5.init_live sp (g_wb g)) (h0 g) vg Tsh (g_gxp g) (g_gnp g) (g_gcp g).

(* the stream's fields after new_stream and a successful inflateInit2_ *)
Definition izinit (z : AM.zfields) : Prop :=
  S5.zf_ok z /\ AM.zf_ni z = nullval /\ AM.zf_ai z = 0 /\ AM.zf_no z = nullval /\ AM.zf_ao z = 0 /\
  AM.zf_tin z = 0 /\ AM.zf_tout z = 0 /\ AM.zf_msg z = None.

(* the malloc tokens of got's buffers of non-zero size (a zero-size one is in head_mem8's btok) *)
Definition nbtok (q : val) (n : Z) : mpred := if zeq n 0 then emp else malloc_token Ews (tarray tuchar n) q.
Definition gtoks (g : gsetup) : mpred :=
  nbtok (g_gxp g) (g_xl g) * nbtok (g_gnp g) (g_nl g + 1) * nbtok (g_gcp g) (g_cl g + 1).

Section Assertions.
Context (gv : globals) (vh vg vc vd vr : val).

Definition lv_locals : list localdef :=
  [lvar _head t_g vh; lvar _got t_g vg; lvar _compressor t_z vc; lvar _decompressor t_z vd;
   lvar _room (tarray tuchar 1) vr; gvars gv].

(* inflate.c's view of the allocator (Callees.zfuncs: what make_func_ptr gives for zcalloc_i / zcfree_i) *)
Definition ifz : mpred := Zlib.proof.inflate.Callees.zfuncs gv.

(* the caller's fields of the compressor right after deflateInit2_: next_in and next_out Z_NULL, avail_in and
   avail_out 0 (as new_stream left them), total_in, total_out, msg and adler as deflateInit2_ set them (their
   ranges come with the loop invariant J) *)
Definition st_raw (st : dside) : mpred :=
  @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT _next_in) nullval vc *
  @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT _avail_in) (vi 0) vc *
  Zlib.proof.deflate.DSpec9.reset_fields vc (vl (st_tin st)) (vl (st_tout st)) (st_msgv st) (vl (st_adler st)) *
  @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT _next_out) nullval vc *
  @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT _avail_out) (vi 0) vc.

(* the same fields with their ranges (DSpec.api_fields) *)
Definition st_fields (st : dside) : mpred :=
  api_fields vc nullval 0 (st_tin st) nullval 0 (st_tout st) (st_msgv st) (st_adler st).

(* the rest of the local compressor after the split of its Tsh into Ews (the specifications' share) and its
   complement: the complement, and the Ews share of the struct's padding *)
Definition srest : mpred := data_at_ BoundKit.Ecomp t_z vc * BoundKit.strm_pad vc.

(* got, the decompressor, room and got's buffers: untouched until statement 44 *)
Definition gside (g : gsetup) : mpred :=
  data_at Tsh t_g (gval g) vg * data_at_ Tsh t_z vd * data_at_ Tsh (tarray tuchar 1) vr * gbufs g.

(* while the compressor holds head (deflateSetHeader .. the end of the deflate loop), the header part of the state
   [hdr_at] and the rest [Hr] give back head with its objects, whatever the state, as long as its gzhead is
   unchanged *)
Definition hclose (g : gsetup) (s : dstate) (hx : share * val * val * val) (Hr : mpred) : Prop :=
  forall s', d_gzhead s' = d_gzhead s -> hdr_at (Some s') vh hx * Hr |-- data_at Tsh t_g (hvals g) vh * hobjs g.

(* after start_function (and make_func_ptr of zcalloc / zcfree) *)
Definition PRE0 : environ -> mpred :=
  PROPx [] (LOCALx lv_locals
  (SEPx [data_at_ Tsh t_g vh; data_at_ Tsh t_g vg; data_at_ Tsh t_z vc; data_at_ Tsh t_z vd;
         data_at_ Tsh (tarray tuchar 1) vr; mem_mgr gv; R gv; ifz])).

(* A26 (statement 34): everything drawn, copied, stored and allocated, none of the nine objects NULL; head holds the
   present fields' objects and Z_NULL for the absent ones *)
Definition A26 (g : gsetup) : environ -> mpred :=
  PROPx [gs_ok g] (LOCALx (gp_locals g ++ gs_locals g ++ lv_locals)
  (SEPx [data_at Tsh t_g (hvals g) vh; data_at Tsh t_g (gval g) vg; data_at_ Tsh t_z vc; data_at_ Tsh t_z vd;
         data_at_ Tsh (tarray tuchar 1) vr; hobjs g; gbufs g; mem_mgr gv; R gv; ifz])).

Context (J0 : Z -> dstate -> Z -> Z -> Z -> Prop) (J : Z -> DS.gzh -> Z -> list Z -> dstate -> Z -> Z -> Z -> Prop).

(* A28 (statement 36): deflateInit2_ returned Z_OK; J0 of its state and fields (G2DFacts.gd_init) *)
Definition A28 (g : gsetup) (st : dside) : environ -> mpred :=
  PROPx [gs_ok g; J0 (g_wb g) (st_s st) (st_tin st) (st_tout st) (st_adler st); msg_ok (st_msg st) (st_msgv st)]
  (LOCALx (gp_locals g ++ gs_locals g ++ lv_locals)
  (SEPx [dstream 2 (Some (st_s st)) vc nullval gv; st_raw st; srest;
         data_at Tsh t_g (hvals g) vh; hobjs g; gside g; mem_mgr gv; R gv; ifz])).

(* A32 (statement 40): deflateSetHeader(&compressor, &head) returned Z_OK, b = deflateBound_z(&compressor, 0),
   compressed = malloc(b) not NULL; the loop invariant J holds with nothing produced (G2DFacts.gd_bound) *)
Definition A32 (g : gsetup) (st : dside) (hx : share * val * val * val) (Hr : mpred) (b : Z) (cbp : val)
    : environ -> mpred :=
  PROPx [gs_ok g; J (g_wb g) (gh_of g) b [] (st_s st) (st_tin st) (st_tout st) (st_adler st);
         msg_ok (st_msg st) (st_msgv st); hclose g (st_s st) hx Hr; isptr cbp]
  (LOCALx (temp _out_size (vl b) :: temp _compressed cbp :: gp_locals g ++ gs_locals g ++ lv_locals)
  (SEPx [dstream 2 (Some (st_s st)) vc vh gv; st_fields st; srest; hdr_at (Some (st_s st)) vh hx; Hr;
         gside g; mem_mgr gv; R gv; ifz; cnew cbp b])).

(* A36 (statement 44): the deflate loop ended with Z_STREAM_END: the compressed object of b bytes starts with the
   gzip stream O of no data with the header gh_of g; the compressor is given back as the local's memory (its
   state's allocations are left in TT), head and its objects too *)
Definition A36 (g : gsetup) (b : Z) (cbp : val) (O : list Z) : environ -> mpred :=
  PROPx [gs_ok g; dfinal [] 2 (rwbe (g_wb g)) (Some (gh_of g)) [] O; rbytes O; Zlength O <= b <= max_u64;
         isptr cbp]
  (LOCALx (temp _compressed_len (vl (Zlength O)) :: temp _compressed cbp :: gp_locals g ++ gs_locals g ++
           lv_locals)
  (SEPx [data_at_ Tsh t_z vc; data_at Tsh t_g (hvals g) vh; hobjs g; gside g; mem_mgr gv; R gv; ifz;
         malloc_token Ews (tarray tuchar b) cbp; data_at Ews (tarray tuchar b) (cbytes b O) cbp; TT])).

(* A38 (statement 46): inflateInit2_ and inflateGetHeader returned Z_OK: got is attached to the stream *)
Definition A38 (g : gsetup) (b : Z) (cbp : val) (O : list Z) (z : AM.zfields) (sp : val) : environ -> mpred :=
  PROPx [gs_ok g; dfinal [] 2 (rwbe (g_wb g)) (Some (gh_of g)) [] O; rbytes O; Zlength O <= b <= max_u64;
         isptr cbp; izinit z]
  (LOCALx (temp _compressed_len (vl (Zlength O)) :: temp _compressed cbp :: gp_locals g ++ gs_locals g ++
           lv_locals)
  (SEPx [Zlib.proof.roundtrip.RTH8Spec.istream8 gv Tsh vd z (Some (gL g sp vg));
         Zlib.proof.roundtrip.RTH8Spec.head_mem8 (gL g sp vg); gtoks g;
         data_at_ Tsh (tarray tuchar 1) vr; data_at_ Tsh t_z vc;
         data_at Tsh t_g (hvals g) vh; hobjs g; mem_mgr gv; R gv; ifz;
         malloc_token Ews (tarray tuchar b) cbp; data_at Ews (tarray tuchar b) (cbytes b O) cbp; TT])).

(* the rest of main's memory after the inflate loop: it gives back the three locals other than head and got *)
Definition dback (Fr : mpred) : Prop :=
  Fr |-- data_at_ Tsh t_z vc * data_at_ Tsh t_z vd * data_at_ Tsh (tarray tuchar 1) vr * TT.

(* A40 (statement 48): the inflate loop ended (no Z_MEM_ERROR); the stream's live part L1: got holds every field
   of gh_of g (G2IFacts.g2_hdr_out) *)
Definition A40 (g : gsetup) (L1 : S5.live) (Fr : mpred) : environ -> mpred :=
  PROPx [gs_ok g; GI.g2_hdr_out (gh_of g) (h0 g) (S5.l_s L1) (S5.l_h L1);
         IR.i_head (S5.l_s L1) = true; S5.l_headp L1 = vg; S5.l_hsh L1 = Tsh;
         S5.l_xb L1 = g_gxp g; S5.l_nb L1 = g_gnp g; S5.l_cb L1 = g_gcp g; dback Fr]
  (LOCALx (gp_locals g ++ gs_locals g ++ lv_locals)
  (SEPx [Zlib.proof.roundtrip.RTH8Spec.head_mem8 L1; gtoks g; data_at Tsh t_g (hvals g) vh; hobjs g; Fr;
         mem_mgr gv; R gv])).
End Assertions.

(** ** The segments *)

Definition seg1_stmt : Prop :=
  forall {Espec : OracleKind} gv vh vg vc vd vr,
  semax Delta_m (PRE0 gv vh vg vc vd vr) seg1 (overridePost (EX g : gsetup, A26 gv vh vg vc vd vr g) POST_m).

Definition seg2_stmt : Prop :=
  forall {Espec : OracleKind} J0 J gv vh vg vc vd vr g,
  g2_dfacts J0 J ->
  semax Delta_m (A26 gv vh vg vc vd vr g) seg2
    (overridePost (EX st : dside, A28 gv vh vg vc vd vr J0 g st) POST_m).

Definition seg3_stmt : Prop :=
  forall {Espec : OracleKind} J0 J gv vh vg vc vd vr g st,
  g2_dfacts J0 J ->
  semax Delta_m (A28 gv vh vg vc vd vr J0 g st) seg3
    (overridePost (EX st' : dside, EX hx : share * val * val * val, EX Hr : mpred, EX b : Z, EX cbp : val,
                     A32 gv vh vg vc vd vr J g st' hx Hr b cbp) POST_m).

Definition seg4_stmt : Prop :=
  forall {Espec : OracleKind} J0 J gv vh vg vc vd vr g st hx Hr b cbp,
  g2_dfacts J0 J ->
  semax Delta_m (A32 gv vh vg vc vd vr J g st hx Hr b cbp) seg4
    (overridePost (EX O : list Z, A36 gv vh vg vc vd vr g b cbp O) POST_m).

Definition seg5_stmt : Prop :=
  forall {Espec : OracleKind} gv vh vg vc vd vr g b cbp O,
  semax Delta_m (A36 gv vh vg vc vd vr g b cbp O) seg5
    (overridePost (EX z : AM.zfields, EX sp : val, A38 gv vh vg vc vd vr g b cbp O z sp) POST_m).

Definition seg6_stmt : Prop :=
  forall {Espec : OracleKind} P gv vh vg vc vd vr g b cbp O z sp,
  GI.g2_ifacts P ->
  semax Delta_m (A38 gv vh vg vc vd vr g b cbp O z sp) seg6
    (overridePost (EX L1 : S5.live, EX Fr : mpred, A40 gv vh vg vc vd vr g L1 Fr) POST_m).

Definition seg7_stmt : Prop :=
  forall {Espec : OracleKind} gv vh vg vc vd vr g L1 Fr,
  semax Delta_m (A40 gv vh vg vc vd vr g L1 Fr) seg7 POST_m.
