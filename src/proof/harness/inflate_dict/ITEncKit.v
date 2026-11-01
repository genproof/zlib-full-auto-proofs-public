(* Law inflate_dict, main's encoder half (ITMainEnc.v): the kit shared by its segment lemmas.
   - the segments of f_main's body, by path (enc_sub);
   - the constants of the encoder (ectx: the drawn parameters, the dictionary, the objects, the local variables'
     addresses) and the ghost of ITFacts.v they give (eg E bs);
   - the assertions at the segments' boundaries: blk_at (the head of the block loop: the blocks bs written, none
     final), blk_mid (after BFINAL), blk_done (after a block), sym_at / sym_room (the symbol loop of a fixed block),
     blk_end (after the block loop);
   - the segment statements (CPS for the prologue and the trailer, a ret_assert for the loop-body pieces);
   - pure lemmas over Format.v (expand / data / blocks_ok / syms_ok / enc_nf of appends) and the compspecs moves
     (the bit writer's struct bw is at inflate_decode's harness CS in DRefSpec.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessRef Zlib.proof.adler32.HarnessBytes
               Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_common.DRefSpec.
Require Import Zlib.proof.harness.inflate_dict.ITLawCS Zlib.proof.harness.inflate_dict.ITGlobals
               Zlib.proof.harness.inflate_dict.ITFacts Zlib.proof.harness.inflate_dict.ITMainKit.
Require Import Zlib.harness.x_inflate_dict.code.
Require Import Zlib.proof.crc32.Spec.

(* ---------------------------------------------------------------------------------------------- *)
(* The segments of f_main's body                                                                 *)

Fixpoint enc_sub (path: list nat) (s: statement) : statement :=
  match path, s with
  | nil, _ => s
  | O :: pth, Ssequence a _ => enc_sub pth a
  | S _ :: pth, Ssequence _ b => enc_sub pth b
  | O :: pth, Sifthenelse _ a _ => enc_sub pth a
  | S _ :: pth, Sifthenelse _ _ b => enc_sub pth b
  | O :: pth, Sloop a _ => enc_sub pth a
  | S _ :: pth, Sloop _ b => enc_sub pth b
  | _, _ => Sskip
  end.

Definition ones (k: nat) : list nat := repeat 1%nat k.

Ltac get_sub pth :=
  let p := eval vm_compute in pth in
  let x := eval cbv beta iota zeta delta [enc_sub f_main fn_body] in (enc_sub p (fn_body f_main)) in
  exact x.

(* main's body without the (dead) final `return 0` that Clight adds *)
Definition S_main : statement := ltac:(get_sub [0%nat]).
(* from the block loop on (`for (;;) {...}` and the rest) *)
Definition S_loop : statement := ltac:(get_sub (0%nat :: ones 24)).
(* after the block loop: bw_align, the trailer, `slen = w.len`, and the inflate half (seg_inf) *)
Definition S_trl : statement := ltac:(get_sub (0%nat :: ones 25)).
(* the body of the block loop (after its leading skip) *)
Definition Q_blk : list nat := (0%nat :: ones 24 ++ [0; 0; 1])%nat.
Definition seg_blk : statement := ltac:(get_sub Q_blk).
(* `if ((btype & 3) == 0) {stored} else {fixed}`: the two branches *)
Definition seg_stored : statement := ltac:(get_sub (Q_blk ++ ones 5 ++ [0; 0])%nat).
Definition Q_fix : list nat := (Q_blk ++ ones 5 ++ [0; 1])%nat.
Definition seg_fixed : statement := ltac:(get_sub Q_fix).
(* the body of the symbol loop (after its leading skip) *)
Definition Q_sym : list nat := (Q_fix ++ [1; 0; 0; 1])%nat.
Definition seg_sym : statement := ltac:(get_sub Q_sym).
(* `if (kind < 128) {literal} else {reference}`: the two branches *)
Definition seg_lit : statement := ltac:(get_sub (Q_sym ++ ones 3 ++ [0])%nat).
Definition seg_ref : statement := ltac:(get_sub (Q_sym ++ ones 3 ++ [1])%nat).

Lemma S_loop_eq : S_loop = Ssequence (Sloop (Ssequence Sskip seg_blk) Sskip) S_trl.
Proof. reflexivity. Qed.
Lemma S_trl_inf : enc_sub (0%nat :: ones 29) (fn_body f_main) = seg_inf.
Proof. vm_compute. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The encoder's constants and abstract state                                                     *)

(* gv; the addresses of the local variables w, s, osnap, dl; the objects dict (dlen bytes), bad, data (2^18 bytes),
   src (2^19 bytes); zlib (wrap <> 0), wb, flevel, isel, wsel; the dictionary *)
Record ectx := EC {
  e_gv : globals; e_vw : val; e_vs : val; e_vosn : val; e_vdl : val;
  e_dictp : val; e_badp : val; e_datap : val; e_srcp : val;
  e_zlib : bool; e_wb : Z; e_flevel : Z; e_isel : Z; e_wsel : Z; e_dict : list Z }.

(* the ghost of ITFacts.v for the blocks bs *)
Definition eg (E: ectx) (bs: list block) : it_ghost :=
  ITG (e_zlib E) (e_wb E) (e_flevel E) (iw_of (e_zlib E) (e_wb E) (e_isel E)) (e_dict E) bs.

Definition edictid (E: ectx) : Z := ref_adler32 1 (e_dict E).
Definition ebad (E: ectx) : list Z := match e_dict E with [] => [0] | b :: r => Z.lxor b 1 :: r end.
Definition edata (E: ectx) (bs: list block) : list Z := data (e_dict E) bs.

Lemma eg_dictid E bs : it_dictid (eg E bs) = edictid E.
Proof. reflexivity. Qed.
Lemma eg_bad E bs : it_bad (eg E bs) = ebad E.
Proof. reflexivity. Qed.
Lemma eg_data E bs : it_data (eg E bs) = edata E bs.
Proof. reflexivity. Qed.

Definition ectx_ok (E: ectx) : Prop :=
  8 <= e_wb E <= 15 /\ 0 <= e_flevel E <= 255 /\ 0 <= e_isel E <= 255 /\ 0 <= e_wsel E <= 255 /\
  Zlength (e_dict E) <= 2 ^ 16 /\ is_bytes (e_dict E) /\
  isptr (e_dictp E) /\ isptr (e_badp E) /\ isptr (e_datap E) /\ isptr (e_srcp E).

Definition nondyn (b: block) : Prop := match b with Dynamic _ _ _ _ _ => False | _ => True end.

(* the blocks so far: stored or fixed, well formed after the dictionary *)
Definition enc_ok (E: ectx) (bs: list block) : Prop :=
  Forall nondyn bs /\ blocks_ok (2 ^ e_wb E) (e_dict E) bs.

(* the object data[0 .. 2^18): the data D first *)
Definition data_ok (dcont: list val) (D: list Z) : Prop :=
  Zlength dcont = 2 ^ 18 /\ Zlength D <= 2 ^ 18 /\ is_bytes D /\ sublist 0 (Zlength D) dcont = bytes_rep D.

(* the zlib header with the dictionary id (empty for raw) *)
Definition hdr_bytes (E: ectx) : list Z :=
  if e_zlib E then zlib_hdr (e_wb E) (Z.land (e_flevel E) 3) true ++ be_bytes (edictid E) 4 else [].

(* the blocks bs, none of them final, from the bit position p of the deflate stream *)
Fixpoint enc_nf (p: Z) (bs: list block) : list bool :=
  match bs with
  | [] => []
  | b :: r => let e := enc_block p false b in e ++ enc_nf (p + Zlength e) r
  end.

(* the bits of the bit writer at the head of the block loop *)
Definition blk_bits (E: ectx) (bs: list block) : list bool := bytes_bits (hdr_bytes E) ++ enc_nf 0 bs.
(* ... in the symbol loop of a fixed block (BFINAL = last, BTYPE = 01, the symbols syms) *)
Definition sym_bits (E: ectx) (bs: list block) (last: Z) (syms: list sym) : list bool :=
  blk_bits E bs ++ bits_le last 1 ++ bits_le 1 2 ++ flat_map (send_one fixed_ll fixed_dl) syms.

(* the rest of the memory the encoder carries along *)
Definition enc_fr (E: ectx) : mpred :=
  (mem_mgr (e_gv E) * zfuncs (e_gv E) * tables_rep Ers (e_gv E) * crc_table_at Ers (e_gv E) *
   version_lit (e_gv E) * it_hversion_lit (e_gv E) *
   malloc_token Ews (tarray tuchar (Zlength (e_dict E))) (e_dictp E) *
   malloc_token Ews (tarray tuchar (Zlength (ebad E))) (e_badp E) *
   data_at Ews (tarray tuchar (Zlength (ebad E))) (bytes_rep (ebad E)) (e_badp E) *
   malloc_token Ews (tarray tuchar (2 ^ 18)) (e_datap E) * malloc_token Ews (tarray tuchar (2 ^ 19)) (e_srcp E) *
   data_at_ Tsh (Tstruct _z_stream_s noattr) (e_vs E) * data_at_ Tsh (tptr tuchar) (e_vosn E) *
   data_at_ Tsh tuint (e_vdl E))%logic.

(* ---------------------------------------------------------------------------------------------- *)
(* The assertions                                                                                 *)

(* the head of the block loop: the blocks bs written (none final), data[0 .. n) = their data *)
Definition blk_at (E: ectx) (bs: list block) (dcont: list val) : environ -> mpred :=
  PROP (ectx_ok E; enc_ok E bs; data_ok dcont (edata E bs))
  LOCAL (temp _zlib (Vint (Int.repr (if e_zlib E then 1 else 0)));
         temp _wb (Vint (Int.repr (e_wb E))); temp _isel (Vint (Int.repr (e_isel E)));
         temp _wsel (Vint (Int.repr (e_wsel E)));
         temp _dlen (Vint (Int.repr (Zlength (e_dict E)))); temp _dict (e_dictp E);
         temp _bad (e_badp E); temp _blen (Vint (Int.repr (Zlength (ebad E))));
         temp _dictid (Vlong (Int64.repr (edictid E)));
         temp _data (e_datap E); temp _src (e_srcp E);
         temp _maxd (Vint (Int.repr (2 ^ e_wb E)));
         temp _n (Vint (Int.repr (Zlength (edata E bs))));
         lvar _w (Tstruct _bw noattr) (e_vw E); lvar _s (Tstruct _z_stream_s noattr) (e_vs E);
         lvar _osnap (tptr tuchar) (e_vosn E); lvar _dl tuint (e_vdl E); gvars (e_gv E))
  SEP (bw_at Tsh Ews (blk_bits E bs) (2 ^ 19) (e_srcp E) (e_vw E);
       data_at Ews (tarray tuchar (2 ^ 18)) dcont (e_datap E);
       data_at Ews (tarray tuchar (Zlength (e_dict E))) (bytes_rep (e_dict E)) (e_dictp E);
       dref_tabs (e_gv E) Ers it_tabs; enc_fr E).

Definition blk_inv (E: ectx) : environ -> mpred := EX bs: list block, EX dcont: list val, blk_at E bs dcont.

(* in the block loop's body, after `bw_bits(&w, last, 1)` (BFINAL), with room for 8 more bytes before it *)
Definition blk_mid (E: ectx) (bs: list block) (dcont: list val) (last: Z) : environ -> mpred :=
  PROP (ectx_ok E; enc_ok E bs; data_ok dcont (edata E bs); last = 0 \/ last = 1;
        Zlength (blk_bits E bs) / 8 + 8 <= 2 ^ 19)
  LOCAL (temp _last (Vint (Int.repr last));
         temp _zlib (Vint (Int.repr (if e_zlib E then 1 else 0)));
         temp _wb (Vint (Int.repr (e_wb E))); temp _isel (Vint (Int.repr (e_isel E)));
         temp _wsel (Vint (Int.repr (e_wsel E)));
         temp _dlen (Vint (Int.repr (Zlength (e_dict E)))); temp _dict (e_dictp E);
         temp _bad (e_badp E); temp _blen (Vint (Int.repr (Zlength (ebad E))));
         temp _dictid (Vlong (Int64.repr (edictid E)));
         temp _data (e_datap E); temp _src (e_srcp E);
         temp _maxd (Vint (Int.repr (2 ^ e_wb E)));
         temp _n (Vint (Int.repr (Zlength (edata E bs))));
         lvar _w (Tstruct _bw noattr) (e_vw E); lvar _s (Tstruct _z_stream_s noattr) (e_vs E);
         lvar _osnap (tptr tuchar) (e_vosn E); lvar _dl tuint (e_vdl E); gvars (e_gv E))
  SEP (bw_at Tsh Ews (blk_bits E bs ++ bits_le last 1) (2 ^ 19) (e_srcp E) (e_vw E);
       data_at Ews (tarray tuchar (2 ^ 18)) dcont (e_datap E);
       data_at Ews (tarray tuchar (Zlength (e_dict E))) (bytes_rep (e_dict E)) (e_dictp E);
       dref_tabs (e_gv E) Ers it_tabs; enc_fr E).

(* after `if ((btype & 3) == 0) {stored} else {fixed}`: the block b written (BFINAL = last) *)
Definition blk_done (E: ectx) (bs: list block) (last: Z) (b: block) (dcont: list val) : environ -> mpred :=
  PROP (ectx_ok E; enc_ok E bs; nondyn b; block_ok (2 ^ e_wb E) (expand (e_dict E) bs) b;
        data_ok dcont (edata E (bs ++ [b])); last = 0 \/ last = 1)
  LOCAL (temp _last (Vint (Int.repr last));
         temp _zlib (Vint (Int.repr (if e_zlib E then 1 else 0)));
         temp _wb (Vint (Int.repr (e_wb E))); temp _isel (Vint (Int.repr (e_isel E)));
         temp _wsel (Vint (Int.repr (e_wsel E)));
         temp _dlen (Vint (Int.repr (Zlength (e_dict E)))); temp _dict (e_dictp E);
         temp _bad (e_badp E); temp _blen (Vint (Int.repr (Zlength (ebad E))));
         temp _dictid (Vlong (Int64.repr (edictid E)));
         temp _data (e_datap E); temp _src (e_srcp E);
         temp _maxd (Vint (Int.repr (2 ^ e_wb E)));
         temp _n (Vint (Int.repr (Zlength (edata E (bs ++ [b])))));
         lvar _w (Tstruct _bw noattr) (e_vw E); lvar _s (Tstruct _z_stream_s noattr) (e_vs E);
         lvar _osnap (tptr tuchar) (e_vosn E); lvar _dl tuint (e_vdl E); gvars (e_gv E))
  SEP (bw_at Tsh Ews (blk_bits E bs ++ enc_block (Zlength (enc_nf 0 bs)) (last =? 1) b) (2 ^ 19)
             (e_srcp E) (e_vw E);
       data_at Ews (tarray tuchar (2 ^ 18)) dcont (e_datap E);
       data_at Ews (tarray tuchar (Zlength (e_dict E))) (bytes_rep (e_dict E)) (e_dictp E);
       dref_tabs (e_gv E) Ers it_tabs; enc_fr E).

(* the symbol loop of a fixed block: the symbols syms written *)
Definition sym_at (E: ectx) (bs: list block) (last: Z) (syms: list sym) (dcont: list val) : environ -> mpred :=
  PROP (ectx_ok E; enc_ok E bs; last = 0 \/ last = 1;
        syms_ok (2 ^ e_wb E) fixed_ll fixed_dl (expand (e_dict E) bs) syms;
        data_ok dcont (edata E (bs ++ [Fixed syms])))
  LOCAL (temp _last (Vint (Int.repr last));
         temp _zlib (Vint (Int.repr (if e_zlib E then 1 else 0)));
         temp _wb (Vint (Int.repr (e_wb E))); temp _isel (Vint (Int.repr (e_isel E)));
         temp _wsel (Vint (Int.repr (e_wsel E)));
         temp _dlen (Vint (Int.repr (Zlength (e_dict E)))); temp _dict (e_dictp E);
         temp _bad (e_badp E); temp _blen (Vint (Int.repr (Zlength (ebad E))));
         temp _dictid (Vlong (Int64.repr (edictid E)));
         temp _data (e_datap E); temp _src (e_srcp E);
         temp _maxd (Vint (Int.repr (2 ^ e_wb E)));
         temp _n (Vint (Int.repr (Zlength (edata E (bs ++ [Fixed syms])))));
         lvar _w (Tstruct _bw noattr) (e_vw E); lvar _s (Tstruct _z_stream_s noattr) (e_vs E);
         lvar _osnap (tptr tuchar) (e_vosn E); lvar _dl tuint (e_vdl E); gvars (e_gv E))
  SEP (bw_at Tsh Ews (sym_bits E bs last syms) (2 ^ 19) (e_srcp E) (e_vw E);
       data_at Ews (tarray tuchar (2 ^ 18)) dcont (e_datap E);
       data_at Ews (tarray tuchar (Zlength (e_dict E))) (bytes_rep (e_dict E)) (e_dictp E);
       dref_tabs (e_gv E) Ers it_tabs; enc_fr E).

Definition sym_inv (E: ectx) (bs: list block) (last: Z) : environ -> mpred :=
  EX syms: list sym, EX dcont: list val, sym_at E bs last syms dcont.

(* in the symbol loop's body, after `if (kind == 0) break;`: room for 8 more bytes (the gp_assume) *)
Definition sym_room (E: ectx) (bs: list block) (last: Z) (syms: list sym) (dcont: list val) : environ -> mpred :=
  PROP (ectx_ok E; enc_ok E bs; last = 0 \/ last = 1;
        syms_ok (2 ^ e_wb E) fixed_ll fixed_dl (expand (e_dict E) bs) syms;
        data_ok dcont (edata E (bs ++ [Fixed syms]));
        Zlength (sym_bits E bs last syms) / 8 + 8 <= 2 ^ 19)
  LOCAL (temp _last (Vint (Int.repr last));
         temp _zlib (Vint (Int.repr (if e_zlib E then 1 else 0)));
         temp _wb (Vint (Int.repr (e_wb E))); temp _isel (Vint (Int.repr (e_isel E)));
         temp _wsel (Vint (Int.repr (e_wsel E)));
         temp _dlen (Vint (Int.repr (Zlength (e_dict E)))); temp _dict (e_dictp E);
         temp _bad (e_badp E); temp _blen (Vint (Int.repr (Zlength (ebad E))));
         temp _dictid (Vlong (Int64.repr (edictid E)));
         temp _data (e_datap E); temp _src (e_srcp E);
         temp _maxd (Vint (Int.repr (2 ^ e_wb E)));
         temp _n (Vint (Int.repr (Zlength (edata E (bs ++ [Fixed syms])))));
         lvar _w (Tstruct _bw noattr) (e_vw E); lvar _s (Tstruct _z_stream_s noattr) (e_vs E);
         lvar _osnap (tptr tuchar) (e_vosn E); lvar _dl tuint (e_vdl E); gvars (e_gv E))
  SEP (bw_at Tsh Ews (sym_bits E bs last syms) (2 ^ 19) (e_srcp E) (e_vw E);
       data_at Ews (tarray tuchar (2 ^ 18)) dcont (e_datap E);
       data_at Ews (tarray tuchar (Zlength (e_dict E))) (bytes_rep (e_dict E)) (e_dictp E);
       dref_tabs (e_gv E) Ers it_tabs; enc_fr E).

(* after the block loop: the blocks bs (the last one final) *)
Definition blk_end (E: ectx) (bs: list block) (dcont: list val) : environ -> mpred :=
  PROP (ectx_ok E; bs <> []; enc_ok E bs; data_ok dcont (edata E bs))
  LOCAL (temp _zlib (Vint (Int.repr (if e_zlib E then 1 else 0)));
         temp _wb (Vint (Int.repr (e_wb E))); temp _isel (Vint (Int.repr (e_isel E)));
         temp _wsel (Vint (Int.repr (e_wsel E)));
         temp _dlen (Vint (Int.repr (Zlength (e_dict E)))); temp _dict (e_dictp E);
         temp _bad (e_badp E); temp _blen (Vint (Int.repr (Zlength (ebad E))));
         temp _dictid (Vlong (Int64.repr (edictid E)));
         temp _data (e_datap E); temp _src (e_srcp E);
         temp _maxd (Vint (Int.repr (2 ^ e_wb E)));
         temp _n (Vint (Int.repr (Zlength (edata E bs))));
         lvar _w (Tstruct _bw noattr) (e_vw E); lvar _s (Tstruct _z_stream_s noattr) (e_vs E);
         lvar _osnap (tptr tuchar) (e_vosn E); lvar _dl tuint (e_vdl E); gvars (e_gv E))
  SEP (bw_at Tsh Ews (bytes_bits (hdr_bytes E) ++ enc_blocks 0 bs) (2 ^ 19) (e_srcp E) (e_vw E);
       data_at Ews (tarray tuchar (2 ^ 18)) dcont (e_datap E);
       data_at Ews (tarray tuchar (Zlength (e_dict E))) (bytes_rep (e_dict E)) (e_dictp E);
       dref_tabs (e_gv E) Ers it_tabs; enc_fr E).

(* main's precondition after start_function, `unfold R; Intros` and the zcalloc/zcfree function pointers *)
Definition pro_pre (gv: globals) (vw vs vosn vdl: val) : environ -> mpred :=
  PROP ()
  LOCAL (lvar _dl tuint vdl; lvar _osnap (tptr tuchar) vosn; lvar _s (Tstruct _z_stream_s noattr) vs;
         lvar _w (Tstruct _bw noattr) vw; gvars gv)
  SEP (zfuncs gv; data_at_ Tsh tuint vdl; data_at_ Tsh (tptr tuchar) vosn;
       data_at_ Tsh (Tstruct _z_stream_s noattr) vs; data_at_ Tsh (Tstruct _bw noattr) vw; mem_mgr gv;
       tables_rep Ers gv; crc_table_at Ers gv; version_lit gv; it_hversion_lit gv; dref_tabs gv Ers it_tabs).

(* ---------------------------------------------------------------------------------------------- *)
(* The segment statements                                                                        *)

(* the prologue: from main's start to the block loop (draws, gp_assume, the four objects (NULL -> return 0), the
   dictionary, the wrong one, dictid, the bit writer, maxd, the zlib header, n = 0), given the rest *)
Definition seg_pro_stmt {Espec: OracleKind} : Prop :=
  forall gv vw vs vosn vdl,
    (forall E, semax Delta_m (blk_inv E) S_loop POST_m) ->
    semax Delta_m (pro_pre gv vw vs vosn vdl) S_main POST_m.

(* a stored block (the then branch of `if ((btype & 3) == 0)`) *)
Definition seg_stored_stmt {Espec: OracleKind} : Prop :=
  forall E bs dcont last (Post: ret_assert),
    semax Delta_m (blk_mid E bs dcont last) seg_stored
      (overridePost (EX l: list Z, EX dcont': list val, blk_done E bs last (Stored l) dcont') Post).

(* a literal of a fixed block (the then branch of `if (kind < 128)`, the end of the symbol loop's body) *)
Definition seg_lit_stmt {Espec: OracleKind} : Prop :=
  forall E bs last syms dcont (Post: ret_assert),
    semax Delta_m (sym_room E bs last syms dcont) seg_lit (loop1_ret_assert (sym_inv E bs last) Post).

(* a back-reference of a fixed block (the else branch: an out-of-range one is skipped by `continue`; the hist loop
   copies it into data; bw_fixed_match) *)
Definition seg_ref_stmt {Espec: OracleKind} : Prop :=
  forall E bs last syms dcont (Post: ret_assert),
    semax Delta_m (sym_room E bs last syms dcont) seg_ref (loop1_ret_assert (sym_inv E bs last) Post).

(* the trailer: from after the block loop to `slen = w.len`, then the inflate half *)
Definition seg_trl_stmt {Espec: OracleKind} : Prop :=
  seg_inf_ok (fun _ => True) ->
  forall E bs dcont, semax Delta_m (blk_end E bs dcont) S_trl POST_m.

(* ---------------------------------------------------------------------------------------------- *)
(* Pure lemmas over Format.v                                                                      *)

Lemma lz_copy_prefix n dist out : exists l, lz_copy n dist out = out ++ l.
Proof.
  revert out; induction n; intros out; simpl.
  - exists []. rewrite app_nil_r. auto.
  - destruct (IHn (out ++ [Znth (Zlength out - dist) out])) as [l E]. rewrite E.
    exists ([Znth (Zlength out - dist) out] ++ l). rewrite app_assoc. auto.
Qed.

Lemma syms_data_prefix syms out : exists l, syms_data out syms = out ++ l.
Proof.
  unfold syms_data. revert out; induction syms as [|s r IH]; intros out; simpl.
  - exists []. rewrite app_nil_r. auto.
  - assert (exists l, sym_data out s = out ++ l) as [l1 E1].
    { destruct s; simpl. exists [b]. auto. apply lz_copy_prefix. }
    destruct (IH (sym_data out s)) as [l2 E2]. rewrite E2, E1. exists (l1 ++ l2). rewrite app_assoc. auto.
Qed.

Lemma block_data_prefix out b : exists l, block_data out b = out ++ l.
Proof. destruct b; simpl; [exists bytes; auto | apply syms_data_prefix | apply syms_data_prefix]. Qed.

Lemma expand_prefix h bs : exists l, expand h bs = h ++ l.
Proof.
  unfold expand. revert h; induction bs as [|b r IH]; intros h; simpl.
  - exists []. rewrite app_nil_r. auto.
  - destruct (block_data_prefix h b) as [l1 E1]. destruct (IH (block_data h b)) as [l2 E2].
    rewrite E2, E1. exists (l1 ++ l2). rewrite app_assoc. auto.
Qed.

Lemma expand_data h bs : expand h bs = h ++ data h bs.
Proof.
  destruct (expand_prefix h bs) as [l E]. unfold data. rewrite E, Zlength_app.
  pose proof (Zlength_nonneg h). pose proof (Zlength_nonneg l).
  rewrite sublist_app2 by lia. rewrite Z.sub_diag. rewrite sublist_same by lia. auto.
Qed.

Lemma expand_snoc h bs b : expand h (bs ++ [b]) = block_data (expand h bs) b.
Proof. unfold expand. rewrite fold_left_app. reflexivity. Qed.

Lemma data_snoc h bs b l : block_data (expand h bs) b = expand h bs ++ l -> data h (bs ++ [b]) = data h bs ++ l.
Proof.
  intros E. pose proof (expand_data h (bs ++ [b])) as E1. rewrite expand_snoc, E, expand_data, <- app_assoc in E1.
  apply app_inv_head in E1. auto.
Qed.

Lemma data_stored h bs l : data h (bs ++ [Stored l]) = data h bs ++ l.
Proof. apply data_snoc. reflexivity. Qed.

Lemma expand_fixed h bs syms : expand h (bs ++ [Fixed syms]) = syms_data (expand h bs) syms.
Proof. apply expand_snoc. Qed.

Lemma data_fixed_nil h bs : data h (bs ++ [Fixed []]) = data h bs.
Proof. rewrite (data_snoc h bs (Fixed []) []); [apply app_nil_r | simpl; rewrite app_nil_r; auto]. Qed.

Lemma syms_data_snoc out syms s : syms_data out (syms ++ [s]) = sym_data (syms_data out syms) s.
Proof. unfold syms_data. rewrite fold_left_app. reflexivity. Qed.

Lemma data_fixed_lit h bs syms c :
  data h (bs ++ [Fixed (syms ++ [Lit c])]) = data h (bs ++ [Fixed syms]) ++ [c].
Proof.
  pose proof (expand_data h (bs ++ [Fixed (syms ++ [Lit c])])) as E1.
  rewrite expand_fixed, syms_data_snoc, <- expand_fixed, expand_data in E1. simpl in E1.
  rewrite <- app_assoc in E1. apply app_inv_head in E1. auto.
Qed.

(* a reference: the history-and-data after it *)
Lemma expand_fixed_ref h bs syms len dist :
  expand h (bs ++ [Fixed (syms ++ [Ref len dist])]) = lz_copy (Z.to_nat len) dist (expand h (bs ++ [Fixed syms])).
Proof. rewrite !expand_fixed, syms_data_snoc. reflexivity. Qed.

Lemma blocks_ok_snoc w h bs b : blocks_ok w h (bs ++ [b]) <-> blocks_ok w h bs /\ block_ok w (expand h bs) b.
Proof.
  unfold expand. revert h; induction bs as [|b0 r IH]; intros h; simpl.
  - tauto.
  - rewrite IH. tauto.
Qed.

Lemma syms_ok_snoc w ll dl out syms s :
  syms_ok w ll dl out (syms ++ [s]) <-> syms_ok w ll dl out syms /\ sym_ok w ll dl (syms_data out syms) s.
Proof.
  unfold syms_data. revert out; induction syms as [|s0 r IH]; intros out; simpl.
  - tauto.
  - rewrite IH. tauto.
Qed.

Lemma enc_nf_cons p b r : enc_nf p (b :: r) = enc_block p false b ++ enc_nf (p + Zlength (enc_block p false b)) r.
Proof. reflexivity. Qed.

Lemma enc_nf_snoc p bs b : enc_nf p (bs ++ [b]) = enc_nf p bs ++ enc_block (p + Zlength (enc_nf p bs)) false b.
Proof.
  revert p; induction bs as [|b0 r IH]; intros p.
  - change ([] ++ [b]) with [b]. rewrite enc_nf_cons. change (enc_nf p []) with (@nil bool).
    rewrite Z.add_0_r. simpl. rewrite app_nil_r. auto.
  - change ((b0 :: r) ++ [b]) with (b0 :: (r ++ [b])). rewrite !enc_nf_cons, IH, Zlength_app, <- app_assoc.
    do 3 f_equal. lia.
Qed.

Lemma enc_blocks_snoc p bs b : enc_blocks p (bs ++ [b]) = enc_nf p bs ++ enc_block (p + Zlength (enc_nf p bs)) true b.
Proof.
  revert p; induction bs as [|b0 r IH]; intros p.
  - change ([] ++ [b]) with [b]. change (enc_nf p []) with (@nil bool). rewrite Z.add_0_r.
    change (enc_blocks p [b]) with (enc_block p true b ++ enc_blocks (p + Zlength (enc_block p true b)) []).
    simpl. rewrite !app_nil_r. auto.
  - change ((b0 :: r) ++ [b]) with (b0 :: (r ++ [b])).
    assert (Hne: r ++ [b] <> []) by (destruct r; discriminate).
    transitivity (enc_block p false b0 ++ enc_blocks (p + Zlength (enc_block p false b0)) (r ++ [b])).
    { change (enc_blocks p (b0 :: (r ++ [b]))) with
        (let e := enc_block p (match r ++ [b] with [] => true | _ => false end) b0 in
         e ++ enc_blocks (p + Zlength e) (r ++ [b])).
      destruct (r ++ [b]); [contradiction | reflexivity]. }
    rewrite IH, enc_nf_cons, Zlength_app, <- app_assoc. do 3 f_equal. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Compspecs moves                                                                               *)

Lemma bytes_adler_cs sh n (v: list val) q:
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.
Lemma bytes_dref_cs sh n (v: list val) q:
  @data_at Zlib.contracts.x_inflate_decode.Harness.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_dref); [apply JMeq_refl | reflexivity]. Qed.
Lemma bw_struct_cs sh (v: val * (val * val)) q:
  @data_at Zlib.contracts.x_inflate_decode.Harness.CS sh t_bw v q = @data_at CS sh (Tstruct _bw noattr) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_dref); [apply JMeq_refl | reflexivity]. Qed.

(* the bit writer at the law's compspecs (to read or write w's fields directly) *)
Lemma bw_at_law sh bsh B cap buf w :
  bw_at sh bsh B cap buf w =
  EX contents: list val, !! bw_bytes_ok B cap contents &&
  (data_at sh (Tstruct _bw noattr) (buf, (Vint (Int.repr (Zlength B / 8)), Vint (Int.repr (Zlength B mod 8)))) w *
   data_at bsh (tarray tuchar cap) contents buf).
Proof. unfold bw_at, bw_rep. rewrite bw_struct_cs. f_equal. extensionality c. rewrite bytes_dref_cs. auto. Qed.
