(* deflate() offered no input object: next_in = Z_NULL with avail_in = 0.

   zlib allows it (deflate tests next_in against Z_NULL only when avail_in != 0, and read_buf returns before
   touching next_in when there is nothing to read); harness/rt_gzip_header.c calls offer(&strm, Z_NULL, 0, out,
   bound) then deflate(&strm, Z_FINISH).  DSpec.deflate_spec cannot express it: next_in is `offset_val nin pin`
   (Vundef for pin = Z_NULL) and the input object `data_at ... pin` (False at Z_NULL).  [deflate_specN] is
   deflate_spec with next_in = [in_ptrN pin nin] and the input object [in_objN ish inb pin]: Z_NULL and no object
   (inb = []) when pin = Z_NULL, deflate_spec's otherwise; the model relation is deflate_spec's.

   Every internal function of deflate.c that carries next_in and the input object in its specification
   (read_buf, flush_pending, fill_window, the five compressors: [in_funs]) needs the same generalization.
   [deflate_bodyN_stmt]: those functions have SOME specifications GN (calling convention cc_default) proved of
   their bodies in their DSpec contexts with GN in place of the DSpec specifications of in_funs, and deflate()'s
   body is proved against deflate_specN in DSpec.Gprog_deflate with GN in place. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.deflate.DCS.
Require Export Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.zutil.Libc Zlib.proof.zutil.Spec.
Require Import Zlib.proof.adler32.Spec Zlib.proof.crc32.Spec.
Require Import Zlib.deflate.code.
Local Open Scope logic.

(* next_in: Z_NULL without an input object, nin bytes into the object at pin otherwise *)
Definition in_ptrN (pin : val) (nin : Z) : val := if eq_dec pin nullval then nullval else offset_val nin pin.

(* the input object: none at Z_NULL (no input), the bytes inb at pin otherwise *)
Definition in_objN (ish : share) (inb : list Z) (pin : val) : mpred :=
  if eq_dec pin nullval then !! (inb = []) && emp
  else @data_at DCS.CS ish (tarray tuchar (Zlength inb)) (map vi inb) pin.

Definition deflate_specN :=
 DECLARE _deflate
 WITH os : option dstate, strmp : val, ghp : val, sp : val, hx : share * val * val * val,
      pin : val, ish : share, inb : list Z, nin : Z, ain : Z, tin : Z, pout : val, rest : list val, W : wvw, tout : Z,
      msgv : val, msg : option Z, adler : Z, flush : Z, r : option dstate * strm * Z, gv : globals
 PRE [ tptr t_strm, tint ]
  PROP (msg_ok msg msgv; readable_share ish; Zlength rest = 0 -> wv_ok W; s32_ok flush;
        strm_ranges (zmk inb nin ain tin (Zlength rest) tout adler msg);
        exists ef, ef_ok gv ef /\
          on_state (fun s z => c_deflate_g ef s z flush) os (zmk inb nin ain tin (Zlength rest) tout adler msg)
            = Some r)
  PARAMS (strmp; vi flush) GLOBALS (gv)
  SEP (dstream_sp 2 os strmp ghp sp gv;
       api_fields strmp (in_ptrN pin nin) ain tin pout (Zlength rest) tout msgv adler;
       in_objN ish inb pin;
       @data_at DCS.CS Ews (tarray tuchar (Zlength rest)) rest pout;
       hdr_at os ghp hx; deflate_globals gv; wv_at W pout)
 POST [ tint ]
  PROP () RETURN (vi (snd r))
  SEP (dstream_sp 2 (fst (fst r)) strmp ghp sp gv;
       EX msgv' : val, !! msg_ok (z_msg (snd (fst r))) msgv' &&
       api_fields strmp (in_ptrN pin (z_next_in (snd (fst r)))) (z_avail_in (snd (fst r)))
         (z_total_in (snd (fst r))) (offset_val (Zlength (z_out (snd (fst r)))) pout)
         (z_avail_out (snd (fst r))) (z_total_out (snd (fst r))) msgv' (z_adler (snd (fst r)));
       in_objN ish inb pin;
       @data_at DCS.CS Ews (tarray tuchar (Zlength rest))
         (map vi (z_out (snd (fst r))) ++ sublist (Zlength (z_out (snd (fst r)))) (Zlength rest) rest) pout;
       hdr_at os ghp hx; deflate_globals gv; wv_at W pout).

(* the internal functions of deflate.c whose specifications carry next_in and the input object *)
Definition in_funs : list ident :=
  [_read_buf; _flush_pending; _fill_window; _deflate_stored; _deflate_fast; _deflate_slow; _deflate_rle;
   _deflate_huff].

(* the specification of i in GN, or d *)
Definition gn_spec (GN : funspecs) (i : ident) (d : funspec) : ident * funspec :=
  (i, match find (fun g : ident * funspec => Pos.eqb (fst g) i) GN with Some g => snd g | None => d end).

(* the context G with GN's specifications in place of G's for the functions GN specifies *)
Definition subst_specs (GN G : funspecs) : funspecs :=
  map (fun f : ident * funspec => gn_spec GN (fst f) (snd f)) G.

Definition deflate_bodyN_stmt : Prop :=
  exists GN : funspecs,
    map fst GN = in_funs /\
    Forall (fun f : ident * funspec => callingconvention_of_funspec (snd f) = cc_default) GN /\
    (forall {Espec: OracleKind},
       @semax_body Zlib.proof.deflate.DSpec.Vprog (subst_specs GN Gprog_read_buf) DCS.CS f_read_buf (gn_spec GN _read_buf (snd read_buf_spec))) /\
    (forall {Espec: OracleKind},
       @semax_body Zlib.proof.deflate.DSpec.Vprog (subst_specs GN Gprog_flush_pending) DCS.CS f_flush_pending
         (gn_spec GN _flush_pending (snd flush_pending_spec))) /\
    (forall {Espec: OracleKind},
       @semax_body Zlib.proof.deflate.DSpec.Vprog (subst_specs GN Gprog_fill_window) DCS.CS f_fill_window
         (gn_spec GN _fill_window (snd fill_window_spec))) /\
    (forall {Espec: OracleKind},
       @semax_body Zlib.proof.deflate.DSpec.Vprog (subst_specs GN Gprog_compress) DCS.CS f_deflate_stored
         (gn_spec GN _deflate_stored (snd deflate_stored_spec))) /\
    (forall {Espec: OracleKind},
       @semax_body Zlib.proof.deflate.DSpec.Vprog (subst_specs GN Gprog_compress) DCS.CS f_deflate_fast
         (gn_spec GN _deflate_fast (snd deflate_fast_spec))) /\
    (forall {Espec: OracleKind},
       @semax_body Zlib.proof.deflate.DSpec.Vprog (subst_specs GN Gprog_compress) DCS.CS f_deflate_slow
         (gn_spec GN _deflate_slow (snd deflate_slow_spec))) /\
    (forall {Espec: OracleKind},
       @semax_body Zlib.proof.deflate.DSpec.Vprog (subst_specs GN Gprog_compress) DCS.CS f_deflate_rle
         (gn_spec GN _deflate_rle (snd deflate_rle_spec))) /\
    (forall {Espec: OracleKind},
       @semax_body Zlib.proof.deflate.DSpec.Vprog (subst_specs GN Gprog_compress) DCS.CS f_deflate_huff
         (gn_spec GN _deflate_huff (snd deflate_huff_spec))) /\
    (forall {Espec: OracleKind},
       @semax_body Zlib.proof.deflate.DSpec.Vprog (subst_specs GN Gprog_deflate) DCS.CS f_deflate deflate_specN).
