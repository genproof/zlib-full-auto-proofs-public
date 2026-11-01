(** * v9 specifications of deflateResetKeep, deflateReset, deflateInit2_ (they supersede DSpec's
      deflateResetKeep_spec, deflateReset_spec, deflateInit2__spec, which stay defined but are no longer used:
      Obligations.v states ob_deflateResetKeep, ob_deflateReset, ob_deflateInit2_ with these)

    Why: compress2_z calls deflateInit on a local z_stream whose next_in, avail_in, total_in,
    next_out, avail_out, total_out, msg, adler are uninitialised; DSpec's specs required them as numbers (api_fields).
    These three functions read none of them; they write total_in, total_out, msg, adler.  The v9 specs take those
    four with any value ([reset_fields]), next_in with any value (deflateStateCheck's validity witness), and do not
    mention avail_in, next_out, avail_out (the caller frames them).  Everything else is DSpec verbatim. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.deflate.DCS.
Require Export Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.zutil.Libc Zlib.proof.zutil.Spec.
Require Import Zlib.proof.adler32.Spec Zlib.proof.crc32.Spec.
Require Import Zlib.deflate.code.
#[export] Existing Instance DCS.CS.

(** v9 (compress2 calls deflateInit on a stream whose fields are uninitialised): deflateResetKeep,
    deflateReset and deflateInit2_ READ none of the caller's z_stream fields and WRITE total_in, total_out, msg, adler
    (only on Z_OK, except msg); their specs take those four with any value ([reset_fields]) and next_in (for
    deflateStateCheck) with any value; avail_in, next_out, avail_out are not touched (framed by the caller).  The model
    runs on [zrst0] (zeros); after the call a written field holds the model's value, an unwritten one its old value. *)
Definition reset_fields (strmp : val) (tin tout msgv adler : val) : mpred :=
  (@field_at DCS.CS Ews t_strm (DOT _total_in) tin strmp *
   @field_at DCS.CS Ews t_strm (DOT _total_out) tout strmp *
   @field_at DCS.CS Ews t_strm (DOT _msg) msgv strmp *
   @field_at DCS.CS Ews t_strm (DOT _adler) adler strmp)%logic.

Definition zrst0 : strm := zmk [] 0 0 0 0 0 0 None.

(** [rfv ok new old]: the field after the call. *)
Definition rfv (ok : bool) (new : Z) (old : val) : val := if ok then vl new else old.

Definition api_simple_spec_v9 (f : ident) (cf : dstate -> strm -> option (dstate * strm * Z))
    (post_lvl : Z -> Z -> Z) :=
 DECLARE f
 WITH lvl : Z, os : option dstate, strmp : val, ghp : val, nextin : val, tin : val, tout : val, msgv : val,
      adler : val, r : option dstate * strm * Z, gv : globals
 PRE [ tptr t_strm ]
  PROP (on_state cf os zrst0 = Some r)
  PARAMS (strmp) GLOBALS (gv)
  SEP (dstream lvl os strmp ghp gv; @field_at DCS.CS Ews t_strm (DOT _next_in) nextin strmp;
       reset_fields strmp tin tout msgv adler; deflate_globals gv)
 POST [ tint ]
  PROP () RETURN (vi (snd r))
  SEP (dstream (post_lvl lvl (snd r)) (fst (fst r)) strmp ghp gv;
       @field_at DCS.CS Ews t_strm (DOT _next_in) nextin strmp;
       EX msgv' : val,
       !! (if snd r =? Z_OK then msg_ok (z_msg (snd (fst r))) msgv' else msgv' = msgv) &&
       reset_fields strmp (rfv (snd r =? Z_OK) (z_total_in (snd (fst r))) tin)
         (rfv (snd r =? Z_OK) (z_total_out (snd (fst r))) tout) msgv'
         (rfv (snd r =? Z_OK) (z_adler (snd (fst r))) adler);
       deflate_globals gv).

(** deflateReset and deflateResetKeep accept any initialisation level (deflateInit2_ calls deflateReset right
    after zmemzero); on Z_OK, ResetKeep has set the descriptors (level >= 1) and Reset also head[] (level 2). *)
Definition deflateReset_spec_v9 := api_simple_spec_v9 _deflateReset c_deflateReset
  (fun lvl code => if code =? Z_OK then 2 else lvl).
Definition deflateResetKeep_spec_v9 := api_simple_spec_v9 _deflateResetKeep c_deflateResetKeep
  (fun lvl code => if code =? Z_OK then Z.max lvl 1 else lvl).

Definition deflateInit2__spec_v9 :=
 DECLARE _deflateInit2_
 WITH strmp : val, level : Z, method : Z, wbits : Z, mem : Z, strategy : Z, vp : val, vsh : share,
      vers : list Z, ssize : Z, ni : val, tin : val, tout : val, msgv : val, adler : val,
      op : val, dt : val, st0 : val, gv : globals
 PRE [ tptr t_strm, tint, tint, tint, tint, tint, tptr tschar, tint ]
  PROP (s32_ok level; s32_ok method; s32_ok wbits; s32_ok mem; s32_ok strategy; s32_ok ssize;
        readable_share vsh; 1 <= Zlength vers; -128 <= Znth 0 vers < 128;
        forall a1 a2 a3 a4 a5, exists r,
          c_deflateInit2_ (Znth 0 vers =? 49) (ssize =? 112) false level method wbits mem strategy a1 a2 a3 a4 a5 zrst0
            = Some r)
  PARAMS (strmp; vi level; vi method; vi wbits; vi mem; vi strategy; vp; vi ssize) GLOBALS (gv)
  SEP (@field_at DCS.CS Ews t_strm (DOT _next_in) ni strmp;
       reset_fields strmp tin tout msgv adler;
       @field_at DCS.CS Ews t_strm (DOT _zalloc) nullval strmp;
       @field_at DCS.CS Ews t_strm (DOT _zfree) nullval strmp;
       @field_at DCS.CS Ews t_strm (DOT _opaque) op strmp;
       @field_at DCS.CS Ews t_strm (DOT _data_type) dt strmp;
       @field_at DCS.CS Ews t_strm (DOT _state) st0 strmp;
       @field_at_ DCS.CS Ews t_strm (DOT _reserved) strmp;
       @data_at DCS.CS vsh (tarray tschar (Zlength vers)) (map vi vers) vp;
       mem_mgr gv; deflate_globals gv)
 POST [ tint ]
  EX a1 : bool, EX a2 : bool, EX a3 : bool, EX a4 : bool, EX a5 : bool, EX r : option dstate * strm * Z,
  PROP (c_deflateInit2_ (Znth 0 vers =? 49) (ssize =? 112) false level method wbits mem strategy a1 a2 a3 a4 a5 zrst0
          = Some r)
  RETURN (vi (snd r))
  SEP (match fst (fst r) with
       | Some _ => dstream 2 (fst (fst r)) strmp nullval gv
       | None => EX st : val, EX za : val, EX zf : val, EX op' : val, EX dt' : val,
                 !! (snd r = Z_VERSION_ERROR -> st = st0) &&
                 (zfuncs gv * @field_at_ DCS.CS Ews t_strm (DOT _reserved) strmp *
                  @field_at DCS.CS Ews t_strm (DOT _state) st strmp *
                  @field_at DCS.CS Ews t_strm (DOT _zalloc) za strmp *
                  @field_at DCS.CS Ews t_strm (DOT _zfree) zf strmp *
                  @field_at DCS.CS Ews t_strm (DOT _opaque) op' strmp *
                  @field_at DCS.CS Ews t_strm (DOT _data_type) dt' strmp)
       end;
       @field_at DCS.CS Ews t_strm (DOT _next_in) ni strmp;
       EX msgv' : val,
       !! (if snd r =? Z_VERSION_ERROR then msgv' = msgv else msg_ok (z_msg (snd (fst r))) msgv') &&
       reset_fields strmp (rfv (snd r =? Z_OK) (z_total_in (snd (fst r))) tin)
         (rfv (snd r =? Z_OK) (z_total_out (snd (fst r))) tout) msgv'
         (rfv (snd r =? Z_OK) (z_adler (snd (fst r))) adler);
       @data_at DCS.CS vsh (tarray tschar (Zlength vers)) (map vi vers) vp;
       mem_mgr gv; deflate_globals gv).

(** The callee contexts of the three bodies with the v9 specs. *)
Definition Gprog_deflateResetKeep_v9 : funspecs := Gprog_deflateResetKeep.
Definition Gprog_deflateReset_v9 : funspecs := [deflateResetKeep_spec_v9; lm_init_spec].
Definition Gprog_deflateInit2__v9 : funspecs :=
  [zcalloc_spec; zcfree_spec; memset_spec; deflateEnd_spec; deflateReset_spec_v9].
