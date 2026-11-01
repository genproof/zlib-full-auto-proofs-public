(** * deflate() with one more witness of the weak validity of next_out

    DSpec.deflate_spec takes from its caller, when there is no output space (avail_out = 0), a witness that
    next_out is weakly valid (deflate tests next_out == Z_NULL): the malloc token of a 0-byte object at
    next_out, or a readable byte just before it ([DSpec.wvw]).  A caller whose output buffer is a nonempty
    object of which nothing is written yet, offering 0 bytes of it (law rt_stream: avail_out = upto(...) may be
    0 at the first call, next_out at the start of the compressed buffer), has neither; it has a readable byte AT
    next_out.  [deflate_specV] is deflate_spec with that third witness ([WVat]); everything else is unchanged,
    so DSpec.deflate_spec is the special case [WVold].  The witness is used only for the
    NULL test of next_out (StageEntry.out_wv), so deflate's body proof carries over
    ([deflate_bodyV_stmt]: the body in deflate's context of Obligations.ob_deflate). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.deflate.code.
#[export] Existing Instance DCS.CS.

(** The witnesses: DSpec's, or a readable byte at the pointer itself. *)
Inductive wvw2 := WVold (w : wvw) | WVat (sh : share) (v : val).
Definition wv2_ok (w : wvw2) : Prop :=
  match w with WVold w => wv_ok w | WVat sh _ => readable_share sh end.
Definition wv2_at (w : wvw2) (p : val) : mpred :=
  match w with WVold w => wv_at w p | WVat sh v => @data_at DCS.CS sh tuchar v p end.

(** DSpec.deflate_spec with the witness [W : wvw2]. *)
Definition deflate_specV :=
 DECLARE _deflate
 WITH os : option dstate, strmp : val, ghp : val, sp : val, hx : share * val * val * val,
      pin : val, ish : share, inb : list Z, nin : Z, ain : Z, tin : Z, pout : val, rest : list val, W : wvw2,
      tout : Z, msgv : val, msg : option Z, adler : Z, flush : Z, r : option dstate * strm * Z, gv : globals
 PRE [ tptr t_strm, tint ]
  PROP (msg_ok msg msgv; readable_share ish; Zlength rest = 0 -> wv2_ok W; s32_ok flush;
        strm_ranges (zmk inb nin ain tin (Zlength rest) tout adler msg);
        exists ef, ef_ok gv ef /\
          on_state (fun s z => c_deflate_g ef s z flush) os (zmk inb nin ain tin (Zlength rest) tout adler msg)
            = Some r)
  PARAMS (strmp; vi flush) GLOBALS (gv)
  SEP (dstream_sp 2 os strmp ghp sp gv;
       api_fields strmp (offset_val nin pin) ain tin pout (Zlength rest) tout msgv adler;
       @data_at DCS.CS ish (tarray tuchar (Zlength inb)) (map vi inb) pin;
       @data_at DCS.CS Ews (tarray tuchar (Zlength rest)) rest pout;
       hdr_at os ghp hx; deflate_globals gv; wv2_at W pout)
 POST [ tint ]
  PROP () RETURN (vi (snd r))
  SEP (dstream_sp 2 (fst (fst r)) strmp ghp sp gv;
       EX msgv' : val, !! msg_ok (z_msg (snd (fst r))) msgv' &&
       api_fields strmp (offset_val (z_next_in (snd (fst r))) pin) (z_avail_in (snd (fst r)))
         (z_total_in (snd (fst r))) (offset_val (Zlength (z_out (snd (fst r)))) pout)
         (z_avail_out (snd (fst r))) (z_total_out (snd (fst r))) msgv' (z_adler (snd (fst r)));
       @data_at DCS.CS ish (tarray tuchar (Zlength inb)) (map vi inb) pin;
       @data_at DCS.CS Ews (tarray tuchar (Zlength rest))
         (map vi (z_out (snd (fst r))) ++ sublist (Zlength (z_out (snd (fst r)))) (Zlength rest) rest) pout;
       hdr_at os ghp hx; deflate_globals gv; wv2_at W pout).

(** deflate's body against deflate_specV, in the context of Obligations.ob_deflate. *)
Definition deflate_bodyV_stmt : Prop :=
  @semax_body DSpec.Vprog DSpec.Gprog_deflate DCS.CS Zlib.deflate.code.f_deflate deflate_specV.
