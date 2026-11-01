(* bytes_eq(a, b, len) (harness/laws_common.h) when a or b may be Z_NULL with len = 0.

   bytes_eq reads nothing when len = 0, so a Z_NULL argument is fine there (api_short_output compares an output
   buffer of capacity 0, which any_bytes may return as Z_NULL; rt_roundtrip compares an output space and a copy
   of the data, both of which may be Z_NULL when the data is empty).  Spec.bytes_eq_spec takes both slices as
   cbuf_ok objects.  [bytes_eq_spec_n] adds the flags isa and isb: isa = isb = false is Spec.bytes_eq_spec exactly;
   isa = true is a = Z_NULL, len = 0, no object for a (likewise isb for b); the result is then 1.
   [bytes_eq_n_stmt]: its body, from Spec's (the body obligation in laws_common_ok) and the empty cases. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.units.Adler32.

Section BytesEqNull.
#[local] Existing Instance Zlib.units.Adler32.CS.

Definition bytes_eq_spec_n :=
  DECLARE HL._bytes_eq
  WITH isa : bool, a : val, sha : share, pa : val, loa : Z, na : Z, ca : list val, da : list Z,
       isb : bool, b : val, shb : share, pb : val, lob : Z, nb : Z, cb : list val, db : list Z, len : Z
  PRE [ tptr tuchar, tptr tuchar, tulong ]
    PROP (0 <= len <= Int64.max_unsigned;
          if isa then a = nullval /\ len = 0 /\ da = [] else cbuf_ok false a sha pa loa na len ca da;
          if isb then b = nullval /\ len = 0 /\ db = [] else cbuf_ok false b shb pb lob nb len cb db)
    PARAMS (a; b; Vlong (Int64.repr len))
    SEP (if isa then emp else data_at sha (tarray tuchar na) ca pa;
         if isb then emp else data_at shb (tarray tuchar nb) cb pb)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (if list_eq_dec Z.eq_dec da db then 1 else 0)))
    SEP (if isa then emp else data_at sha (tarray tuchar na) ca pa;
         if isb then emp else data_at shb (tarray tuchar nb) cb pb).

Definition bytes_eq_n_stmt : Prop :=
  laws_common_ok -> @semax_body Vprog_lc Gprog_bytes_eq Zlib.units.Adler32.CS HL.f_bytes_eq bytes_eq_spec_n.

End BytesEqNull.
