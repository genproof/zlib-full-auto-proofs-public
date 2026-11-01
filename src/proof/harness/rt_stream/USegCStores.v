(* Law rt_stream (data of any length), main: the stores `decompressor.next_in = compressed;
   decompressor.next_out = out;` (statements 28-29 of main's body, the end of UMainKit.segC) on a decompressor of
   any contents.  Stated for any values of main's temporaries and any frame, so that USegC.useg_c uses it right
   after inflateInit2_ returned Z_OK and main asserted it; it is a file of its own because the two stores into the 14-field struct are
   slow to elaborate. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream.UMainKit.
Require Import Zlib.harness.rt_stream.code.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.

(* statements 28-29 of main's body *)
Definition segC_stores : statement := ltac:(get_stmt (suf 6 (take 8 (suf 22 body0)))).

(* main's temporaries after inflateInit2_'s result was tested and asserted, with any values; the local struct
   position at is not touched *)
Definition scs_locals (t ln lv wb ml st dl cap dp ep cp op vd vc va : val) (gv : globals) : list localdef :=
  [temp _code t; temp _compressed_len ln; temp _level lv; temp _window_bits wb; temp _mem_level ml;
   temp _strategy st; temp _data_len dl; temp _out_size cap; temp _data dp; temp _expected ep; temp _compressed cp;
   temp _out op;
   lvar _decompressor t_z vd; lvar _at t_p va; lvar _compressor t_z vc; gvars gv].

(* the two stores replace the struct's next_in by compressed and its next_out by out, the rest is unchanged *)
Lemma useg_c_stores {Espec : OracleKind} t ln lv wb ml st dl cap dp ep cp op vd vc va gv (R : list mpred)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 : val) :
  semax Delta_m
    (PROPx [] (LOCALx (scs_locals t ln lv wb ml st dl cap dp ep cp op vd vc va gv)
      (SEPx (data_at Tsh t_z (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (a8, (a9, (a10, (a11, (a12, a13))))))))))))) vd
             :: R))))
    segC_stores
    (normal_ret_assert
      (PROPx [] (LOCALx (scs_locals t ln lv wb ml st dl cap dp ep cp op vd vc va gv)
        (SEPx (data_at Tsh t_z (cp, (a1, (a2, (op, (a4, (a5, (a6, (a7, (a8, (a9, (a10, (a11, (a12, a13))))))))))))) vd
               :: R))))).
Proof.
  unfold scs_locals, segC_stores.
  forward.
  forward.
  apply ENTAIL_refl.
Qed.
