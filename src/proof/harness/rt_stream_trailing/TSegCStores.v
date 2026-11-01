(* Law rt_stream_trailing (harness/rt_stream_trailing.c), main: the stores `decompressor.next_in = input;
   decompressor.next_out = out;` (statements 32-33 of main's body, the end of TMainKit.segC_t) on a decompressor of
   any contents.  Stated for any values of main's temporaries and any frame, so that TSegC.tseg_c uses it right
   after inflateInit2_ returned Z_OK and main asserted it; it is a file of its own because the two stores into the
   14-field struct are slow to elaborate (as rt_stream's USegCStores.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream.UMainKit.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainKit.
Require Import Zlib.harness.rt_stream_trailing.code.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.

(* statements 32-33 of main's body *)
Definition segC_t_stores : statement := ltac:(get_stmt_t (suf 5 (take 7 (suf 27 body0_t)))).

(* main's temporaries after inflateInit2_'s result was tested and asserted, with any values; the local struct
   position at is not touched *)
Definition tcs_locals (t ln af ip lv wb ml st dl cap dp ep cp op vd vc va : val) (gv : globals) : list localdef :=
  [temp _code t; temp _compressed_len ln; temp _after af; temp _input ip; temp _level lv; temp _window_bits wb;
   temp _mem_level ml; temp _strategy st; temp _data_len dl; temp _out_size cap; temp _data dp; temp _expected ep;
   temp _compressed cp; temp _out op;
   lvar _decompressor t_z vd; lvar _at t_p va; lvar _compressor t_z vc; gvars gv].

(* the two stores replace the struct's next_in by input and its next_out by out, the rest is unchanged *)
Lemma tseg_c_stores {Espec : OracleKind} t ln af ip lv wb ml st dl cap dp ep cp op vd vc va gv (R : list mpred)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 : val) :
  semax Delta_t
    (PROPx [] (LOCALx (tcs_locals t ln af ip lv wb ml st dl cap dp ep cp op vd vc va gv)
      (SEPx (data_at Tsh t_z (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (a8, (a9, (a10, (a11, (a12, a13))))))))))))) vd
             :: R))))
    segC_t_stores
    (normal_ret_assert
      (PROPx [] (LOCALx (tcs_locals t ln af ip lv wb ml st dl cap dp ep cp op vd vc va gv)
        (SEPx (data_at Tsh t_z (ip, (a1, (a2, (op, (a4, (a5, (a6, (a7, (a8, (a9, (a10, (a11, (a12, a13))))))))))))) vd
               :: R))))).
Proof.
  unfold tcs_locals, segC_t_stores.
  forward.
  forward.
  apply ENTAIL_refl.
Qed.
