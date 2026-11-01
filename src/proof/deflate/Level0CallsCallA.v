(** * Level 0 over several deflate() calls: the first call

    The first call of the harnesses' loop, on the state deflateInit2_ left, with [k] blocks drawn: Z_NO_FLUSH when
    data is left after them ([Level0CallsCallANf]), Z_FINISH otherwise ([Level0CallsCallAFin]); a cut trailer
    only when the data needed [k] blocks or more. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.Level0CallsCallAFin.
Import ListNotations.
Local Open Scope Z_scope.

Theorem l0_callA wbits data room pos O s tin tout adler msg k :
  l0_com wbits data room pos O s tin tout adler -> l0_stA wbits pos O s adler -> 1 <= k <= 65532 ->
  l0_call_post wbits data room pos O s tin tout adler msg k (l0_blocks (Zlength data) <= k).
Proof.
  intros Hcom HA Hk.
  destruct (Z_lt_le_dec (65535 * k) (Zlength data)) as [Hnf|Hfin].
  - pose proof (l0_callA_nf wbits data room pos O s tin tout adler msg k Hcom HA Hk Hnf) as P.
    unfold l0_call_post in *.
    destruct P as (s' & z' & code & E & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & Fok & Fend).
    exists s', z', code.
    do 10 (split; [assumption|]).
    split; [|exact Fend].
    intros Ec. destruct (Fok Ec) as [Hi Hc]. split; [exact Hi|]. intros C. destruct (Hc C).
  - exact (l0_callA_fin wbits data room pos O s tin tout adler msg k Hcom HA Hk Hfin).
Qed.
