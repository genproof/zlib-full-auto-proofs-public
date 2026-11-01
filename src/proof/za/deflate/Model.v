(* The model of one deflate() call right after a successful deflateInit2_ is defined for any flush, any input
   and any output space of up to 2^32-1 bytes (Stmt.v, za_deflate_model_stmt). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.za.deflate.Stmt.
Require Zlib.proof.za.deflate.ModelCall.

Lemma za_deflate_model : za_deflate_model_stmt.
Proof.
  intros level method wbits mem strategy s z1 inb aout flush _ _ _ _ _ HI Hb Hl Ha _.
  exact (Zlib.proof.za.deflate.ModelCall.first_call Zlib.proof.za.deflate.ModelCore.first_core
           level method wbits mem strategy zrst0 s z1 inb aout flush HI Hb ltac:(rep_lia) ltac:(rep_lia)).
Qed.
