(* The case LENLENS (17) of inflate()'s switch cut into its three statements (Cases5_TL.v):
   ll_loop1: while (state->have < state->ncode) { NEEDBITS(3); state->lens[order[state->have++]] = BITS(3); DROPBITS(3); }
   then `if (leave) break;`,
   ll_zero:  while (state->have < 19) state->lens[order[state->have++]] = 0;
   ll_tail:  next = codes; lencode = distcode = next; lenbits = 7; ret = inflate_table(CODES, ...);
             if (ret) { msg; mode = BAD; break; } have = 0; mode = CODELENS; *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CaseHyps5.
#[local] Existing Instance Zlib.units.Inflate.CS.

Definition ll_body : statement := case_body 17.
Definition ll_loop1 : statement := match ll_body with Ssequence l _ => l | _ => Sskip end.
Definition ll_rest1 : statement := match ll_body with Ssequence _ r => r | _ => Sskip end.
Definition ll_zero : statement := match ll_rest1 with Ssequence _ (Ssequence z _) => z | _ => Sskip end.
Definition ll_tail : statement := match ll_rest1 with Ssequence _ (Ssequence _ t) => t | _ => Sskip end.

Lemma ll_body_eq: ll_body =
  Ssequence ll_loop1 (Ssequence (Sifthenelse (Etempvar _leave tint) Sbreak Sskip) (Ssequence ll_zero ll_tail)).
Proof. reflexivity. Qed.

(* the Clight of the parts *)
Ltac ll_stmt := cbv beta iota zeta delta [ll_loop1 ll_zero ll_tail ll_rest1 ll_body case_body inflate_LS find_switch
  f_inflate fn_body ls_drop].

(* the machine after the first loop *)
Definition ll_exit (m m1: mst) : Prop :=
  lenlens_loop 19 m = m1 /\ mwf m1 /\ m_mode m1 = LENLENS /\
  (m_leave m1 = 1 \/ (m_leave m1 = 0 /\ i_ncode (m_s m1) <= i_have (m_s m1))).
