From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.
From mathcomp
Require Import choice fintype finset tuple finfun.
From CoqEAL
Require Import hrel param refinements.

Require Import bitseq bitword notation axioms.

Import Refinements.Op.
Import Logical.Op.


Local Open Scope rel_scope.
Local Open Scope bits_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



(**

 The refinement relations have a type of the following form

 <<
   R : specification -> implementation -> Type
 >>

  while the transport lemmas have the form

   <<
     Lemma R_op: refines refinement_relation specification implementation.
   >>

*)


(************************************************************************)
(** * Refinement Relations                                                 *)
(************************************************************************)

(* XXX: the following refinement are not in the correct order
(spec/implem): this must be updated. *)

(* 

Definition Rword {n} : 'B_n -> word n -> Type := fun_hrel (@bitw n).
Definition Rtuple {n} : bitseq -> 'B_n -> Type := fun_hrel val.
Definition Rbits {n} : bitseq -> word n -> Type := Rtuple \o Rword.
Definition Rnat: nat -> bitseq -> Type := fun_hrel nats.

*)


(** ** Refinement from bit sequences to machines words *)

Parameter w: nat.

Module Wordsize.
  Definition wordsize := w.
End Wordsize.
Module Native := Make(Wordsize).

Definition Rnative: bitseq -> Native.Int -> Type := fun_hrel (bitsFromInt Native.w).

(* "small" integers (ie. less than the word size) for shifts *)
CoInductive Ridx: nat -> Native.Int -> Type := 
  Ridx_spec (n: nat)(i: Native.Int) of 
    (n <= Native.w)%N
  & bitsFromInt Native.w i = bitn Native.w n : Ridx n i.

(************************************************************************)
(** * From machine words to bit sequences                               *)
(************************************************************************)


Global Instance Rnative_eq:
  refines (Rnative ==> Rnative ==> param.bool_R)%rel (eqtype.eq_op) Native.eq.
Proof.
  rewrite !refinesE => bs1 w1 <- bs2 w2 <-.
  suff -> : Native.eq w1 w2 = (bitsFromInt w w1 == bitsFromInt w w2)
    by exact: bool_Rxx.
  apply/eqIntP/eqP => [->//|]; exact: Native.bitsFromInt_inj.
Qed.

Global Instance Rnative_zero: refines Rnative '0_w Native.zero.
Proof. 
  rewrite refinesE. 
  have /eqIntP -> := Native.zero_valid.
  by rewrite /Rnative/fun_hrel Native.bitsToIntK. 
Qed.

Global Instance Rnative_one: refines Rnative (bitn w 1) Native.one.
Proof. 
  rewrite refinesE. 
  have /eqIntP -> := Native.one_valid.
  by rewrite /Rnative/fun_hrel Native.bitsToIntK. 
Qed.

Global Instance Rnative_lnot:
  refines (Rnative ==> Rnative) negs Native.lnot.
Proof.
  rewrite refinesE=> bs w <-.
  have /forallIntP /(_ w) /eqIntP -> := Native.lnot_valid.
  by rewrite /Rnative/Native.Tnative/fun_hrel Native.bitsToIntK.
Qed.

Global Instance Rnative_land:
  refines (Rnative ==> Rnative ==> Rnative) ands Native.land.
Proof.
  rewrite !refinesE => bs1 w1 <- bs2 w2 <-.
  have /forallIntP /(_ w1) /forallIntP /(_ w2) /eqIntP -> := Native.land_valid.
  by rewrite /Rnative/fun_hrel Native.bitsToIntK.
Qed.

Global Instance Rnative_lor: 
  refines (Rnative ==> Rnative ==> Rnative) ors Native.lor.
Proof.
  rewrite !refinesE => bs1 w1 <- bs2 w2 <-.
  have /forallIntP /(_ w1) /forallIntP /(_ w2) /eqIntP -> := Native.lor_valid.
  by rewrite /Rnative/fun_hrel Native.bitsToIntK.
Qed.

Global Instance Rnative_lxor: 
  refines (Rnative ==> Rnative ==> Rnative) xors Native.lxor.
Proof.
  rewrite !refinesE => bs1 w1 <- bs2 w2 <-.
  have /forallIntP /(_ w1) /forallIntP /(_ w2) /eqIntP -> := Native.lxor_valid.
  by rewrite /Rnative/fun_hrel Native.bitsToIntK.
Qed.

Global Instance Rnative_lsr: 
  refines (Rnative ==> Ridx ==> Rnative) shrs Native.lsr.
Proof.
  rewrite !refinesE => bs1 w1 <- _ _ [n i Hn Hi].
  have H : nats (bitsFromInt Native.w i) = n
    by rewrite Hi bitnK; 
       try (eapply leq_ltn_trans, ltn_expl).
  subst n.
  have /forallIntP /(_ w1) /forallIntP /(_ i) /implyP /(_ Hn) /eqIntP -> := Native.lsr_valid.
  by rewrite /Rnative/fun_hrel Native.bitsToIntK.
Qed.

Global Instance lsl_repr: 
  refines (Rnative ==> Ridx ==> Rnative) shls Native.lsl.
Proof.
  rewrite !refinesE => bs1 w1 <- _ _ [n i Hn Hi].
  have H : nats (bitsFromInt Native.w i) = n
    by rewrite Hi bitnK; 
       try (eapply leq_ltn_trans, ltn_expl).
  subst n.
  have /forallIntP /(_ w1) /forallIntP /(_ i) /implyP /(_ Hn) /eqIntP -> := Native.lsl_valid.
  by rewrite /Rnative/fun_hrel Native.bitsToIntK.
Qed.

