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

(************************************************************************)
(** * Refinement Relations                                                 *)
(************************************************************************)

Parameter w: nat.


Definition Rword {n} : 'B_n -> word n -> Type := fun_hrel (@bitw n).
Definition Rtuple {n} : bitseq -> 'B_n -> Type := fun_hrel val.
Definition Rbits {n} : bitseq -> word n -> Type := Rtuple \o Rword.

Definition Rnat {n} : bitseq -> nat -> Type := fun_hrel (bitn n).

Module Wordsize.
  Definition wordsize := w.
End Wordsize.
Module Native := Make(Wordsize).

Definition Rnative: Native.Int -> bitseq -> Type := Native.Tnative.
Definition Rnum: Native.Int -> nat -> Type := Rnative \o (@Rnat w).

(************************************************************************)
(** * From machine words to bit sequences                               *)
(************************************************************************)

(* Pierre: there is a problem with [eq_adj] and the way we deal with [bitseq]s. *)

Section Try.

Import Native.
Definition NInt_rel (i: Int) (bs: bitseq) : Prop := bs = bitsFromInt w i.

Global Instance eq_Rnative_try:
  refines (NInt_rel ==> NInt_rel ==> param.bool_R)%rel Native.eq (eqtype.eq_op).
Proof.
rewrite !refinesE => w1 bs1 -> w2 bs2 ->.
suff -> : eq w1 w2 = (bitsFromInt w w1 == bitsFromInt w w2).
  exact: bool_Rxx.
by apply/eqIntP/eqP => [->//|]; exact: bitsFromInt_inj.
Qed.

Global Instance land_Rnative_try:
  refines (NInt_rel ==> NInt_rel ==> NInt_rel) Native.land ands.
Proof.
rewrite !refinesE => w1 bs1 -> w2 bs2 ->.
have /forallIntP /(_ w1) /forallIntP /(_ w2) /eqIntP -> := land_valid.
by rewrite /NInt_rel bitsToIntK.
Qed.

End Try.

(*
Proof.
  rewrite refinesE=> i1 bs1 Ribs1 i2 bs2 Ribs2.
  move: Ribs1 Ribs2.
  rewrite /eq_op/eq_NativeInt/Rnative/Native.Tnative.
  rewrite Native.eq_adj.
  repeat (rewrite Native.eq_adj; move/eqP=> ->).
  have ->: (NativeInt.eq i1 i2) = (bitsFromInt w i1 == bitsFromInt w i2)
    by apply/eqIntP/eqP; intro; subst; auto using Native.bitsFromInt_inj.
  exact: bool_Rxx.
Qed.
*)

Global Instance zero_Rnative: refines Rnative Native.zero '0_w.
Proof. rewrite refinesE. apply Native.zero_valid. Qed.

Global Instance one_Rnative: refines Rnative Native.one (bitn w 1).
Proof. rewrite refinesE. apply Native.one_valid. Qed.

Global Instance lnot_Rnative:
  refines (Rnative ==> Rnative) Native.lnot negs.
Admitted.
(*
Proof.
  rewrite refinesE=> i bs.
  rewrite /Rnative/Native.Tnative Native.eq_adj.
  move/eqP=> ->.
  move: i; apply/forallIntP.
  by apply Native.lnot_valid.
Qed.
*)

Global Instance land_Rnative:
  refines (Rnative ==> Rnative ==> Rnative) Native.land ands.
Admitted.
(*
Proof.
  rewrite refinesE=> i1 bs1 Ribs1 i2 bs2 Ribs2. move: Ribs1 Ribs2.
  repeat (rewrite /Rnative/Native.Tnative Native.eq_adj; move/eqP=> ->).
  move: i2; apply: forallIntP.
  move: i1; apply: forallIntP.
  by apply Native.land_valid.
Qed.
*)

Global Instance lor_Rnative: 
  refines (Rnative ==> Rnative ==> Rnative) Native.lor ors.
Admitted.
(*
Proof.
  rewrite refinesE=> i1 bs1 Ribs1 i2 bs2 Ribs2.
  move: Ribs1 Ribs2.
  repeat (rewrite /Rnative/Native.Tnative Native.eq_adj; move/eqP=> ->).
  move: i2; apply: forallIntP.
  move: i1; apply: forallIntP.
  by apply Native.lor_valid.
Qed.
*)

Global Instance lxor_Rnative: 
  refines (Rnative ==> Rnative ==> Rnative) Native.lxor xors.
Admitted.
(*
Proof.
  rewrite refinesE=> i1 bs1 Ribs1 i2 bs2 Ribs2.
  move: Ribs1 Ribs2.
  repeat (rewrite /Rnative/Native.Tnative Native.eq_adj; move/eqP=> ->).
  move: i2; apply: forallIntP.
  move: i1; apply: forallIntP.
  by apply Native.lxor_valid.
Qed.
*)

(* XXX: explicit bounding of k is not satisfactory. *)
Global Instance lsr_Rnative: forall k n, (n <= w)%N -> Rnum k n ->
  refines (Rnative ==> Rnative) (fun i => Native.lsr i k) (fun i => shrs i n).
Admitted.
(*
Proof.
  move=> k n Hleq Rkn.
  rewrite refinesE=> i bs Ribs.
  move: Rkn Ribs.
  rewrite /Rnum/Rnat/Rnative/Native.Tnative.
  rewrite /comp_hrel.
  move=> [bs2 [/eqIntP Hi2 Hbs2]].
  rewrite /Rnative/Native.Tnative Native.eq_adj; move/eqP=> ->.

  have Hn: n = nats (bitsFromInt w k).
  rewrite Hi2.
  
  
  
  Search bitsFromInt bitsToInt.
  rewrite Native.eq_adj.

  rewrite <-Hbs2 in Hi2.
  move/eqIntP: Hi2=> Hi2.
  rewrite -[NativeInt.eq _ _]/(eq_op _ _) in Hi2.
  
  rewrite Hbs2 in Hi2.
  rewrite eq_adj in Hi2.


    := forallInt (fun i =>
       forallInt (fun i' =>
         let n := nats (bitsFromInt w i') in
         (n <= w) ==>
         Tnative (lsr i i') 
                 (shrs (bitsFromInt w i) n))).


  move/existsP=> [bs' /andP [H /eqP H']].
  rewrite /Rnative eq_adj in H.
  move/eqP: H=> H.
  apply/eqInt32P.
  have Hk: k = toNat (bitsFromInt32 i').
    rewrite H.
    have ->: k = toNat (fromNat (n := wordsize) k).
      rewrite toNat_fromNatBounded=> //.
      by apply (leq_ltn_trans (n := wordsize)).
    by rewrite H'.
  rewrite Hk.
  rewrite Hk in ltn_k.
  clear H H' Hk.
  move: i' ltn_k; apply/(forallInt32P (fun i' => implb (toNat (bitsFromInt32 i') <= wordsize)%nat (eq (lsr i i') (bitsToInt32 (shrBn (bitsFromInt32 i) (toNat ((bitsFromInt32 i')))))))).
  move=> i'.
  apply/equivP.
  apply/implyP.
  split=> H H'.
  move: (H H')=> H''.
  by apply/eqInt32P.
  move: (H H')=> H''.
  by apply/eqInt32P.
  move: i; apply/forallInt32P; last by apply lsr_valid.
  move=> i'; apply idP.
Qed.
*)

(*
Global Instance lsl_repr: 
  refines (Rnative ==> Rnative ==> Rnative) <<< (fun x y => shlBn x (toNat y)).
Admitted.
(*
Proof.
  move=> i i' ? k ltn_k.
  rewrite /Rnative eq_adj; move/eqP=> <-.
  rewrite /natural_repr.
  move/existsP=> [bs' /andP [H /eqP H']].
  rewrite /Rnative eq_adj in H.
  move/eqP: H=> H.
  apply/eqInt32P.
  have Hk: k = toNat (bitsFromInt32 i').
    rewrite H.
    have ->: k = toNat (fromNat (n := wordsize) k).
      rewrite toNat_fromNatBounded=> //.
      by apply (leq_ltn_trans (n := wordsize)).
    by rewrite H'.
  rewrite Hk.
  rewrite Hk in ltn_k.
  clear H H' Hk.
  move: i' ltn_k; apply/(forallInt32P (fun i' => implb (toNat (bitsFromInt32 i') <= wordsize)%nat (eq (lsl i i') (bitsToInt32 (shlBn (bitsFromInt32 i) (toNat ((bitsFromInt32 i')))))))).
  move=> i'.
  apply/equivP.
  apply/implyP.
  split=> H H'.
  move: (H H')=> H''.
  by apply/eqInt32P.
  move: (H H')=> H''.
  by apply/eqInt32P.
  move: i; apply/forallInt32P; last by apply lsl_valid.
  move=> i'; apply idP.
Qed.
*)
*)

(************************************************************************)
(** * Drafts of instances                                               *)
(************************************************************************)

(* XXX: this must be removed/updated *)

(*
Axiom W0 : forall n,  word n.+1.

Global Instance zero_Rword {n}: refines Rword (B0 (W0 n).
Admitted.

Global Instance zero_Rtuple {n}: refines Rtuple '0_n (B0 n).
Admitted.

Global Instance zero_Rbits {n}: refines Rbits '0_n (W0 n).
Proof. eapply refines_trans; tc. Qed.

Axiom andw: forall {n}, word n -> word n -> word n.
Axiom negw: forall {n}, word n -> word n.
Axiom negBB: forall {n}, 'B_n -> 'B_n.

Global Instance and_Rword {n}: 
  refines (Rword ==> Rword ==> Rword) (@andB n) andw.
Admitted.

Global Instance and_Rtuple {n}: 
  refines (Rtuple ==> Rtuple ==> Rtuple) ands (@andB n).
Admitted.

Global Instance and_Rbits {n}: 
  refines (Rbits ==> Rbits ==> Rbits) ands (@andw n).
Proof. eapply refines_trans; tc. Qed.


Section Operations.

Variable (Bits : Type).
Variable (and : Bits -> Bits -> Bits).
Variable (not : Bits -> Bits).

Definition nand (bs bs': Bits): Bits 
  := not (and bs bs').

End Operations.

Parametricity nand.

Check nand_R.

Global Instance neg_Rbits {n}: 
  refines (Rbits ==> Rbits) negB (@negw n).
Admitted.

Global Instance nand_Rbits {n}: 
  refines (Rbits ==> Rbits ==> Rbits) 
          (@nand _ ands negB) 
          (@nand _ (@andw n) negw). 
Proof. param nand_R. Qed.
*)
