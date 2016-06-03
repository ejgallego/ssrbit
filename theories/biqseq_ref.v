(******************************************************************************)
(* A bit library for Coq: refinements of bit sequences.                       *)
(******************************************************************************)
(*                                                                            *)
(* (c) 2016, MINES ParisTech                                                  *)
(*                                                                            *)
(* Written by Pierre-Evariste Dagand                                          *)
(*            Emilio J. Gallego Arias                                         *)
(*                                                                            *)
(* LICENSE: CECILL-B                                                          *)
(*                                                                            *)
(******************************************************************************)

From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.
From mathcomp
Require Import choice fintype finset tuple finfun.
From mathcomp
Require Import bigop ssralg ssrnum fingroup perm finalg zmodp ssrint.

From CoqEAL
Require Import hrel refinements pos.

Require Import bitseq.

(* Refinements by P-E Dagand *)
Section BitFFun.

Variable k : nat.

Definition BitSeq := {ffun 'I_k -> bool}.
Implicit Type (b : k.-tuple bool) (f : BitSeq).

Definition orB b1 b2          := [tuple of liftz false orb b1 b2].
Definition orF f1 f2 : BitSeq := [ffun j => f1 j || f2 j].

Definition R_bitseq b f : Prop := f =1 getb b.
Notation "b ≈ f" := (R_bitseq b f) (at level 42).
(* Even if like this more *)
(* Definition R_bitseq b f : bool := [forall j, f j == getb b j]. *)

Lemma getb_liftz (j : 'I_k) d op b1 b2 :
  getb (liftz d op b1 b2) j = op (nth d b1 j) (nth d b2 j).
Proof.
rewrite /getb /liftz (nth_map (d, d)) ?nth_zipd //.
by rewrite size_zipd !size_tuple maxnn.
Qed.

Lemma R_or b1 f1 (hR1 : b1 ≈ f1) b2 f2 (hR2 : b2 ≈ f2) : [tuple of orB b1 b2] ≈ orF f1 f2.
Proof. by move=> x; rewrite ffunE hR1 hR2 getb_liftz. Qed.

Global Instance or_refineP : refines (R_bitseq ==> R_bitseq ==> R_bitseq)%rel orB orF.
Proof. by rewrite refinesE; exact: R_or. Qed.

Definition funB bv : BitSeq := [ffun x : 'I_k => getb bv x].

Lemma funbP bv : funB bv =1 getb bv.
Proof. exact: ffunE. Qed.

(* Require Import Parametricty. *)

End BitFFun.

