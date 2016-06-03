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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import bitseq.

(* Refinements by P-E Dagand *)
Section BitFFun.

Variable k : nat.

Definition BitSeq := {ffun 'I_k -> bool}.
Implicit Type (b : bitseq) (f : BitSeq).

Definition orB b1 b2          := liftz false orb b1 b2.
Definition orF f1 f2 : BitSeq := [ffun j => f1 j || f2 j].

Definition R_bitseq b f : Prop := b = fgraph f.
Notation "b ≈ f" := (R_bitseq b f) (at level 42).
(* Even if like this more *)
(* Definition R_bitseq b f : bool := [forall j, f j == getb b j]. *)

Lemma size_ref b f : b ≈ f -> size b = k.
Proof. by move ->; rewrite size_tuple card_ord. Qed.

Lemma R_or b1 f1 (hR1 : b1 ≈ f1) b2 f2 (hR2 : b2 ≈ f2) : orB b1 b2 ≈ orF f1 f2.
Proof.
have sz1 := size_ref hR1.
have sz2 := size_ref hR2.
have szO : size (orB b1 b2) = k by rewrite size_liftz sz1 sz2 maxnn.
apply: (@eq_from_nth _ false); first by rewrite szO size_tuple card_ord.
move=> i i_lt; rewrite /liftz (nth_map (false,false)).
  have lt : i < #|'I_k| by rewrite card_ord -szO.
  have U x : ((fgraph x)`_i)%B = tnth (fgraph x) (Ordinal lt).
    by rewrite (tnth_nth false).
  by rewrite nth_zipd hR1 hR2 !U /orF !tnth_fgraph ffunE.
by rewrite size_zipd sz1 sz2 maxnn -szO.
Qed.

Global Instance or_refineP : refines (R_bitseq ==> R_bitseq ==> R_bitseq)%rel orB orF.
Proof. by rewrite refinesE; exact: R_or. Qed.

Definition funB bv : BitSeq := [ffun x : 'I_k => getb bv x].

Lemma funbP bv : funB bv =1 getb bv.
Proof. exact: ffunE. Qed.

(* Require Import Parametricty. *)

End BitFFun.

