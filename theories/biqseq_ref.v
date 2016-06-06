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
Implicit Type (b : bitseq) (bt : k.-tuple bool) (f : BitSeq).

Definition orB b1 b2          := liftz false orb b1 b2.
Definition orF f1 f2 : BitSeq := [ffun j => f1 j || f2 j].

Definition R_bitseq b f : Prop := b = fgraph f.
Notation "b ≈ f" := (R_bitseq b f) (at level 42).
(* Even if like this more *)
(* Definition R_bitseq b f : bool := [forall j, f j == getb b j]. *)

Lemma size_ref b f : b ≈ f -> size b = k.
Proof. by move->; rewrite size_tuple card_ord. Qed.

Lemma R_or b1 f1 (hR1 : b1 ≈ f1) b2 f2 (hR2 : b2 ≈ f2) : orB b1 b2 ≈ orF f1 f2.
Proof.
have sz1 := size_ref hR1.
have sz2 := size_ref hR2.
have szO : size (orB b1 b2) = k by rewrite size_liftz sz1 sz2 maxnn.
apply: (@eq_from_nth _ false); first by rewrite size_tuple card_ord szO.
move=> i hsz; rewrite !nth_liftz ?(sz2, sz1) -?szO //.
have hlt : i < k by rewrite -szO.
by rewrite hR1 hR2 !(nth_fgraph_ord false (Ordinal hlt)) ffunE.
Qed.

Global Instance or_refineP : refines (R_bitseq ==> R_bitseq ==> R_bitseq)%rel orB orF.
Proof. by rewrite refinesE; exact: R_or. Qed.

Definition funB bv : BitSeq := [ffun x : 'I_k => getb bv x].

Lemma funbP bv : funB bv =1 getb bv.
Proof. exact: ffunE. Qed.

(* Require Import Parametricty. *)

End BitFFun.

Section BitFFunTuples.

(* A different attempt with composition of refinments *)
Variable k : nat.

Implicit Type (b : k.-tuple bool) (f : BitSeq k).

Definition orT b1 b2 := [tuple of liftz false orb b1 b2].

Definition R_bittup b f : Prop := (tnth b) =1 f.
Notation "b ≈ f" := (R_bittup b f) (at level 42).

Lemma R_orT b1 f1 (hR1 : b1 ≈ f1) b2 f2 (hR2 : b2 ≈ f2) : orT b1 b2 ≈ orF f1 f2.
Proof. by move=> i; rewrite !tnth_liftz ffunE hR1 hR2. Qed.

End BitFFunTuples.

Section BitSeqTuples.

Variable k : nat.

Implicit Type (b : bitseq) (bt : k.-tuple bool).

Definition R_seqtup b bt : Prop := b = bt.
Notation "b ≈ f" := (R_seqtup b f) (at level 42).

Lemma R_orB b1 bt1 (hR1 : b1 ≈ bt1) b2 bt2 (hR2 : b2 ≈ bt2) : orB b1 b2 ≈ orT bt1 bt2.
Proof. by rewrite hR1 hR2. Qed.

End BitSeqTuples.

(* XXX: The below seems broken *)
Section BitFFun2.

(* A different attempt trying to preseve sizes *)
Variable k : nat.

Definition BitSeq2 := {ffun 'I_k -> bool}.
Implicit Type (b : bitseq) (bt : k.-tuple bool) (f : BitSeq2).

Definition orB2 b1 b2           := liftz false orb b1 b2.
Definition orF2 f1 f2 : BitSeq2 := [ffun j => f1 j || f2 j].

Definition bsgraph f : k.-tuple bool := tcast (card_ord k) (fgraph f).

Lemma bsgraphE f : bsgraph f = fgraph f :> bitseq.
Proof.
apply: (@eq_from_nth _ false).
  by rewrite !size_tuple card_ord.
move=> i; rewrite size_tuple => hi.
rewrite (_ : i = Ordinal hi) // !nth_fgraph_ord -tnth_nth.
rewrite /bsgraph tcastE tnth_fgraph; congr (f _).
by apply/val_inj; rewrite enum_val_ord cast_ordKV.
Qed.

Definition R_bitgraph b f : Prop := b = bsgraph f.
Notation "b ≈ f" := (R_bitgraph b f) (at level 42).
(* Even if like this more *)
(* Definition R_bitseq b f : bool := [forall j, f j == getb b j]. *)

Lemma size_ref' b f : b ≈ f -> size b = k.
Proof. by move ->; rewrite size_tuple. Qed.

(* Lemma R_inj bt f : tnth bt =1 f -> bt ≈ f. *)
(* Proof. *)
(* (* There is a problem with dependent types to solve here. *) *)
(* move=> heq; apply: (@eq_from_nth _ false). *)
(*   by rewrite !size_tuple card_ord. *)
(* move=> i hi. *)
(* have lt1 : i < #|'I_k| by rewrite card_ord -(size_tuple bt). *)
(* have lt2 : i < k       by rewrite size_tuple in hi. *)
(* rewrite -(tnth_nth false _ (Ordinal lt1)). *)
(* rewrite -(tnth_nth false _ (Ordinal lt2)). *)
(* by rewrite heq tnth_fgraph; congr (f _); apply/val_inj; rewrite enum_val_ord. *)
(* Qed. *)

Lemma R_orF b1 f1 (hR1 : b1 ≈ f1) b2 f2 (hR2 : b2 ≈ f2) : orB b1 b2 ≈ orF f1 f2.
Proof.
have/eqP sz1 := size_ref' hR1.
have/eqP sz2 := size_ref' hR2.

rewrite (_ : orB b1 b2 = [tuple of orB (Tuple sz1) (Tuple sz2)]) //.
apply: (congr1 val); apply: eq_from_tnth => x.
rewrite /bsgraph tcastE tnth_fgraph enum_val_ord cast_ordKV.
rewrite /orF ffunE.
rewrite hR1 in sz1 *.
rewrite hR2 in sz2 *.
rewrite /= /orB tnth_liftz.

apply: R_inj => x; rewrite /orF ffunE.


rewrite /orB.
move=> i i_lt; rewrite /liftz (nth_map (false,false)).
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

