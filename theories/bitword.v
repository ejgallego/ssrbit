(******************************************************************************)
(* A bit library for Coq: extensional theory of words.                        *)
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
(* From mathcomp *)
(* Require Import bigop ssralg ssrnum fingroup perm finalg zmodp ssrint. *)

Require Import bitseq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(*                                                                            *)
(* We develop the theory of bit sequences or words. This file provides a high *)
(* level, non-computable extensional specification of the theory.             *)
(*                                                                            *)
(*      word = {ffun 'I_n -> bool}                                            *)
(*                                                                            *)
(* We define all bit operations over this representation, and provide a       *)
(* bijection with the compuational representation.                            *)
(*                                                                            *)
(******************************************************************************)

Section BitFFun.

Variable k : nat.

(* We thank Cyril Cohen for the suggestion *)
Definition word := {ffun 'I_k -> bool}.

Implicit Type (b : bitseq) (t : k.-tuple bool) (w : word).

Definition seqw w        := val (fgraph w).
Definition wrds b : word := [ffun i => nth false b (val i)].

Lemma size_seqw w : size (seqw w) = k.
Proof. by rewrite size_tuple card_ord. Qed.

Lemma seqwK : cancel seqw wrds.
Proof. by move=> w; apply/ffunP=> i; rewrite /= !ffunE nth_fgraph_ord. Qed.

Lemma wrdbK : {in [pred x | size x == k], cancel wrds seqw}.
Proof.
move=> b /eqP hsz; apply: (@eq_from_nth _ false); first by rewrite size_seqw.
move=> i; rewrite size_seqw => hlt.
by rewrite (_ : i = (Ordinal hlt)) // nth_fgraph_ord ffunE.
Qed.
About tnth.
Definition bitw w        := tcast (@card_ord k) (fgraph w).
Definition wrdt t : word := [ffun i => tnth t i].

Lemma val_tcast T n m (t : n.-tuple T) (eq_nm : n = m) :
  val (tcast eq_nm t) = val t.
Proof.
by move: (eq_nm); rewrite /tcast -eq_nm => eq_nn; rewrite eq_axiomK.
Qed.

Lemma bitwE w : bitw w = seqw w :> bitseq.
Proof. by rewrite val_tcast. Qed.

(* The rest should follow from the cancellation lemmas *)
Lemma wrdtK : cancel wrdt bitw.
Proof.
move=> t; apply: eq_from_tnth => i.
by rewrite tcastE tnth_fgraph ffunE enum_val_ord cast_ordKV.
Qed.

End BitFFun.
