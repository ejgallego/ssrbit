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
From mathcomp
Require Import bigop ssralg ssrnum fingroup perm finalg zmodp ssrint.

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
(* The main operations are:                                                   *)
(*                                                                            *)
(*    seqw w  == returns the underlying sequence.                             *)
(*    wrds bs == builds a word from a bitseq                                  *)
(*                                                                            *)
(* and their stronger counterparts:                                           *)
(*                                                                            *)
(*    bitw w == returns the underlying tuple.                                 *)
(*    wrdB t == builds a word from t : 'B_n                                   *)
(*                                                                            *)
(* We define all bit operations over this representation, and provide a       *)
(* bijection with the compuational representation.                            *)
(*                                                                            *)
(******************************************************************************)

(* Aux lemmas *)
Lemma val_tcast T n m (t : n.-tuple T) (eq_nm : n = m) :
  val (tcast eq_nm t) = val t.
Proof. by move: (eq_nm); rewrite /tcast -eq_nm => eq_nn; rewrite eq_axiomK. Qed.

(* Umm *)
Lemma nth_rot T x0 n i (s : seq T) (i_lt_s : i < size s) :
  nth x0 (rot n s) i = nth x0 s ((n + i) %% size s).
Proof.
rewrite nth_cat nth_drop; case: ltnP; rewrite size_drop => hs.
- admit.
rewrite nth_take.
Admitted.

Lemma nth_rotr T x0 n i (s : seq T) (i_lt_s : i < size s) :
  nth x0 (rotr n s) i = nth x0 s ((size s - n + i) %% size s).
Proof. by rewrite /rotr nth_rot. Qed.

(* We thank Cyril Cohen for the suggestion *)
Section BitWord.

Local Open Scope bits_scope.

Variable n : nat.

Definition word := {ffun 'I_n -> bool}.

Implicit Type (s : bitseq) (b : 'B_n) (w : word).

Definition seqw w        := val (fgraph w).
Definition wrds s : word := [ffun i => nth false s (val i)].

Lemma size_seqw w : size (seqw w) = n.
Proof. by rewrite size_tuple card_ord. Qed.

Lemma seqwK : cancel seqw wrds.
Proof. by move=> w; apply/ffunP=> i; rewrite /= !ffunE nth_fgraph_ord. Qed.

Lemma wrdbK : {in [pred x | size x == n], cancel wrds seqw}.
Proof.
move=> b /eqP hsz; apply: (@eq_from_nth _ false); first by rewrite size_seqw.
move=> i; rewrite size_seqw => hlt.
by rewrite (_ : i = (Ordinal hlt)) // nth_fgraph_ord ffunE.
Qed.

Definition bitw w        := tcast (@card_ord n) (fgraph w).
Definition wrdB t : word := [ffun i => tnth t i].

Lemma bitwE w : bitw w = seqw w :> bitseq.
Proof. by rewrite val_tcast. Qed.

(* The rest should follow from the cancellation lemmas *)
Lemma wrdtK : cancel wrdB bitw.
Proof.
move=> t; apply: eq_from_tnth => i.
by rewrite tcastE tnth_fgraph ffunE enum_val_ord cast_ordKV.
Qed.

End BitWord.

(* Properties for lifted operators: *)
Section WordLifted.
(* Rot/Shift: *)
End WordLifted.

Section WordIdx.

Variable n : nat.
Notation word := (word n.+1).

Implicit Type (s : bitseq) (b : 'B_n.+1) (w : word).

Definition rolw k w : word := [ffun i => w (i+k)%R].
Definition rorw k w : word := [ffun i => w (i-k)%R].

Lemma rolwP k w : bitw (rolw k w) = rolB k (bitw w).
Proof.
apply/eq_from_tnth=> i.
rewrite tcastE tnth_fgraph ffunE enum_val_ord !cast_ordKV.
rewrite /rolB (tnth_nth false) nth_rot ?size_tuple // val_tcast.
by rewrite (_ : (_ %% _) = (i+k)%R) ?nth_fgraph_ord // addnC.
Qed.

(*
Definition shlw k w : word :=
  [ffun i => if  <(i+k)%R]%R.

Definition shrw k w : word :=
  [ffun i => w (i-k)%R].
*)
End WordIdx.

(* Arithmetic *)

Section WordRing.

End WordRing.
