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

(* XXX: Move. Note this is "list order" *)
Lemma nth_rot T x0 n i (s : seq T) (i_lt_s : i < size s) (n_lt_s : n <= size s) :
  nth x0 (rot n s) i = nth x0 s ((n + i) %% size s).
Proof.
rewrite nth_cat nth_drop; case: ltnP; rewrite size_drop ?ltn_subRL => hs.
  by rewrite modn_small.
(* Second case, we are taking after the drop *)
rewrite nth_take.
Admitted.

Lemma nth_rotr T x0 n i (s : seq T) (i_lt_s : i < size s) (n_lt_s : n <= size s) :
  nth x0 (rotr n s) i = nth x0 s ((size s - n + i) %% size s).
Proof. by rewrite /rot nth_rot // leq_subr. Qed.

Lemma tnth_rot T k n (n_lt_s : n <= k.+1) (t : k.+1.-tuple T) (i : 'I_k.+1):
  tnth [tuple of rot n t] i = tnth t (inZp n + i)%R.
Proof.
set x0 := tnth t ord0.
by rewrite !(tnth_nth x0) nth_rot ?size_tuple // /inZp /= modnDml.
Qed.

Lemma nth_shls x0 n s i : nth x0 (shls s n) i =
                          if n <= i then nth x0 s (i - n) else false.
Proof.
rewrite /shls nth_cat size_nseq nth_nseq.
set k := size s.
Admitted.


Definition word n := {ffun 'I_n -> bool}.

Notation "''W_' n" := (word n)
  (at level 8, n at level 2, format "''W_' n").

(* We thank Cyril Cohen for the suggestion *)
Section BitWord.

Local Open Scope bits_scope.

Variable n : nat.
Notation word := (word n).

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
Lemma wrdBK : cancel wrdB bitw.
Proof.
move=> t; apply: eq_from_tnth => i.
by rewrite tcastE tnth_fgraph ffunE enum_val_ord cast_ordKV.
Qed.

Lemma wordP w : tnth (bitw w) =1 w.
Proof.
by move=> i; rewrite /bitw tcastE tnth_fgraph enum_val_ord cast_ordKV.
Qed.

End BitWord.

(* Properties for lifted operators: *)
Section WordLifted.

Variable k : nat.
Notation word := (word k).
Implicit Type (s : bitseq) (b : 'B_k) (w : word).

Definition orw  w1 w2 := [ffun i => w1 i || w2 i].
Definition andw w1 w2 := [ffun i => w1 i && w2 i].
Definition negw w     := [ffun i => ~~ w i].

End WordLifted.

Section WordIdx.

Variable k : nat.
Notation word := (word k.+1).

Local Open Scope ring_scope.

Implicit Type (s : bitseq) (b : 'B_k.+1) (w : word).

(* Rotation *)
Definition rolw k w : word := [ffun i => w (i+k)].
Definition rorw k w : word := [ffun i => w (i-k)].

Lemma rolwP n w : bitw (rolw n w) = rolB n (bitw w).
Proof.
apply/eq_from_tnth=> i.
rewrite tcastE tnth_fgraph ffunE enum_val_ord !cast_ordKV.
rewrite /rolB (tnth_nth false) nth_rotr ?size_tuple //.
  rewrite val_tcast (_ : (_ %% _) = (i+n)) ?nth_fgraph_ord //.
  admit.
by rewrite ltnW.
Admitted.

(******************************************************************************)
(* Word Shift                                                                 *)
(******************************************************************************)

Definition shlw (n : 'I_k.+1) w : word :=
  [ffun i : 'I_k.+1 => (n <= i)%N && w (i-n) ].

Definition shrw (n : 'I_k.+1) w : word :=
  [ffun i : 'I_k.+1 => (i < k.+1 - n)%N && w (i+n) ].

Lemma shlwP n w : bitw (shlw n w) = shlB (bitw w) n.
Proof.
apply/eq_from_tnth=> i; rewrite tcastE tnth_fgraph ffunE enum_val_ord cast_ordKV.
rewrite tnth_shlB wordP; case: leqP => //= h_leq.
(* Boring arithmetic, we may streamline this *)
suff -> : insubd i (i - n)%N = i - n by [].
apply/val_inj; rewrite val_insubd /=; set u := k.+1.
have in_ltn_u : (i - n < u)%N.
  by rewrite (leq_ltn_trans (leq_subr _ _)).
rewrite in_ltn_u !modnDmr addnBA 1?ltnW //.
by rewrite  addnC -addnBA // modnDl modn_small.
Qed.

Lemma shrwP n w : bitw (shrw n w) = shrB (bitw w) n.
Proof.
apply/eq_from_tnth=> i; rewrite tcastE tnth_fgraph ffunE enum_val_ord cast_ordKV.
rewrite tnth_shrB wordP; case: ltnP => //= h_leq.
(* Boring arithmetic, we may streamline this *)
suff -> : insubd i (i + n)%N = i + n by [].
apply/val_inj; rewrite val_insubd /=; set u := k.+1 in h_leq *.
by rewrite ltn_subRL addnC in h_leq; rewrite h_leq modn_small.
Qed.

End WordIdx.

(* Arithmetic *)

Section WordRing.

End WordRing.
