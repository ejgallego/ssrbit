(******************************************************************************)
(* A bit library for Coq: sets encoded as bitseqs.                            *)
(******************************************************************************)
(*                                                                            *)
(* (c) 2016, MINES ParisTech                                                  *)
(*                                                                            *)
(* Written by Arthur Blot                                                     *)
(*            Pierre-Evariste Dagand                                          *)
(*            Emilio J. Gallego Arias                                         *)
(*                                                                            *)
(* LICENSE: CECILL-B                                                          *)
(*                                                                            *)
(******************************************************************************)
From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.
From mathcomp
Require Import choice fintype finset tuple path bigop.

(******************************************************************************)
(* Convenience Theory for extraction to ocaml integers                        *)
(******************************************************************************)
(*                                                                            *)
(* In particular we provide:                                                  *)
(*                                                                            *)
(* - An optimized "cardinality" count, based on population count.             *)
(* - An optimized "find first bit set", based on cardinality.                 *)
(*                                                                            *)
(* Moving the defined set/get operations could be considered.                 *)
(*                                                                            *)
(******************************************************************************)

Require Import bitseq notation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope bits_scope.

(* Optimized cardinality *)
Section Card.

Implicit Types (n k : nat).

(* ss is a partition of S then *)
(*  "cardb S = \sum(s <- ss) cardb s" *)

Definition bit_tmp k o := [tuple of bitn k o]. (* XXX: Emilio? *)

(* XXX: Factor out k of the recursion *)
Definition pop_table {n} k : seq 'B_n :=
  mkseq (fun i => bit_tmp n (count id (bitn k i))) (2^k).

Eval compute in (map val (@pop_table 4 2)).

Definition pop_elem n k (bs: 'B_n) i : 'B_n :=
  let x :=
      andB (shrB bs (i * k))
           (decB (shlB [bits of bitn n 1] k))
  in nth '0 (pop_table k) (nats x).

Eval compute in (val (@pop_elem 3 1 [tuple true; false; true] 0)).

Fixpoint popAux n k (bs: 'B_n) i : 'B_n :=
  match i with
  | 0     => '0
  | i'.+1 => addB (pop_elem k bs i') (popAux k bs i')
  end.

Definition cardinal {n} (k: nat)(bs: 'B_n): 'B_n :=
  popAux k bs (n %/ k).

Eval compute in (map val (@pop_table 4 2)).
Eval compute in (val (cardinal 1 [tuple true; false])).

Lemma cardinalP k (s : 'B_k) i (div_i: i %| k) (ltz_i: i > 0) :
  nats (cardinal i s) = count id s.
Proof.
Admitted.

End Card.

Section BitMin.

(* Set containing only the minimum *)
Definition keep_min n (bs: 'B_n) : 'B_n := andB bs (oppB bs).

(* Lemma keep_min_repr n (bs: 'B_n) x y : x \in setB bs -> *)
(*   setB (keep_min bs) = [set [arg min_(k < y in setB bs) k]]. *)

(* Emilio: we relate this to index instead *)
Lemma keep_minP n (bs: 'B_n) :
  keep_min bs = sets '0_n (index true bs) true :> bitseq.
(* XXX: maybe ripple_repr could be useful here, as neg is (inv + 1) *)
Admitted.

(* Value of the minimum (ie number of trailing zeroes) *)
Definition ntz n (k: nat) (bs: 'B_n) : 'B_n :=
  subB (bit_tmp n n) (cardinal k (orB bs (oppB bs))).

(* Lemma ntz_repr k (bs : 'B_k) i (div_i : i %| k) (ltz_i : i > 0) x y : x \in setB bs -> *)
(*     ntz i bs = bit_tmp k [arg min_(k < y in setB bs) k]. *)
(* Admitted. *)

End BitMin.
