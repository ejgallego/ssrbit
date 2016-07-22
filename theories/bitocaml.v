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
Require Import choice fintype finfun finset tuple path bigop.

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
Definition tobit k o := [bits of bitn k o].

Section Card.

Section CardDef.

Variable (n k : nat).

(* Cardinality table *)
Definition ctable  := seq 'B_n.
Definition ctableP (t : ctable) :=
  forall (bk : 'B_k), nth '0 t (nats bk) = tobit n (count id bk).

(** [pop_table] returns a k-list of words of size [n]
  * counting the numbers of bits.
  *)
Definition pop_table : seq 'B_n :=
  mkseq (fun i => tobit n (count id (bitn k i))) (2^k).

Lemma pop_table_size : size pop_table = 2^k.
Proof. by rewrite size_mkseq. Qed.

Lemma pop_tableP : ctableP pop_table.
Proof.
move=> bk; rewrite nth_mkseq -?{1}(size_tuple bk) ?natsK //.
by rewrite -{2}(size_tuple bk) nats_ltn.
Qed.

(* An alternative way is to define pop_table as a map: *)
Definition pop_table_fun {n} k : {ffun 'B_k -> 'B_n} :=
  [ffun bk => [bits of bitn n (count id (val bk))]].

Lemma pop_table_funP (bk : 'B_k) :
  pop_table_fun k bk = tobit n (count id bk).
Proof. by rewrite ffunE. Qed.

(** [pop_elem bs i] return the cardinality of the [i]-th part of
  * of [bs].
  *)
Definition pop_elem (bs: 'B_n) i : 'B_n :=
  let x := andB (shrB bs (i * k))
                (decB (shlB [bits of bitn n 1] k))
  in nth '0 pop_table (nats x).

(* Don't we want to shift here maybe ? *)
Definition card_rec (bs: 'B_n) := fix cr i : 'B_n :=
    match i with
    | 0     => '0
    | i'.+1 => addB (pop_elem bs i') (cr i')
    end.

(** [cardinal k bs] returns the number of bits set in [bs] to one using a
  * table of size [k]
  *)
Definition cardinal (bs: 'B_n) : 'B_n := card_rec bs (n %/ k).

End CardDef.

Eval compute in (map val (@pop_table 4 2)).
Eval compute in (val (@pop_elem 3 1 [tuple true; false; true] 0)).
Eval compute in (val (cardinal 2 [tuple true; true])).

Section CardTheory.

Lemma card_rec_cons n k i (bv : 'B_n) :
  card_rec k bv i.+1 =
  addB (pop_elem k bv i) (card_rec k bv i).
Proof. by []. Qed.

(* ss is a partition of S then *)
(*  "cardb S = \sum(s <- ss) cardb s" *)
Lemma cardinalE n k (bv : 'B_n) :
  nats (cardinal k bv) =
  \sum_(pbv <- reshape (nseq (n %/ k) k) bv) (nats pbv).
Proof.
rewrite /cardinal.
elim: (n %/ k) {1 2 3 6}n bv => [|nk ihnk] nv bv.
  by rewrite nats_zero big_nil.
rewrite card_rec_cons [reshape _ _]/= big_cons -ihnk.
Admitted.

(* Lemma cardinalE : \sum_(l reshape  *)

(* Lemma cardinalP k (s : 'B_k) i (* (div_i: i %| k) (ltz_i: i > 0) *) : *)
Lemma cardinalP k (s : 'B_k) i :
  nats (cardinal i s) = count id s.

Proof.
Admitted.

End CardTheory.
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

Definition bit_tmp n: nat -> 'B_n. Admitted.

(* Value of the minimum (ie number of trailing zeroes) *)
Definition ntz n (k: nat) (bs: 'B_n) : 'B_n :=
  subB (bit_tmp n n) (cardinal k (orB bs (oppB bs))).

(* Lemma ntz_repr k (bs : 'B_k) i (div_i : i %| k) (ltz_i : i > 0) x y : x \in setB bs -> *)
(*     ntz i bs = bit_tmp k [arg min_(k < y in setB bs) k]. *)
(* Admitted. *)

End BitMin.
