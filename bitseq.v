(******************************************************************************)
(* (c) Emilio J. Gallego Arias, MINES ParisTech                               *)
(******************************************************************************)
From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.
From mathcomp
Require Import choice fintype finset tuple.
From mathcomp
Require Import bigop ssralg ssrnum fingroup perm finalg zmodp ssrint.

(******************************************************************************)
(* A bit library for Coq: bit sequences.                                      *)
(******************************************************************************)
(*                                                                            *)
(* We only consider non-empty bit sequences:                                  *)
(*                                                                            *)
(*        'B_n == type of n.+1 bit sequences                                  *)
(*                                                                            *)
(* A bit sequence is just a list or tuple of booleans, and it inherits        *)
(* zmodType and ringType structures.                                          *)
(*                                                                            *)
(*  ** Bit Operations:                                                        *)
(*                                                                            *)
(*  Most operations are already in the seq library,                           *)
(*                                                                            *)
(*  We'd like to formalize at least the ocaml operations on bits              *)
(*                                                                            *)
(*     setb bs i b == sets bit i in bs to b                                   *)
(*           bs`_i == gets bit i in bs                                        *)
(*                                                                            *)
(*   these two are just aliases for nth set_nth                               *)
(*                                                                            *)
(*  ** Unsigned modular arithmetic.                                           *)
(*                                                                            *)
(*     bito o  == k.-bit sequence for ordinal o : 'I_(2^k)                    *)
(*     ordb bs == 2^k ordinal for k.-bit sequence bs                          *)
(*                                                                            *)
(*  ** Signed modular arithmetic.                                             *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(******************************************************************************)

(******************************************************************************)
(* Some references:                                                           *)
(*                                                                            *)
(* + https://coq.inria.fr/library/Coq.Bool.Bvector.html                       *)
(* + http://why3.lri.fr/stdlib-0.87.0/bv.html                                 *)
(* + https://github.com/artart78/coq-bitset                                   *)
(*                                                                            *)
(* The library was started after reading that last reference but it           *)
(* shares no code so far.                                                     *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope bits_scope with B.
Local Open Scope bits_scope.

(* We define some notations over sets and tuples *)
Notation "[ 'bits' 'of' s ]" := (tuple (fun sP => @Tuple _ bool s sP))
  (at level 0, format "[ 'bits'  'of'  s ]") : bits_scope.

Notation "s `_ i" := (seq.nth false s i) : bits_scope.

(* Non-empty bit vectors *)
Notation "''B_' n" := (n.+1.-tuple bool)
  (at level 8, n at level 2, format "''B_' n").

Section BitOps.

Variable k : nat.
Implicit Types (s : bitseq) (bv : 'B_k) (b : bool).

(* Size-preserving set *)
Definition setb s i b :=
  if i < size s then set_nth false s i b else s.

Lemma setb_tupleP bv i b : size (setb bv i b) == k.+1.
Proof.
rewrite fun_if size_set_nth size_tuple.
by case: ifP => // /maxn_idPr ->.
Qed.

Canonical setB bv i b := Tuple (setb_tupleP bv i b).

(* Properties of bget bset wrt to bit operations *)

(* Bigops? *)

End BitOps.

(* Unsigned modular arithmetic *)
Section Unsigned.

Implicit Types (bs : bitseq).

Fixpoint natb_rec bs : nat :=
  if bs is b :: bs then b + (natb_rec bs).*2 else 0.

Definition natb := nosimpl natb_rec.

Lemma natb_cons b bs : natb [:: b & bs] = b + (natb bs).*2.
Proof. by []. Qed.

(* bitsequence of a nat *)
Fixpoint bitn_rec n k : bitseq :=
  if n is n.+1
  then [:: odd k & bitn_rec n k./2]
  else [::].

Definition bitn := nosimpl bitn_rec.

Lemma bitn_cons n k : bitn n.+1 k = [:: odd k & bitn n k./2].
Proof. by []. Qed.

(* We can fix the cancellation using tuples and ordinals *)
Lemma size_bitn n k : size (bitn n k) = n.
Proof. by elim: n k => //= n ihn k; rewrite (ihn k./2). Qed.

Lemma size_bitnP n k : size (bitn n k) == n.
Proof. exact/eqP/size_bitn. Qed.

Canonical bitn_tuple n k := Tuple (size_bitnP n k).

Lemma natbK : forall m, bitn (size m) (natb m) = m.
Proof.
elim=> // -[] /= m ihm.
  by rewrite !bitn_cons !natb_cons /= odd_double uphalf_double ihm.
by rewrite bitn_cons odd_double (half_bit_double _ false) ihm.
Qed.

(* We need a truncation here. *)
Lemma bitnK n k : n < 2^k -> natb (bitn k n) = n.
Proof.
elim: k n => //= [|k ihk] n hn; first by case: n hn.
rewrite natb_cons ihk ?odd_double_half // -ltn_double.
suff U: (n./2).*2 <= n.
  by rewrite (leq_ltn_trans U); rewrite // -mul2n expnS in hn *.
by rewrite -{2}[n](odd_double_half n) leq_addl.
Qed.

(* Bound on the integer we get... *)
Lemma natb_ltn m : natb m < 2^(size m).
Proof.
elim: m => //= b m ihm.
rewrite natb_cons expnS mul2n -!addnn addnA -addnS leq_add //.
by case: b; rewrite //= ltnW.
Qed.

(* Development of the bounded operators *)
Section BitTuples.

(* We only consider non-empty bitseq to have the proper algebraic
   properties *)
Variable k : nat.
Implicit Types (bv : 'B_k).
Implicit Types (o  : 'Z_(2^k.+1)).

(* Bits of an unsigned *)
Definition bito o  := [tuple of bitn k.+1 o].

Lemma texp_fact bv : 2^size bv = 2^k.+1.
Proof. by rewrite size_tuple. Qed.

Lemma cast_zord_proof n m (i : 'Z_n) : n = m -> i < m.-2.+2.
Proof. by move <-. Qed.

Definition cast_zord n m eq_n_m i := Ordinal (@cast_zord_proof n m i eq_n_m).

Lemma nPPSS n : 2 <= n -> n.-2.+2 = n.
Proof. by case: n => // -[]. Qed.

Lemma expkS_ge2 n : 2 <= 2 ^ n.+1.
Proof. by elim: n => // n ihn; rewrite expnS mul2n -addnn ltn_addl. Qed.

Lemma ZeP n : (n < (Zp_trunc (2 ^ k.+1)).+2) = (n < 2 ^ k.+1).
Proof. by rewrite /Zp_trunc /= nPPSS ? expkS_ge2. Qed.

Lemma ltn_m_in_z bv : natb bv < (2^k.+1).-2.+2.
Proof. by rewrite ZeP -{2}(size_tuple bv) natb_ltn. Qed.

Definition ordb bv : 'Z_(2^k.+1) := Ordinal (ltn_m_in_z bv).

Definition ordb' bv : 'Z_(2^k.+1) := inZp (natb bv).

Lemma ordbK : cancel ordb bito.
Proof.
by move=> b; apply/val_inj; rewrite /= -{1}(size_tuple b); apply/natbK.
Qed.

Lemma ordbK' : cancel ordb' bito.
Proof.
move=> b. apply/val_inj; rewrite /= modn_small ?ltn_m_in_z //.
by rewrite /= -{1}(size_tuple b); apply/natbK.
Qed.

Lemma bitoK : cancel bito ordb.
Proof. by move=> o; apply/val_inj/bitnK; rewrite -ZeP. Qed.

Lemma bitoK' : cancel bito ordb'.
Proof. move=> o; apply/val_inj; rewrite /= modn_small ?ltn_m_in_z //.
by apply/bitnK; rewrite -ZeP.
Qed.

End BitTuples.

Prenex Implicits bitoK ordbK.

Section BitAlgebra.

Variable k : nat.

Definition B0          : 'B_k  := bito 0%R.
Definition addB (b1 b2 : 'B_k) := bito (ordb b1 + ordb b2)%R.
Definition oppB (b     : 'B_k) := bito (- ordb b)%R.

Import GRing.Theory.

Lemma add0B : left_id B0 addB.
Proof. by move => x; apply/(can_inj ordbK); rewrite !bitoK add0r. Qed.

Lemma addNB : left_inverse B0 oppB addB.
Proof. by move=> x; apply/(can_inj ordbK); rewrite !bitoK addNr. Qed.

Lemma addBA : associative addB.
Proof.
by move=> x y z; apply/(can_inj ordbK); rewrite !bitoK addrA. Qed.

Lemma addBC : commutative addB.
Proof. by move=> x y; apply: val_inj; rewrite /= addnC. Qed.

Definition B_zmodMixin := ZmodMixin addBA addBC add0B addNB.
Canonical B_zmodType := Eval hnf in ZmodType ('B_k) B_zmodMixin.
Canonical B_finZmodType := Eval hnf in [finZmodType of 'B_k].
Canonical B_baseFinGroupType := Eval hnf in [baseFinGroupType of 'B_k for +%R].
Canonical B_finGroupType := Eval hnf in [finGroupType of 'B_k for +%R].

Definition mulB k (b1 b2 : 'B_k) := bito (ordb b1 * ordb b2)%R.

End BitAlgebra.
End Unsigned.

Section Examples.

Eval compute in val (addB [tuple true; false; true] [tuple false; true; true]).
Eval compute in val (oppB [tuple true; false; false]).
Eval compute in val (addB [tuple true; false; true] (oppB [tuple true; false; false])).
Eval compute in val ([tuple true; false; true] + [tuple false; true; true])%R.

Eval vm_compute in val ([tuple true;  false; true; true; false; true; false; true; false; false; false; true; false; true]
                      + [tuple false; true;  true; true; true;  true; true;  true; true;  true;  true;  true; true;  true])%R.

End Examples.

Section Signed.

Implicit Types (s : bitseq).

(* Bits to/from integers ! *)
Definition sign s := last   (head false s) (behead s).
Definition bnum s := belast (head false s) (behead s).

Definition intb s :=
  (if sign s && (0 < size s) then Negz (natb (bnum s))
                             else Posz (natb (bnum s))).

Lemma intb_ltn m : `|intb m| < 2^(size m).-1 + (intb m \is Num.neg).
Proof.
case: m / lastP => // num sig.
rewrite /intb /sign /bnum !size_rcons //= andbT.
case: num => // [|s num] //=; case: sig => //=;
rewrite !last_rcons !belast_rcons /=.
  by rewrite -add1n addnC leq_add // natb_ltn.
by rewrite addn0 natb_ltn.
Qed.

Definition bitz z k := match z with
| Posz n => rcons (bitn k n) false
| Negz n => rcons (bitn k n) true
end.

Lemma size_bitz z k : size (bitz z k) = k.+1.
Proof. by case: z => n; rewrite /= size_rcons size_bitn. Qed.

Section Defs.
Variable k : nat.

(* TODO: pick a definition of modular signed arithmetic. *)
(* Definition sordb s := *)

End Defs.

End Signed.


