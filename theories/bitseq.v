(******************************************************************************)
(* A bit library for Coq: bit sequences.                                      *)
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
Require Import choice fintype finset tuple finfun.
From mathcomp
Require Import bigop ssralg ssrnum fingroup perm finalg zmodp ssrint.

(******************************************************************************)
(*                                                                            *)
(* We develop the theory of bit sequences, AKA, words. This file deals with   *)
(* the computable part of the theory, based on the standard type:             *)
(*                                                                            *)
(*      bitseq == seq bool                                                    *)
(*                                                                            *)
(* We define bit operations over this representation, using a zip with        *)
(* default operation that respects most algebraic properties without          *)
(* requiring arguments of the same length.                                    *)
(*                                                                            *)
(* In the second part of the file, we provide bit sequence arithmetic.        *)
(*                                                                            *)
(* Bitseq are naturally viewed as tuples:                                     *)
(*                                                                            *)
(*        'B_n == type of sequences of n bits, note that for many             *)
(*                constructions you need to use 'B_n.+1                       *)
(*                                                                            *)
(* In all cases, the tuple operations are based on their bitseq counterpart.  *)
(*                                                                            *)
(*  ** Bit Operations:                                                        *)
(*                                                                            *)
(*  Quite a few operations are already provided by the standard seq library,  *)
(*  including `setb` and `getb` which are just aliaes for `nth`, `set_nth`:   *)
(*                                                                            *)
(*     sets bs i b == sets bit i in bs to b                                   *)
(*           bs`_i == gets bit i in bs (or false if out of range)             *)
(*                                                                            *)
(*  We additionally provide:                                                  *)
(*                                                                            *)
(*  ** Unsigned modular arithmetic.                                           *)
(*                                                                            *)
(*  We provide conversion functions to/from bitseqs to natural numbers.       *)
(*                                                                            *)
(*     bito o  == k.-bit sequence for ordinal o : 'I_(2^k)                    *)
(*     ordB bs == 2^k ordinal for k.-bit sequence bs                          *)
(*                                                                            *)
(*  Note that we actually use 'Z_2^k to inherit algebraic instances, so be    *)
(*  aware of the implications.                                                *)
(*                                                                            *)
(*  Note the choice to reject producing 0-size ordinals.                      *)
(*                                                                            *)
(*  'B_n/'B_n.+1 inherit the zmodType/ringType structures.                    *)
(*                                                                            *)
(*                                                                            *)
(*  ** Signed modular arithmetic.                                             *)
(*                                                                            *)
(*                                                                            *)
(* This file uses the following suffix conventions:                           *)
(*   s  - operations on bitseq                                                *)
(*   B  - operations on 'B_n                                                  *)
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

(************************************************************************)
(* Main notations and basic definitions                                 *)
(************************************************************************)

Delimit Scope bits_scope with B.
Local Open Scope bits_scope.

Notation "''0_' n" := (nseq n false)
  (at level 8, n at level 2, format "''0_' n") : bits_scope.

Notation "''1_' n" := (nseq n true)
  (at level 8, n at level 2, format "''1_' n") : bits_scope.

Definition sets bs i b := set_nth false bs i b.

Notation "bs `_ i" := (nth false bs i) : bits_scope.

(* We define some notations over sets and tuples *)
Notation "[ 'bits' 'of' s ]" := (tuple (fun sP => @Tuple _ bool s sP))
  (at level 0, format "[ 'bits'  'of'  s ]") : bits_scope.

(* Bit vectors *)
Notation "''B_' n" := (n.-tuple bool)
  (at level 8, n at level 2, format "''B_' n").

Notation "''0'" := [bits of nseq _ false] (at level 8) : bits_scope.

Notation "''1'" := [bits of nseq _ true] (at level 8) : bits_scope.

Section AuxTheory.

Lemma tnth_nseq m T (x : T) i : tnth [tuple of nseq m x] i = x.
Proof. by rewrite (tnth_nth x) nth_nseq ltn_ord. Qed.

End AuxTheory.

(************************************************************************)
(* Zip with a default. It is worth defining our own version of zip
 * such that preserves the length of the greatest list. An
 * alternative is using the regular list + padding but we'd like to
 * have a nice computational interpretation.
 *)
Section ZipD.

Variables S T : Type.
Variables (sd : S) (td : T).

Fixpoint zipd (s : seq S) (t : seq T) {struct t} :=
  match s, t with
  | x :: s', y :: t' => (x, y)  :: zipd s' t'
  | s, [::]          => zip s (nseq (size s) td)
  | [::], t          => zip (nseq (size t) sd) t
  end.

Lemma size_zipd s t : size (zipd s t) = maxn (size s) (size t).
Proof.
elim: s t => [|x s IHs] [|y t] //=; last by rewrite IHs maxnSS.
  by rewrite size_zip max0n size_nseq minnn.
by rewrite size_zip maxn0 size_nseq minnn.
Qed.

Lemma zipd0 s : zipd s [::] = zip s (nseq (size s) td).
Proof. by case: s. Qed.

Lemma zip0d t : zipd [::] t = zip (nseq (size t) sd) t.
Proof. by case: t. Qed.

Lemma zipd_zip s t : size s = size t ->
                     zipd s t = zip s t.
Proof. by elim: s t => [|x s IHs] [|y t] //= [/IHs]->. Qed.

Lemma nth_zipd s t i :
   nth (sd, td) (zipd s t) i = (nth sd s i, nth td t i).
Proof.
elim: i s t => [|i IHi] [|x s] [|y t] //=.
  by rewrite nth_zip ?size_nseq ?nth_nseq //; case: ifP.
by rewrite nth_zip ?size_nseq ?nth_nseq //; case: ifP.
Qed.

End ZipD.

(******************************************************************************)
(* Lifting of a binary operator throu zipd                                    *)
(******************************************************************************)
Section LiftZ.

Variable (T : Type) (d : T) (op : T -> T -> T).
Implicit Types (s t : seq T).

Definition liftz s t :=
  [seq op x.1 x.2 | x <- zipd d d s t].

Lemma liftz_cons x y s t :
  liftz (x :: s) (y :: t) = (op x y) :: liftz s t.
Proof. by []. Qed.

Lemma liftz_nil : liftz [::] [::] = [::].
Proof. by []. Qed.

Lemma lift_nil_cons y t :
  liftz [::] (y :: t) = (op d y) :: liftz [::] t.
Proof. by case: t. Qed.

Lemma lift_cons_nil x s :
  liftz (x :: s) [::] = (op x d) :: liftz s [::].
Proof. by case: s. Qed.

Definition liftE := (lift_nil_cons, lift_cons_nil, liftz_cons, liftz_nil).

Lemma lift0z (hIl : left_id d op) : left_id [::] liftz.
Proof. by elim=> [|x s IHs]; rewrite // !liftE IHs hIl. Qed.

Lemma liftz0 (hIr : right_id d op) : right_id [::] liftz.
Proof. by elim=> [|x s IHs]; rewrite // !liftE IHs hIr. Qed.

Lemma size_liftz s t : size (liftz s t) = maxn (size s) (size t).
Proof.
elim: s t => [|x s ihs] [|y t] //=; last by rewrite ihs maxnSS.
  by rewrite max0n size_map size_zip size_nseq minnn.
by rewrite maxn0 size_map size_zip size_nseq minnn.
Qed.

Lemma nth_liftz d0 s t i (i_le_s : i < size s) (i_le_t : i < size t) :
  nth d0 (liftz s t) i = op (nth d0 s i) (nth d0 t i).
Proof.
rewrite (nth_map (d0,d0)) ?size_zipd ?leq_max ?i_le_s //.
rewrite (set_nth_default (d,d) (d0,d0)) ?nth_zipd //.
  by rewrite !(set_nth_default d0 d).
by rewrite size_zipd leq_max i_le_s.
Qed.

(* XXX: Weird version *)
Lemma nth_liftz_idem s t i (op_id : idempotent op) :
  nth d (liftz s t) i = op (nth d s i) (nth d t i).
Proof.
case: (i < maxn (size s) (size t)) / leqP.
  rewrite geq_max; case/andP=> hs ht; rewrite !nth_default //.
  by rewrite size_liftz geq_max hs.
rewrite leq_max; case/orP=> hs.
  by rewrite !(nth_map (d,d) _) /= ?nth_zipd ?size_zipd ?leq_max ?hs.
by rewrite !(nth_map (d,d) _) /= ?nth_zipd ?size_zipd ?leq_max ?hs ?orbT.
Qed.

Lemma liftz_tupleP k (s t : k.-tuple T) : size (liftz s t) == k.
Proof. by rewrite size_liftz !size_tuple maxnn. Qed.

(* XXX: This can be improved *)
Lemma liftzC (hC : commutative op) : commutative liftz.
Proof.
elim=> [|x s IHs] [|y t]; rewrite ?liftE 1?hC ?IHs //.
by congr cons; elim: t => //= z t IHt; rewrite !liftE hC IHt.
Qed.

Lemma lift0z' (hIl : left_id d op) k :
  {in [pred s | k <= size s], left_id (nseq k d) liftz}.
Proof.
move=> s; elim: s k => [|x s IHs] [|k]; rewrite !inE !liftE ?hIl //.
  by rewrite (IHs 0).
by move/IHs->.
Qed.

Lemma liftz0' (hIl : right_id d op) k :
  {in [pred s | k <= size s], right_id (nseq k d) liftz}.
Proof.
move=> s; elim: s k => [|x s IHs] [|k]; rewrite !inE !liftE ?hIl //.
  by rewrite (IHs 0).
by move/IHs->.
Qed.

Definition liftA := (lift0z, liftz0).

Lemma liftzA (hIl : left_id  d op) (hIr : right_id d op) (hA : associative op) :
  associative liftz.
Proof.
by elim=> [|x s IHs] [|y t] [|z u]; rewrite ?(liftE, liftA, hIl, hIr) 1?hA ?IHs.
Qed.

End LiftZ.

Canonical liftz_tuple T d op k (s t : k.-tuple T) := Tuple (liftz_tupleP d op s t).

(* Tuple theory *)
Section LiftzTuple.

Lemma tnth_liftz T d op k (s t : k.-tuple T) i :
  tnth [tuple of liftz d op s t] i = op (tnth s i) (tnth t i).
Proof. by rewrite !(tnth_nth d) nth_liftz ?size_tuple. Qed.

End LiftzTuple.

(******************************************************************************)
(* Bit operations                                                             *)
(******************************************************************************)
Section BitOps.

Variable k : nat.
Implicit Types (i : nat) (j : 'I_k) (bs : bitseq) (bv : 'B_k) (b : bool).

(* Untyped versions *)

Lemma gets0 i : '0_k`_i = false.
Proof. by elim: i k => [|i IHi] [|k'] //=. Qed.

Lemma sets_tupleP bv j b :
  size (sets bv j b) == k.
Proof. by rewrite size_set_nth size_tuple; apply/eqP/maxn_idPr. Qed.

(* XXX: Clash with bitset:setB *)
Canonical setB bv j b := Tuple (sets_tupleP bv j b).

(* Size-preserving version *)
Definition setls bs i b :=
  if i < size bs then set_nth false bs i b else bs.

Lemma setls_tupleP bv i b : size (setls bv i b) == k.
Proof.
by rewrite fun_if size_set_nth size_tuple; case: ifP => // /maxn_idPr ->.
Qed.

Canonical setlB bv j b := Tuple (setls_tupleP bv j b).

(* Properties of bget bset wrt to bit operations *)
(* Bigops? *)

Definition ors  := liftz false orb.
Definition ands := liftz true andb.
Definition xors := liftz false xorb.

Lemma ors_cons b1 b2 bs1 bs2 : ors (b1 :: bs1) (b2 :: bs2) = b1 || b2 :: ors bs1 bs2.
Proof. by []. Qed.

Lemma or0s : left_id [::] ors.
Proof. exact: lift0z. Qed.

Lemma ors0 : right_id [::] ors.
Proof. exact: (liftz0 orbF). Qed.

Lemma or0s' : {in [pred s | k <= size s], left_id '0_k ors}.
Proof. exact: lift0z'. Qed.

Lemma ors0' : {in [pred s | k <= size s], right_id '0_k ors}.
Proof. exact: (liftz0' orbF). Qed.

Lemma orsC : commutative ors.
Proof. exact: (liftzC _ orbC). Qed.

Lemma orsA : associative ors.
Proof. exact: (liftzA orFb orbF orbA). Qed.

Lemma ands_cons b1 b2 bs1 bs2 : ands (b1 :: bs1) (b2 :: bs2) = b1 && b2 :: ands bs1 bs2.
Proof. by []. Qed.

Lemma andsC : commutative ands.
Proof. exact: (liftzC _ andbC). Qed.

Lemma andsA : associative ands.
Proof. exact: (liftzA andTb andbT andbA). Qed.

Lemma and1s : left_id [::] ands.
Proof. exact: (lift0z andTb). Qed.

Lemma ands1 : right_id [::] ands.
Proof. exact: (liftz0 andbT). Qed.

Section OpsTup.

Variable k' : nat.
Implicit Type (t : 'B_k').

Definition orB  t1 t2 := [bits of ors  t1 t2].
Definition andB t1 t2 := [bits of ands t1 t2].
Definition xorB t1 t2 := [bits of xors t1 t2].

Lemma and0B t : andB '0 t = '0.
Proof.
(* XXX : use right_zero *)
apply: val_inj; case: t => [t /= /eqP ht].
by elim: t k' ht => [|b t iht] [|k0] //= [/iht]{2}<-.
Qed.

Lemma andBC : commutative andB.
Proof. by move=> t1 t2; apply/val_inj/andsC. Qed.

End OpsTup.

Lemma or0B bv : orB '0 bv = bv.
Proof. by apply: val_inj; rewrite /= or0s' ?inE ?size_tuple. Qed.

Lemma andB_cons b1 b2 (t1 t2 : 'B_k) :
  andB [bits of b1 :: t1] [bits of b2 :: t2] =
  [bits of b1 && b2 :: andB t1 t2].
Proof. exact: val_inj. Qed.

(* Aliases for rotation, note the discrepancy in direction *)
Definition rors := @rot bool.
Definition rols := @rotr bool.

Lemma rolK n : cancel (rols n) (rors n).
Proof. exact: rotrK. Qed.

Lemma rorK n : cancel (rors n) (rols n).
Proof. exact: rotK. Qed.

Definition rolB n (t : 'B_k) := [bits of rols n t].
Definition rorB n (t : 'B_k) := [bits of rors n t].

(* Shift to left/right *)
Definition shls s n := '0_(minn (size s) n) ++ take (size s - n) s.
Definition shrs s n := drop n s ++ '0_(minn (size s) n).

(* XXX *)
Lemma size_shls n s : size (shls s n) = size s.
Proof. by rewrite size_cat size_nseq size_takel ?minnE ?subnK ?leq_subr. Qed.

Lemma size_shrs n s : size (shrs s n) = size s.
Proof. by rewrite size_cat size_nseq size_drop minnE subnKC ?leq_subr. Qed.

Lemma shls0 s : shls s 0 = s.
Proof. by rewrite /shls minn0 subn0 take_oversize. Qed.

(* Lemma take_nseq T n m (x : T) : take n (nseq m x) = nseq (minn n m) x. *)
(* Proof. by elim: n m => [|n ihn] [|m]; rewrite ?minnSS //= ihn. Qed. *)

(* Example lemmas from the old lib: compare *)
Lemma shls_overflow n s (hs : size s <= n) : shls s n = '0_(size s).
Proof. by rewrite /shls (eqP hs) (minn_idPl hs) take0 cats0. Qed.

Lemma shrs_overflow n s (hs : size s <= n) : shrs s n = '0_(size s).
Proof.
Proof. by rewrite /shrs (minn_idPl hs) drop_oversize. Qed.

Lemma shls_tupleP n (t : 'B_k) : size (shls t n) == k.
Proof. by rewrite size_shls size_tuple. Qed.

Lemma shrs_tupleP n (t : 'B_k) : size (shrs t n) == k.
Proof. by rewrite size_shrs size_tuple. Qed.

Canonical shlB (t : 'B_k) n := Tuple (shls_tupleP n t).
Canonical shrB (t : 'B_k) n := Tuple (shrs_tupleP n t).

(* Inversion of bits *)
Definition negs s := [seq negb b | b <- s].
Definition negB (t : 'B_k) := [bits of negs t].

(* adder : c b1 b2 -> carry * res *)
Definition adder carry b1 b2 :=
  let: r := carry + b1 + b2 in
  (r > 1, r %% 2 != 0).

Lemma adderC c b1 b2 : adder c b1 b2 = adder c b2 b1.
Proof. by rewrite /adder addnAC. Qed.

(* XXX: Use a big_iter *)
Fixpoint adcB_p (carry : bool) (s : seq (bool * bool)) :=
  if s is (b1, b2) :: s then
    let: (nc, rb) := adder carry b1 b2 in
    let: (fc, rs) := adcB_p  nc s      in
    (fc, rb :: rs)
  else (carry, [::]).

Lemma size_adcB_p c s : size (adcB_p c s).2 = size s.
Proof.
elim: s c => //= -[r1 r2] l ihl c; rewrite -(ihl (adder c r1 r2).1).
by case: adcB_p.
Qed.

(* XXX: refine into carry and res... *)
Definition adcB c s1 s2 := adcB_p c (zipd false false s1 s2).

Lemma adcB_cons c x s y t :
 adcB c (x :: s) (y :: t) =
 let: (nc, rb) := adder c  x y in
 let: (fc, rs) := adcB  nc s t in
 (fc, rb :: rs).
Proof. by []. Qed.

Lemma size_adcB c s1 s2 : size (adcB c s1 s2).2 = maxn (size s1) (size s2).
Proof. by rewrite /adcB size_adcB_p size_zipd. Qed.

Compute (adcB true [:: true; false; true] [:: true; true; false]).

Lemma adc0BC c s : adcB c [::] s = adcB c s [::].
Proof.
rewrite /adcB zipd0 zip0d; elim: s c => //= b l ihl c.
by rewrite ihl addnAC.
Qed.

Lemma adcBC c : commutative (adcB c).
Proof.
move=> s t; elim: s t c => [|x s ihs] [|y t] c; rewrite ?zipd0 ?zip0d ?adc0BC //.
by rewrite !adcB_cons adderC /= ihs.
Qed.

Definition sbbB borrow s1 s2 :=
  let: (carry, res) := adcB (~~ borrow) s1 (negB s2) in
  (~~carry, res).

(* Old: "Absurdily complicated"  EG: Not sure this makes sense *)
(* Lemma sbb0B_carry s : fst (sbbB false [::] s) = (s != '0_(size s)). *)
(* Proof. *)
(* elim: s => //= b l ihl; rewrite /sbbB /adcB /=. *)
(* rewrite !addn0. *)
(* Admitted. *)

(* XXX: rcons *)

(* Definition adcB (carry : bool) s1 s2 := *)
(*   foldl (fun carry (e1, e2) => ) (carry, []) *)
(*         (zipd false false s1 s2). *)

(*
Definition sbbB {n} borrow (arg1 arg2: BITS n) :=
  let (carry, res) := eta_expand (adcB (~~borrow) arg1 (invB arg2)) in
  (~~carry, res).

(* Old: "Absurdily complicated" *)
Lemma sbb0B_carry n (p: BITS n.+1) : fst (sbbB false #0 p) = (p != #0).
*)

End BitOps.

(* May need improvement *)
Canonical ors_monoid := Monoid.Law orsA or0s ors0.
Canonical ors_com    := Monoid.ComLaw orsC.

Canonical ands_monoid := Monoid.Law andsA and1s ands1.
Canonical ands_com    := Monoid.ComLaw andsC.

(* Unsigned modular arithmetic *)
Section Unsigned.

Implicit Types (bs : bitseq).

Fixpoint nats_rec bs : nat :=
  if bs is b :: bs then b + (nats_rec bs).*2 else 0.

Definition nats := nosimpl nats_rec.

Lemma nats_cons b bs : nats [:: b & bs] = b + (nats bs).*2.
Proof. by []. Qed.

(* bitsequence of a nat *)
Fixpoint bitn_rec n k : bitseq :=
  if n is n.+1
  then [:: odd k & bitn_rec n k./2]
  else [::].

Definition bitn := nosimpl bitn_rec.

Eval compute in bitn 10 00.
Eval compute in nats [:: false; true; false; false; false; false; false;
           false; false; false].

Lemma bitn_cons n k : bitn n.+1 k = [:: odd k & bitn n k./2].
Proof. by []. Qed.

(* We can fix the cancellation using tuples and ordinals *)
Lemma size_bitn n k : size (bitn n k) = n.
Proof. by elim: n k => //= n ihn k; rewrite (ihn k./2). Qed.

Lemma size_bitnP n k : size (bitn n k) == n.
Proof. exact/eqP/size_bitn. Qed.

Canonical bitn_tuple n k := Tuple (size_bitnP n k).

Lemma natsK : forall m, bitn (size m) (nats m) = m.
Proof.
elim=> // -[] /= m ihm.
  by rewrite !bitn_cons !nats_cons /= odd_double uphalf_double ihm.
by rewrite bitn_cons odd_double (half_bit_double _ false) ihm.
Qed.

Lemma nats_inj k : {in [pred x | size x == k] &
                       [pred x | size x == k] , injective nats}.
Proof.
move=> x y /eqP sx /eqP sy /(congr1 (bitn (size x))).
by rewrite {2}sx -sy !natsK.
Qed.

(* We may want a truncation here. *)
Lemma bitnK k : {in [pred n | n < 2^k], cancel (bitn k) nats}.
Proof.
elim: k => //= [|k ihk] n hn; first by case: n hn.
rewrite nats_cons ihk ?odd_double_half //= inE -ltn_double.
suff U: (n./2).*2 <= n.
  by rewrite (leq_ltn_trans U); rewrite // -mul2n expnS in hn *.
by rewrite -{2}[n](odd_double_half n) leq_addl.
Qed.

Lemma bitn_inj k : {in [pred n | n < 2^k] &, injective (bitn k)}.
Proof. exact: can_in_inj (@bitnK k). Qed.

(* Bound on the integer we get... *)
Lemma nats_ltn m : nats m < 2^(size m).
Proof.
elim: m => //= b m ihm.
rewrite nats_cons expnS mul2n -!addnn addnA -addnS leq_add //.
by case: b; rewrite //= ltnW.
Qed.

(* Theory on nats *)
Lemma nats_zero j : nats '0_j = 0%N.
Proof. by elim: j => //= j ihj; rewrite nats_cons ihj. Qed.

Lemma bitn_zero j : '0_j = bitn j 0.
Proof.
apply: (@nats_inj j); rewrite ?inE ?size_nseq ?size_bitn ?eqxx //.
by rewrite nats_zero bitnK // inE expn_gt0.
Qed.

Lemma nats_one k : nats '1_k = 2^k - 1.
Proof.
elim: k => //= k ihk; rewrite nats_cons ihk.
by rewrite expnS -addnn !mulSn mul0n addn0 addnA subnKC ?addnBA ?expn_gt0.
Qed.

(* Development of the bounded operators *)
Section BitSizeCast.

Lemma cast_ord_P_proof k : 2^k = (2^k).-1.+1.
Proof. by rewrite prednK ?expn_gt0. Qed.

Definition cast_ord_P k (o : 'I_(2^k)) : 'I_(2^k).-1.+1 :=
  cast_ord (cast_ord_P_proof k) o.

(* Lemma nPPSS n : 2 <= n -> n.-2.+2 = n. *)
(* Proof. by case: n => // -[]. Qed. *)

Lemma expnS_ge2 n : 2 <= 2 ^ n.+1.
Proof. by elim: n => // n ihn; rewrite expnS mul2n -addnn ltn_addl. Qed.

(* Lemma cast_ord_PP_proof k : 2^k.+1 = (2^k.+1).-2.+2. *)
(* Proof. by rewrite nPPSS ?expkS_ge2. Qed. *)

(* Definition cast_ord_PP k (o : 'Z_(2^k.+1)) : 'I_(2^k.+1).-2.+2 := *)
(*   cast_ord (cast_ord_PP_proof k) o. *)

End BitSizeCast.

Section BitTuples.

Variable k : nat.
Implicit Types (bv : 'B_k).
Implicit Types (o  : 'I_(2^k).-1.+1).

(* Bits of an unsigned *)
Definition bito o     := [tuple of bitn k o].
(* Unsigned of bits *)
Lemma nats_ltn_exp bv : nats bv < 2^k.
Proof. by have := nats_ltn bv; rewrite size_tuple. Qed.

Definition ordB bv : 'I_(2^k).-1.+1 := cast_ord_P (Ordinal (nats_ltn_exp bv)).

Lemma ordBK : cancel ordB bito.
Proof. by move=> b; apply/val_inj; rewrite /= -{1}(size_tuple b) natsK. Qed.

Lemma bitoK : cancel bito ordB.
Proof.
by move=> b; apply/val_inj; rewrite /= bitnK // inE {2}cast_ord_P_proof.
Qed.

End BitTuples.

Prenex Implicits bitoK ordBK.

Section BitZModule.

Variable k : nat.

Definition B0          : 'B_k  := bito 0%R.
Definition addB (b1 b2 : 'B_k) := bito (ordB b1 + ordB b2)%R.
Definition oppB (b     : 'B_k) := bito (- ordB b)%R.

Import GRing.Theory.

Lemma add0B : left_id B0 addB.
Proof. by move=> x; apply/(can_inj ordBK); rewrite !bitoK add0r. Qed.

Lemma addNB : left_inverse B0 oppB addB.
Proof. by move=> x; apply/(can_inj ordBK); rewrite !bitoK addNr. Qed.

Lemma addBA : associative addB.
Proof.
by move=> x y z; apply/(can_inj ordBK); rewrite !bitoK addrA. Qed.

Lemma addBC : commutative addB.
Proof. by move=> x y; apply: val_inj; rewrite /= addnC. Qed.

Definition B_zmodMixin := ZmodMixin addBA addBC add0B addNB.
Canonical B_zmodType := Eval hnf in ZmodType ('B_k) B_zmodMixin.
Canonical B_finZmodType := Eval hnf in [finZmodType of 'B_k].
Canonical B_baseFinGroupType := Eval hnf in [baseFinGroupType of 'B_k for +%R].
Canonical B_finGroupType := Eval hnf in [finGroupType of 'B_k for +%R].

(* Start of theory: *)

Implicit Types (b : 'B_k).

Definition subB b1 b2 := (b1 - b2)%R.
Definition incB b := (b + [bits of bitn k 1])%R.
Definition decB b := (b - [bits of bitn k 1])%R.

(* XXX: Improve Vs *)
(* Lemma nats_one  k : nats '1_k = 2^k - 1. *)
Lemma one_def: '1 = decB '0.
Proof.
apply: (can_inj ordBK); apply: val_inj => /=.
rewrite prednK ?expn_gt0 // nats_zero nats_one add0n.
case: k => // j; rewrite !bitnK ?inE ?expnS_ge2 ?ltn_pmod ?expn_gt0 //.
by rewrite modn_mod modn_small // -addn1 subnK ?expn_gt0.
Qed.

End BitZModule.

Section SeqZModule.

Lemma size_zip_proof bs1 bs2 :
  size (zip bs1 bs2) == minn (size bs1) (size bs2).
Proof. by rewrite size_zip. Qed.

Definition lift_top bs1 bs2 :=
  ([tuple of unzip1 (Tuple (size_zip_proof bs1 bs2))],
   [tuple of unzip2 (Tuple (size_zip_proof bs1 bs2))]).

Definition adds bs1 bs2 : bitseq :=
  let t := lift_top bs1 bs2 in
  val (t.1 + t.2)%R.

(* Example of refinement *)
Definition R_seqtup k bs (bt : 'B_k) : Prop := bs = bt.
Local Notation "b ≈ f" := (R_seqtup b f) (at level 42).

Lemma adds_relE k bs1 bs2 (bv1 bv2 : 'B_k) :
  bs1 ≈ bv1 -> bs2 ≈ bv2 -> adds bs1 bs2 ≈ (bv1 + bv2)%R.
Proof.
move=> ->->.
by rewrite /adds /lift_top /= !size_tuple !minnn unzip1_zip ?unzip2_zip ?size_tuple.
Qed.

End SeqZModule.

Arguments B0 [k].

(*
Section BitRing.

Import GRing.Theory.

Variable k : nat.

Definition B1 : 'B_k.+1  := bito 1%R.

Definition mulB (b1 b2 : 'B_k.+1) := bito (ordB b1 * ordB b2)%R.

Lemma mulBA : associative mulB.
Proof. by move => x y z; apply/(can_inj ordBK); rewrite !bitoK mulrA. Qed.

Lemma mul1B : left_id B1 mulB.
Proof. by move => x; apply/(can_inj ordBK); rewrite !bitoK mul1r. Qed.

Lemma mulB1 : right_id B1 mulB.
Proof. by move => x; apply/(can_inj ordBK); rewrite !bitoK mulr1. Qed.

Lemma mulBDl : left_distributive mulB (@addB k.+1).
Proof. by move => x y z; apply/(can_inj ordBK); rewrite !bitoK mulrDl. Qed.

Lemma mulBDr : right_distributive mulB (@addB k.+1).
Proof. by move => x y z; apply/(can_inj ordBK); rewrite !bitoK mulrDr. Qed.

Lemma oneB_neq0 : (@B1 k.+1) != B0.
Proof. by []. Qed.


Definition B_ringMixin := RingMixin mulBA mul1B mulB1 mulBDl mulBDr oneB_neq0.
Canonical B_ringType := Eval hnf in RingType _ B_ringMixin.

Lemma mulBC : commutative mulB.
Proof. by move => x y; apply/(can_inj ordBK); rewrite !bitoK mulrC. Qed.

Canonical B_comRingType := Eval hnf in ComRingType _ mulBC.

End BitRing.
*)

End Unsigned.

Arguments B0 [_].
(* Arguments B1 [_]. *)

(* Lemma shlsS_bitn n i k : i < k -> shls (bitn k n) i.+1 = shls (bitn k n.*2) i. *)

Lemma take_belast T x (s : seq T) k (k_size : k <= size s) :
  take k (x :: s) = take k (belast x s).
Proof.
by elim: s x k k_size => [|y s ihs] x [|k] //= k_size; rewrite -take_cons ihs.
Qed.

Lemma bitn_one_def k : bitn k 1 = belast true '0_k.
Proof.
case: k => // k; rewrite bitn_cons /=; congr cons.
by elim: k => // k ihk; rewrite bitn_cons ihk.
Qed.

Lemma shlsS x s i : shls [:: x & s] i.+1 = [:: false & shls (belast x s) i].
Proof. by rewrite /shls minnSS size_belast subSS take_belast ?leq_subr. Qed.

Lemma shl_one k i : i < k -> shls (bitn k 1) i = sets '0_k i true.
Proof.
elim: i k => [|i ihi] [|k] // i_lt; first by rewrite shls0 bitn_cons bitn_zero.
by rewrite bitn_cons shlsS /= -bitn_zero -ihi ?bitn_one_def.
Qed.

(* Definition of get/test bit in terms of shifts *)
Lemma gets_def s i : let B n := bitn (size s) n in
  s`_i = (ands s (shls (B 1) i) != B 0).
Proof.
elim: s i => [|x s ihs] i //=.
  by rewrite nth_nil and1s /bitn /= /shls min0n.
Admitted.

(* Be a bit stringent as to be commutative *)
Lemma set_bitE bs n : sets bs n true = ors bs (sets [::] n true).
Proof.
(* XXX: clean up *)
elim: bs n => [|b bs ihb] [|n] //=; first by rewrite or0s.
  by rewrite ors_cons ors0 orbT.
by rewrite ors_cons orbF ihb /sets set_nth_nil.
Qed.

Lemma sets_def s i b : let B n := bitn (size s) n in
  sets s i b = if b then
                 ors  s (      shls (B 1) i)
               else
                 ands s (negs (shls (B 1) i)).
Proof.
case: b => //=.
  rewrite set_bitE; congr ors.
Search ors.
Admitted.

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
  (if sign s && (0 < size s) then Negz (nats (bnum s))
                             else Posz (nats (bnum s))).

Lemma intb_ltn m : `|intb m| < 2^(size m).-1 + (intb m \is Num.neg).
Proof.
case: m / lastP => // num sig.
rewrite /intb /sign /bnum !size_rcons //= andbT.
case: num => // [|s num] //=; case: sig => //=;
rewrite !last_rcons !belast_rcons /=.
  by rewrite -add1n addnC leq_add // nats_ltn.
by rewrite addn0 nats_ltn.
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
(* Definition sordB s := *)

End Defs.

End Signed.

(*

Definition bitU m1 m2 :=
  let lm := maxn (size m1) (size m2)    in
  let p1 := nseq (lm - (size m1)) false in
  let p2 := nseq (lm - (size m2)) false in
  let ms := zip  (m1 ++ p1) (m2 ++ p2)  in
  map (fun b => orb b.1 b.2) ms.

Lemma bitU_cons x y xl yl :
  bitU (x :: xl) (y :: yl) = [:: x || y & bitU xl yl].
Proof. by rewrite /bitU maxnSS. Qed.

(*
Lemma bit0U y yl : bitU [::] (y :: yl) = [:: y & bitU [::] yl].
Proof. by rewrite /bitU /= subn0 !max0n. Qed.

Lemma bitU0 x xl : bitU (x :: xl) [::] = [:: x & bitU xl [::] ].
Proof. by rewrite /bitU /= orbF subn0 !maxn0. Qed.
*)
(*
(* Lemma bitU0b y : bitU [::] y = y. *)
(* Proof. elim: y => //= y yl ihl; rewrite bit0U bitU0 ihl. Qed. *)
*)
Lemma bitUA : associative bitU.
Admitted.

Lemma bitUC : commutative bitU.
Admitted.

(* Oh so we indeed should pad! *)
Lemma bit0U k : left_id (nseq k false) bitU.
Admitted.

Lemma bitU0 k : right_id (nseq k false) bitU.
Admitted.

About Monoid.Law.
Canonical bitU_monoid k := Monoid.Law bitUA (bit0U k) (bitU0 k).
Canonical bitU_com    k := @Monoid.ComLaw _ _ (bitU_monoid k) bitUC.

(*
Proof.
elim=> [|x xl ihx] [|y yl]; rewrite ?bit0U ?bitU0 //.
+ by rewrite bit0C.
+ by rewrite bit0C.
by rewrite !bitU_cons orbC ihx.
Qed.

About Monoid.Law.

Lemma zip0s T U (s : seq U) : @zip T _ [::] s = [::].
Proof. by case: s. Qed.

Lemma zips0 T U (s : seq T) : @zip _ U s [::] = [::].
Proof. by case: s. Qed.

Lemma bitUA : associative bitU.
Proof.
elim=> [|x xl ihx] [|y yl] z //=.
+ rewrite bit0U.
 [|z zl] //=.
+ by rewrite /bitU zip0s.
+ by rewrite /bitU !zips0.
+ by rewrite !bitU_cons orbA ihx.
Qed.



Search _ zip.

Definition from_set' k s := \
*)
*)

(******************************************************************************)
(* Typeclass notations                                                        *)
(******************************************************************************)

From CoqEAL
     Require Import refinements.
Require Import notation.

Import Refinements.Op.
Import Logical.Op.

(* For bit sequences: *)

Global Instance eq_s   : eq_of bitseq   := fun x y => x == y.

Global Instance not_s  : not_of bitseq  := negs.
Global Instance or_s   : or_of bitseq   := ors.
Global Instance and_s  : and_of bitseq  := ands.
Global Instance xxor_s : xor_of bitseq  := xors.
Global Instance shr_s  : shr_of bitseq  := (fun x y => shrs x (nats y)).
Global Instance shl_s  : shl_of bitseq  := (fun x y => shls x (nats y)).

(* XXX: don't know the size of the words *)
Global Instance zero_s : zero_of bitseq . Admitted.
Global Instance one_s  : one_of bitseq  . Admitted.
Global Instance sub_s  : sub_of bitseq  . Admitted.

(* For bit vectors: *)

Global Instance eq_B  {n} : eq_of 'B_n := fun x y => x == y.

Global Instance not_B {n} : not_of 'B_n := @negB _.
Global Instance or_B  {n} : or_of  'B_n := @orB _.
Global Instance and_B {n} : and_of 'B_n := @andB _.
Global Instance xor_B {n} : xor_of 'B_n := @xorB _.
Global Instance shr_B {n} : shr_of 'B_n := (fun x y => @shrB _ x (nats y)).
Global Instance shl_B {n} : shl_of 'B_n := (fun x y => @shlB _ x (nats y)).

Global Instance zero_B {n} : zero_of 'B_n := [tuple of '0_n].
Global Instance one_B  {n} : one_of  'B_n := [tuple of bitn n 1].
Global Instance sub_B  {n} : sub_of 'B_n  := (@subB _).

