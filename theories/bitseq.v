(******************************************************************************)
(* A bit library for Coq: bit sequences.                                      *)
(******************************************************************************)
(*                                                                            *)
(* (c) 2016, MINES ParisTech                                                  *)
(*                                                                            *)
(* Written by Emilio J. Gallego Arias                                         *)
(*                                                                            *)
(* LICENSE: CECILL-B                                                          *)
(*                                                                            *)
(******************************************************************************)

From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.
From mathcomp
Require Import choice fintype finset tuple.
From mathcomp
Require Import bigop ssralg ssrnum fingroup perm finalg zmodp ssrint.

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
(* This file uses the following suffix conventions:                           *)
(*   B - operation on bitseq                                                  *)
(*   W - operation on k.-tuple bool                                           *)
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


Notation "''0_' n" := (nseq n false)
  (at level 8, n at level 2, format "''0_' n").

Notation "''1_' n" := (nseq n true)
  (at level 8, n at level 2, format "''1_' n").

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

Lemma nth_liftz s t i (op_id : idempotent op) :
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

Delimit Scope bits_scope with B.
Local Open Scope bits_scope.

(* We define some notations over sets and tuples *)
Notation "[ 'bits' 'of' s ]" := (tuple (fun sP => @Tuple _ bool s sP))
  (at level 0, format "[ 'bits'  'of'  s ]") : bits_scope.

Notation "s `_ i" := (nth false s i) : bits_scope.

(* Non-empty bit vectors *)
Notation "''B_' n" := (n.+1.-tuple bool)
  (at level 8, n at level 2, format "''B_' n").


(******************************************************************************)
(* The bit operations themselves                                              *)
(******************************************************************************)
Section BitOps.

Variable k : nat.
Implicit Types (i : nat) (j : 'I_k.+1) (bs : bitseq) (bv : 'B_k) (b : bool).

(* Untyped versions *)
Definition setb bs i b := set_nth false bs i b.
Definition getb bs i   := nth false bs i.

Lemma getbE bs i : getb bs i = bs`_i.
Proof. by []. Qed.

Lemma getb0 i : '0_k`_i = false.
Proof. by elim: i k => [|i IHi] [|k'] //=. Qed.

Lemma setb_tupleP bv j b :
  size (setb bv j b) == k.+1.
Proof. by rewrite size_set_nth size_tuple; apply/eqP/maxn_idPr. Qed.

Canonical setb_tuple bv j b := Tuple (setb_tupleP bv j b).

(* Size-preserving version *)
Definition setlb bs i b :=
  if i < size bs then set_nth false bs i b else bs.

Lemma setlb_tupleP bv i b : size (setlb bv i b) == k.+1.
Proof.
by rewrite fun_if size_set_nth size_tuple; case: ifP => // /maxn_idPr ->.
Qed.

Canonical setlB bv j b := Tuple (setlb_tupleP bv j b).

(* Properties of bget bset wrt to bit operations *)
(* Bigops? *)

Definition orB  := liftz false orb.
Definition andB := liftz true andb.

Lemma orB_cons b1 b2 bs1 bs2 : orB (b1 :: bs1) (b2 :: bs2) = b1 || b2 :: orB bs1 bs2.
Proof. by []. Qed.

Lemma or0B : left_id [::] orB.
Proof. exact: lift0z. Qed.

Lemma orB0 : right_id [::] orB.
Proof. exact: (liftz0 orbF). Qed.

Lemma or0B' : {in [pred s | k <= size s], left_id '0_k orB}.
Proof. exact: lift0z'. Qed.

Lemma orB0' : {in [pred s | k <= size s], right_id '0_k orB}.
Proof. exact: (liftz0' orbF). Qed.

Lemma orBC : commutative orB.
Proof. exact: (liftzC _ orbC). Qed.

Lemma orBA : associative orB.
Proof. exact: (liftzA orFb orbF orbA). Qed.

Lemma andBC : commutative andB.
Proof. exact: (liftzC _ andbC). Qed.

Lemma andBA : associative andB.
Proof. exact: (liftzA andTb andbT andbA). Qed.

Lemma and1B : left_id [::] andB.
Proof. exact: (lift0z andTb). Qed.

Lemma andB1 : right_id [::] andB.
Proof. exact: (liftz0 andbT). Qed.

End BitOps.

Canonical setb_tuple.

(* May need improvement *)
Canonical orB_monoid := Monoid.Law orBA or0B orB0.
Canonical orb_com    := Monoid.ComLaw orBC.

Canonical andB_monoid := Monoid.Law andBA and1B andB1.
Canonical andb_com    := Monoid.ComLaw andBC.

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

(* We may want a truncation here. *)
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
