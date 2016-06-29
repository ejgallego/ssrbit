From Coq
     Require Import ZArith.ZArith.
From mathcomp
     Require Import ssreflect ssrbool eqtype ssrnat seq fintype ssrfun zmodp tuple.
From CoqEAL
     Require Import hrel param refinements.
Require Import bitseq notation.

Require Import ExtrOcamlBasic.

Import Refinements.Op.
Import Logical.Op.

(** * An axiomatization of OCaml native integers *)

(** This module should not be used directly. *)
Module NativeInt.

(** We assume that we are running on a 64 bit machine. *)

Axiom Int: Type.
Axiom eq: Int -> Int -> bool.

Axiom zero : Int.
Axiom one : Int.
Axiom neg: Int -> Int.
Axiom add: Int -> Int -> Int.
Axiom sub: Int -> Int -> Int.
Axiom mul: Int -> Int -> Int.

Axiom lnot: Int -> Int.
Axiom lor: Int -> Int -> Int.
Axiom land: Int -> Int -> Int.
Axiom lxor: Int -> Int -> Int.
Axiom lsr: Int -> Int -> Int.
Axiom lsl: Int -> Int -> Int.

Extract Inlined Constant Int => "int".
Extract Inlined Constant eq => "(=)".
Extract Inlined Constant zero => "0".
Extract Inlined Constant one => "1".
Extract Inlined Constant lor => "(lor)".
Extract Inlined Constant land => "(land)".
Extract Inlined Constant lsr => "(lsr)".
Extract Inlined Constant lxor => "(lxor)".

(** One must be careful to re-normalize the following operations when
using them at smaller wordsize: *)

Extract Inlined Constant lsl => "(lsl)".
Extract Inlined Constant neg => "(fun x -> -x)".
Extract Inlined Constant lnot => "lnot".
Extract Inlined Constant add => "(+)".
Extract Inlined Constant sub => "(-)".
Extract Inlined Constant mul => "( * )".

End NativeInt.

Global Instance eq_NativeInt : eq_of NativeInt.Int := fun x y => NativeInt.eq x y.
Global Instance zero_NativeInt : zero_of NativeInt.Int := NativeInt.zero.
Global Instance one_NativeInt : one_of NativeInt.Int := NativeInt.one.
Global Instance or_NativeInt : or_of NativeInt.Int := NativeInt.lor.
Global Instance shl_NativeInt : shl_of NativeInt.Int := NativeInt.lsl.
Global Instance and_NativeInt : and_of NativeInt.Int := NativeInt.land.
Global Instance shr_NativeInt : shr_of NativeInt.Int := NativeInt.lsr.
Global Instance opp_NativeInt : opp_of NativeInt.Int := NativeInt.neg.
Global Instance not_NativeInt : not_of NativeInt.Int := NativeInt.lnot.
Global Instance xor_NativeInt : xor_of NativeInt.Int := NativeInt.lxor.
Global Instance add_NativeInt : add_of NativeInt.Int := NativeInt.add.
Global Instance sub_NativeInt : sub_of NativeInt.Int := NativeInt.sub.
Global Instance mul_NativeInt : mul_of NativeInt.Int := NativeInt.mul.

(** * Conversion between machine integers and bit sequences *)

Fixpoint bitsToInt (p: bitseq): NativeInt.Int :=
  (match p with
    | true :: p => 1 || ((bitsToInt p) <<< 1)
    | false :: p => (bitsToInt p) <<< 1
    | [::] => 0
  end)%C.

Definition bitsToIntB {n} (bs: 'B_n): NativeInt.Int := bitsToInt bs.

(** * Extraction  *)

(* Following CompCert's Integer module *)
Module Type WORDSIZE.
  Variable wordsize: nat.
End WORDSIZE.

Axiom forallIntG : NativeInt.Int -> (NativeInt.Int -> bool) -> bool.
Extract Inlined Constant forallIntG => "Forall.forall_int".

(* Our trusted computing base sums up in these two operations and
their associated  reflection principles in Coq. *)

Section Trust.

(* Axiom 1: Equality of integer is embedded within Coq's propositional equality: *)
Axiom eqIntP : Equality.axiom NativeInt.eq.

Definition viewP (P: pred NativeInt.Int) (PP: NativeInt.Int -> Prop) := forall x, reflect (PP x) (P x).

(* Axiom 2: If a property is true for all integers, then it is propositionally true *)
Axiom forallIntP : forall w P PP,
    viewP P PP ->
    reflect (forall x, PP x) (forallIntG w (fun x => P x)).

End Trust.

(* Extract Constant eqIntP => "fun _ -> failwith ""eqIntP: not extractable.""". *)


Module Make (WS: WORDSIZE).

Fixpoint bitsFromInt_rec (k: nat)(n: NativeInt.Int): bitseq :=
  (match k with
    | 0 => [::]
    | k.+1 =>
      let p := bitsFromInt_rec k (n >>> 1) in
      ((n && 1) == 1) :: p                     
  end)%C.

Lemma bitsFromInt_recP {k} (n: NativeInt.Int): size (bitsFromInt_rec k n) == k.
Proof.
  elim: k n => // [k IH] n //=.
  rewrite eqSS //.
Qed.

Canonical bitsFromIntB (n: NativeInt.Int): 'B_WS.wordsize
  := Tuple (@bitsFromInt_recP WS.wordsize n).

Definition Int := NativeInt.Int.
Definition eq := NativeInt.eq.
Definition zero := NativeInt.zero.
Definition one := NativeInt.one.
Definition lor := NativeInt.lor.
Definition land := NativeInt.land.
Definition lsr := NativeInt.lsr.
Definition lxor := NativeInt.lxor.

Definition wordsize := bitsToInt (bitn 63 WS.wordsize).
Definition bitmask := 
  NativeInt.sub
    (NativeInt.lsl one wordsize) 
    one.
Definition mask_unop (f : Int -> Int) x := land bitmask (f x).
Definition mask_binop (f : Int -> Int -> Int) x y := land bitmask (f x y).

Definition neg := mask_unop NativeInt.neg.
Definition lnot := mask_unop NativeInt.lnot.

Definition lsl := mask_binop NativeInt.lsl.
Definition add := mask_binop NativeInt.add.
Definition sub := mask_binop NativeInt.sub.
Definition mul := mask_binop NativeInt.mul.


Definition forallInt := forallIntG wordsize.


(* All the axiomatized properties below are exhautively tested. *)

(** * Cancelation of [bitsToInt] on [bitsFromInt] *)

Definition bitsToIntK_test: bool :=
 [forall bs: 'B_WS.wordsize, bitsFromIntB (bitsToIntB bs) == bs ].

(* Validation condition:
    Experimentally, [bitsToInt32] must be cancelled by [bitsFromInt32] *)
Axiom bitsToIntK_valid: bitsToIntK_test.

Lemma bitsToIntK: cancel bitsToIntB bitsFromIntB.
Proof.
  move=> bs; apply/eqP; move: bs.
  apply/forallP: bitsToIntK_valid.
Qed.

(** * Injectivity of [bitsFromInt32] *)


Definition bitsFromInt_inj_test: bool := 
  forallInt (fun x =>
    forallInt (fun y => 
      (bitsFromIntB x == bitsFromIntB y) ==> eq x y)).

Axiom bitsFromInt_inj_valid: bitsFromInt_inj_test.

Lemma bitsFromInt_inj: injective bitsFromIntB.
Proof.
  move=> x y /eqP H.
  apply/eqIntP.
  move: H; apply/implyP.
  move: y; apply: forallIntP.
  move=> y; apply idP.
  move: x; apply/forallIntP; last by apply bitsFromInt_inj_valid.
  move=> x; apply idP.
Qed.

Lemma bitsFromIntK: cancel bitsFromIntB bitsToIntB.
Proof.
  apply: inj_can_sym; auto using bitsToIntK, bitsFromInt_inj.
Qed.

(** * Bijection [Int32] vs. [BITS wordsize] *)

Lemma bitsFromInt32_bij: bijective bitsFromIntB.
Proof.
  split with (g := bitsToIntB);
  auto using bitsToIntK, bitsFromIntK.
Qed.


(** * Representation relation *)

(** We say that an [n : Int32] is the representation of a bitvector
[bs : BITS ] if they satisfy the axiom [repr_native]. Morally, it
means that both represent the same number (ie. the same 
booleans). *)

Definition test_native (i: Int)(bs: 'B_WS.wordsize): bool
  := eq i (bitsToIntB bs).

(* TODO: use [fun_hrel] *)
Definition Rnative: Int -> 'B_WS.wordsize -> Type := test_native.

(** * Representation lemma: equality *)

Lemma eq_adj: forall i bs, eq i (bitsToIntB bs) = (bitsFromIntB i == bs) .
Proof.
  move=> i bs.
  apply/eqIntP/eqP; intro; subst;
  auto using bitsFromIntK, bitsToIntK.
Qed.

Lemma eq_Rnative:
  refines (Rnative ==> Rnative ==> param.bool_R)%rel eq_op eqtype.eq_op.
Proof.
  rewrite refinesE=> i1 bs1 Ribs1 i2 bs2 Ribs2.
  move: Ribs1 Ribs2.
  rewrite /eq_op/eq_NativeInt/Rnative/test_native.
  repeat (rewrite eq_adj; move/eqP=> <-).
  have ->: (NativeInt.eq i1 i2) = (bitsFromIntB i1 == bitsFromIntB i2)
    by apply/eqIntP/eqP; intro; subst; auto using bitsFromInt_inj.
  exact: bool_Rxx.
Qed.

(** * Representation lemma: individuals *)

(*
Definition zero_test: bool 
  := eq zero (bitsToIntB (B0 WS.wordsize)).
  
(* Validation condition:
   bit vector [#0] corresponds to machine [0] *)
Axiom zero_valid: zero_test.

Global Instance zero_Rnative: refines Rnative 0%C 0%C.
Proof. rewrite refinesE. apply zero_valid. Qed.
  
Definition one_test: bool
  := eq one (bitsToInt32 #1).

(* Validation condition:
   bit vector [#1] corresponds to machine [1] *)
Axiom one_valid: one_test.

Global Instance one_Rnative: refines Rnative 1%C 1%C.
Proof. rewrite refinesE. apply one_valid. Qed.

(** * Representation lemma: successor *)
(*
Definition succ_test: bool
  := forallInt32 (fun i =>
     Rnative (succ i) (incB (bitsFromInt32 i))).

(* Validation condition:
    [succ "n"] corresponds to machine [n + 1] *)
Axiom succ_valid: succ_test.

Global Instance succ_Rnative: 
  refines (Rnative ==> Rnative) succ incB.
forall i bs,
    Rnative i bs -> Rnative (succ i) (incB bs).
Proof.
  move=> i ?.
  rewrite /Rnative eq_adj.
  move/eqP=> <-.
  apply/eqInt32P.
  move: i; apply/forallInt32P; last by apply succ_valid.
  move=> x; apply/eqInt32P.
Qed.
*)

(** * Representation lemma: negation *)

Definition lnot_test: bool
  := forallInt32 (fun i =>
       test_native (lnot i) (invB (bitsFromInt32 i))).

(* Validation condition:
    [invB "n"] corresponds to machine [lnot n] *)
Axiom lnot_valid: lnot_test.

Global Instance lnot_Rnative: 
  refines (Rnative ==> Rnative) ~%C ~%C.
Proof.
  rewrite refinesE=> i bs.
  rewrite /Rnative/test_native eq_adj.
  move/eqP=> <-.
  apply/eqInt32P.
  move: i; apply/forallInt32P; last by apply lnot_valid.
  move=> i; apply/eqInt32P.
Qed.

(** * Representation lemma: logical and *)

Definition land_test: bool
  := forallInt32 (fun i =>
       forallInt32 (fun i' =>
         test_native (land i i') (andB (bitsFromInt32 i) (bitsFromInt32 i')))).

(* Validation condition:
    [land "m" "n"] corresponds to machine [m land n] *)
Axiom land_valid: land_test.

Global Instance land_Rnative:
  refines (Rnative ==> Rnative ==> Rnative) &&%C andB.
Proof.
  rewrite refinesE=> i1 bs1 Ribs1 i2 bs2 Ribs2. move: Ribs1 Ribs2.
  repeat (rewrite /Rnative/test_native eq_adj; move/eqP=> <-).
  apply/eqInt32P.
  rewrite /and_op/and_Int32.
  move: i2; apply: forallInt32P.
  move=> i'; apply/eqInt32P.
  move: i1; apply: forallInt32P; last by apply land_valid.
  move=> i2; apply idP.
Qed.

(** * Representation lemma: logical or *)

Definition lor_test: bool
  := forallInt32 (fun i =>
       forallInt32 (fun i' =>
         test_native (lor i i') (orB (bitsFromInt32 i) (bitsFromInt32 i')))).

(* Validation condition:
    [lor "m" "n"] corresponds to machine [m lor n] *)
Axiom lor_valid: lor_test.

Global Instance lor_Rnative: 
  refines (Rnative ==> Rnative ==> Rnative) ||%C orB.
Proof.
  rewrite refinesE=> i1 bs1 Ribs1 i2 bs2 Ribs2.
  move: Ribs1 Ribs2.
  repeat (rewrite /Rnative/test_native eq_adj; move/eqP=> <-).
  apply/eqInt32P.
  move: i2; apply: forallInt32P.
  move=> i2; apply/eqInt32P.
  move: i1; apply: forallInt32P; last by apply lor_valid.
  move=> i1; apply idP.
Qed.

(** * Representation lemma: logical xor *)

Definition lxor_test: bool
  := forallInt32 (fun i =>
       forallInt32 (fun i' =>
         test_native (lxor i i') (xorB (bitsFromInt32 i) (bitsFromInt32 i')))).

(* Validation condition:
    [lxor "m" "n"] corresponds to machine [m lxor n] *)
Axiom lxor_valid: lxor_test.


Global Instance lxor_Rnative: 
  refines (Rnative ==> Rnative ==> Rnative) ^^%C xorB.
Proof.
  rewrite refinesE=> i1 bs1 Ribs1 i2 bs2 Ribs2.
  move: Ribs1 Ribs2.
  repeat (rewrite /Rnative/test_native eq_adj; move/eqP=> <-).
  apply/eqInt32P.
  move: i2; apply: forallInt32P.
  move=> i2; apply/eqInt32P.
  move: i1; apply: forallInt32P; last by apply lxor_valid.
  move=> i2; apply idP.
Qed.

(** * Representation of naturals *)

(** We extend the refinement relation (by composition) to natural
numbers, going through a [BITS wordsize] word. *)

Definition natural_repr (i: Int32)(n: nat): bool :=
  [exists bs, test_native i bs && (# n == bs)].

(** * Representation lemma: logical shift right *)

Definition lsr_test: bool
  := forallInt32 (fun i =>
       forallInt32 (fun i' =>
         implb (toNat (bitsFromInt32 i') <= wordsize)%nat (test_native (lsr i i') (shrBn (bitsFromInt32 i) (toNat (bitsFromInt32 i')))))).

(* Validation condition:
    [lsr "m" "n"] corresponds to machine [m lsr n] *)
Axiom lsr_valid: lsr_test.

Global Instance lsr_Rnative: 
  refines (Rnative ==> Rnative ==> Rnative) >>%C (fun bs1 bs2 => shrBn bs1 (toNat bs2)).
Admitted.
(*
Proof.
  rewrite refinesE=> i1 bs1 Ribs1 i2 bs2 Ribs2.
  move: Ribs1 Ribs2.
  rewrite /Rnative eq_adj; move/eqP=> <-.
  rewrite /natural_repr.
  move/existsP=> [bs' /andP [H /eqP H']].
  rewrite /Rnative eq_adj in H.
  move/eqP: H=> H.
  apply/eqInt32P.
  have Hk: k = toNat (bitsFromInt32 i').
    rewrite H.
    have ->: k = toNat (fromNat (n := wordsize) k).
      rewrite toNat_fromNatBounded=> //.
      by apply (leq_ltn_trans (n := wordsize)).
    by rewrite H'.
  rewrite Hk.
  rewrite Hk in ltn_k.
  clear H H' Hk.
  move: i' ltn_k; apply/(forallInt32P (fun i' => implb (toNat (bitsFromInt32 i') <= wordsize)%nat (eq (lsr i i') (bitsToInt32 (shrBn (bitsFromInt32 i) (toNat ((bitsFromInt32 i')))))))).
  move=> i'.
  apply/equivP.
  apply/implyP.
  split=> H H'.
  move: (H H')=> H''.
  by apply/eqInt32P.
  move: (H H')=> H''.
  by apply/eqInt32P.
  move: i; apply/forallInt32P; last by apply lsr_valid.
  move=> i'; apply idP.
Qed.
*)

(** * Representation lemma: logical shift left *)

Definition lsl_test: bool
  := forallInt32 (fun i =>
       forallInt32 (fun i' =>
          implb (toNat (bitsFromInt32 i') <= wordsize)%nat
                (test_native (lsl i i') (shlBn (bitsFromInt32 i) (toNat (bitsFromInt32 i')))))).

(* Validation condition:
    [lsl "m" "n"] corresponds to machine [m lsl n] *)
Axiom lsl_valid: lsl_test.

Global Instance lsl_repr: 
  refines (Rnative ==> Rnative ==> Rnative) <<%C (fun x y => shlBn x (toNat y)).
Admitted.
(*
Proof.
  move=> i i' ? k ltn_k.
  rewrite /Rnative eq_adj; move/eqP=> <-.
  rewrite /natural_repr.
  move/existsP=> [bs' /andP [H /eqP H']].
  rewrite /Rnative eq_adj in H.
  move/eqP: H=> H.
  apply/eqInt32P.
  have Hk: k = toNat (bitsFromInt32 i').
    rewrite H.
    have ->: k = toNat (fromNat (n := wordsize) k).
      rewrite toNat_fromNatBounded=> //.
      by apply (leq_ltn_trans (n := wordsize)).
    by rewrite H'.
  rewrite Hk.
  rewrite Hk in ltn_k.
  clear H H' Hk.
  move: i' ltn_k; apply/(forallInt32P (fun i' => implb (toNat (bitsFromInt32 i') <= wordsize)%nat (eq (lsl i i') (bitsToInt32 (shlBn (bitsFromInt32 i) (toNat ((bitsFromInt32 i')))))))).
  move=> i'.
  apply/equivP.
  apply/implyP.
  split=> H H'.
  move: (H H')=> H''.
  by apply/eqInt32P.
  move: (H H')=> H''.
  by apply/eqInt32P.
  move: i; apply/forallInt32P; last by apply lsl_valid.
  move=> i'; apply idP.
Qed.
*)

(** * Representation lemma: negation *)

Definition neg_test: bool
  := forallInt32 (fun i =>
       test_native (neg i) (negB (bitsFromInt32 i))).

(* Validation condition:
    [negB "m"] corresponds to machine [- m] *)
Axiom neg_valid: neg_test.

Global Instance neg_repr: 
  refines (Rnative ==> Rnative) -%C negB.
Proof.
  rewrite refinesE=> i bs.
  rewrite /Rnative/test_native eq_adj.
  move/eqP=> <-.
  apply/eqInt32P.
  move: i; apply/forallInt32P; last by apply neg_valid.
  move=> i; apply: eqInt32P.
Qed.


(** * Representation lemma: addition *)

Definition add_test: bool
  := forallInt32 (fun i =>
       forallInt32 (fun i' =>
         test_native (add i i') (addB (bitsFromInt32 i) (bitsFromInt32 i')))).

(* Validation condition:
    [decB "m"] corresponds to machine [dec m] *)
Axiom add_valid: add_test.

Global Instance add_Rnative:
  refines (Rnative ==> Rnative ==> Rnative) +%C (fun x y => addB x y).
Proof.
  rewrite refinesE=> i1 bs1 Ribs1 i2 bs2 Ribs2. move: Ribs1 Ribs2.
  repeat (rewrite /Rnative/test_native eq_adj; move/eqP=> <-).
  apply/eqInt32P.
  move: i2; apply: forallInt32P.
  move=> i2; apply/eqInt32P.
  move: i1; apply/forallInt32P; last by apply add_valid.
  move=> i1; apply idP.
Qed.

(** * Representation lemma: subtraction *)

Definition sub_test: bool
  := forallInt32 (fun i =>
       forallInt32 (fun j =>
         test_native (sub i j) (subB (bitsFromInt32 i) (bitsFromInt32 j)))).

Axiom sub_valid: sub_test.

Global Instance sub_Rnative: 
  refines (Rnative ==> Rnative ==> Rnative) sub_op sub_op.
Proof.
  rewrite /sub_op/sub_Int32/sub_Bits.
  rewrite refinesE=> i1 bs1 Ribs1 i2 bs2 Ribs2.
  move: Ribs1 Ribs2.
  repeat (rewrite /Rnative/test_native eq_adj; move/eqP=> <-).
  apply/eqInt32P.
  move: i2; apply: forallInt32P.
  move=> i2; apply/eqInt32P.
  move: i1; apply/forallInt32P; last by apply sub_valid.
  move=> i1; apply idP.
Qed.


(** * Representation lemma: multiplication *)

Definition mul_test: bool
  := forallInt32 (fun i =>
       forallInt32 (fun i' =>
         test_native (mul i i') (mulB (bitsFromInt32 i) (bitsFromInt32 i')))).

Axiom mul_valid: mul_test.

Global Instance mul_Rnative:
  refines (Rnative ==> Rnative ==> Rnative) *%C (fun x y => mulB x y).
Proof.
  rewrite refinesE=> i1 bs1 Ribs1 i2 bs2 Ribs2. move: Ribs1 Ribs2.
  repeat (rewrite /Rnative/test_native eq_adj; move/eqP=> <-).
  apply/eqInt32P.
  move: i2; apply: forallInt32P.
  move=> i2; apply/eqInt32P.
  move: i1; apply/forallInt32P; last by apply mul_valid.
  move=> i1; apply idP.
Qed.

*)

(** Extract the tests: they should all return true! *)

Definition allb s := foldr (andb) true s.

(*
Definition binop_tests x bitsX y :=
  let bitsY := bitsFromInt32 y in
  allb
    [:: implb (bitsX == bitsY) (eq x y) ;
      test_native (land x y) (andB bitsX bitsY) ;
      test_native (lor x y) (orB bitsX bitsY) ;
      test_native (lxor x y) (xorB bitsX bitsY) ;
      implb (toNat bitsY <= wordsize)%nat (test_native (lsr x y) (shrBn bitsX (toNat bitsY))) ;
      implb (toNat bitsY <= wordsize)%nat (test_native (lsl x y) (shlBn bitsX (toNat bitsY))) ;
      test_native (add x y) (addB bitsX bitsY)].

Definition unop_tests x :=
  let bitsX := bitsFromInt32 x in
  allb
    [:: (*Rnative (succ x) (incB bitsX) ;*)
      test_native (lnot x) (invB bitsX) ;
      test_native (neg x) (negB bitsX) ;
(*      Rnative (dec x) (decB bitsX) ; *)
      forallInt32
        (fun y => binop_tests x bitsX y)].
*)

Definition tests
  := allb
       [:: bitsToIntK_test (*;
         zero_test ;
         one_test ;
         forallInt32 
           (fun x => unop_tests x) *)].

(*
Lemma implies_unop : tests -> forall x, unop_tests x.
  move=> /andP [_ /andP [_ /andP[_ /andP [H _]]]] x.
  rewrite /unop_tests.
  move: H=> /forallInt32P H.
  move: (H unop_tests)=> H'.
  apply H'=> x'.
  by apply idP.
Qed.

Lemma implies_binop : tests -> forall x y, binop_tests x (bitsFromInt32 x) y.
  move => H x y.
  have H': unop_tests x by apply implies_unop.
  move: H'=> /andP [_ /andP [_ /andP [H1 _]]].
  move: H1=> /forallInt32P H1.
  move: (H1 (binop_tests x (bitsFromInt32 x)))=> H2.
  apply H2=> y'.
  by apply idP.
Qed.

Lemma implies_bitsToInt32K : tests -> bitsToInt32K_test.
  by move=> /andP [H _].
Qed.

Lemma implies_bitsFromInt32_inj : tests -> bitsFromInt32_inj_test.
  move=> H.
  apply/forallInt32P=> x.
  apply idP.
  apply/forallInt32P=> y.
  apply idP.
  have H': binop_tests x (bitsFromInt32 x) y by apply implies_binop.
  by move: H'=> /andP [H' _].
Qed.

Lemma implies_zero : tests -> zero_test.
  by move=> /andP [_ /andP [H _]].
Qed.

Lemma implies_one : tests -> one_test.
  by move=> /andP [_ /andP [_ /andP[H _]]].
Qed.

(*
Lemma implies_succ : tests -> succ_test.
  move=> H.
  apply/forallInt32P=> x.
  apply idP.
  have H': unop_tests x by apply implies_unop.
  by move: H'=> /andP [H1 _].
Qed.
*)

Lemma implies_lnot : tests -> lnot_test.
  move=> H.
  apply/forallInt32P=> x.
  apply idP.
  have H': unop_tests x by apply implies_unop.
  by move: H'=> /andP [H1 _].
Qed.

Lemma implies_land : tests -> land_test.
  move=> H.
  apply/forallInt32P=> x.
  apply idP.
  apply/forallInt32P=> y.
  apply idP.
  have H': binop_tests x (bitsFromInt32 x) y by apply implies_binop.
  by move: H'=> /andP [_ /andP [H' _]].
Qed.

Lemma implies_lor : tests -> lor_test.
  move=> H.
  apply/forallInt32P=> x.
  apply idP.
  apply/forallInt32P=> y.
  apply idP.
  have H': binop_tests x (bitsFromInt32 x) y by apply implies_binop.
  by move: H'=> /andP [_ /andP [_ /andP [H' _]]].
Qed.

Lemma implies_lxor : tests -> lxor_test.
  move=> H.
  apply/forallInt32P=> x.
  apply idP.
  apply/forallInt32P=> y.
  apply idP.
  have H': binop_tests x (bitsFromInt32 x) y by apply implies_binop.
  by move: H'=> /andP [_ /andP [_ /andP [_ /andP [H' _]]]].
Qed.

Lemma implies_lsr : tests -> lsr_test.
  move=> H.
  apply/forallInt32P=> x.
  apply idP.
  apply/forallInt32P=> y.
  apply idP.
  have H': binop_tests x (bitsFromInt32 x) y by apply implies_binop.
  by move: H'=> /andP [_ /andP [_ /andP [_ /andP [_ /andP [H' _]]]]].
Qed.

Lemma implies_lsl : tests -> lsl_test.
  move=> H.
  apply/forallInt32P=> x.
  apply idP.
  apply/forallInt32P=> y.
  apply idP.
  have H': binop_tests x (bitsFromInt32 x) y by apply implies_binop.
  by move: H'=> /andP [_ /andP [_ /andP [_ /andP [_ /andP [_ /andP [H' _]]]]]].
Qed.

Lemma implies_neg : tests -> neg_test.
  move=> H.
  apply/forallInt32P=> x.
  apply idP.
  have H': unop_tests x by apply implies_unop.
  by move: H'=> /andP [_ /andP [H1 _]].
Qed.

(*
Lemma implies_dec : tests -> dec_test.
  move=> H.
  apply/forallInt32P=> x.
  apply idP.
  have H': unop_tests x by apply implies_unop.
  by move: H'=> /andP [_ /andP [_ /andP [H1 _]]].
Qed.
*)

Lemma implies_add : tests -> add_test.
  move=> H.
  apply/forallInt32P=> x.
  apply idP.
  apply/forallInt32P=> y.
  apply idP.
  have H': binop_tests x (bitsFromInt32 x) y by apply implies_binop.
  by move: H'=> /andP [_ /andP [_ /andP [_ /andP [_ /andP [_ /andP [_ /andP [H' _]]]]]]].
Qed.
*)


End Make.

(*
Extract Constant inj_eqAxiom => "failwith ""a""".
Extract Constant choice.PcanChoiceMixin => "failwith ""foo""".
Extract Constant inj_eqAxiom => "failwith ""b""".
Extract Constant inj_eqAxiom => "failwith ""eqseqP""".
Extract Constant choice.seq_choiceMixin => "failwith ""c""".
Extract Constant eqnP => "failwith ""c""".
Extract Constant eqbP => "failwith ""d""".
Extract Constant eqP => "failwith ""eqP""".
Extract Constant idP => "failwith ""idP""".
Extract Constant choice.nat_choiceMixin => "failwith ""d""".
Extract Constant val_eqP => "failwith ""e""".
*)

Module Wordsize_32.
  Definition wordsize := 32.
End Wordsize_32.

Module Int32 := Make(Wordsize_32).


Module Wordsize_16.
  Definition wordsize := 16.
End Wordsize_16.

Module Int16 := Make(Wordsize_16).

Module Wordsize_8.
  Definition wordsize := 8.
End Wordsize_8.

Module Int8 := Make(Wordsize_8).

Cd "../test".
Extraction "test_int8.ml" Int8.tests.
Extraction "test_int16.ml" Int16.tests.
Extraction "test_int32.ml" Int32.tests.

