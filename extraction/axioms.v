(******************************************************************************)
(* A bit library for Coq: bit sequences.                                      *)
(******************************************************************************)
(*                                                                            *)
(* (c) 2016, ENS Lyon, LIP6, MINES ParisTech                                  *)
(*                                                                            *)
(* Written by Arthur Blot                                                     *)
(*            Pierre-Evariste Dagand                                          *)
(*            Emilio J. Gallego Arias                                         *)
(*                                                                            *)
(* LICENSE: Dual CECILL-B / Apache 2.0                                        *)
(*                                                                            *)
(******************************************************************************)


From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.

From mathcomp
Require Import tuple ssralg ssrnum zmodp.

From CoqEAL
Require Import hrel param refinements.

From ssrbit
Require Import bitseq notation.

From Coq
Require Import ZArith.ZArith ExtrOcamlBasic.

Import Refinements.Op.
Import Logical.Op.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * An axiomatization of OCaml native integers *)

(** This module should not be used directly. *)
Module NativeInt.

(** We assume that we are running on a 64 bit machine. *)
Axiom Int : Type.
Axiom eq  : Int -> Int -> bool.

Axiom zero : Int.
Axiom one  : Int.
Axiom neg  : Int -> Int.
Axiom add  : Int -> Int -> Int.
Axiom sub  : Int -> Int -> Int.
Axiom mul  : Int -> Int -> Int.

Axiom lnot : Int -> Int.
Axiom lor  : Int -> Int -> Int.
Axiom land : Int -> Int -> Int.
Axiom lxor : Int -> Int -> Int.
Axiom lsr  : Int -> Int -> Int.
Axiom lsl  : Int -> Int -> Int.

Extract Inlined Constant Int  => "int".
Extract Inlined Constant eq   => "(=)".
Extract Inlined Constant zero => "0".
Extract Inlined Constant one  => "1".
Extract Inlined Constant lor  => "(lor)".
Extract Inlined Constant land => "(land)".
Extract Inlined Constant lsr  => "(lsr)".
Extract Inlined Constant lxor => "(lxor)".

(** One must be careful to re-normalize the following operations when
using them at smaller wordsize: *)

Extract Inlined Constant lsl  => "(lsl)".
Extract Inlined Constant neg  => "(fun x -> -x)".
Extract Inlined Constant lnot => "lnot".
Extract Inlined Constant add  => "(+)".
Extract Inlined Constant sub  => "(-)".
Extract Inlined Constant mul  => "( * )".

End NativeInt.

Global Instance   eq_NativeInt : eq_of   NativeInt.Int := NativeInt.eq.
Global Instance zero_NativeInt : zero_of NativeInt.Int := NativeInt.zero.
Global Instance  one_NativeInt : one_of  NativeInt.Int := NativeInt.one.
Global Instance   or_NativeInt : or_of   NativeInt.Int := NativeInt.lor.
Global Instance  shl_NativeInt : shl_of  NativeInt.Int := NativeInt.lsl.
Global Instance  and_NativeInt : and_of  NativeInt.Int := NativeInt.land.
Global Instance  shr_NativeInt : shr_of  NativeInt.Int := NativeInt.lsr.
Global Instance  opp_NativeInt : opp_of  NativeInt.Int := NativeInt.neg.
Global Instance  not_NativeInt : not_of  NativeInt.Int := NativeInt.lnot.
Global Instance  xor_NativeInt : xor_of  NativeInt.Int := NativeInt.lxor.
Global Instance  add_NativeInt : add_of  NativeInt.Int := NativeInt.add.
Global Instance  sub_NativeInt : sub_of  NativeInt.Int := NativeInt.sub.
Global Instance  mul_NativeInt : mul_of  NativeInt.Int := NativeInt.mul.

(** * Conversion between machine integers and bit sequences *)

(* Enumeration for 'B_n, from G. Gonthier's mailing list post at:

 *)
Section AllPairsExtra.

Lemma map_allpairs S T R O s t (op : S -> T -> R) (f : R -> O) :
  [seq f x | x <- allpairs op s t] = [seq f (op x y) | x <- s, y <- t].
Proof.
by elim: s t => [|x s ihs] [|y t] //=; rewrite -ihs map_cat -map_comp.
Qed.

Lemma allpairss0 S T R s (op : S -> T -> R) :
    [seq op x y | x <- s, y <- [::]] = [::].
Proof. by elim s. Qed.

Lemma allpairs_map S T R U V s t (f : S -> T -> R) (g : U -> S) (h : V -> T) :
  allpairs f (map g s) (map h t) = allpairs (fun x y => f (g x) (h y)) s t.
Proof.
elim: s t => [|x s ihs] [|y t] //=; first by rewrite !allpairss0.
by rewrite -ihs -map_comp.
Qed.

End AllPairsExtra.

Section TupleEnum.

Fixpoint all_seqs T (e : seq T) n : seq (seq T) :=
  if n isn't m.+1 then [:: [::]] else
    [seq [:: x & t] | x <- e, t <- all_seqs e m].

Fixpoint all_tuples T (e : seq T) n : seq (n.-tuple T) :=
  if n isn't m.+1 then [:: [tuple]] else
    [seq cons_tuple x t | x <- e, t <- all_tuples e m].

Lemma all_tuplesE T (e : seq T) n :
  map val (all_tuples e n) = all_seqs e n.
Proof.
by elim: n => //= n <-; rewrite !map_allpairs -{3}[e]map_id allpairs_map.
Qed.

Lemma perm_enum_tuples n (T : finType) :
  perm_eq (enum {:n.-tuple T}) (all_tuples (enum T) n).
Proof.
rewrite uniq_perm_eq ?enum_uniq //.
elim: n => //= n IHn; rewrite allpairs_uniq ?enum_uniq //.
  by move=> [x1 t1] [x2 t2] _ _ [-> /val_inj->].
elim: n => [|n IHn] t; rewrite mem_enum ?tuple0 //=; apply/esym/allpairsP.
by case/tupleP: t => x t; exists (x, t); rewrite -IHn !mem_enum.
Qed.

Lemma perm_enum_bits n : perm_eq (enum {:'B_n}) (all_tuples (enum {: bool}) n).
Proof. exact: perm_enum_tuples. Qed.

Lemma enum_bool : enum {: bool} = [:: true; false].
Proof. by rewrite enumT unlock. Qed.

(* XXX: State up to permutation of enum {: bool} ? *)
Lemma perm_benum_bits n :
  perm_eq (map val (enum {:'B_n})) (all_seqs [:: true; false] n).
Proof.
by rewrite -enum_bool -all_tuplesE perm_map ?perm_enum_tuples.
Qed.

(* XXX: Doing a pred-only version for now *)
Lemma forall_bitE n (p : pred bitseq) :
  [forall b : 'B_n, p b] = all p (all_seqs [:: true; false] n).
Proof.
rewrite -enum_bool -all_tuplesE all_map.
have/perm_eq_mem/eq_all_r <- := perm_enum_tuples n [finType of bool].
by apply/forallP/allP => //= hx x; apply: (hx x); rewrite mem_enum.
Qed.

Lemma forall_bitP n (p : pred bitseq) :
  reflect (forall b : 'B_n, p b) (all p (all_seqs [:: true; false] n)).
Proof. by rewrite -forall_bitE; exact: forallP. Qed.

End TupleEnum.

Section EqOps.

(* This is useful to have cleaner extraction. *)
Definition eqseqb := (fix eqseq (s1 s2 : seq bool) {struct s2} : bool :=
     match s1 with
     | [::] => match s2 with
               | [::] => true
               | _ :: _ => false
               end
     | x1 :: s1' =>
       match s2 with
       | [::] => false
       | x2 :: s2' => (eqb x1 x2) && eqseq s1' s2'
      end
  end).

(* R is for refinement *)
Lemma eqseqR (t1 t2 : bitseq) : (t1 == t2) = eqseqb t1 t2.
Proof. by []. Qed.

Lemma eqBR n (t1 t2 : 'B_n) : (t1 == t2) = eqseqb t1 t2.
Proof. by []. Qed.

End EqOps.

Section BitExtract.

Variable n : nat.
Implicit Types (s : bitseq) (b : 'B_n).

Fixpoint bitsToInt s : NativeInt.Int :=
  (match s with
    | [::]           => 0
    | [:: false & s] =>       bitsToInt s <<< 1
    | [:: true  & s] => 1 || (bitsToInt s <<< 1)
  end)%C.

Fixpoint bitsFromInt (k: nat) (n: NativeInt.Int) : bitseq :=
  (match k with
    | 0 => [::]
    | k.+1 =>
      let p := bitsFromInt k (n >>> 1) in
      ((n && 1) == 1) :: p
  end)%C.

End BitExtract.

(** * Extraction  *)
(* Following CompCert's Integer module *)
Module Type WORDSIZE.
  Variable wordsize: nat.
End WORDSIZE.

(* Our trusted computing base is formed by:
 - a trusted equality operator.
 - a trusted efficient checker operator.
 *)

Axiom forallIntG : NativeInt.Int -> (NativeInt.Int -> bool) -> bool.
Extract Inlined Constant forallIntG => "Forall.forall_int".

Section Trust.

(* Axiom 1: Equality of integer is embedded within Coq's propositional equality: *)
Axiom eqIntP : Equality.axiom NativeInt.eq.

(* Axiom 2: If a property is true for all integers, then it is
   propositionally true. We restrict to boolean properties *)
Axiom forallIntP : forall w (P : pred _),
    reflect (forall x, P x) (forallIntG w P).

End Trust.

Module Make (WS: WORDSIZE).

Definition n := WS.wordsize.

Definition Int  := NativeInt.Int.
Definition eq   := NativeInt.eq.
Definition zero := NativeInt.zero.
Definition one  := NativeInt.one.
Definition lor  := NativeInt.lor.
Definition land := NativeInt.land.
Definition lsr  := NativeInt.lsr.
Definition lxor := NativeInt.lxor.

Definition wordsize := bitsToInt (bitn 63 WS.wordsize).

Definition bitmask := ((NativeInt.lsl one wordsize) - one)%C.

Definition mask_unop  (f : Int -> Int) x := land bitmask (f x).
Definition mask_binop (f : Int -> Int -> Int) x y := land bitmask (f x y).

Definition neg  := mask_unop NativeInt.neg.
Definition lnot := mask_unop NativeInt.lnot.

Definition lsl := mask_binop NativeInt.lsl.
Definition add := mask_binop NativeInt.add.
Definition sub := mask_binop NativeInt.sub.
Definition mul := mask_binop NativeInt.mul.

Definition forallInt := forallIntG wordsize.

(* Validation condition:
   Experimentally, [bitsToInt32] must be cancelled by [bitsFromInt32] *)
Definition test_bitsToIntK :=
  all (fun s => eqseqb (bitsFromInt n (bitsToInt s)) s)
      (all_seqs [:: true; false] n).

(* XXX: Fix *)
Definition prop_bitsToIntK := forall b : 'B_n,
    [fun s => bitsFromInt n (bitsToInt s) == s] b.

(* XXX: Improve *)
(* [Avoid reflect to clean up extraction, can we may blacklist it?] *)
Lemma iff_bitsToIntK :
  test_bitsToIntK <-> prop_bitsToIntK.
Proof.
split; last by move/forall_bitP.
by move=> hall x; apply/forall_bitP.
Qed.

Axiom bitsToIntK_valid : prop_bitsToIntK.

Lemma bitsToIntK: cancel bitsToInt (bitsFromInt n).
Proof.
move=> bs; apply/eqP.
Admitted.


(** * Injectivity of [bitsFromInt32] *)

(* Emilio: this seems more expensive than just doing the test.
Definition bitsFromInt_inj_test: bool :=
  forallInt (fun x =>
    forallInt (fun y =>
                 (* XXX use the refined operator for bitseq *)
      (eqseqb (bitsFromInt_rec WS.wordsize x) (bitsFromInt_rec WS.wordsize y)) ==> eq x y)).

Axiom bitsFromInt_inj_valid: bitsFromInt_inj_test.
*)

(*
Lemma bitsFromInt_inj: injective bitsFromInt.
Proof.
have := can_inj bitsToIntK.
  move=> x y /eqP H.
  apply/eqIntP.
  move: H; apply/implyP.
  move: y; apply: forallIntP.
  move=> y; apply idP.
  move: x; apply/forallIntP; last by apply bitsFromInt_inj_valid.
  move=> x; apply idP.
Qed.
*)

Lemma bitsFromIntK: cancel (bitsFromInt n) bitsToInt.
Proof.
Admitted.
(* apply: inj_can_sym; auto using bitsToIntK, bitsFromInt_inj. *)
(* Qed. *)

(** * Representation relation *)

(** We say that an [n : Int32] is the representation of a bitvector
    [bs : BITS ] if they satisfy the axiom [repr_native]. Morally, it
    means that both represent the same number (ie. the same
    booleans). *)

Definition test_native (i: Int) (bs: 'B_WS.wordsize) : bool :=
  (i == bitsToInt bs)%C.

(* TODO: use [fun_hrel] *)
Definition Rnative: Int -> 'B_WS.wordsize -> Type := test_native.

(** * Representation lemma: equality *)

Lemma eq_adj i bs : (i == bitsToInt bs)%C = (bs == bitsFromInt n i).
Proof. by apply/eqIntP/eqP => ->; rewrite ?bitsFromIntK ?bitsToIntK. Qed.

(*
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
*)

(** * Representation lemma: individuals *)

Open Scope bits_scope.

Definition zero_test : bool := (zero == bitsToInt ('0_WS.wordsize))%C.

(* Validation condition:
   bit vector [#0] corresponds to machine [0] *)
(*
Axiom zero_valid: zero_test.

Global Instance zero_Rnative: refines Rnative 0%C 0%C.
Proof. rewrite refinesE. apply zero_valid. Qed.
*)

Definition one_test : bool := (one == bitsToInt '1_WS.wordsize)%C.

(* Validation condition:
   bit vector [#1] corresponds to machine [1] *)
(*
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

(* Tests we need:

## Binary ops.

Definition binop_tests x bitsX y :=
  let bitsY := bitsFromInt32 y in
  allb [:: implb (bitsX == bitsY) (eq x y)
        ;  test_native (land x y) (andB bitsX bitsY)
        ;  test_native (lor  x y) (orB  bitsX bitsY)
        ;  test_native (lxor x y) (xorB bitsX bitsY)
        ;  implb (toNat bitsY <= wordsize)%nat (test_native (lsr x y) (shrBn bitsX (toNat bitsY)))
        ;  implb (toNat bitsY <= wordsize)%nat (test_native (lsl x y) (shlBn bitsX (toNat bitsY)))
        ;  test_native (add x y) (addB bitsX bitsY)
       ].

## Unary ops.

 Definition unop_tests x :=
  let bitsX := bitsFromInt32 x in
  allb [:: (*Rnative (succ x) (incB bitsX) ;*)
         ; test_native (lnot x) (invB bitsX)
         ; test_native (neg x)  (negB bitsX)
         ; Rnative (dec x) (decB bitsX)
         ; forallInt (fun y => binop_tests x bitsX y)
         ].
*)

Definition tests
  := all id
       [:: test_bitsToIntK
         ; zero_test
         ; one_test
       ].

End Make.

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

Extraction "test_int8.ml"  Int8.tests.
Extraction "test_int16.ml" Int16.tests.
Extraction "test_int32.ml" Int32.tests.

