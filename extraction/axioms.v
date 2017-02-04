(******************************************************************************)
(* A bit library for Coq: extraction to machine words.                        *)
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
Module Native.

(** We assume that we are running on a 64 bit machine. *)
Axiom Int : Type.
Axiom eq  : Int -> Int -> bool.

Axiom zero : Int.
Axiom one  : Int.
Axiom opp  : Int -> Int.
Axiom sub  : Int -> Int -> Int.
Axiom add  : Int -> Int -> Int.

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
Extract Inlined Constant lnot => "lnot".
Extract Inlined Constant add  => "(+)".
Extract         Constant opp  => "(fun x -> -x)".
Extract Inlined Constant sub  => "(-)".

End Native.

Import Native.

Global Instance   eq_Native : eq_of   Int := eq.

Global Instance zero_Native : zero_of Int := zero.
Global Instance  one_Native : one_of  Int := one.
Global Instance  opp_Native : opp_of  Int := opp.
Global Instance  sub_Native : sub_of  Int := sub.
Global Instance  add_Native : add_of  Int := add.

Global Instance  not_Native : not_of  Int := lnot.
Global Instance   or_Native : or_of   Int := lor.
Global Instance  and_Native : and_of  Int := land.
Global Instance  xor_Native : xor_of  Int := lxor.
Global Instance  shl_Native : shl_of  Int Int := lsl.
Global Instance  shr_Native : shr_of  Int Int := lsr.

Section BitExtract.

Variable n : nat.
Implicit Types (s : bitseq) (b : 'B_n).

Fixpoint bitsToInt s : Int :=
  (match s with
    | [::]           => 0
    | [:: false & s] =>      bitsToInt s :<<: 1
    | [:: true  & s] => 1 || (bitsToInt s :<<: 1)
  end)%C.

Fixpoint bitsFromInt (k: nat) (n: Int) : bitseq :=
  (match k with
    | 0 => [::]
    | k.+1 =>
      let p := bitsFromInt k (n :>>: 1) in
      ((n && 1) == 1) :: p
  end)%C.

Lemma bitsFromIntP {k} (i: Int): size (bitsFromInt k i) == k.
Proof.
  elim: k i => // [k IH] i //=; rewrite eqSS //.
Qed.

Canonical bitsFromInt_tuple (i: Int): 'B_n
  := Tuple (bitsFromIntP i).


End BitExtract.

(** * Extraction  *)

(* Following CompCert's Integer module *)
Module Type WORDSIZE.
  Variable wordsize: nat.
End WORDSIZE.

Module MakeOps (WS: WORDSIZE).

Definition w := WS.wordsize.

Definition Int  := Native.Int.
Definition eq   := Native.eq.
Definition zero := Native.zero.
Definition one  := Native.one.
Definition lor  := Native.lor.
Definition land := Native.land.
Definition lsr  := Native.lsr.
Definition lxor := Native.lxor.

Definition wordsize := bitsToInt (bitn 63 WS.wordsize).

Definition bitmask := ((1 :<<: wordsize) - 1: Int)%C.

Definition mask_unop  (f : Int -> Int) x := (bitmask && f x)%C.
Definition mask_binop (f : Int -> Int -> Int) x y := (bitmask && f x y)%C.

Definition lnot := mask_unop Native.lnot.
Definition opp  := mask_unop Native.opp.

Definition lsl := mask_binop Native.lsl.
Definition add := mask_binop Native.add.
Definition sub := mask_binop Native.sub.

End MakeOps.

Module Wordsize_32.
  Definition wordsize := 32.
End Wordsize_32.

Module Int32 := MakeOps(Wordsize_32).

Module Wordsize_16.
  Definition wordsize := 16.
End Wordsize_16.

Module Int16 := MakeOps(Wordsize_16).

Module Wordsize_8.
  Definition wordsize := 8.
End Wordsize_8.

Module Int8 := MakeOps(Wordsize_8).
