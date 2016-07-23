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
Module NativeInt.

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

End NativeInt.

Local Instance   eq_NativeInt : eq_of   NativeInt.Int := NativeInt.eq.

Local Instance zero_NativeInt : zero_of NativeInt.Int := NativeInt.zero.
Local Instance  one_NativeInt : one_of  NativeInt.Int := NativeInt.one.
Local Instance  opp_NativeInt : opp_of  NativeInt.Int := NativeInt.opp.
Local Instance  sub_NativeInt : sub_of  NativeInt.Int := NativeInt.sub.
Local Instance  add_NativeInt : add_of  NativeInt.Int := NativeInt.add.

Local Instance  not_NativeInt : not_of  NativeInt.Int := NativeInt.lnot.
Local Instance   or_NativeInt : or_of   NativeInt.Int := NativeInt.lor.
Local Instance  and_NativeInt : and_of  NativeInt.Int := NativeInt.land.
Local Instance  xor_NativeInt : xor_of  NativeInt.Int := NativeInt.lxor.
Local Instance  shl_NativeInt : shl_of  NativeInt.Int NativeInt.Int := NativeInt.lsl.
Local Instance  shr_NativeInt : shr_of  NativeInt.Int NativeInt.Int := NativeInt.lsr.

(** * Conversion between machine integers and bit sequences *)

(* Enumeration for tuples, from G. Gonthier's mailing list post at:

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

Fixpoint all_tuples T (e : seq T) n : seq (n.-tuple T) :=
  if n isn't m.+1 then [:: [tuple]] else
    [seq cons_tuple x t | x <- e, t <- all_tuples e m].

(* We add a version of all_tuples but operating plain lists. The
   benefits in extraction are mininal as the tuple proof component is
   erased anyways, however, we feel it is a bit clearer.
 *)
Fixpoint all_seqs T (e : seq T) n : seq (seq T) :=
  if n isn't m.+1 then [:: [::]] else
    [seq [:: x & t] | x <- e, t <- all_seqs e m].

Lemma all_tuplesE T (e : seq T) n :
  map val (all_tuples e n) = all_seqs e n.
Proof.
by elim: n => //= n <-; rewrite !map_allpairs -{3}[e]map_id allpairs_map.
Qed.

(* Thanks to George Gonthier *)
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
Proof. by rewrite -enum_bool -all_tuplesE perm_map ?perm_enum_tuples. Qed.

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

(* This section is useful to have cleaner extraction. *)
Section EqOps.

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
    | [:: false & s] =>      bitsToInt s :<<: 1
    | [:: true  & s] => 1 || (bitsToInt s :<<: 1)
  end)%C.

Fixpoint bitsFromInt (k: nat) (n: NativeInt.Int) : bitseq :=
  (match k with
    | 0 => [::]
    | k.+1 =>
      let p := bitsFromInt k (n :>>: 1) in
      (n && 1 == 1) :: p
  end)%C.

Lemma bitsFromIntP {k} (i: NativeInt.Int): size (bitsFromInt k i) == k.
Proof.
  elim: k i => // [k IH] i //=; rewrite eqSS //.
Qed.

Canonical bitsFromInt_tuple (i: NativeInt.Int): 'B_n
  := Tuple (bitsFromIntP i).


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

Axiom forallIntG  : NativeInt.Int -> (NativeInt.Int -> bool) -> bool.
Extract Inlined Constant forallIntG => "Forall.forall_int".

Axiom forallInt2G : NativeInt.Int -> (NativeInt.Int -> NativeInt.Int -> bool) -> bool.
Extract Inlined Constant forallInt2G => "Forall.forall_int2".

Section Trust.

(* Axiom 1: Equality of integer is embedded within Coq's propositional equality: *)
Axiom eqIntP : Equality.axiom NativeInt.eq.

(* Axiom 2: If a property is true for all integers, then it is
   propositionally true. We restrict to boolean properties *)
Axiom forallIntP : forall w (P : pred _),
    reflect (forall x, P x) (forallIntG w P).

Axiom forallInt2P : forall w (P : _ -> _ -> bool),
    reflect (forall x y, P x y) (forallInt2G w P).

End Trust.

Axiom assertion : bool -> bool.
Extract Constant assertion =>
  "fun b -> if b then (Gc.print_stat stderr; b) else failwith ""Test failure""".

Module Make (WS: WORDSIZE).

Definition w := WS.wordsize.

Definition Int  := NativeInt.Int.
Definition eq   := NativeInt.eq.
Definition zero := NativeInt.zero.
Definition one  := NativeInt.one.
Definition lor  := NativeInt.lor.
Definition land := NativeInt.land.
Definition lsr  := NativeInt.lsr.
Definition lxor := NativeInt.lxor.

Definition wordsize := bitsToInt (bitn 63 WS.wordsize).

Definition bitmask := ((1 :<<: wordsize) - 1: Int)%C.

Definition mask_unop  (f : Int -> Int) x := (bitmask && f x)%C.
Definition mask_binop (f : Int -> Int -> Int) x y := (bitmask && f x y)%C.

Definition lnot := mask_unop NativeInt.lnot.
Definition opp  := mask_unop NativeInt.opp.

Definition lsl := mask_binop NativeInt.lsl.
Definition add := mask_binop NativeInt.add.
Definition sub := mask_binop NativeInt.sub.

Definition forallInt  := forallIntG wordsize.
Definition forallInt2 := forallInt2G wordsize.

Definition forallSeq (p : pred bitseq) := all p (all_seqs [:: true; false] w).


(** ** Cancelativity of bitsFromInt *)

(* Validation condition:
   Experimentally, [bitsToInt] must be cancelled by [bitsFromInt] *)
Definition bitsToIntK_test :=
  forallSeq (fun s => eqseqb (bitsFromInt w (bitsToInt s)) s).

(* This was the previous condition: *)
(*
Definition test_bitsToIntK :=
  forallInt (fun s => (bitsToInt (bitsFromInt n s) == s)%C).
*)

Axiom bitsToIntK_valid : bitsToIntK_test.

Lemma bitsToIntK (b: 'B_w) : bitsFromInt w (bitsToInt b) = b.
Proof.
by have/forall_bitP/(_ b) := bitsToIntK_valid; rewrite -eqseqR => /eqP.
Qed.

(** * Injectivity of [bitsFromInt] *)

(* Emilio: this seems more expensive than just doing the test. *)
(* Pierre: which test? *)

Definition bitsFromInt_inj_test: bool :=
  forallInt2 (fun x y =>
      (eqseqb (bitsFromInt w x) (bitsFromInt w y)) ==> eq x y).

Axiom bitsFromInt_inj_valid: bitsFromInt_inj_test.

Lemma bitsFromInt_inj: injective (bitsFromInt w).
Proof.
  move=> x y /eqP H.
  have Hseq: eqseqb (bitsFromInt w x) (bitsFromInt w y)
    by rewrite -eqseqR; move/eqP: H=> -> //.
  clear H.
  apply/eqIntP.
  move: Hseq; apply/implyP.
  move: x y; apply/forallInt2P.
  by apply bitsFromInt_inj_valid.
Qed.

Lemma bitsFromIntK: cancel (bitsFromInt w) bitsToInt.
Proof.
  move=> i.
  suff: bitsFromInt w (bitsToInt (bitsFromInt w i)) = bitsFromInt w i
    by apply bitsFromInt_inj.
  apply bitsToIntK.
Qed.

(** * Representation tests *)

(** We say that an [n : Int] is the representation of a bit sequence
    [bs : bitseq] if they satisfy the axiom [Rnative]. Morally, it
    means that both represent the same number. *)

Definition Tnative (i: Int) (bs: bitseq) : bool := (i == bitsToInt bs)%C.

(** ** Individuals *)

Open Scope bits_scope.

Definition zero_test : bool := (Tnative zero ('0_WS.wordsize))%C.
Axiom zero_valid: zero_test.

Definition one_test : bool := (Tnative one (bitn w 1))%C.
Axiom one_valid: one_test.

(** ** Logical operators *)

Definition lnot_test: bool
  := forallInt (fun i =>
       Tnative (lnot i) (negs (bitsFromInt w i))).

Axiom lnot_valid: lnot_test.

Definition land_test: bool
  := forallInt2 (fun i i' =>
         Tnative (land i i')
                 (ands (bitsFromInt w i) (bitsFromInt w i'))).

Axiom land_valid: land_test.

Definition lor_test: bool
  := forallInt2 (fun i i' =>
         Tnative (lor i i')
                 (ors (bitsFromInt w i) (bitsFromInt w i'))).

Axiom lor_valid: lor_test.

Definition lxor_test: bool
  := forallInt2 (fun i i' =>
         Tnative (lxor i i')
                 (xors (bitsFromInt w i) (bitsFromInt w i'))).

Axiom lxor_valid: lxor_test.

Definition lsr_test: bool
  := forallInt2 (fun i i' =>
         let n := nats (bitsFromInt w i') in
         (n <= w) ==>
         Tnative (lsr i i') 
                 (shrs (bitsFromInt w i) n)).

Axiom lsr_valid: lsr_test.

Definition lsl_test: bool
  := forallInt2 (fun i i' =>
          let n := nats (bitsFromInt w i') in 

          (* XXX: in fact, we need [n <= 64] (as opposed to [n <= w])
             since Ocaml's [lsl] is unspecified beyond 64 *)

          (n <= w) ==> 
           Tnative (lsl i i')
                   (shls (bitsFromInt w i) n)).

Axiom lsl_valid: lsl_test.


(** ** Arithmetic *)

Definition opp_test: bool
  := forallInt (fun i =>
         Tnative (opp i) 
                 (opps_eff w (bitsFromInt w i))).

Axiom opp_valid: opp_test.

Definition sub_test: bool
  := forallInt2 (fun i j =>
         Tnative (sub i j) 
                 (subs_eff w (bitsFromInt w i) (bitsFromInt w j))).

Axiom sub_valid: sub_test.

 
Definition add_test: bool
  := forallInt2 (fun i j =>
         Tnative (add i j)
                 (adds_eff w (bitsFromInt w i) (bitsFromInt w j))).

Axiom add_valid: add_test.

(** * Tests extraction *)

(** All the tests should return true! *)

Definition allb s := foldr (andb) true s.

Definition binop_tests x bitsX y bitsY :=
  allb
    [:: (bitsX == bitsY) ==> (eq x y) 
    ;   Tnative (land x y) (ands bitsX bitsY) 
    ;   Tnative (lor x y) (ors bitsX bitsY) 
    ;   Tnative (lxor x y) (xors bitsX bitsY) 
    ;   Tnative (add x y) (adds_eff w bitsX bitsY)
    ;   Tnative (sub x y) (subs_eff w bitsX bitsY)].

Definition shift_tests x toNatX y bitsY :=
  allb
    [:: Tnative (lsr y x) (shrs bitsY toNatX) 
    ;   Tnative (lsl y x) (shls bitsY toNatX)].

Definition unop_tests x :=
  let bitsX := bitsFromInt w x in
  let toNatX := nats bitsX in
  allb
    [:: Tnative (lnot x) (negs bitsX) 
    ;   Tnative (opp x) (opps_eff w bitsX) 
    ;   if (toNatX <= w) then
          forallInt (fun y =>
            let bitsY := bitsFromInt w y in
            allb
              [:: binop_tests x bitsX y bitsY
              ;   shift_tests x toNatX y bitsY ])
        else
          forallInt (fun y => 
             binop_tests x bitsX y (bitsFromInt w y))].


Definition tests
  := assertion 
       (allb
          [:: bitsToIntK_test 
          ;   zero_test 
          ;   one_test 
          ;   forallInt (fun x => unop_tests x)]).

(* XXX: show that [tests_valid] implies each individual "axiom" *)

(*
Definition tests
  := assertion (all id
       [:: bitsToIntK_test
        ; bitsFromInt_inj_test
        ; zero_test
        ; one_test 
        ; lnot_test
        ; land_test
        ; lor_test
        ; lxor_test
        ; lsr_test
        ; lsl_test
        ; opp_test
        ; sub_test
        ; add_test
       ]).
*)

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

