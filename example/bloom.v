From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.
From mathcomp
Require Import choice fintype finset tuple matrix.
From CoqEAL
Require Import hrel param refinements.
From Coq
Require Import Relation_Operators Lexicographic_Product Wf_nat.

Require Import bitseq bitword bitset notation bits.

Import Refinements.Op.
Import Logical.Op.
Import Sets.Op.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition w := 32.
Definition T := [finType of 'I_w].

Module Fintype : FINTYPE with Definition T := T.
  Definition T: finType := T.
End Fintype.

Module R  := Make(Fintype).
Module Native := R.Native.

(** * Parametric definition *)

Section Bloom_parametric.

Variables (S : Type)
          (P: Type)
          (I : Type).

Context `{eq_of S}.
Context `{union_of S}.
Context `{inter_of S}.
Context `{singleton_of I S}.
Context `{empty_of S}.

Local Open Scope computable_scope.

(* =bloomsig= *)
Fixpoint bloomSig_aux (H: seq (P -> I))(e: P)(filter: S): S
 := match H with
    | [::] => filter
    | h :: H => bloomSig_aux H e ([SET (h e) ] :|: filter) 
    end.

Definition bloomSig (H: seq (P -> I))(e: P): S
 := bloomSig_aux H e SET0.
(* =end= *)

(* =bloomadd= *)
Definition bloomAdd (H: seq (P -> I))(add_elt: P)(filter: S): S
 := filter :|: bloomSig H add_elt.
(* =end= *)

(* =bloomcheck= *)
Definition bloomCheck (H: seq (P -> I))(e: P)(filter: S) : bool
 := let sig := bloomSig H e in (sig :&: filter == sig)%C.
(* =end= *)

End Bloom_parametric.

Parametricity bloomSig_aux.
Parametricity bloomSig.
Parametricity bloomAdd.
Parametricity bloomCheck.

Section Refinements.

(* We are can choose any (related) list of hashing functions. *)
Variable Q: Type.
Variable hSpec: seq (Q -> T).
Variable hImpl: seq (Q -> Native.Int).
Variable hash_spec: refines (list_R (@Logic.eq Q ==> R.Rbits))%rel hSpec hImpl.

Local Instance hash_Rbits: 
  refines (list_R (@Logic.eq Q ==> R.Rbits))%rel hSpec hImpl 
  := hash_spec.

Local Instance refl_Q (x : Q) : refines Logic.eq x x.
Proof. by rewrite refinesE //. Qed.

Local Instance bloomSig_aux_Rbitset: 
  refines ((list_R (@Logic.eq Q ==> R.Rbits)) ==> @Logic.eq Q ==> R.Rbitset ==> R.Rbitset)%rel
          (bloomSig_aux (I := T))
          (bloomSig_aux (I := Native.Int)).
Proof. 
param (bloomSig_aux_R (P_R := @Logic.eq Q)(S_R := R.Rbitset)(I_R := R.Rbits)).
Qed.

Local Instance bloomSig_Rbitset:
  refines ((list_R (@Logic.eq Q ==> R.Rbits)) ==> @Logic.eq Q ==> R.Rbitset)%rel
          (bloomSig (I := T))
          (bloomSig (I := Native.Int)).
Proof.
param (bloomSig_R (P_R := @Logic.eq Q)(S_R := R.Rbitset)(I_R := R.Rbits)).
Qed.

Local Instance bloomAdd_Rbitset:
  refines ((list_R (@Logic.eq Q ==> R.Rbits)) ==> @Logic.eq Q ==> R.Rbitset ==> R.Rbitset)%rel
          (bloomAdd (I := T)) 
          (bloomAdd (I := Native.Int)).
Proof.
param (bloomAdd_R (P_R := @Logic.eq Q)(S_R := R.Rbitset)(I_R := R.Rbits)).
Qed.

Local Instance bloomCheck_Rbitset:
  refines ((list_R (@Logic.eq Q ==> R.Rbits)) ==> @Logic.eq Q ==> R.Rbitset ==> bool_R)%rel
          (bloomCheck (I := T)) 
          (bloomCheck (I := Native.Int)).
Proof.
param (bloomCheck_R (P_R := @Logic.eq Q)(S_R := R.Rbitset)(I_R := R.Rbits)).
Qed.

End Refinements.

Section Correctness.

Variables (Q : Type)
          (H : seq (Q -> T)).

(* =bloom_correct= *)
Lemma bloom_correct: forall (add check: Q)(bset: {set T}), 
  (~ bloomCheck H check (bloomAdd H add bset)) ->
    (~ bloomCheck H check bset) /\ (add <> check).
(* =end= *)
Proof.
  Local Arguments inter_op /.
  Local Arguments inter_fin /.
  Local Arguments union_op /.
  Local Arguments union_fin /.
  Local Arguments eq_op /.
  Local Arguments eq_fin /.
  Arguments bloomCheck /.

  move=> add check T Hyp.
  split.
  - move=> Habs; apply: Hyp=> /=.
    rewrite setIUr.
    rewrite /bloomCheck /inter_op /inter_fin in Habs.
    move/eqP: Habs => ->.
    apply/eqP/setUidPl.
    by apply subsetIl.
  - move=> Habs.
    rewrite Habs in Hyp.
    apply Hyp.
    rewrite /bloomCheck /bloomAdd; simpC. 
    rewrite eqEsubset.
    apply /andP; split.
    + by apply subsetIl.
    + rewrite subsetI.
      apply /andP; split=> //.
      by apply subsetUr.
Qed.

End Correctness.


Definition bloom_add_int
  := bloomAdd (S := Native.Int)(P := Native.Int)(I := Native.Int).
Definition bloom_check_int
  := bloomCheck (S := Native.Int)(P := Native.Int)(I := Native.Int).


Cd "example".

Require Import ExtrOcamlBasic.

Extraction "bloom.ml" bloom_add_int bloom_check_int.

Cd "..".
