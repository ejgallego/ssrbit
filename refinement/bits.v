From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.
From mathcomp
Require Import choice fintype finset tuple finfun.
From CoqEAL
Require Import hrel param refinements.

Require Import bitseq bitword notation axioms.

Import Refinements.Op.
Import Logical.Op.
Import Sets.Op.


Local Open Scope rel_scope.
Local Open Scope bits_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



(**

 The refinement relations have a type of the following form

<<
   R : specification -> implementation -> Type
>>

  while the transport lemmas have the form

<<
   Lemma R_op: refines refinement_relation specification implementation.
>>

*)


(************************************************************************)
(** * Refinement Relations                                                 *)
(************************************************************************)

Require Import bitset.

Parameter T: finType.

Definition Rfin (A: {set T})(b: 'B_#| T |): Type  := A = [set x : T | b`_(enum_rank x)].

Definition Rword {n} : word n -> 'B_n -> Type := fun_hrel (@wrdB n).
Definition Rtuple {n} : 'B_n -> bitseq -> Type. Admitted. (* := fun_hrel val. *)

Definition Rnat: nat -> bitseq -> Type := fun_hrel nats.
Definition Renum: T -> nat -> Type. Admitted.
Definition Rord: T -> 'B_#| T | -> Type := Renum \o Rnat.

(** ** Refinement from bit sequences to machines words *)

Parameter w: nat.

Module Wordsize.
  Definition wordsize := w.
End Wordsize.
Module Native := Make(Wordsize).

Definition Rnative: bitseq -> Native.Int -> Type := fun_hrel (bitsFromInt Native.w).

(* "small" integers (ie. less than the word size) for shifts *)
CoInductive Ridx: nat -> Native.Int -> Type := 
  Ridx_spec (n: nat)(i: Native.Int) of 
    (n <= Native.w)%N
  & bitsFromInt Native.w i = bitn Native.w n : Ridx n i.

(************************************************************************)
(** * From machine words to bit sequences                               *)
(************************************************************************)

Global Instance Rnative_eq:
  refines (Rnative ==> Rnative ==> param.bool_R)%rel (eqtype.eq_op) Native.eq.
Proof.
  rewrite !refinesE => bs1 w1 <- bs2 w2 <-.
  suff -> : Native.eq w1 w2 = (bitsFromInt w w1 == bitsFromInt w w2)
    by exact: bool_Rxx.
  apply/eqIntP/eqP => [->//|]; exact: Native.bitsFromInt_inj.
Qed.

Global Instance Rnative_zero: refines Rnative '0_w Native.zero.
Proof. 
  rewrite refinesE. 
  have /eqIntP -> := Native.zero_valid.
  by rewrite /Rnative/fun_hrel Native.bitsToIntK. 
Qed.

Global Instance Rnative_one: refines Rnative (bitn w 1) Native.one.
Proof. 
  rewrite refinesE. 
  have /eqIntP -> := Native.one_valid.
  by rewrite /Rnative/fun_hrel Native.bitsToIntK. 
Qed.

Global Instance Rnative_lnot:
  refines (Rnative ==> Rnative) negs Native.lnot.
Proof.
  rewrite refinesE=> bs w <-.
  have /forallIntP /(_ w) /eqIntP -> := Native.lnot_valid.
  by rewrite /Rnative/Native.Tnative/fun_hrel Native.bitsToIntK.
Qed.

Global Instance Rnative_land:
  refines (Rnative ==> Rnative ==> Rnative) ands Native.land.
Proof.
  rewrite !refinesE => bs1 w1 <- bs2 w2 <-.
  have /forallIntP /(_ w1) /forallIntP /(_ w2) /eqIntP -> := Native.land_valid.
  by rewrite /Rnative/fun_hrel Native.bitsToIntK.
Qed.

Global Instance Rnative_lor: 
  refines (Rnative ==> Rnative ==> Rnative) ors Native.lor.
Proof.
  rewrite !refinesE => bs1 w1 <- bs2 w2 <-.
  have /forallIntP /(_ w1) /forallIntP /(_ w2) /eqIntP -> := Native.lor_valid.
  by rewrite /Rnative/fun_hrel Native.bitsToIntK.
Qed.

Global Instance Rnative_lxor: 
  refines (Rnative ==> Rnative ==> Rnative) xors Native.lxor.
Proof.
  rewrite !refinesE => bs1 w1 <- bs2 w2 <-.
  have /forallIntP /(_ w1) /forallIntP /(_ w2) /eqIntP -> := Native.lxor_valid.
  by rewrite /Rnative/fun_hrel Native.bitsToIntK.
Qed.

Global Instance Rnative_lsr: 
  refines (Rnative ==> Ridx ==> Rnative) shrs Native.lsr.
Proof.
  rewrite !refinesE => bs1 w1 <- _ _ [n i Hn Hi].
  have H : nats (bitsFromInt Native.w i) = n
    by rewrite Hi bitnK; 
       try (eapply leq_ltn_trans, ltn_expl).
  subst n.
  have /forallIntP /(_ w1) /forallIntP /(_ i) /implyP /(_ Hn) /eqIntP -> := Native.lsr_valid.
  by rewrite /Rnative/fun_hrel Native.bitsToIntK.
Qed.

Global Instance Rnative_lsl: 
  refines (Rnative ==> Ridx ==> Rnative) shls Native.lsl.
Proof.
  rewrite !refinesE => bs1 w1 <- _ _ [n i Hn Hi].
  have H : nats (bitsFromInt Native.w i) = n
    by rewrite Hi bitnK; 
       try (eapply leq_ltn_trans, ltn_expl).
  subst n.
  have /forallIntP /(_ w1) /forallIntP /(_ i) /implyP /(_ Hn) /eqIntP -> := Native.lsl_valid.
  by rewrite /Rnative/fun_hrel Native.bitsToIntK.
Qed.

(************************************************************************)
(** * From finset to bit word                                           *)
(************************************************************************)

Lemma eq_bool_R x y : x = y -> bool_R x y.
Proof. by move->; apply/bool_Rxx. Qed.

Global Instance Rfin_eq:
  refines (Rfin ==> Rfin ==> param.bool_R) eq_op eq_op.
Proof.
  rewrite refinesE=> E bs -> E' bs' ->.
  apply/eq_bool_R.

  have: [set x : T | bs`_(enum_rank x)] == [set x | bs'`_(enum_rank x)] <-> bs == bs'.
  split.
  - move/eqP/setP=> H.
    apply/eqP/eq_from_tnth=> x.
    move/(_ (enum_val x)): H.
    by rewrite !in_set !enum_valK -!tnth_nth.
  - by move/eqP=> -> ; apply/eqP/setP=> //=.

Admitted.


(* XXX: re-prove these theorems. *)
(* XXX: rename to follow convention *)
Lemma andB_mask1:
  forall n (bs: 'B_n.+1),
    (andB bs 1 = if bs`_0 then 1 else 0)%C.
Admitted.

Lemma getBit_shrBn:
  forall n (bs: 'B_n) k k', k + k' < n ->
    (shrB bs k)`_k' = bs`_(k + k').
Admitted.

Global Instance Rfin_get: 
  refines (Rord ==> Rfin ==> param.bool_R) get_op get_op.
Proof.
  rewrite refinesE=> k bs1 [n [Rkn Rnbs1]] E bs2 -> /=.
Admitted.
(*
  case eq:(k < n.+1).
  - rewrite /Rord/fun_hrel in Hbs1.
    apply f_equal with (f := nats) in Hbs1.
    rewrite bitnK in Hbs1; last by admit.
    rewrite Hbs1 in eq.
    rewrite /get/and_op/and_Bits/shr_op/shr_Bits andB_mask1 getBit_shrBn addn0;
      last by apply eq.
    rewrite -Hbs1=> //.
    rewrite /Rfin/fun_hrel in HE.
    apply f_equal with (f := @setB _) in HE.
    rewrite setnK in HE.
    rewrite HE.
    rewrite setb_def.
    rewrite in_set.
    case: (bs2`_k)=> //=.
    have //= ->: (B1 == B1) by move=> m; apply/eqP=> //.
      by apply bool_Rxx.
  - have H:= leq_total k n.
    rewrite -ltnS in H.
    rewrite eq in H.
    rewrite /= in H.

Qed.
*)



Global Instance Rfin_singleton:
    refines (Rord ==> Rfin) singleton_op singleton_op.
Admitted.
(*
Proof.
  rewrite refinesE=> bs k Hbsk.
  rewrite /Rfin -setP 
          /singleton_op/singleton_Finset/singleton_Bitset
          /singleton/one_op/one_Bits/shl_op/shl_Bits Hbsk /eq_mem=> x.
  rewrite !in_set.
  case x_eq_k: (x == k).
  + (* x == k *)
    move/eqP: x_eq_k ->.
    by rewrite getBit_shlBn_true.
  + (* x <> k *)
    rewrite getBit_shlBn_false //.
    apply not_eq_sym=> x_is_k.
    move/eqP: x_eq_k=>x_eq_k.
    apply x_eq_k.
    by apply ord_inj.
Qed.
*)

Global Instance Rfin_compl: 
  refines (Rfin ==> Rfin) compl_op compl_op.
Admitted.
(*
Proof.
  rewrite refinesE /Rfin=> bs E HE.
  rewrite -setP /eq_mem=> x.
  by rewrite in_setC HE !in_set getBit_liftUnOp.
Qed.
*)


Global Instance Rfin_full: 
  refines Rfin full_op full_op.
Admitted.
(*
Proof.
  Local Arguments full_op /.
  Local Arguments full_Finset /.
  Local Arguments full_Bitset /.

  rewrite refinesE.
  rewrite /Rfin /= -setP /eq_mem=> x.
  rewrite !in_set.
  rewrite /sub_op/sub_Bits/sub/zero_op/zero_Bits.
  by rewrite subB1 -fromNat0 -makeOnes getBit_ones=> //.
Qed.
*)


Global Instance Rfin_empty: 
  refines Rfin empty_op empty_op.
Admitted.
(*
Proof.
  Local Arguments empty_op /.
  Local Arguments empty_Finset /.
  Local Arguments empty_Bitset /.
  Local Arguments zero_op /.
  Local Arguments zero_Bits /.
  Local Arguments create /.

  rewrite refinesE //= /Rfin -setP /eq_mem=> i.
  by rewrite in_set in_set0 /empty_op/empty_Bitset/create -fromNat0 getBit_zero.
Qed.
*)


Global Instance Rfin_insert:
  refines (Rord ==> Rfin ==> Rfin) set_op set_op.
Admitted.
(*
Proof.
  rewrite refinesE.
  move=> bs k Hbsk bs' E HE /=.
  rewrite /Rfin -setP /eq_mem=> x.
  rewrite /set_op/set_Finset/set_Bitset
          /insert/one_op/one_Bits/or_op/or_Bits/shl_op/shl_Bits.
  rewrite in_set Hbsk getBit_set_true=> //.
  rewrite fun_if.
  case H: (x == k).
    + (* Case: x == k *)
      move/eqP: H ->.
      by rewrite eq_refl setU11.
    + (* Case: x <> k *)
      rewrite ifF=> //.
      by rewrite in_setU1 H HE in_set.
Qed.
*)

Global Instance Rfin_remove:
  refines (Rfin ==> Rord ==> Rfin) remove_op remove_op.
Admitted.
(*
Proof.
  rewrite refinesE.
  move=> bs E HE bs' k Hbsk.
  rewrite /Rfin -setP /eq_mem=> x.
  rewrite /remove_op/remove_Bitset/remove/and_op/and_Bits/shl_op/shl_Bits Hbsk.
  rewrite in_set getBit_set_false=> //.
  rewrite fun_if.
  case H: (x == k).
    + (* Case: x == k *)
      move/eqP: H ->.
      rewrite ifT=> //.
      by rewrite setD11.
    + (* Case: x <> k *)
      rewrite ifF=> //.
      by rewrite in_setD1 H HE in_set.
Qed.
*)


Global Instance Rfin_inter:
  refines (Rfin ==> Rfin ==> Rfin) inter_op inter_op.
Admitted.
(*
Proof.
  rewrite refinesE.
  move=> bs E HE bs' E' HE'.
  rewrite /Rfin -setP /eq_mem=> x.
  by rewrite in_setI /inter /andB HE HE' !in_set getBit_liftBinOp.
Qed.
*)


Global Instance Rfin_union:
  refines (Rfin ==> Rfin ==> Rfin) union_op union_op.
Admitted.
(*
Proof.
  rewrite refinesE.
  move=> bs E HE bs' E' HE'.
  rewrite /Rfin -setP /eq_mem=> x.
  by rewrite in_setU /union /orB HE HE' !in_set getBit_liftBinOp.
Qed.
*)

Global Instance Rfin_symdiff:
  refines (Rfin ==> Rfin ==> Rfin) symdiff_op symdiff_op.
Admitted.
(*
Proof.
  rewrite refinesE.
  move=> bs E HE bs' E' HE'.
  rewrite /Rfin -setP /eq_mem=> x /=.
  rewrite in_setU !in_setD.
  rewrite /symdiff /xorB HE HE' !in_set getBit_liftBinOp=> //.
  case: (getBit bs x)=> //.
  + (* getBit bs x = true *)
    by rewrite andbT orbF Bool.xorb_true_l.
  + (* getBit bs x = false *)
    by rewrite andbF orbC orbF andbC andbT Bool.xorb_false_l.
Qed.
*)


Global Instance Rfin_subset:
  refines (Rfin ==> Rfin ==> bool_R) subset_op subset_op.
Admitted.
(*
Proof.
  rewrite refinesE=> bs E HE bs' E' HE'.
  rewrite /subset_op/subset_Bitset/subset_Finset/subset.
  have ->: E \subset E' = (E :&: E' == E).
  apply/setIidPl/eqP=> //=.
  eapply refinesP; tc.
Qed.
*)
