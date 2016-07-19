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

Definition Rfin: {set T} -> 'B_#| T | -> Type  := fun_hrel (@finB T). 

CoInductive Rord: T -> 'B_#| T | -> Type := 
  Rord_spec (t: T)(bs: 'B_#| T |)(k: 'I_#| T |) of
      t = enum_val k 
    & bs = [tuple of bitn #| T | k ] : Rord t bs.

Definition Rtuple: 'B_#| T | -> bitseq -> Type :=  fun a b => val a = b.

(* Definition Rnat: nat -> bitseq -> Type := fun_hrel nats. *)
(* Definition Rword {n} : word n -> 'B_n -> Type := fun_hrel (@wrdB n). *)

(** ** Refinement from bit sequences to machines words *)

Module Wordsize.
  Definition wordsize := #| T |.
End Wordsize.
Module Native := Make(Wordsize).

Definition Rnative: bitseq -> Native.Int -> Type := fun_hrel (bitsFromInt Native.w).

Definition Rbitset: {set T} -> Native.Int -> Type :=
  Rfin \o Rtuple \o Rnative.

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
  suff -> : Native.eq w1 w2 = (bitsFromInt Native.w w1 == bitsFromInt Native.w w2)
    by exact: bool_Rxx.
  apply/eqIntP/eqP => [->//|]; exact: Native.bitsFromInt_inj.
Qed.

Global Instance Rnative_zero: refines Rnative '0_Native.w Native.zero.
Proof. 
  rewrite refinesE. 
  have /eqIntP -> := Native.zero_valid.
  by rewrite /Rnative/fun_hrel Native.bitsToIntK. 
Qed.

Global Instance Rnative_one: refines Rnative (bitn Native.w 1) Native.one.
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
(** * From finset to bit vectors                                        *)
(************************************************************************)

Lemma eq_bool_R x y : x = y -> bool_R x y.
Proof. by move->; apply/bool_Rxx. Qed.

Lemma mem_can_imset (aT rT: finType)(f: aT -> rT)(A: {set aT}) y:
  injective f -> f y \in [set f x | x in A ] = (y \in A).
Proof.
  move=> Hinj.
  apply/imsetP/idP=> [[a Ha Hfeq] | H].
  - rewrite (Hinj _ _ Hfeq) //=.
  - exists y=> //.
Qed.

Let can_enum D := can2_imset_pre D (@enum_valK T) (@enum_rankK _).
Let enum_can D := can2_imset_pre D (@enum_rankK T) (@enum_valK _).


Global Instance Rfin_eq:
  refines (Rfin ==> Rfin ==> param.bool_R) eq_op eq_op.
Proof.
  rewrite refinesE=> E bs <- E' bs' <-.
  apply/eq_bool_R.
  apply/eqP/eqP=> [|-> //].
  apply: (can_inj (@bitFK _)).
Qed.

Global Instance Rfin_get: 
  refines (Rord ==> Rfin ==> param.bool_R) get_op get_op.
Proof.
  rewrite refinesE => _ _ [t bs1 k Htk Hbs1k] E2 bs2 <- .
  apply eq_bool_R.
  rewrite /finB/get_op/get_fin/get_B Htk mem_can_imset ?mem_setb; 
    last by apply (can_inj (@enum_valK _)).
  rewrite /get /one_op /one_B /zero_op /zero_B /shl_op /shl_B
          /eq_op /eq_B /and_op/and_B.
  rewrite gets_def Hbs1k bitnK; 
    last by (eapply leq_ltn_trans; 
             [ apply ltnW, ltn_ord 
             | apply: ltn_expl ]).
  by rewrite -val_eqE !size_tuple -bitn_zero.
Qed.

Global Instance Rfin_singleton:
    refines (Rord ==> Rfin) singleton_op singleton_op.
Proof.
  rewrite refinesE => _ _ [t bs k Ttk Hbsk].
  rewrite /Rfin/fun_hrel/singleton_op/singleton_B/singleton_fin/singleton.
  rewrite /shl_op/shl_B.
  rewrite /one_op/one_B.
  rewrite /finB.
(* XXX: waiting for Emilio's characterisation of bitset *)
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

Global Instance Rfin_full: 
  refines Rfin full_op full_op.
Proof.
rewrite refinesE.
rewrite /full_op/full_B/full_fin/create/Rfin/fun_hrel
        /finB/zero_op/zero_B/sub_op/sub_B/one_op/one_B.
(* XXX: Emilio *)
Admitted.
(* apply/setP=> t. *)
(* by rewrite can_enum inE mem_setb nth_nseq ltn_ord inE. *)
(* Qed. *)

Global Instance Rfin_empty: 
  refines Rfin empty_op empty_op.
Proof.
rewrite refinesE.
rewrite /empty_op/empty_B/empty_fin/create/Rfin/fun_hrel
        /finB/zero_op/zero_B/sub_op/sub_B/one_op/one_B.
apply/setP=> t.
by rewrite can_enum inE mem_setb nth_nseq ltn_ord inE.
Qed.

Global Instance Rfin_insert:
  refines (Rord ==> Rfin ==> Rfin) set_op set_op.
(* XXX: waiting for Emilio's characterisation of bit set *)
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
(* XXX: waiting for Emilio's characterisation of bit set *)
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


Global Instance Rfin_compl: 
  refines (Rfin ==> Rfin) compl_op compl_op.
Proof. 
rewrite refinesE => E bs <-.
by rewrite /Rfin /fun_hrel Fcompl_morphL.
Qed.

Global Instance Rfin_union:
  refines (Rfin ==> Rfin ==> Rfin) union_op union_op.
Proof.
rewrite refinesE => E1 bs1 <- E2 bs2 <- .
by rewrite /Rfin /fun_hrel Funion_morphL.
Qed.

Global Instance Rfin_inter:
  refines (Rfin ==> Rfin ==> Rfin) inter_op inter_op.
Proof.
rewrite refinesE => E1 bs1 <- E2 bs2 <- .
by rewrite /Rfin /fun_hrel Finter_morphL.
Qed.

Global Instance Rfin_symdiff:
  refines (Rfin ==> Rfin ==> Rfin) symdiff_op symdiff_op.
Proof.
rewrite refinesE => E1 bs1 <- E2 bs2 <- .
by rewrite /Rfin /fun_hrel Fsymdiff_morphL.
Qed.

Global Instance Rfin_subset:
  refines (Rfin ==> Rfin ==> bool_R) subset_op subset_op.
Proof.
rewrite refinesE => E1 bs1 <- E2 bs2 <- .
apply eq_bool_R.
rewrite /subset_op/subset_fin/subset_B/subset.
apply/setIidPl/idP.
- rewrite -Finter_morphL=> H.
  apply/eqP. 
  by apply: (can_inj (@bitFK _))=> //.
- rewrite -Finter_morphL=> /eqP {2}<- //. 
Qed.
