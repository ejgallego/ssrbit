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

Module Wordsize.
  Definition wordsize := #| T |.
End Wordsize.
Module Native := Make(Wordsize).


(** ** From sets over a finite type to machine words: *)

(* =Rfin= *)
Definition Rfin: {set T} -> 'B_#| T | -> Type
  := fun_hrel (@finB T). 
(* =end= *)
(* =Rtuple= *)
Definition Rtuple: 'B_#| T | -> bitseq -> Type
  :=  fun a b => val a = b.
(* =end= *)
(* =Rnative= *)
Definition Rnative: bitseq -> Native.Int -> Type
  := fun_hrel (bitsFromInt Native.w).
(* =end= *)

(* =Rbitset= *)
Definition Rbitset: {set T} -> Native.Int -> Type
  := Rfin \o (Rtuple \o Rnative).
(* =end= *)

(** ** From finite type to machine words: *)

(* =Rord= *)
Definition Rord: T -> 'I_#| T | -> Type
  := fun t n => enum_rank t = n.
(* =end= *)
(* =RidxI= *)
Definition RidxI: 'I_#| T | -> nat -> Type
  := fun k n => val k = n.
(* =end= *)
(* =RidxN= *)
CoInductive RidxN: nat -> Native.Int -> Type := 
  Ridx_spec (k: nat)(i: Native.Int)(b: bitseq) of 
    Rnative b i
  & (k <= #| T |)%N
  & b = bitn #| T | k : RidxN k i.
(* =end= *)

(* =Rbits= *)
Definition Rbits: T -> Native.Int -> Type :=
  Rord \o (RidxI \o RidxN).
(* =end= *)


(************************************************************************)
(** * Notations                                                         *)
(************************************************************************)

(** ** Notations for native integers *)

Global Instance   eq_N : eq_of   Native.Int := Native.eq.
Global Instance zero_N : zero_of Native.Int := Native.zero.
Global Instance  one_N : one_of  Native.Int := Native.one.
Global Instance   or_N : or_of   Native.Int := Native.lor.
Global Instance  shl_N : shl_of  Native.Int Native.Int := Native.lsl.
Global Instance  and_N : and_of  Native.Int := Native.land.
Global Instance  shr_N : shr_of  Native.Int Native.Int := Native.lsr.
Global Instance  not_N : not_of  Native.Int := Native.lnot.
Global Instance  xor_N : xor_of  Native.Int := Native.lxor.
Global Instance  add_N : add_of  Native.Int := Native.add.
Global Instance  sub_N : sub_of  Native.Int := Native.sub.
Global Instance  opp_N : opp_of  Native.Int := Native.opp.

Global Instance get_N       : get_of Native.Int Native.Int       := get.
Global Instance singleton_N : singleton_of Native.Int Native.Int := singleton.
Global Instance compl_N     : compl_of Native.Int                := compl.
Global Instance full_N      : full_of Native.Int                 := create (Bits := Native.Int) true.
Global Instance empty_N     : empty_of Native.Int                := create (Bits := Native.Int) false.
Global Instance set_N       : set_of Native.Int Native.Int       := insert.
Global Instance remove_N    : remove_of Native.Int Native.Int    := remove.
Global Instance inter_N     : inter_of Native.Int                := inter.
Global Instance union_N     : union_of Native.Int                := union.
Global Instance symdiff_N   : symdiff_of Native.Int              := symdiff.
Global Instance subset_N    : subset_of Native.Int               := subset.

(** ** Notations for bit sequences (of size #| T |) *)

(* These classes are not strictly necessary: the code below would work
without them. *)

Global Instance eq_s   : eq_of bitseq   := fun x y => x == y.
Global Instance zero_S : zero_of bitseq := '0_#| T |.
Global Instance  one_S : one_of  bitseq := bitn #| T | 1.
Global Instance   or_S : or_of   bitseq := ors.
Global Instance  shl_S : shl_of  nat bitseq := shls.
Global Instance  and_S : and_of  bitseq := ands.
Global Instance  shr_S : shr_of  nat bitseq := shrs.
Global Instance  not_S : not_of  bitseq := negs.
Global Instance  xor_S : xor_of  bitseq := xors.
Global Instance  add_S : add_of  bitseq := adds.
Global Instance  sub_S : sub_of  bitseq := subs.

Global Instance get_S       : get_of nat bitseq       := get.
Global Instance singleton_S : singleton_of nat bitseq := singleton.
Global Instance compl_S     : compl_of bitseq            := compl.
Global Instance full_S      : full_of bitseq             := create (Bits := bitseq) true.
Global Instance empty_S     : empty_of bitseq            := create (Bits := bitseq) false.
Global Instance set_S       : set_of nat bitseq       := insert.
Global Instance remove_S    : remove_of nat bitseq    := remove.
Global Instance inter_S     : inter_of bitseq            := inter.
Global Instance union_S     : union_of bitseq            := union.
Global Instance symdiff_S   : symdiff_of bitseq          := symdiff.
Global Instance subset_S    : subset_of bitseq           := subset.


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


Lemma ltn_2ord: forall n (k: 'I_n), k < 2 ^ n.
Proof. 
move=> n k.
apply: leq_ltn_trans; last by apply: ltn_expl.
apply ltnW, ltn_ord.
Qed.

(* =Rfin_get= *)
Global Instance Rfin_get: 
  refines (Rord ==> Rfin ==> param.bool_R)
          (fun k E => k \in E) get.
(* =end= *)
Proof.
  rewrite refinesE => t _ <- E2 bs2 <- .
  apply eq_bool_R.
  rewrite /finB/get_op/get_fin/get_B
          /get /one_op /one_B /zero_op /zero_B /shl_op /shl_B
          /eq_op /eq_B /and_op/and_B.
by rewrite  can_enum inE mem_setb gets_def !size_tuple -val_eqE bitn_zero.
Qed.

Global Instance Rfin_singleton:
    refines (Rord ==> Rfin) singleton_op singleton_op.
Proof.
rewrite refinesE => t _ <-.
apply/setP=> x.
rewrite /Rfin /fun_hrel /finB 
        /singleton_op /singleton_B /singleton_fin /singleton
        /shl_op /shl_B /one_op /one_B.
rewrite !inE can_enum inE mem_setb.
have ->: val (shlB [bits of bitn #|T| 1] (enum_rank t)) = setls '0_#| T | (enum_rank t) true.
by rewrite -[shlB _ _]or0B
             -[orB _ _]/[bits of ors _ (shls (bitn _ _) _) ] /=
             sets_def size_tuple.
rewrite /setls size_tuple ltn_ord nth_set_nth /= gets0 val_eqE.
apply/idP/eqP=> [ | ->  ].
by case: ifP=> /eqP => //= He _; apply: enum_rank_inj.
by rewrite eq_refl.
Qed.

Global Instance Rfin_full: 
  refines Rfin full_op full_op.
Proof.
rewrite refinesE.
rewrite /full_op/full_B/full_fin/create/Rfin/fun_hrel
        /finB/zero_op/zero_B/sub_op/sub_B/one_op/one_B.
Proof.
apply/setP=> t.
by rewrite can_enum inE mem_setb
           -[subB _ _]/(decB _) -one_def
           nth_nseq ltn_ord inE.
Qed.

Global Instance Rfin_empty: 
  refines Rfin empty_op empty_op.
Proof.
rewrite refinesE.
rewrite /empty_op/empty_B/empty_fin/create/Rfin/fun_hrel
        /finB/zero_op/zero_B/sub_op/sub_B/one_op/one_B.
apply/setP=> t.
by rewrite can_enum inE mem_setb nth_nseq ltn_ord inE.
Qed.

(* =Rfin_insert= *)
Global Instance Rfin_insert:
  refines (Rord ==> Rfin ==> Rfin) (fun k E => k |: E) insert.
(* =end= *)
Proof.
rewrite refinesE => t _ <- E bs2 <- .
rewrite /Rfin /fun_hrel /set_op /set_B /set_fin.
rewrite /insert/one_op/one_B/or_op/or_B/shl_op/shl_B.
rewrite /finB.
apply/setP=> x.
rewrite can_enum inE mem_setb.

have ->: val (orB bs2 (shlB [bits of bitn #|T| 1] (enum_rank t))) = setls bs2 (enum_rank t) true
    by rewrite sets_def /= size_tuple.

rewrite /setls size_tuple ltn_ord nth_set_nth /= !inE.
(* XXX: this is not pretty. There must be a better way. *)
case: ifP.
- move=> H.
  have -> : x == t
    by apply/eqP; apply enum_rank_inj;
       rewrite val_eqE in H;
       apply/eqP: H.
  done.
- move=> H.
  have -> // : (x == t) = false
    by apply/eqP=> Hxt;
       rewrite Hxt  eq_refl // in H.
  by rewrite can_enum inE mem_setb.
Qed.

(* =Rfin_remove= *)
Global Instance Rfin_remove:
  refines (Rfin ==> Rord ==> Rfin) (fun A a => A :\ a) remove.
(* =end= *)
Proof.
(* XXX: proof duplication with [Rfin_insert] *)
rewrite refinesE => E bs2 <- t _ <-  .
rewrite /Rfin /fun_hrel /remove_op /remove_B /remove_fin.
rewrite /remove/one_op/one_B/or_op/or_B/shl_op/shl_B.
rewrite /finB.
apply/setP=> x.
rewrite can_enum inE mem_setb.

have ->: val (andB bs2 (negB (shlB [bits of bitn #| T | 1] (enum_rank t)))) = setls bs2 (enum_rank t) false
    by rewrite sets_def /= size_tuple.

rewrite /setls size_tuple ltn_ord nth_set_nth /= !inE.
case: ifP.
- move=> H.
  have -> : x == t
    by apply/eqP; apply enum_rank_inj;
       rewrite val_eqE in H;
       apply/eqP: H.
  done.
- move=> H.
  have -> // : (x == t) = false
    by apply/eqP=> Hxt;
       rewrite Hxt eq_refl // in H.
  by rewrite can_enum inE mem_setb.
Qed.

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

(* =Rnative_lnot= *)
Global Instance Rnative_lnot:
  refines (Rnative ==> Rnative) negs Native.lnot.
(* =end= *)
Proof.
  rewrite refinesE=> bs w <- . rewrite /not_op /not_N.
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
  refines (Rnative ==> RidxN ==> Rnative) shrs Native.lsr.
Proof.
rewrite !refinesE => bs1 w1 <- _ _ [n w2 _ <- Hbnd Hw2n].

have H2bnd: n < 2 ^ #|T|
  by eapply leq_ltn_trans; [ apply Hbnd | apply ltn_expl ].

have Hlt: (nats (bitsFromInt Native.w w2) <= Native.w)%N
  by rewrite Hw2n bitnK // ?inE ?H2bnd.

have /forallIntP /(_ w1) 
     /forallIntP /(_ w2) 
     /implyP    /(_ Hlt) 
     /eqIntP -> := Native.lsr_valid.
by rewrite /Rnative/fun_hrel Native.bitsToIntK Hw2n bitnK ?inE ?H2bnd.
Qed.


Global Instance Rnative_lsl: 
  refines (Rnative ==> RidxN ==> Rnative) shls Native.lsl.
rewrite !refinesE => bs1 w1 <- _ _ [n w2 _ <- Hbnd Hw2n].

have H2bnd: n < 2 ^ #|T|
  by eapply leq_ltn_trans; [ apply Hbnd | apply ltn_expl ].

have Hlt: (nats (bitsFromInt Native.w w2) <= Native.w)%N
  by rewrite Hw2n bitnK // ?inE ?H2bnd.

have /forallIntP /(_ w1) 
     /forallIntP /(_ w2) 
     /implyP    /(_ Hlt) 
     /eqIntP -> := Native.lsl_valid.
by rewrite /Rnative/fun_hrel Native.bitsToIntK Hw2n bitnK ?inE ?H2bnd.
Qed.

Global Instance Rnative_add:
  refines (Rnative ==> Rnative ==> Rnative) adds Native.add.
Proof.
rewrite !refinesE => bs1 w1 <- bs2 w2 <-.
have /forallIntP /(_ w1) 
     /forallIntP /(_ w2) 
     /eqIntP ->  := Native.add_valid.
by rewrite /Rnative/fun_hrel Native.bitsToIntK.
Qed.

Global Instance Rnative_sub:
  refines (Rnative ==> Rnative ==> Rnative) subs Native.sub.
Proof.
rewrite !refinesE => bs1 w1 <- bs2 w2 <-.
have /forallIntP /(_ w1) 
     /forallIntP /(_ w2) 
     /eqIntP ->  := Native.sub_valid.
by rewrite /Rnative/fun_hrel Native.bitsToIntK.
Qed.

Global Instance Rnative_opp:
  refines (Rnative ==> Rnative) opps Native.opp.
Proof.
rewrite !refinesE => bs w <- .
have /forallIntP /(_ w) 
     /eqIntP ->  := Native.opp_valid.
by rewrite /Rnative/fun_hrel Native.bitsToIntK.
Qed.

(************************************************************************)
(** * From bit vectors to bit sequences                                 *)
(************************************************************************)

Global Instance Rtuple_eq:
  refines (Rtuple ==> Rtuple ==> param.bool_R) eq_op eq_op.
Proof.
rewrite refinesE => a _ <- b _ <-.
rewrite /eq_op/eq_B/eq_s val_eqE.
by apply eq_bool_R.
Qed.

Global Instance Rtuple_zero: refines Rtuple 0%C 0%C.
Proof. by rewrite refinesE. Qed.

Global Instance Rtuple_one: refines Rtuple 1%C 1%C.
Proof. by rewrite refinesE. Qed.

Global Instance Rtuple_lnot:
  refines (Rtuple ==> Rtuple) ~%C ~%C.
Proof. by rewrite refinesE=> bs w <-. Qed.

(* =Rtuple_land= *)
Global Instance Rtuple_land:
  refines (Rtuple ==> Rtuple ==> Rtuple) (@andB _) ands.
Proof. by rewrite !refinesE => bs1 w1 <- bs2 w2 <-. Qed.
(* =end= *)

Global Instance Rtuple_lor: 
  refines (Rtuple ==> Rtuple ==> Rtuple) ||%C ||%C.
Proof. by rewrite !refinesE => bs1 w1 <- bs2 w2 <-. Qed.

Global Instance Rtuple_lxor: 
  refines (Rtuple ==> Rtuple ==> Rtuple) ^^%C ^^%C.
Proof. by rewrite !refinesE => bs1 w1 <- bs2 w2 <-. Qed.

Global Instance Rtuple_lsr: 
  refines (Rtuple ==> RidxI ==> Rtuple) :>>:%C :>>:%C.
Proof. by rewrite !refinesE => bs1 w1 <- bs2 w2 <-. Qed.

Global Instance Rtuple_lsl: 
  refines (Rtuple ==> RidxI ==> Rtuple) :<<:%C :<<:%C.
Proof. by rewrite !refinesE => bs1 w1 <- bs2 w2 <-. Qed.

Global Instance Rtuple_add: 
  refines (Rtuple ==> Rtuple ==> Rtuple) (@addB _) adds.
Proof.
rewrite !refinesE => bs1 w1 <- bs2 w2 <-.
by rewrite (adds_relE (k := #| T |)(bv1 := bs1)(bv2 := bs2)).
Qed.

Global Instance Rtuple_sub: 
  refines (Rtuple ==> Rtuple ==> Rtuple) (@subB _) subs.
Proof.
rewrite !refinesE => bs1 w1 <- bs2 w2 <-.
by rewrite (subs_relE (k := #| T |)(bv1 := bs1)(bv2 := bs2)).
Qed.

Global Instance Rtuple_opp: 
  refines (Rtuple ==> Rtuple) (@oppB _) opps.
Proof.
rewrite !refinesE => bs w <- .
by rewrite (opps_relE (k := #| T |)(bv := bs)).
Qed.


(************************************************************************)
(** * Compositions                                                      *)
(************************************************************************)

Global Instance Rbitset_get: 
  refines (Rbits ==> Rbitset ==> param.bool_R) get_op get_op.
Proof.
eapply refines_trans; tc.
(* XXX: this should follow by composition. 
   Instead, I've to manually instantiate [Bits_R] *)
eapply refines_trans; tc.
- param get_R.
- Opaque Native.lsl.
  param (get_R (Idx_R := RidxN)(Bits_R := Rnative)). 
Qed.

Global Instance Rbitset_singleton:
  refines (Rbits ==> Rbitset) singleton_op singleton_op.
Proof.
eapply refines_trans; tc.
eapply refines_trans; tc.
- param singleton_R.
- param (singleton_R (Idx_R := RidxN)(Bits_R := Rnative)).
Qed.

Global Instance Rbitset_full:
  refines Rbitset full_op full_op.
Proof.
eapply refines_trans; tc.
eapply refines_trans; tc.
- param (create_R (Bits_R := Rtuple)).
- param (create_R (Bits_R := Rnative)).
Qed.


Global Instance Rbitset_empty: 
  refines Rbitset empty_op empty_op.
Proof.
eapply refines_trans; tc.
eapply refines_trans; tc. 
(* XXX: this is a bit surprising: why did that go through when
[Rbitset_full] was a problem *)
Qed.

Global Instance Rbitset_insert:
  refines (Rbits ==> Rbitset ==> Rbitset) set_op set_op.
Proof.
eapply refines_trans; tc.
eapply refines_trans; tc.
- param insert_R.
- param (insert_R (Idx_R := RidxN)(Bits_R := Rnative)).
Qed.

Global Instance Rcomp_not: 
  refines (Rtuple \o Rnative ==> Rtuple \o Rnative) ~%C ~%C.
Proof.
eapply refines_trans; tc.
Qed.

Global Instance Rbitset_remove:
  refines (Rbitset ==> Rbits ==> Rbitset) remove_op remove_op.
Proof.
eapply refines_trans; tc.
eapply refines_trans; tc.
- param remove_R.
- Local Opaque negs.
- param (remove_R (Idx_R := RidxN)(Bits_R := Rnative)).
Qed.

(* =Rbitset_compl= *)
Global Instance Rbitset_compl: 
  refines (Rbitset ==> Rbitset) (@setC _) compl.
(* =end= *)
Proof. by eapply refines_trans; tc. Qed.

Global Instance Rbitset_union:
  refines (Rbitset ==> Rbitset ==> Rbitset) union_op union_op.
Proof. by eapply refines_trans; tc; param_comp union_R. Qed.

Global Instance Rbitset_inter:
  refines (Rbitset ==> Rbitset ==> Rbitset) inter_op inter_op.
Proof. by eapply refines_trans; tc; param_comp inter_R. Qed.

Global Instance Rbitset_symdiff:
  refines (Rbitset ==> Rbitset ==> Rbitset) symdiff_op symdiff_op.
Proof. by eapply refines_trans; tc; param_comp symdiff_R. Qed.

Global Instance Rbitset_subset:
  refines (Rbitset ==> Rbitset ==> bool_R) subset_op subset_op.
Proof. 
eapply refines_trans; tc.
eapply refines_trans; tc.
- param (subset_R (Bits_R := Rtuple)).
- param (subset_R (Bits_R := Rnative)).
Qed.
