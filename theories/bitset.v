(******************************************************************************)
(* A bit library for Coq: sets encoded as bitseqs.                            *)
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
Require Import choice fintype finset tuple path bigop.

(******************************************************************************)
(* A bit library for Coq: sets encoded as bitseqs.                            *)
(* WARNING: This library is just a proof of concept and extremely unstable.   *)
(*                                                                            *)
(* Operations:                                                                *)
(*                                                                            *)
(*   to_set b == seq of nats representing the bits set in bitseq b            *)
(* from_set s == bitseq correponding to (s : seq nat)                         *)
(*                                                                            *)
(*     seqn s == k.-bit tuple for (s : seq 'I_k)                              *)
(*     setn S == k.-bit_tuple for (S : {set 'I_k})                            *)
(*                                                                            *)
(*     seqB B ==  seq 'I_k  corresponding to (B : k.-bit_tuple)               *)
(*     setB B == {set 'I_k} corresponding to (B : k.-bit_tuple)               *)
(*                                                                            *)
(* Future                                                                     *)
(*     seqF F ==  seq 'I_k  corresponding to (B : {ffun ...}                  *)
(*     setF B == {ffun 'I_k... } corresponding to (B : k.-bit_tuple)          *)
(*                                                                            *)
(* Operations are designed to cancel in the proper way, the *_morphL family   *)
(* or lemmas provide the correspondence between set and bit operations.       *)
(*                                                                            *)
(* This file uses the following suffix conventions (FIXME):                   *)
(*                                                                            *)
(*  n - operations on nat seq/seq representation.                             *)
(*  B - operations on k.-tuple bool                                           *)
(*                                                                            *)
(******************************************************************************)

(* Import bits operations. *)
Require Import bitseq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Hint Resolve orbb andbb.

Section MemIota.
(* Indexes *)
Implicit Types (i j : nat).
Implicit Types (s : seq nat).

(* Auxiliary results *)
Lemma memS_mask l i m j k : size m <= k ->
  (l + i \in mask m (iota (l + j) k)) =
  (    i \in mask m (iota      j  k)).
Proof.
elim: k m i j l => [|k ihk] [|b m] i j l hs; rewrite // !mem_mask_cons.
by rewrite eqn_add2l -addnS ihk.
Qed.

Lemma mem_mask_gt i j k m : i < j -> (i \in mask m (iota j k)) = false.
Proof.
elim: k i j m => [|k ihk] i j m hij; first by rewrite mask0.
by case: m => // -[] m; rewrite mem_mask_cons ihk ?(ltn_eqF hij) ?ltnS // ltnW.
Qed.

(* Main lemma relating bitmasks with their enumerations *)
Lemma mem_mask_iota k i j m : j <= i < k -> size m <= k ->
   i \in mask m (iota j k) = getb m (i - j).
Proof.
elim: k i j m => [|k ihk] i j [|b m] /andP [hji hik] hs //.
  by rewrite /getb nth_nil.
rewrite mem_mask_cons; case: eqP => [->|/eqP/negbTE neq_ij].
  by rewrite mem_mask_gt // subnn andbT orbF.
have hj : j < i by rewrite ltn_neqAle hji eq_sym neq_ij.
case: i hji hik {neq_ij} hj => // i hji hik hj.
rewrite (memS_mask 1) // andbF (ihk i) ?subSn //.
by rewrite ltnS in hj; rewrite hj.
Qed.
End MemIota.

(* Untyped operations, useful for computing and avoid {set _} *)
Definition to_set   m := mask m (iota 0 (size m)).
(* Definition from_set k s := foldr (fun idx bs => setb bs idx true) (nseq k false) s. *)
Definition from_set s := foldr (fun idx bs => setb bs idx true) [::] s.

(* Be a bit stringent as to be commutative *)
Lemma set_bitE bs n : setb bs n true = orB bs (setb [::] n true).
Proof.
(* XXX: clean up *)
elim: bs n => [|b bs ihb] [|n] //=; first by rewrite or0B.
  by rewrite orB_cons orB0 orbT.
by rewrite orB_cons orbF ihb /setb set_nth_nil.
Qed.

Lemma size_from_set s : size (from_set s) = \max_(n <- s) n.+1.
Proof.
by elim: s => [|n s ihs]; rewrite ?big_nil ?big_cons ?size_nseq ?size_set_nth // ihs.
Qed.

Lemma from_setE s : from_set s = \big[orB/[::]]_(n <- s) setb [::] n true.
Proof.
elim: s => [|n s ihs]; rewrite ?(big_nil, big_cons) //=.
by rewrite set_bitE ?size_from_set orBC ihs.
Qed.

Lemma eq_perm_from_set s1 s2 : perm_eq s1 s2 ->
  from_set s1 = from_set s2.
Proof. rewrite !from_setE; exact: eq_big_perm. Qed.

(* TODO: We must work up to (perm_eq uniq) for the image of to_set *)
Lemma eq_from_set s1 s2 : uniq s1 -> uniq s2 -> s1 =i s2 ->
                  from_set s1 = from_set s2.
Proof. by move=> ? ? ?; apply/eq_perm_from_set/uniq_perm_eq. Qed.

Lemma from_set_tupleP k (s : seq 'I_k) : size (orB (from_set (map val s)) '0_k) == k.
Proof.
rewrite size_liftz size_nseq size_from_set big_map.
elim/big_rec: _ => [|j n _ /eqP/maxn_idPr ihj]; first by rewrite max0n.
by apply/eqP/maxn_idPr; rewrite geq_max ltn_ord.
Qed.

Definition seqn k (s : seq 'I_k)   := Tuple (from_set_tupleP s).
Definition setn k (s : {set 'I_k}) := seqn (enum s).

Definition seqB k (m : k.-tuple bool) := mask m (enum 'I_k).
Definition setB k (m : k.-tuple bool) := [set x in seqB m].

(* Alternative *)
Definition setb' k (m : k.-tuple bool) := [set i in 'I_k | getb m i].

Lemma val_mem_seq (T : eqType) (P : pred T) (sT : subType P)
      (i : sT) (s : seq sT) : (i \in s) = (val i \in [seq val x | x <- s]).
Proof. by elim: s => //= x s ihs; rewrite !inE val_eqE ihs. Qed.

(* This is interesting (and true) but a bit cumbersome to prove *)
Lemma setb_def k (m : k.-tuple bool) : setB m = [set i in 'I_k | getb m i].
Proof.
apply/setP=> i; rewrite !inE val_mem_seq map_mask val_enum_ord.
by rewrite mem_mask_iota ?subn0 ?ltn_ord ?size_tuple.
Qed.

Lemma eq_seqn k (s1 s2 : seq 'I_k) :
  uniq s1 -> uniq s2 -> s1 =i s2 -> seqn s1 = seqn s2.
Proof.
move=> u1 u2 hi; apply/val_inj; congr orB.
apply/eq_from_set; rewrite ?(map_inj_uniq val_inj) //.
by move=> u; apply/mapP/mapP=> -[v v1 ->]; exists v; rewrite ?hi // -hi.
Qed.

Lemma seqb_uniq k (s : k.-tuple bool) : uniq (seqB s).
Proof. by rewrite mask_uniq ?enum_uniq. Qed.

Lemma mem_setb k (b : k.-tuple bool) (i : 'I_k) :
  (i \in setB b) = (getb b i).
Proof.
rewrite inE val_mem_seq !map_mask val_enum_ord.
by rewrite mem_mask_iota ?subn0 ?ltn_ord ?size_tuple.
Qed.

(* XXX: Needs fixing *)
(* Lemma seqn_cons k n (s : seq 'I_k) : *)
(*   seqn (n :: s) = [tuple of setb (seqn s) n true]. *)
(* Proof. exact: val_inj. Qed. *)

Lemma nth_orB0 bs i k : ((orB bs '0_k)`_i)%B = (bs`_i)%B.
Proof. by rewrite /orB nth_liftz ?getb0 ?orbF. Qed.

(* Perm_eq is not enoguht as we also remove the dups *)
Lemma seqnK k (x : seq 'I_k) : (seqB (seqn x)) =i x.
Proof.
move=> i; rewrite val_mem_seq map_mask val_enum_ord.
rewrite mem_mask_iota ?ltn_ord ?size_tuple ?subn0 // /getb /seqn /= nth_orB0.
elim: x => [|x s ihs]; first by rewrite nth_nil.
rewrite inE nth_set_nth /=; case: (i == x) / boolP => [/eqP->|/negbTE heq].
  by rewrite eqxx.
by rewrite val_eqE heq ihs.
Qed.

Lemma nth_from_set s i : (nth false (from_set s)) i = (i \in s).
Proof.
elim: s => [|x s ihs]; first by rewrite nth_nil.
by rewrite nth_set_nth /= !inE; case: eqP.
Qed.

Lemma seqbK k : cancel (@seqB k) (@seqn _).
Proof.
move=> b; apply: eq_from_tnth => i.
rewrite !(tnth_nth false) /seqn /setB /= nth_orB0 nth_from_set ?ltn_ord //.
by rewrite map_mask val_enum_ord mem_mask_iota ?subn0 ?ltn_ord ?size_tuple.
Qed.

Lemma setnK k : cancel (@setn k) (@setB _).
Proof. by move=> x; apply/setP=> i; rewrite inE seqnK mem_enum. Qed.

Lemma setbK k : cancel (@setB k) (@setn _).
Proof.
move=> t; rewrite -{2}[t]seqbK; apply/eq_seqn; rewrite ?mask_uniq ?enum_uniq //.
by move => i; rewrite mem_enum inE.
Qed.

Prenex Implicits setnK setbK.

(* Example property: union *)
(* XXX: move to use {morph ...} notation *)
Lemma union_morphL k (b1 b2 : k.-tuple bool) :
  setB [tuple of orB b1 b2] = (setB b1 :|: setB b2).
Proof. by apply/setP=> i; rewrite !mem_setb inE !mem_setb /orB !getbE nth_liftz. Qed.

(* Example of derived property *)
Lemma union_morphR k (s1 s2 : {set 'I_k}) :
  [tuple of orB (setn s1) (setn s2)] = setn (s1 :|: s2).
Proof. by apply: (can_inj setbK); rewrite union_morphL !setnK. Qed.

(* Basically the same proof. *)
Lemma inter_morphL k (b1 b2 : k.-tuple bool) :
  setB [tuple of andB b1 b2] = (setB b1 :&: setB b2).
Proof.
apply/setP=> i; rewrite !mem_setb inE !mem_setb /andB !getbE /=.
by rewrite /liftz zipd_zip ?(nth_map (false, false)) ?nth_zip ?size_tuple.
Qed.

(* More properties: singleton *)
(* XXX: This should be one liner as you can see with the mismatches *)
Lemma setB1 k (n : 'I_k.+1) :
  setB [tuple of setlB [tuple of '0_k.+1] n true] = [set n].
Proof.
apply/setP=> i; rewrite mem_setb /= inE /setlb size_tuple ltn_ord.
rewrite /getb nth_set_nth /=; case: eqP => [/eqP|] heq.
  by rewrite -val_eqE heq.
by rewrite -val_eqE (getb0 k.+1); apply/esym/eqP.
Qed.

(* Cardinality *)
Definition cardb k (s : k.-tuple bool) := count id s.

Arguments seqb_uniq [k s].

(* This follows directly from the library *)
Lemma cardbP k (s : k.-tuple bool) : #| setB s | = cardb s.
Proof.
by rewrite cardsE (card_uniqP seqb_uniq) size_mask // size_tuple size_enum_ord.
Qed.

(******************************************************************************)
(* Bijection to any set of cardinality n, from an idea by Arthur Blot.        *)
(******************************************************************************)
Section FinSet.

Variable T : finType.
Implicit Types (A B : {set T}).
Implicit Types (b : #|T|.-tuple bool).

(* From a finite set to tuple *)
Definition bitF A := setn [set enum_rank x | x in A].

(* From a tuple to a finite set *)
Definition finB b := [set enum_val x | x in setB b].

Lemma finBK : cancel bitF finB.
Proof.
move=> A; rewrite /finB /bitF setnK -imset_comp (eq_imset _ (@enum_rankK _)).
exact: imset_id.
Qed.

Lemma bitFK : cancel finB bitF.
Proof.
move=> b; rewrite /finB /bitF -imset_comp (eq_imset _ (@enum_valK _)) imset_id.
exact: setbK.
Qed.

Definition f_repr b A := A = [set x : T | getb b (enum_rank x)].

(* XXX: Refactor, should be easier. *)
Lemma f_repr_uniq b E : f_repr b E -> E = finB b.
Proof.
move->; rewrite /finB (can2_imset_pre _ (@enum_valK _) (@enum_rankK _)).
apply/setP=> k; rewrite !inE /seqB.
rewrite -[val (enum_rank k)]subn0 -(@mem_mask_iota #|T|) ?size_tuple //.
  by rewrite val_mem_seq map_mask val_enum_ord.
by rewrite leq0n ltn_ord.
Qed.

End FinSet.

(******************************************************************************)
(* Taken from PE paper, we see indeed that there exists a unique repr which   *)
(* is the one given by setB.                                                  *)
(******************************************************************************)
Definition s_repr k (bs : k.-tuple bool) E :=
  E = [set x : 'I_k | getb bs x].

Lemma s_repr_uniq k (bs : k.-tuple bool) E : s_repr bs E -> E = setB bs.
Proof. by move ->; rewrite setb_def. Qed.

Lemma count_repr k (bs : k.-tuple bool) E : s_repr bs E -> count_mem true bs = #|E|.
Proof. by move -> ; rewrite -setb_def cardbP; apply: eq_count; case. Qed.
