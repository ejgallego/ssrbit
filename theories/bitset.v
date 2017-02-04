(******************************************************************************)
(* A bit library for Coq: sets encoded as bitseqs.                            *)
(******************************************************************************)
(*                                                                            *)
(* (c) 2016, MINES ParisTech                                                  *)
(*                                                                            *)
(* Written by Arthur Blot                                                     *)
(*            Pierre-Evariste Dagand                                          *)
(*            Emilio J. Gallego Arias                                         *)
(*                                                                            *)
(* LICENSE: CECILL-B                                                          *)
(*                                                                            *)
(******************************************************************************)
From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.
From mathcomp
Require Import choice fintype finset tuple path bigop.
From mathcomp
Require Import ssralg ssrnum fingroup perm finalg zmodp.

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
(*     setn S == k.-bit tuple for (S : {set 'I_k})                            *)
(*                                                                            *)
(*     seqB B ==  seq 'I_k  corresponding to (B : k.-bit_tuple)               *)
(*     setB B == {set 'I_k} corresponding to (B : k.-bit_tuple)               *)
(*                                                                            *)
(* Future:                                                                    *)
(*                                                                            *)
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
Require Import bitseq notation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope bits_scope.

Hint Resolve orbb andbb.

Section MemIota.
(* Indexes *)
Implicit Types (i j : nat).
Implicit Types (s : seq nat).

(* Auxiliary results *)
Lemma memS_mask l i m j k :
  (l + i \in mask m (iota (l + j) k)) =
  (    i \in mask m (iota      j  k)).
Proof.
elim: k m i j l => [|k ihk] [|b m] i j l; rewrite // !mem_mask_cons.
by rewrite eqn_add2l -addnS ihk.
Qed.

Lemma mem_mask_gt i j k m : i < j -> (i \in mask m (iota j k)) = false.
Proof.
elim: k i j m => [|k ihk] i j m hij; first by rewrite mask0.
by case: m => // -[] m; rewrite mem_mask_cons ihk ?(ltn_eqF hij) ?ltnS // ltnW.
Qed.

(* Main lemma relating bitmasks with their enumerations *)
(* =mem_mask_iota= *)
Lemma mem_mask_iota k i j m : j <= i < k ->
   i \in mask m (iota j k) = m`_(i - j).
(* =end= *)
Proof.
elim: k i j m => [|k ihk] i j [|b m] /andP [hji hik] //.
  by rewrite nth_nil.
rewrite mem_mask_cons; case: eqP => [->|/eqP/negbTE neq_ij].
  by rewrite mem_mask_gt // subnn andbT orbF.
have hj : j < i by rewrite ltn_neqAle hji eq_sym neq_ij.
case: i hji hik {neq_ij} hj => // i hji hik hj.
rewrite (memS_mask 1) // andbF (ihk i) ?subSn //.
by rewrite ltnS in hj; rewrite hj.
Qed.

End MemIota.

(* Untyped operations, useful for computing and avoid {set _} *)
(* =to_set= *)
Definition to_set   m := mask m (iota 0 (size m)).
(* =end= *)
(* Definition from_set k s := foldr (fun idx bs => setb bs idx true) (nseq k false) s. *)
(* =from_set= *)
Definition from_set s :=
  foldr (fun idx bs => sets bs idx true) [::] s.
(* =end= *)

Lemma size_from_set s : size (from_set s) = \max_(n <- s) n.+1.
Proof.
by elim: s => [|n s ihs]; rewrite ?big_nil ?big_cons ?size_nseq ?size_set_nth // ihs.
Qed.

Lemma from_setE s : from_set s = \big[ors/[::]]_(n <- s) sets [::] n true.
Proof.
elim: s => [|n s ihs]; rewrite ?(big_nil, big_cons) //=.
by rewrite set_bitE ?size_from_set orsC ihs.
Qed.

Lemma eq_perm_from_set s1 s2 : perm_eq s1 s2 ->
  from_set s1 = from_set s2.
Proof. rewrite !from_setE; exact: eq_big_perm. Qed.

(* TODO: We must work up to (perm_eq uniq) for the image of to_set *)
Lemma eq_from_set s1 s2 : uniq s1 -> uniq s2 -> s1 =i s2 ->
                  from_set s1 = from_set s2.
Proof. by move=> ? ? ?; apply/eq_perm_from_set/uniq_perm_eq. Qed.

Lemma from_set_tupleP k (s : seq 'I_k) : size (ors (from_set (map val s)) '0_k) == k.
Proof.
rewrite size_liftz size_nseq size_from_set big_map.
elim/big_rec: _ => [|j n _ /eqP/maxn_idPr ihj]; first by rewrite max0n.
by apply/eqP/maxn_idPr; rewrite geq_max ltn_ord.
Qed.

Definition seqn k (s : seq 'I_k)   := Tuple (from_set_tupleP s).
(* =setn= *)
Definition setn k (s : {set 'I_k}): 'B_k
(* =end= *)
  := seqn (enum s).

Definition seqB k (m : 'B_k) := mask m (enum 'I_k).
(* =setB= *)
Definition setB k (m : 'B_k): {set 'I_k}
(* =end= *)
  := [set x in seqB m].

(* Alternative *)
Definition setb' k (m : 'B_k) := [set i in 'I_k | m`_i].

Lemma val_mem_seq (T : eqType) (P : pred T) (sT : subType P)
      (i : sT) (s : seq sT) : (i \in s) = (val i \in [seq val x | x <- s]).
Proof. by elim: s => //= x s ihs; rewrite !inE val_eqE ihs. Qed.

(* This is interesting (and true) but a bit cumbersome to prove *)
Lemma setb_def k (m : 'B_k) : setB m = [set i in 'I_k | m`_i].
Proof.
apply/setP=> i; rewrite !inE val_mem_seq map_mask val_enum_ord.
by rewrite mem_mask_iota ?subn0 ?ltn_ord ?size_tuple.
Qed.

Lemma eq_seqn k (s1 s2 : seq 'I_k) :
  uniq s1 -> uniq s2 -> s1 =i s2 -> seqn s1 = seqn s2.
Proof.
move=> u1 u2 hi; apply/val_inj; congr ors.
apply/eq_from_set; rewrite ?(map_inj_uniq val_inj) //.
by move=> u; apply/mapP/mapP=> -[v v1 ->]; exists v; rewrite ?hi // -hi.
Qed.

Lemma seqb_uniq k (s : 'B_k) : uniq (seqB s).
Proof. by rewrite mask_uniq ?enum_uniq. Qed.

Lemma mem_setb k (b : 'B_k) (i : 'I_k) :
  (i \in setB b) = b`_i.
Proof.
rewrite inE val_mem_seq !map_mask val_enum_ord.
by rewrite mem_mask_iota ?subn0 ?ltn_ord ?size_tuple.
Qed.

(* =mem_setB= *)
Lemma mem_setB k (b : 'B_k) (i : 'I_k) :
  (i \in setB b) = tnth b i.
(* =end= *)
Proof. by rewrite mem_setb (tnth_nth false). Qed.

(* XXX: Needs fixing *)
(* Lemma seqn_cons k n (s : seq 'I_k) : *)
(*   seqn (n :: s) = [tuple of setb (seqn s) n true]. *)
(* Proof. exact: val_inj. Qed. *)

Lemma nth_ors0 bs i k : (ors bs '0_k)`_i = bs`_i.
Proof. by rewrite /ors nth_liftz_idem ?gets0 ?orbF. Qed.

(* Perm_eq is not enough as we also remove the dups *)
Lemma seqnK k (x : seq 'I_k) : (seqB (seqn x)) =i x.
Proof.
move=> i; rewrite val_mem_seq map_mask val_enum_ord.
rewrite mem_mask_iota ?ltn_ord ?size_tuple ?subn0 // /seqn /= nth_ors0.
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
rewrite !(tnth_nth false) /seqn /setB /= nth_ors0 nth_from_set ?ltn_ord //.
by rewrite map_mask val_enum_ord mem_mask_iota ?subn0 ?ltn_ord ?size_tuple.
Qed.


Section SetK.

Variable k: nat.

Local Notation setB := (@setB k).
Local Notation setn := (@setn k).

(* =setnK= *)
Lemma setnK : cancel setn setB.
(* =end= *)
Proof. by move=> x; apply/setP=> i; rewrite inE seqnK mem_enum. Qed.

(* =setbK= *)
Lemma setbK : cancel setB setn.
(* =end= *)
Proof.
move=> t; rewrite -{2}[t]seqbK; apply/eq_seqn; rewrite ?mask_uniq ?enum_uniq //.
by move => i; rewrite mem_enum inE.
Qed.

End SetK.


Prenex Implicits setnK setbK.

(******************************************************************************)
(** Main operators, union, intersection                                       *)
(******************************************************************************)

(* Example property: union *)
(* XXX: move to use {morph ...} notation *)
Lemma union_morphL k (b1 b2 : 'B_k) :
  setB (orB b1 b2) = (setB b1 :|: setB b2).
Proof.
by apply/setP=> i; rewrite !mem_setb inE !mem_setb nth_liftz ?size_tuple.
Qed.

(* Example of derived property *)
Lemma union_morphR k (s1 s2 : {set 'I_k}) :
  orB (setn s1) (setn s2) = setn (s1 :|: s2).
Proof. by apply: (can_inj setbK); rewrite union_morphL !setnK. Qed.

(* Basically the same proof. *)
(* =inter_morphL= *)
Lemma inter_morphL k (b1 b2 : 'B_k) :
  setB (andB b1 b2) = (setB b1 :&: setB b2).
(* =end= *)
Proof.
by apply/setP=> i; rewrite !mem_setb inE !mem_setb nth_liftz ?size_tuple.
Qed.

Lemma neg_morphL k (b : 'B_k) :
  setB (negB b) = ~: (setB b).
Proof.
by apply/setP=> i; rewrite !mem_setb inE !mem_setb (nth_map false) ?size_tuple.
Qed.

Lemma symdiff_morphL k (b1 b2 : 'B_k) :
  setB (xorB b1 b2) = (setB b1 :\: setB b2 :|: setB b2 :\: setB b1).
Proof.
apply/setP=> i.
rewrite !mem_setb 2!inE !mem_setb inE !mem_setb nth_liftz ?size_tuple //.
case: b1`_i b2`_i=> -[] // .
Qed.

(* More properties: singleton *)
(* XXX: This should be one liner as you can see with the mismatches *)
Lemma setB1 k (n : 'I_k.+1) :
  setB [tuple of setlB [tuple of '0_k.+1] n true] = [set n].
Proof.
apply/setP=> i; rewrite mem_setb /= inE /setls size_tuple ltn_ord.
rewrite nth_set_nth /=; case: eqP => [/eqP|] heq.
  by rewrite -val_eqE heq.
by rewrite -val_eqE (gets0 k.+1); apply/esym/eqP.
Qed.

(* Operations to do *)
(* remove. *)
(* inter. *)
(* symdiff. *)
(* insert. *)
(* union. *)
(* compl. *)
(* shift. *)
(* get. *)

(******************************************************************************)
(** Cardinality                                                               *)
(******************************************************************************)
Definition cardb k (s : 'B_k) := count id s.

Arguments seqb_uniq [k s].

(* This follows directly from the library *)
Lemma cardbP k (s : 'B_k) : #| setB s | = cardb s.
Proof.
by rewrite cardsE (card_uniqP seqb_uniq) size_mask // size_tuple size_enum_ord.
Qed.

(* test for Zero*)
Lemma mem_setBN n (bs : 'B_n) (hN : forall i, i \notin setB bs) :
  true \notin bs.
Proof. by apply/tnthP => -[xi hi]; have := hN xi; rewrite mem_setB -hi. Qed.

Lemma mem_setBN' n (bs : 'B_n) (hN : forall i, i \in setB bs = false) :
  true \notin bs.
Proof. by apply/tnthP => -[xi hi]; have := hN xi; rewrite mem_setB -hi. Qed.

(******************************************************************************)
(** Minimum                                                                   *)
(******************************************************************************)

Section MinOrdSet.

Variable (n : nat).
Variable (T : finType).
Implicit Types (A : {set 'I_n}).

Definition setmin  A := [set [arg min_(k<x in A) k] | x in A].

(* Definition setmin' A := [set x in A | [forall y in A, x < y] ]. *)

(* Lemma u A : setmin A = setmin' A. *)
(* Proof. *)
(* apply/setP=> x; rewrite /setmin !inE. *)
(* apply/imsetP/andP. *)
(* + case=> x0 x0_in -> {x}; case: arg_minP => // i _ hmin; split. *)
(*   admit. *)
(*   apply/forallP. *)

Lemma min1P A x (x_inA : x \in A) : setmin A = [set [arg min_(k<x in A) val k]].
Proof.
apply/setP=> i; rewrite /min !inE; apply/imsetP/eqP; last by exists x.
case=> [u u_in ->]; case: arg_minP => // i1 I1 h1; case: arg_minP => // i2 I2 h2.
by apply/val_inj/eqP; rewrite eqn_leq h1 // h2.
Qed.

Lemma min0P A : (setmin A == set0) = (A == set0).
Proof. by rewrite /min imset_eq0. Qed.

Lemma card_setmin A : (0 < #|setmin A|) = (A != set0).
Proof. by rewrite -min0P card_gt0. Qed.

(* Lemma card_setmin A : (0 < #|setmin A|) = (A != set0). *)
(* Proof. by rewrite -min0P card_gt0. Qed. *)

End MinOrdSet.

Section MinIndex.


Lemma indexP (T : eqType) d (x : T) s idx :
  d != x ->
  nth d s idx = x ->
  (forall j, j < size s -> nth d s j = x -> idx <= j) ->
  index x s = idx.
Proof.
elim: s idx => [|s ss ihs] idx hneq; first by move/eqP: hneq; rewrite nth_nil.
case: idx => /= [->|idx]; first by rewrite eqxx.
move=> /ihs-/(_ hneq) {ihs} ihs hj.
case: ifP => [/eqP|] he; first by have /= := hj 0 erefl he; rewrite ltn0.
by congr S; apply: ihs => j hjs hnt; have := hj j.+1 hjs hnt.
Qed.

(* Lemma min_ref A : min A = index true (setn A). *)

(* Lemma min_ref (A : {set 'I_n}) x (x_inA : x \in A) : *)

(* This should be improved. *)
Lemma index_repr n (bs : 'B_n) x (hs : x \in setB bs) :
  index true bs = [arg min_(k < x in setB bs) val k].
Proof.
case: arg_minP => // i ih h_min.
have/indexP: bs`_i = true by rewrite -mem_setb.
apply=> // j hj hnt; rewrite size_tuple in hj.
by have:= h_min (Ordinal hj); apply; rewrite mem_setb.
Qed.

(* XXX: A likely better approach is to work with the modular version,
   as index will overflow if the bitseq is empty *)

Lemma index_repr_mod n (bs : 'B_n) x (hs : x \in setB bs) :
  index true bs = [arg min_(k < x in setB bs) val k] %[mod n].
Proof.
Admitted.

Require Import bitocaml.

Lemma mask_setls_one T d n m (l : seq T) :
  m < n -> n <= size l ->
  mask (setls '0_n m true) l = [:: nth d l m].
Proof.
elim: n m l => //= n ihn [|m] [| x l] //= hs /ihn ihn'.
  by rewrite mask_false.
by rewrite setls_cons /= ihn'.
Qed.

Lemma setminP n (bs : 'B_n) : setmin (setB bs) = setB (keep_min bs).
Proof.
case: [pick x | x \in setB bs] / pickP => [x xin|nin].
  rewrite (min1P xin) /setB /seqB keep_minP.
  apply/setP=> u; rewrite !inE -val_eqE /= -(index_repr xin).
  have idx_size: index true bs < n.
    rewrite -{2}(size_tuple bs) index_mem.
    move: xin; rewrite mem_setb => <-.
    by rewrite mem_nth // ?size_tuple.
  rewrite (mask_setls_one x) ?size_enum_ord // inE -val_eqE /= nth_enum_ord //.
have U: setB bs = set0.
  by apply/setP=> x; rewrite nin inE.
have V: bs = '0.
  apply/(can_inj setbK); rewrite U.
  by apply/setP=> x; rewrite !inE /= /seqB mask_false.
have W : setmin set0 = set0.
  by move=> k; apply/eqP; rewrite min0P.
rewrite U W V; apply/setP => o.
rewrite !inE /seqB keep_minP.
rewrite setls_default /= ?size_nseq ?mask_false //.
have: true \notin '0_n. by elim: n {bs nin U V W o}.
by rewrite -index_mem ltnNge negbK size_nseq.
Qed.

Print Assumptions setminP.

(* Lemma  n (bs : 'B_n) x (hs : x \in setB bs) : *)
(*   index true bs = [arg min_(k < x in setB bs) val k] %[mod n]. *)
(* Proof. *)
(* Admitted. *)

(* Extend with the minimum *)
(* Definition extm n (A : {set 'I_n}) : {set 'I_n.+1} := *)
(*   [set widen_ord (@leqnSn _) x | x in A] :|: [set inord n]. *)

(* Lemma index_repr' n (bs : 'B_n) : *)
(*   index true bs = [arg min_(k < inord n in extm (setB bs)) val k]. *)
(* Proof. *)
(* Admitted. *)

(* Corollary *)
(* Lemma index_reprP n (bs : 'B_n) (x : 'I_n) (hs : x \in setB bs) : *)
(*   index true bs \in map val (enum (min (setB bs))). *)

End MinIndex.

(* =keep_setP= *)
(* Lemma keep_min_setP n (bs : 'B_n) : *)
(*   if [pick x in setB bs] is Some x *)
(*   then setB (keep_min bs) = [set [arg min_(i < x in setB bs) i]] *)
(*   else setB (keep_min bs) = set0. *)
(* (* =end= *) *)
(* Proof. *)
(* case: pickP => [x xin|inN]. *)
(*   have bs_x := xin; rewrite mem_setb in bs_x. *)
(*   apply/setP => y; rewrite mem_setb keep_minP. *)
(*   rewrite /setls size_nseq -[n in _ < n](size_tuple bs). *)
(*   rewrite index_mem -bs_x mem_nth ?size_tuple // !inE. *)
(*   case: arg_minP => // i hin hmin; rewrite nth_set_nth /=. *)
(*   admit. (* Import indexP from old development *) *)
(* apply/setP => y; rewrite mem_setb keep_minP. *)
(* have:= mem_setBN' inN; rewrite -index_mem /setls size_tuple size_nseq. *)
(* by move/negbTE->; rewrite nth_nseq ltn_ord inE. *)
(* Admitted. *)
(* =end= *)

(* =ntz_setP= *)
(* Lemma ntz_setP n (bs : 'B_n) : *)
(*   if [pick x in setB bs] is Some x *)
(*   then ntz bs = inB [arg min_(k < x in setB bs) k] *)
(*   else ntz bs = inB n. *)
(* (* =end= *) *)
(* Proof. *)
(* case: pickP => [x xinT|xinN]. *)
(*   case: arg_minP => // y yin ymin; rewrite ntzP; congr inB. *)
(*   (* Same applications of indexP as before *) *)
(*   admit. *)
(* have:= mem_setBN' xinN; rewrite -index_mem ltn_neqAle index_size andbT negbK. *)
(* by rewrite size_tuple ntzP => /eqP ->. *)
(* Admitted. *)
(* =end= *)

(* XXX: Emilio: move? *)
Definition ord_iota k m n : seq 'I_k := pmap insub (iota m n).
Definition set_iota k m n : {set 'I_k} := [set x in ord_iota k m n].

(* Initial segment (ie set containing element orders 0, ..., k) *)
(* XXX: Emilio? *)
(*
Definition initseg k i := @decB k (shlB (bito 1%R) i).

Lemma initseg_repr k i : setB (initseg k i) = set_iota k 0 i.
(* Admitted. *)
*)

(* Add a bitset with 1 bit to true to any bitset *)
Definition set_isNext_g {n} (S: {set 'I_n.+1}) y x := (y \notin S) && (y >= x).
Definition set_next_g   {n} (S: {set 'I_n.+1}) x := [arg min_(y < ord0 | set_isNext_g S y x) y].

(* Lemma ripple_repr_1 k (bs: 'B_k.+1) (x: 'I_k.+1) f (isNext_f: set_isNext_g (setB bs) f x) : *)
(*   setB (addB (setn [set x]) bs) = *)
(*   (set_next_g (setB bs) x) |: [set y in (setB bs) | y < x] :|: [set y in (setB bs) | y > set_next_g (setB bs) x]. *)
(* XXX: Arthur *)
(* Admitted. *)

(******************************************************************************)
(** Set Shifting                                                              *)
(******************************************************************************)

Section SetShift.

(* Local Open Scope ring_scope. *)
Import GRing.Theory.

(* Aux lemmas *)

Lemma ord_add_mod k (i n : 'I_k.+1) (in_le_k : i + n < k.+1) :
  (i + n)%R = i + n :> nat.
Proof. by rewrite /= modn_small. Qed.

Lemma ord_sub_mod k (i n : 'I_k.+1) (n_le_i : n <= i) : (i - n)%R = i - n :> nat.
Proof.
rewrite /= modnDmr addnBA 1?ltnW // addnC -addnBA //.
by rewrite modnDl modn_small // (leq_ltn_trans (leq_subr _ _)).
Qed.

(* Shift a set *)
Definition shlS k (s : {set 'I_k.+1}) (n : 'I_k.+1) :=
  [set (i + n)%R | i in s & i < k.+1 - n].

Lemma shl_morph k (b : 'B_k.+1) (n : 'I_k.+1) :
  setB (shlB b n) = shlS (setB b) n.
Proof.
apply/setP=> i; rewrite mem_setB tnth_shlB /shlS.
apply/andP/imsetP=> /= [[h_le_i hnth]|[x]].
  exists (i-n)%R; last by rewrite addrNK.
  by rewrite inE mem_setB hnth ord_sub_mod ?ltn_sub2r.
rewrite inE; case/andP; rewrite mem_setB => [htnth hlt ->].
rewrite ord_add_mod ?addrK ?htnth ?leq_addl //.
by rewrite ltn_subRL addnC in hlt.
Qed.

Definition shrS k (s : {set 'I_k.+1}) (n : 'I_k.+1) :=
  [set (i - n)%R | i in s & n <= i].

Lemma shr_morph k (b : 'B_k.+1) (n : 'I_k.+1) :
  setB (shrB b n) = shrS (setB b) n.
Proof.
apply/setP=> i; rewrite mem_setB tnth_shrB /shrS.
apply/andP/imsetP=> /= [[h_le_i hnth]|[x]].
  exists (i+n)%R; last by rewrite addrK.
  rewrite inE mem_setB hnth ord_add_mod ?leq_addl //.
  by rewrite ltn_subRL addnC in h_le_i.
rewrite inE mem_setB; case/andP=> [htnth hnx ->{i}].
by rewrite addrNK htnth ord_sub_mod ?ltn_sub2r.
Qed.

End SetShift.

(******************************************************************************)
(* Bijection to any set of cardinality n, from an o
idea by Arthur Blot.        *)
(******************************************************************************)
Section FinSet.

Variable T : finType.
Implicit Types (A B : {set T}).
Implicit Types (b : 'B_#|T|).

(* From a finite set to tuple *)
(* =bitF= *)
Definition bitF (A: {set T}): 'B_#| T |
(* =end= *)
  := setn [set enum_rank x | x in A].

(* From a tuple to a finite set *)
(* =finB= *)
Definition finB (b: 'B_#| T |): {set T}
(* =end= *)
  := [set enum_val x | x in setB b].

(* Aux Lemma to avoid using prenex implicits *)
Let can_enum D := can2_imset_pre D (@enum_valK T) (@enum_rankK _).
Let enum_can D := can2_imset_pre D (@enum_rankK T) (@enum_valK _).

Lemma preimsetK (U V : finType) (A : {set U}) (f : U -> V)
                (f_inj : injective f) :
  f @^-1: (f @: A) = A.
Proof.
apply/setP=> x; rewrite inE; apply/imsetP/idP; last by move=> x_in; exists x.
by case=> y y_in /f_inj->.
Qed.

(* =finBK= *)
Lemma finBK : cancel bitF finB.
(* =end= *)
Proof.
by move=> A; rewrite /finB can_enum setnK (preimsetK _ enum_rank_inj).
(* move=> A; rewrite /finB /bitF setnK -imset_comp (eq_imset _ (@enum_rankK _)). *)
(* exact: imset_id. *)
Qed.

(* =bitFK= *)
Lemma bitFK : cancel finB bitF.
(* =end= *)
Proof.
by move=> A; rewrite /finB /bitF enum_can (preimsetK _ enum_val_inj) setbK.
(* move=> b; rewrite /finB /bitF -imset_comp (eq_imset _ (@enum_valK _)) imset_id. *)
(* exact: setbK. *)
Qed.

Definition f_repr b A := A = [set x : T | b`_(enum_rank x)].

Lemma f_repr_uniq b E : f_repr b E -> E = finB b.
Proof.
by move->; rewrite /finB can_enum; apply/setP=> ?; rewrite !inE -mem_setb inE.
Qed.

Lemma setDB (b: 'B_#| T |):
  [set enum_val x | x in ~: setB b] =  ~: [set enum_val x | x in setB b].
Proof. by apply/setP=> t; rewrite in_setC !can_enum !inE. Qed.

Lemma Fcompl_morphL (b : 'B_#|T|) :
  finB (negB b) = ~: (finB b).
Proof. by rewrite /finB neg_morphL setDB. Qed.

Lemma Funion_morphL (b1 b2 : 'B_#|T|) :
  finB (orB b1 b2) = (finB b1 :|: finB b2).
Proof. by rewrite /finB -imsetU union_morphL. Qed.

Lemma Finter_morphL (b1 b2 : 'B_#|T|) :
  finB (andB b1 b2) = (finB b1 :&: finB b2).
Proof.
rewrite /finB inter_morphL imsetI //.
by move=> x y _ _; apply: enum_val_inj.
Qed.

Lemma Fsymdiff_morphL (b1 b2 : 'B_#|T|) :
  finB (xorB b1 b2) = (finB b1 :\: finB b2 :|: finB b2 :\: finB b1).
Proof.
rewrite !setDE /finB symdiff_morphL imsetU !setDE !imsetI.
  by rewrite !setDB.
- move=> x y _ _; apply: enum_val_inj.
- move=> x y _ _; apply: enum_val_inj.
Qed.

End FinSet.

(******************************************************************************)
(* Taken from the paper, we see indeed that there exists a unique repr which  *)
(* is the one given by setB.                                                  *)
(******************************************************************************)

Section ReprUniq.
Definition s_repr k (bs : 'B_k) E :=
  E = [set x : 'I_k | bs`_x].

Lemma s_repr_uniq k (bs : 'B_k) E : s_repr bs E -> E = setB bs.
Proof. by move ->; rewrite setb_def. Qed.

Lemma count_repr k (bs : 'B_k) E : s_repr bs E -> count_mem true bs = #|E|.
Proof. by move -> ; rewrite -setb_def cardbP; apply: eq_count; case. Qed.
End ReprUniq.


(** * Generic set-theoretic operations *)

(**

  The following operations are defined parametrically wrt. the
  underlying implementation of bitvectors. This means that we can
  instantiate them to [BITS n] and later to, say, Int32. This also
  means that we can use domain-specific notations for defining them.

 *)

From CoqEAL Require Import hrel param refinements.

Import Refinements.Op.
Import Logical.Op.

Section Operations.

Variables (Idx : Type).
Variables (Bits : Type).

Context `{eq_of   Bits}.
Context `{sub_of  Bits}.
Context `{zero_of Bits}.
Context `{one_of  Bits}.

Context `{not_of Bits}.
Context `{or_of  Bits}.
Context `{and_of Bits}.
Context `{xor_of Bits}.
Context `{shl_of Idx Bits}.
Context `{shr_of Idx Bits}.

Implicit Types (k: Idx)(bs : Bits).
Local Open Scope computable_scope.

(* =get= *)
Definition get k bs
  := negb ((bs && (1 :<<: k)) == 0)%C.
(* =end= *)
Definition singleton k := 1 :<<: k.
Definition compl     bs := ~ bs.

Definition empty : Bits := (0)%C.
Definition full  : Bits := (0-1)%C.

Definition inter bs bs' := bs && bs'.
Definition union bs bs' := bs || bs'.
Definition keep_min bs  := bs && ~ bs.


(* XXX: Order of arguments *)
(* =insert= *)
Definition insert  k bs
  := bs || (1 :<<: k).
(* =end= *)
(* =remove= *)
Definition remove  bs k
  := bs && (~ (1 :<<: k)).
(* =end= *)
Definition symdiff bs1 bs2 := bs1 ^^ bs2.
Definition subset  bs1 bs2 := (bs1 && bs2) == bs1.

End Operations.

Arguments get {_}{_}{_}{_}{_}{_}{_} k bs.
Arguments singleton {_}{_}{_}{_} k.
Arguments compl {_}{_} bs.
Arguments empty {_}{_}.
Arguments full {_}{_}{_}{_}.
Arguments inter {_}{_} bs bs'.
Arguments union {_}{_} bs bs'.
Arguments keep_min {_}{_}{_} bs.
Arguments insert {_}{_}{_}{_}{_} k bs.
Arguments remove {_}{_}{_}{_}{_}{_} bs k.
Arguments symdiff {_}{_} bs1 bs2.
Arguments subset {_}{_}{_} bs1 bs2.

Parametricity get.
Parametricity singleton.
Parametricity compl.
Parametricity full.
Parametricity empty.
Parametricity inter.
Parametricity union.
Parametricity keep_min.
Parametricity insert.
Parametricity remove.
Parametricity symdiff.
Parametricity subset.

(******************************************************************************)
(* Typeclass notations                                                        *)
(******************************************************************************)

From CoqEAL
     Require Import refinements.
Require Import notation.

Import Refinements.Op.
Import Logical.Op.
Import Sets.Op.

(* For finset: *)

Section OpFin.

Variable T: finType.

Global Instance eq_fin:        eq_of {set T}    := fun x y => x == y.

Global Instance get_fin:       get_of T       {set T} := fun k E => k \in E.
Global Instance singleton_fin: singleton_of T {set T} := fun k => [set k].

Global Instance compl_fin:     compl_of {set T} := @setC _.
Global Instance full_fin:      full_of  {set T} := [set : T ].
Global Instance empty_fin:     empty_of {set T} := set0.

Global Instance set_fin:       set_of    T {set T} := fun k E => k |: E.
Global Instance remove_fin:    remove_of T {set T} := fun A a => A :\ a.

Global Instance inter_fin: inter_of {set T} := @setI _.
Global Instance union_fin: union_of {set T} := @setU _.
Global Instance symdiff_fin: symdiff_of {set T} := fun E E' => ((E :\: E') :|: (E' :\: E)).
Global Instance subset_fin:  subset_of {set T}  := fun E E' => E \subset E'.

Global Instance cardinal_fin:  cardinal_of nat {set T}  := fun E => #| E |.
Global Instance keep_min_fin:  keep_min_of {set T}  := 
  fun E => [set x in E | [forall (y | y \in E), enum_rank x <= enum_rank y]].

End OpFin.

(* For ordinals: *)

Section OpOrds.

Variable n: nat.

Global Instance pred_fin:  pred_of {set 'I_n.+1}  := 
  fun E => shlS E (inord 1).
Global Instance succ_fin:  succ_of {set 'I_n.+1}  := 
  fun E => shrS E (inord 1).

End OpOrds.

(* For bit vectors: *)

Section OpB.

Variable n: nat.

Global Instance get_B       : get_of 'I_n 'B_n       := get.
Global Instance singleton_B : singleton_of 'I_n 'B_n := singleton.
Global Instance compl_B     : compl_of 'B_n          := compl.
Global Instance empty_B     : empty_of 'B_n          := empty (Bits := 'B_n).
Global Instance full_B      : full_of 'B_n           := full  (Bits := 'B_n).
(* This creates a problem in typeclass resolution, see Rbitset_full *)
(* Global Instance full_B      : full_of 'B_n           := '1. (* Optimized *) *)
Global Instance set_B       : set_of 'I_n 'B_n       := insert.
Global Instance remove_B    : remove_of 'I_n 'B_n    := remove.
Global Instance inter_B     : inter_of 'B_n          := inter.
Global Instance union_B     : union_of 'B_n          := union.
Global Instance symdiff_B   : symdiff_of 'B_n        := symdiff.
Global Instance subset_B    : subset_of 'B_n         := subset.
Global Instance cardinal_B  : cardinal_of nat 'B_n   := 
  (fun x => nats (cardinal_smart x)).
Global Instance keep_min_B  : keep_min_of 'B_n. Admitted.


End OpB.
