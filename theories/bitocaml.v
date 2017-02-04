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
Require Import choice fintype finfun finset tuple path bigop.

(******************************************************************************)
(* Convenience Theory for extraction to ocaml integers                        *)
(******************************************************************************)
(*                                                                            *)
(* In particular we provide:                                                  *)
(*                                                                            *)
(* - An optimized "cardinality" count, based on population count.             *)
(* - An optimized "find first bit set", based on cardinality.                 *)
(*                                                                            *)
(* Moving the defined set/get operations could be considered.                 *)
(*                                                                            *)
(******************************************************************************)

Require Import bitseq notation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope bits_scope.

(* Optimized cardinality *)
Section Card.

Section CardDef.

Variable (n k : nat).

(* Cardinality table *)
Definition ctable  := seq 'B_n.
Definition ctableP (t : ctable) :=
  forall (bk : 'B_k), nth '0 t (nats bk) = inB (count id bk).

(** [pop_table] returns a k-list of words of size [n]
  * counting the numbers of bits.
  *)
(* =pop_table= *)
Definition pop_table : seq 'B_n :=
  mkseq (fun i => inB (count id (bitn k i))) (2^k).
(* =end= *)

Lemma pop_table_size : size pop_table = 2^k.
Proof. by rewrite size_mkseq. Qed.

Lemma pop_tableP : ctableP pop_table.
Proof.
move=> bk; rewrite nth_mkseq -?{1}(size_tuple bk) ?natsK //.
by rewrite -{2}(size_tuple bk) nats_ltn.
Qed.

(* An alternative way is to define pop_table as a map: *)
Definition pop_table_fun {n} k : {ffun 'B_k -> 'B_n} :=
  [ffun bk => inB (count id (val bk))].

Lemma pop_table_funP (bk : 'B_k) :
  pop_table_fun k bk = @inB n (count id bk).
Proof. by rewrite ffunE. Qed.

(** [pop_elem bs i] return the cardinality of the [i]-th part of
  * of [bs].
  *)
(* =pop_elem= *)
Definition pop_elem (bs: 'B_n) i : 'B_n :=
  let x := andB (shrB bs (i * k))
                (decB (shlB (inB 1) k))
  in nth '0 pop_table (nats x).
(* =end= *)

(* Don't we want to shift here maybe ? *)
(* =card= *)
Definition card_rec (bs: 'B_n) := fix cr i : 'B_n :=
    match i with
    | 0     => '0
    | i'.+1 => addB (pop_elem bs i') (cr i')
    end.

Definition cardinal (bs: 'B_n) : 'B_n
  := card_rec bs (n %/ k).
(* =end= *)

End CardDef.

(* Poor man's square root *)
Definition pm_sqrt n :=
  let sq := fix sq m := if m*m <= n then m else
                        if m is m.+1 then sq m else 0
  in sq n.

(* This version uses an heuristic *)
Definition cardinal_smart n (bs: 'B_n) : 'B_n :=
  cardinal (pm_sqrt n) bs.

Eval compute in (map (fun n => nats (tval n)) (@pop_table 4 2)).
Eval compute in (map (fun n => nats (tval n)) (@pop_table 32 4)).
Eval compute in (val (@pop_elem 3 1 [tuple true; false; true] 0)).
Eval compute in (val (cardinal 2 [tuple true; true])).

Section CardTheory.

Lemma card_rec_cons n k i (bv : 'B_n) :
  card_rec k bv i.+1 =
  addB (pop_elem k bv i) (card_rec k bv i).
Proof. by []. Qed.

(* ss is a partition of S then *)
(*  "cardb S = \sum(s <- ss) cardb s" *)
(* Lemma cardinalE n k (bv : 'B_n) : *)
(*   nats (cardinal k bv) = *)
(*   \sum_(pbv <- reshape (nseq (n %/ k) k) bv) (nats pbv). *)
(* Proof. *)
(* rewrite /cardinal. *)
(* elim: (n %/ k) {1 2 3 6}n bv => [|nk ihnk] nv bv. *)
(*   by rewrite nats_zero big_nil. *)
(* rewrite card_rec_cons [reshape _ _]/= big_cons -ihnk. *)
(* Admitted. *)

(* Lemma cardinalE : \sum_(l reshape  *)

(* Lemma cardinalP k (s : 'B_k) i (* (div_i: i %| k) (ltz_i: i > 0) *) : *)
(* Lemma cardinalP k (s : 'B_k) i : *)
(*   nats (cardinal i s) = count id s. *)
(* Proof. *)
(* Admitted. *)

End CardTheory.
End Card.

Section BitMin.

Section Local.

From CoqEAL
Require Import refinements.
Import Refinements.Op.

Local Open Scope computable_scope.

(* Set containing only the minimum *)
(* =keep_min= *)
Definition keep_min n (bs: 'B_n) : 'B_n
  := bs && - bs.
(* =end= *)

End Local.

(* XXX: Move *)
Lemma setls_here y s x : setls [:: y & s] 0 x = [:: x & s].
Proof. by []. Qed.

(* XXX: Better proof using tuples? *)
(* Lemma keep_minP n (bs: 'B_n) : *)
(*   keep_min bs = setlB '0 (index true bs) true. *)
(* eq_from_tnth *)

(* Lemma andB_invB: *)
(*   forall n (bs: BITS n), *)
(*     andB bs (invB bs) = zero n. *)

(* Ummm *)
(* Lemma oppB_def n (bs : 'B_n) : oppB bs = incB (negB bs). *)
(* Proof. *)
(* case: n bs => [|n] [s hs]; apply/val_inj; rewrite /= ?bitn_nil //. *)
(* congr bitn. *)
(* rewrite addnC bitnK ?inE ?expnS_ge2 //. *)
(* elim: n s hs => [|n ihn] [|b s] hs //. *)
(*   by case: s hs => //= _; case: b. *)
(* rewrite !nats_cons expnS mul2n. *)
(* Admitted. *)

Lemma exp2n_gt0 m : 0<2^m.
Proof. by rewrite expn_gt0. Qed.

(* Lemma nats_one : nats *)

Lemma oppB_def n (bs : 'B_n) : oppB bs = incB (negB bs).
Proof.
apply/val_inj; rewrite /= prednK ?expn_gt0 //.
case: n bs => [|n] // bs.
case: (bs == '0) / eqP => [->|hbs].
  rewrite nats_zero subn0 modnn negs_zero nats_full.
  by rewrite bitnK ?inE ?expnS_ge2 // subnK ?expn_gt0 // modnn.
have n_gt0 : 0 < nats bs.
  move/eqP: hbs; rewrite -val_eqE /=; case: bs => /=.
  elim: n => [|n ihn] [|b s] //= hs.
    by case: s hs; case: b.
  rewrite eqseq_cons /=; case: b; rewrite // negb_and eqxx /=.
  by rewrite nats_cons add0n double_gt0 => /ihn ->.
have n_leq : nats (negs bs) < (2^n.+1).-1.
  admit.
rewrite bitnK ?inE ?expnS_ge2 //.
rewrite modn_small; last first.
  by rewrite -[X in _ < X]subn0 ltn_sub2l ?expn_gt0.
rewrite modn_small; last first.
  move: (n_leq).
  rewrite -subn_gt0 -(ltn_add2l 1).
  rewrite addn0 -ltn_subRL addnBA; last by rewrite ltnW.
  by rewrite add1n prednK ?expn_gt0.
congr bitn.
Search _ nats.
have U s: 1 + nats (negs s) = 2^(size s) - nats s.
  elim: s => [|b s ihs].
    by rewrite /= (nats_zero 0) expn0.
Admitted.

Lemma negs_cons b s : negs [:: b & s] = [:: ~~ b & negs s].
Proof. by []. Qed.

Lemma negs_one n : negs '1_n = '0_n.
Proof. by rewrite /negs map_nseq. Qed.

Lemma ands_negs s : ands s (negs s) = '0_(size s).
Proof. by elim: s => // b s ihs; rewrite ands_cons andbN ihs. Qed.

From CoqEAL
Require Import refinements.
Import Refinements.Op.
Import Logical.Op.

(* =keep_minP= *)
Lemma keep_minP n (bs: 'B_n) :
  keep_min bs = setls '0_n (index true bs) true :> bitseq.
(* =end= *)
Proof.
rewrite /keep_min/opp_op/opp_B/and_op/and_B oppB_def; case: bs => [s hs] /=.
case: n hs => // [|n hs].
  by rewrite bitn_nil; case: s.
rewrite bitnK ?(ltn_predK (expnS_ge2 _)) ?inE ?expnS_ge2 //.
(* We need to case on wether we overflow or not *)
case: (s == '0_n.+1) / eqP => [->|hno].
  rewrite negs_zero nats_full subn1 addn1 (ltn_predK (expnS_ge2 _)) modnn.
  rewrite and0s ?inE ?size_bitn //=.
  rewrite setls_default //= size_nseq.
  have/(congr1 negb) := index_mem true '0_n.
  rewrite ltnNge negbK size_nseq ltnS => ->.
  by elim: n {hs}.
rewrite modn_small addnC; last first.
  elim: n s hs hno => [|n ihn] [|b s] hs hno //=.
    by case: s hs hno => //; case: b.
    rewrite expnS nats_cons mul2n.
    case: b hs hno => //= hs hno.
      rewrite add0n.
      have := nats_ltn (negs s).
      have hss : size s = n.+1 by case/eqP: hs.
      rewrite size_map hss.
      by rewrite -doubleS leq_double.
    rewrite !add1n -doubleS ltn_double ihn //.
    by move/eqP: hno; rewrite eqseq_cons eqxx negb_and /= => /eqP.
elim: n s hs hno => [|n ihn] [|b s] hs hno //=.
  by case: s hs hno => //; case: b.
rewrite nats_cons bitn_cons ands_cons /=.
case: b hs hno => //= /eqP [hs] /eqP hno.
  rewrite setls_here add0n uphalf_double.
  have hss: size (negs s) = n.+1 by rewrite size_map.
  by rewrite -hss natsK ands_negs hs odd_double.
rewrite setls_cons half_double -add1n ihn ?hs //.
by move: hno; rewrite eqseq_cons eqxx negb_and /= => /eqP.
Qed.

(* Value of the minimum (ie number of trailing zeroes) *)
(* =ntz= *)
Definition ntz n (bs: 'B_n) : 'B_n :=
  subB (inB n) (cardinal_smart (orB bs (oppB bs))).
(* =end= *)

(* =ntzP= *)
(* Lemma ntzP n (bs : 'B_n) : ntz bs = inB (index true bs). *)
(* =end= *)
(* Proof. *)
(* rewrite /ntz. *)
(* suff : n - count id (orB bs (oppB bs)) = index true bs. *)
(*   admit. *)
(* apply: (@addIn (count id (orB bs (oppB bs)))). *)
(* rewrite subnK ?(leq_trans (count_size _ _)) ?size_tuple //. *)
(*
This should derive from the mask theory.
orB bs (oppB bs) = 00000011111111111 = bmask (index ) n
                         ^ index

Useful lemma from the old development:
Definition negB {n} (p: BITS n) := incB (invB p).

*)
(* Admitted. *)

(*  *)
Definition U_test n (bs : 'B_n) :=
  (nats (ntz bs),
   nats (@inB n (index true bs)),
   nats (keep_min bs),
   nats (setls '0_n (index true bs) true)).

Definition U_inputs :=
[:: ( 0, [::])
 ;  ( 1, [:: false])
 ;  ( 2, [:: true ; true])
 ;  ( 3, [:: true ; false])
 ;  ( 4, [:: false; true])
 ;  ( 5, [:: false; false])
 ;  ( 6, [:: false; false; false; false; false])
 ;  ( 7, [:: true; false;  false; false; false])
 ;  ( 8, [:: false; false; true;  false; false])
 ;  ( 9, [:: false; false; true;  false; true])
 ;  (10, [:: false; false; false; false; true])
].

(* Compute map (fun u => (u.1, U_test (in_tuple u.2))) U_inputs. *)
(* Definition ntz' n b := n - count id (ors b (opps b)). *)

End BitMin.
