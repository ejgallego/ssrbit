From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.

From mathcomp
Require Import choice fintype finset tuple ssralg zmodp matrix bigop mxalgebra.
From CoqEAL
Require Import hrel param refinements.

Require Import bitseq bitword notation bits bitocaml bitset.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Refinements.Op.
Import Logical.Op.
Import Sets.Op.

(* Board size *)
Definition n := 8. (* XXX: generalize to any [n > 0] *)

Definition T := [finType of 'I_n].

Module Fintype : FINTYPE with Definition T := T.
  Definition T: finType := T.
End Fintype.


(*****************************************************************)
(** * n-queens positions                                         *)
(*****************************************************************)

(** We offer a generic, iterator-like interface for board positions,
    together with an accessibility predicate for recursion over
    positions. *)

Module Type POS.

Parameter pos : Type.

Parameter initp  : pos.
Parameter fullp  : pos -> bool.
Parameter validp : pos -> bool.
(* Next from actual position *)
Parameter nextp  : pos -> pos.
(* Alternative from actual position *)
Parameter altp   : pos -> pos.
Parameter le_pos : pos -> pos -> Prop.

Axiom le_pos_wf : well_founded le_pos.
Axiom nextp_wf  : forall p, le_pos (nextp p) p.
Axiom altp_wf   : forall p, le_pos (altp  p) p.

End POS.

(*********************************************************)
(** ** Board specification                               *)
(*********************************************************)

(** This is the proof-oriented and computationally inert specification
of the board position. *)

Module Spec <: POS.

Local Open Scope ring_scope.

Definition board := 'M[bool]_n.
Definition rowt  := 'I_n.
Definition colt  := 'I_n.

Implicit Types (b : board) (i : rowt) (j : colt).

Record pos' := mk_pos { p_board    :> board ;
                        p_curr_row :  rowt  ;
                        p_curr_col :  colt  ;
                      }.

(* XXX: Why couldn't I directly declare [pos] as a [record]? *)
Definition pos := pos'.
Implicit Types (p : pos).

Coercion to_board p : 'M_n := p_board p.

(* EG: Improvements welcome *)
Notation "p .'i" := (p_curr_row p)
  (at level 2, left associativity, format "p .'i") : pair_scope.

Notation "p .'j" := (p_curr_col p)
  (at level 2, left associativity, format "p .'j") : pair_scope.

(* Coercion to_pos p : (rowt * colt) := (p_curr_row p, p_curr_col p). *)

Definition valC p :=
  [forall (x : rowt | x < p.'i), ~~ p x p.'j].

(* Valid row *)
Definition valR p :=
  [forall (y : colt | y != p.'j), ~~ p p.'i y].

(* Valid ascending diagonal *)
Definition valA p :=
  [forall (x : rowt | x < p.'i),
   forall (y : colt | (maxn p.'i p.'j - minn p.'i p.'j == maxn x y - minn x y)%N),
   ~~ p x y ].

(* Valid descending diagonal *)
Definition valD p :=
  [forall (x : rowt | x < p.'i),
   forall (y : colt | (p.'i + p.'j == x + y)%N),
   ~~ p x y].

(* Valid position *)
Definition valp p := [&& valC p, valR p, valA p & valD p].

(* Update column *)
Definition upC p j := mk_pos p p.'i j.

Definition upC_id p : upC p p.'j = p.
Proof. by case: p. Qed.

(* Update row *)
Definition upR p i := mk_pos p i p.'j.
Definition upR_id p j : upR p p.'i = p.
Proof. by case: p. Qed.

Definition full_below p :=
  [forall (x : rowt | x < p.'i),
   exists j, p x j && valp (upC p j) ].

(* Lemma is_full_belowP b i j : *)
(*   reflect (exists ) (is_full_below b i j) *)

Definition empty_above p :=
  [forall (x : rowt | x > p.'i), forall j, ~~ p x j].

Definition Inv p :=
  [&&
   (* Current position is valid: *)
     valp p
   (* One valid queen on each row below [p_curr_row]: *)
   , full_below p
   (* No queen on any row above [p_curr_row]: *)
   & empty_above p ].


Definition cols p :=
  [set j in colt | valC (upC p j)].

Lemma pred_ord_nat (p : pred nat) k :
  #|[pred x : 'I_k | p x] | = count p (iota 0 k).
Proof.
rewrite cardE size_filter.
have h_eq: [pred x : 'I_k | p x] =1 (preim val p) by [].
by rewrite (eq_count h_eq) -count_map unlock val_ord_enum.
Qed.

Lemma count_iota (i j n : nat) : count [pred x | x < j] (iota i n) = minn (j - i)%N n.
Proof.
elim: n i => [|n ihn] i /=; first by rewrite minn0.
rewrite {}ihn subnS; case: ltnP; rewrite ?(add1n, add0n).
  by case: j => // j hj; rewrite subSn ?minnSS.
by rewrite -subn_eq0 => /eqP ->; rewrite !min0n.
Qed.

Lemma curr_col_cols p : Inv p -> p.'i = (n - #| cols p |)%N :> nat.
Proof.
rewrite /Inv /cols /=.
case/and3P => /and4P [h11 h12 h13 h14].
move/forallP=> h_full_below.
move/forallP=> h_empty_above.
simpl in *.
(* rewrite cardsE /= eqnE. *)
(* have U u : [forall (x : 'I_n | x < i), ~~ b x u] =  *)
  admit.
(* rewrite cardsE /= (eq_card U) (pred_ord_nat [pred x | x < j]). *)
(* rewrite count_iota subn0. *)
Admitted.

Definition asc_diag   p := [set j in colt | valA (upC p j) ].

Definition desc_diag  p := [set j in colt | valD (upC p j) ].

Definition valid_cols p := [set y in colt | (p.'j <= y) && valp (upC p y) ].

Lemma curr_col_valid  p : Inv p ->
    p.'j = [arg min_(j' < p.'j | j' \in valid_cols p ) j' ]%N.
Proof.
case/and3P=> [Hval_ij Hfull Hemp]; simpl in *.
case: arg_minP => [|x]; first by rewrite inE; apply/and3P.
rewrite !inE; case/and4P=> [H11 H12 H13 H14] H2.
have H3: (x <= p.'j) by apply H2; rewrite inE; apply/and3P.
by apply/val_inj/eqP; rewrite /= eqn_leq H12.
Qed.

Definition init : pos := mk_pos (const_mx false) ord0 ord0.

Lemma inv_init: Inv init.
apply/and3P; split.
(* XXX: no is_valid_posP ?? *)
+ apply/and4P; split.
  (* XXX: no is_valid_colP ?? *)
  - by apply/forallP.
  - by apply/'forall_implyP=> x hx; rewrite mxE.
  - by apply/'forall_implyP=> x hx; apply/forallP=> y; rewrite mxE.
  - by apply/'forall_implyP=> x hx; apply/forallP=> y; rewrite mxE.
  (* A pity the lack of computation in forallP... *)
+ by apply/'forall_implyP=> x hx; apply/'exists_andP; exists ord0.
+ by apply/'forall_implyP=> x hx; apply/forallP=> y; rewrite mxE.
Qed.

Definition is_full   p := #| cols p | == 0%N.
Definition has_valid p := #| valid_cols p | != 0%N.

Definition next_row (i : 'I_n) : 'I_n := insubd ord_max i.+1.

Lemma leq_next_row i i' : (i < next_row i') = (i <= i').
Proof.
rewrite val_insubd; case: ifP => // /negbT.
rewrite ltnNge negbK.
Admitted.

(* j is the column *)
Definition update_board_nosimpl p j :=
  mk_pos (\matrix_(x , y) ([&& x == p.'i & y == p.'j] || p x y)) (next_row p.'i) j.

Definition update_board := nosimpl update_board_nosimpl.

Lemma update_board_M p k (x y : 'I_n) :
  (to_board (update_board p k)) x y = [&& x == p.'i & y == p.'j] || p x y.
Proof. by rewrite mxE. Qed.

Lemma update_board_i p j : (update_board p j).'i = next_row p.'i.
Proof. by []. Qed.

Lemma update_board_j p j : (update_board p j).'j = j.
Proof. by []. Qed.

Lemma upC_update_board p j j' : upC (update_board p j) j' = update_board p j'.
Proof. by []. Qed.

Definition upE := (update_board_M, update_board_i, update_board_j, upC_update_board).

Definition compute_pos p : option pos :=
  match [pick col in 'I_n | valp (update_board p col) ] with
  | None     => None
  | Some col => Some (update_board p col)
  end.

(* Main next position *)
Definition nextp p :=
  match compute_pos p with
  | None    => p
  | Some p' => p'
  end.

CoInductive nextp_spec p : pos -> Prop :=
 | NVC_Same   : (forall j, ~ valp (update_board p j)) ->
                nextp_spec p p
 | NVC_Update : forall j,    valp (update_board p j) ->
                nextp_spec p (update_board p j)
 .

Lemma nextpP p : nextp_spec p (nextp p).
Proof.
rewrite /nextp /compute_pos; case: pickP => [w /andP [hw1 hw2] |hwN].
  by constructor 2.
by constructor 1 => j hj; have/negP := hwN j.
Qed.

Lemma inv_next_valid_with_curr p : Inv p -> Inv (nextp p).
Proof.
case: nextpP => // j hj /and3P[hi1 hi2 hi3]; apply/and3P; split => //.
+ rewrite /full_below update_board_i; apply/'forall_implyP=> i hi.
  apply/'exists_andP; exists p.'j; split; rewrite !upE.
  - admit.
  - admit.
Admitted.

Lemma next_with_cols p (hinv : Inv p) : cols (nextp p) = cols p :\ p.'j.
Proof.
case/and3P: hinv => hi1 hi2 hi3; case: nextpP => //= [hvalN | j hval].
  rewrite /cols; apply/setP=> j0; rewrite !inE /= andb_idl //.
  move=> _; apply/negP=> _ {j0}.
  apply: (hvalN p.'j) => {hvalN}.
  move/'forall_implyP: hi2 => hi2.
  rewrite /update_board /update_board_nosimpl /=.
  admit.
rewrite /cols; apply/setP=> j0; rewrite !inE /= upC_update_board.
case: eqP => [->| hjneq] //=.
+ apply/negbTE; rewrite /valC -negb_exists_in negbK !upE.
  apply/existsP; exists (p.'i); rewrite !upE !eqxx /= andbT.
  (* Ummm. *)
  case/and4P: hval => h11 h12 h13 h14.
  admit.
rewrite /valC -!negb_exists_in; congr negb.
apply/existsP/existsP=> -[j1]; rewrite 2!upE /=.
  case/andP=> hj /orP[ /andP[/eqP h1 /eqP h2 //]|hp].
  rewrite leq_next_row in hj.
  exists j1.
  (* Does this mean that we need to add a side condition on p.'i ?? *)
  admit.
case/andP => hj hpj.
exists j1; rewrite mxE hpj orbT andbT.
by rewrite leq_next_row ltnW.
Admitted.

Lemma next_with_asc_diag p : Inv p ->
    p.'i < n ->
    asc_diag (nextp p) = shrS (p.'j |: asc_diag p) (inord 1).
Admitted.

Lemma next_with_desc_diag p : Inv p ->
    p.(p_curr_row) < n ->
    desc_diag (nextp p) = shlS (p.'j |: desc_diag p) (inord 1).
Admitted.

Lemma next_with_valid_cols' p :
    valid_cols (nextp p) = valid_cols p :\ p.'j.
Admitted.

Lemma next_with_valid_cols p p' : Inv p ->
    p' = nextp p ->
    valid_cols p' = cols p' :&: ~: (asc_diag p' :|: desc_diag p').
Admitted.

(*********** Emilio ***********)

Definition next_valid_without_curr (p: Pos): Pos :=
  let b := p.(p_board) in
  let i := p.(p_curr_row) in
  let j := p.(p_curr_col) in
  match [pick col in 'I_n | (j < col) && is_valid_pos b i col ] with
  | Some col => 
    let 'col := [arg min_(j' < col | (j < j') && is_valid_pos b i j') j' ]%N in
    Mk_pos' b i col
  | None => p
  end.

Lemma inv_next_valid_without_curr: forall p, Inv p -> Inv (next_valid_without_curr p).
Admitted.

Lemma next_without_cols: forall p, Inv p ->
    cols (next_valid_without_curr p) = cols p.
Proof.
move=> [b i j] /and3P[Hv Hf Hb] //=.
rewrite /next_valid_without_curr.
by case pickP=> [col /and3P [Hcol1 Hcol2 Hcol3]|Hempty].
Qed.

Lemma next_without_asc_diag: forall p, Inv p ->
    asc_diag (next_valid_without_curr p) = asc_diag p.
move=> [b i j] /and3P[Hv Hf Hb] //=.
rewrite /next_valid_without_curr.
by case: pickP=> [col /and3P [Hcol1 Hcol2 Hcol3]|Hempty].
Qed.

Lemma next_without_desc_diag: forall p, Inv p ->
    desc_diag (next_valid_without_curr p) = desc_diag p.
move=> [b i j] /and3P[Hv Hf Hb] //=.
rewrite /next_valid_without_curr.
by case pickP=> [col /and3P [Hcol1 Hcol2 Hcol3]|Hempty].
Qed.

Lemma next_without_valid_cols: forall p, Inv p ->
    valid_cols (next_valid_without_curr p) = valid_cols p :\ p.(p_curr_col).
Proof.
move=> [b i j] /and3P[Hv Hf Hb].
rewrite /next_valid_without_curr.
case pickP=> [col /and3P [Hcol1 Hcol2 Hcol3]|Hempty].
- simpl in *.
  apply/setP=> y; rewrite !inE /=.
  apply/andP/and3P.
  + move=> [H1 H2].
    have Hjy: j < y.
      rewrite (leq_trans _ H1) //.
      by case: arg_minP; rewrite ?Hcol2 ?Hcol3 // => k /andP[hk _].
    split=> //.
    * by rewrite neq_ltn Hjy orbT.
    * by apply: ltnW.
  + move=> [H1 H2 Hval].
    split=> //.
    case arg_minP.
    * by apply/andP; split.
    * move=> y' /andP [Hjy' Hval_y'] H.
      apply H. apply /andP; split=> //.
      rewrite ltn_neqAle; apply /andP; split=> //.
      apply/eqP=> H'.
      apply val_inj in H'.
      rewrite H' //= in H1 .
      move/eqP: H1.
      exact.
- have H0: valid_cols {| p_board := b; p_curr_row := i; p_curr_col := j |} = set0.
  simpl in *.
  apply/setP=> c; rewrite !inE; apply/and3P; case=> [/= _ h1 /and4P /= [h2 h3 h4 h5]].
  have := Hempty c; move/idP; apply.
  rewrite /is_valid_pos h2 h3 h4 h5 !andbT.
  admit.
  by rewrite H0 set0D.
Admitted.

Require Import Wellfounded.Lexicographic_Product.
Import Relation_Operators.

Definition Pos_order (p1 p2: Pos): Prop.
(* XXX: disgusting and useless definition *)
eapply lexprod with (A := 'I_n)(B := fun _ => ('I_n * board)%type).
exact (fun x y => lt (val x) (val y)).
move=> ?.
intros.
eapply lexprod with (A := 'I_n) (B := fun _ => board).
exact (fun x y => lt (val x) (val y)).
move=> ?.
exact (fun b1 b2 => [forall i, [forall j, b1 i j ==> b2 i j]]).
split; case:X => [? ?] //.
split; case:X0 => [? ?] //.
split; [|split]; case: p1=> [? ? ?]//.
split; [|split]; case: p2=> [? ? ?]//.
Defined.

Lemma Pos_wf: well_founded Pos_order.
Admitted. (* XXX: define *)
 Lemma next_valid_with_curr_wf: forall p, Pos_order (next_valid_with_curr p) p.
Admitted. (* XXX: prove *)
Lemma next_valid_without_curr_wf: forall p, Pos_order (next_valid_without_curr p) p.
Admitted. (* XXX: prove *)

(*
Lemma lt_wf: well_founded lt.
Proof.
have H : forall m n, (n < m)%coq_nat -> Acc lt n.
{
  move=> m; elim: m=> [|m IHm] n Hlt_n.
  - inversion Hlt_n.
  - constructor=> y Hlt_y.
    eapply IHm, PeanoNat.Nat.lt_le_trans; eauto using Lt.lt_n_Sm_le. 
}
by move=> n; constructor; apply H.
Qed.
*)

Local Close Scope ring_scope.

End Spec.

(*********************************************************)
(** ** Board implementation                              *)
(*********************************************************)

(** This is the computation-oriented implementation of the board
    position. It is parameterized over the concrete implementation of
    machine words: we shall do a refinement there too, once using the
    axiomatized (native) integers and once using the ssrbit model. *)

Section Machine.

Variable (int: Type).

Context `{eq_of int}.
Context `{inter_of int}.
Context `{compl_of int}.
Context `{union_of int}.
Context `{empty_of int}.
Context `{full_of int}.
Context `{keep_min_of int}.
Context `{cardinal_of nat int}.
Context `{succ_of int}.
Context `{pred_of int}.

Record Pos := Mk_pos { p_cols: int ; 
                       p_asc_diag: int;
                       p_desc_diag: int;
                       p_valid: int }.

Definition Pos_order (p1 p2: Pos): Prop :=
    (cardinal_op p1.(p_cols) < cardinal_op p2.(p_cols))
  \/ (  cardinal_op p1.(p_cols) = cardinal_op p2.(p_cols)
     /\ cardinal_op p1.(p_valid) < cardinal_op p2.(p_valid)).

Definition init := Mk_pos full_op full_op full_op full_op.
Definition is_full p := eq_op p.(p_cols) empty_op.
Definition has_valid p := negb (eq_op p.(p_valid) empty_op).

Definition next_valid_with_curr p :=
  let d := keep_min_op p.(p_valid) in
  let cols := (p.(p_cols) :&: (compl_op d))%C in
  let asc_diag := succ_op (p.(p_asc_diag) :|: d)%C in
  let desc_diag := pred_op (p.(p_desc_diag) :|: d)%C in
  let valid := (cols :&: compl_op (asc_diag :|: desc_diag))%C in
  Mk_pos cols asc_diag desc_diag valid.

Definition next_valid_without_curr p :=
  let d := keep_min_op p.(p_valid) in
  let valid := (p.(p_valid) :&: (compl_op d))%C in
  Mk_pos p.(p_cols) p.(p_asc_diag) p.(p_desc_diag) valid.


End Machine.

Arguments Mk_pos {_} p_cols p_asc_diag p_desc_diag p_valid.
Arguments p_cols [_] p.
Arguments p_asc_diag [_] p.
Arguments p_desc_diag [_] p.
Arguments p_valid [_] p.

Parametricity Pos.
(* Parametricity Pos_order. *)
Parametricity init.
Parametricity is_full.
Parametricity has_valid.
Parametricity next_valid_with_curr.
Parametricity next_valid_without_curr.

(*************************************************)
(** *** Abstract machine board                   *)
(*************************************************)

(** This implementation models the behavior of the machine
    representation. It is proof-oriented. *)

Module FSet <: POS.

Definition Pos := Pos {set 'I_n}.
Definition Pos_order := Pos_order {set 'I_n}.

Definition init := init {set 'I_n}.
Definition is_full := is_full {set 'I_n}.
Definition has_valid := has_valid {set 'I_n}.
Definition next_valid_with_curr := next_valid_with_curr {set 'I_n}.
Definition next_valid_without_curr := next_valid_without_curr {set 'I_n}.


Lemma Pos_wf: well_founded Pos_order. 
Proof.
Admitted. (* XXX: TODO *)

Lemma next_valid_with_curr_wf: forall p, Pos_order (next_valid_with_curr p) p.
Admitted. (* XXX: TODO *)

Lemma next_valid_without_curr_wf: forall p, Pos_order (next_valid_without_curr p) p.
Admitted. (* XXX: TODO *)

End FSet.

(*************************************************)
(** *** Native machine board                     *)
(*************************************************)

(** This is the extraction-oriented definition. It is purely axiomatic
    and won't execute inside Coq. *)

Module R  := Make(Fintype).
Module Native := R.Native.

Module NSet <: POS.

Definition Pos := Pos Native.Int.
Definition Pos_order := Pos_order Native.Int.

Definition init := init Native.Int.
Definition is_full := is_full Native.Int.
Definition has_valid := has_valid Native.Int.
Definition next_valid_with_curr := next_valid_with_curr Native.Int.
Definition next_valid_without_curr := next_valid_without_curr Native.Int.

(* XXX: Follow from the refinements above. *)
Axiom Pos_wf: well_founded Pos_order.
Axiom next_valid_with_curr_wf: forall p, Pos_order (next_valid_with_curr p) p. 
Axiom next_valid_without_curr_wf: forall p, Pos_order (next_valid_without_curr p) p.

End NSet.

(*********************************************************)
(** ** Board refinement                                  *)
(*********************************************************)

Local Open Scope rel.

(*************************************************)
(** *** Abstract [->] Machine refinement         *)
(*************************************************)

(** From the abstract board to the machine board *)

Local Open Scope ring_scope.

Definition Rspec (p_spec: Spec.Pos)(p_word: FSet.Pos): Type :=
  [/\ Spec.Inv p_spec
   ,  Spec.cols p_spec =i p_word.(p_cols)
   ,  Spec.asc_diag p_spec =i p_word.(p_asc_diag)
   ,  Spec.desc_diag p_spec =i p_word.(p_desc_diag)
   &  Spec.valid_cols p_spec =i p_word.(p_valid) ].
  
Global Instance Rspec_init: 
  refines Rspec Spec.init FSet.init.
Proof.
rewrite refinesE; split.
- by apply Spec.inv_init.
- rewrite /Spec.init/Spec.is_valid_col/Spec.cols /= /full_op/bitset.full_fin.
  move=> k /=.
  rewrite !inE. 
  apply/forallP=> i.
  apply/implyP=> _.
  by rewrite mxE.
- move=> k /=.
  rewrite !inE.
  apply/forallP=> x.
  by apply/implyP.
- move=> k /=.
  rewrite !inE /=.
  apply/forallP=> x.
  by apply/implyP.
- move=> k /=.
  rewrite !inE /=.
  apply/and4P; split=> //.
  + apply/forallP=> x.
    by apply/implyP.
  + apply/forallP=> x.
    apply/implyP=> _.
    by rewrite mxE.
  + apply/forallP=> x.
    by apply/implyP.
  + apply/forallP=> x.
    by apply/implyP.
Qed.

Global Instance Rspec_is_full: 
  refines (Rspec ==> param.bool_R) Spec.is_full FSet.is_full.
Proof.
rewrite refinesE.
move=> x y [Hinv Hcols Hasc_diag Hdesc_diag Hvalid].
suff ->: (Spec.is_full x = FSet.is_full y)
  by apply bool_Rxx.
rewrite /Spec.is_full/FSet.is_full/is_full
        /empty_op/bitset.empty_fin/eq_op/bitset.eq_fin.
move/setP: Hcols=> ->.
apply cards_eq0.
Qed.

Global Instance Rspec_has_valid: 
  refines (Rspec ==> param.bool_R) Spec.has_valid FSet.has_valid.
Proof.
rewrite refinesE.
move=> x y [Hinv Hcols Hasc_diag Hdesc_diag Hvalid].
suff ->: (Spec.has_valid x = FSet.has_valid y)
  by apply bool_Rxx.
rewrite /Spec.has_valid/FSet.has_valid/has_valid
        /empty_op/bitset.empty_fin/eq_op/bitset.eq_fin.
rewrite -lt0n.
move/setP: Hvalid=> ->.
apply card_gt0.
Qed.

Global Instance Rspec_next_valid_with_curr: 
  refines (Rspec ==> Rspec) Spec.next_valid_with_curr FSet.next_valid_with_curr.
Proof.
rewrite refinesE.
move=> x y [Hinv Hcols Hasc_diag Hdesc_diag Hvalid].
(* XXX: Emilio fix this !! *)
have Hspec_curr: [set Spec.p_curr_col x] = keep_min_op (p_valid y) 
  by admit. (* XXX: Need good spec for [keep_min_op] *)
split=> //=;
  first by apply Spec.inv_next_valid_with_curr.
- rewrite Spec.next_with_cols ?Hspec_curr //.
  move/setP: Hcols=> ->.
  by rewrite setDE.
- rewrite (Spec.next_with_asc_diag x) //.
  rewrite /succ_op/succ_fin.
  move/setP: Hasc_diag=> ->.
  by rewrite Hspec_curr setUC.
- rewrite (Spec.next_with_desc_diag x) //.
  rewrite /succ_op/succ_fin.
  move/setP: Hdesc_diag=> ->.
  by rewrite Hspec_curr setUC.
- rewrite (Spec.next_with_valid_cols x) 
          ?Spec.next_with_cols ?Hspec_curr
          ?(Spec.next_with_asc_diag x)
          ?(Spec.next_with_desc_diag x) //.
  move/setP: Hcols=> ->.
  move/setP: Hasc_diag=> ->.
  move/setP: Hdesc_diag=> ->.
  rewrite Hspec_curr 
          /compl_op/compl_fin
          /succ_op/succ_fin
          /pred_op/pred_fin //=.
  by rewrite !setDE ![(keep_min_op _) :|: _]setUC.
Admitted.

Global Instance Rspec_next_valid_without_curr: 
  refines (Rspec ==> Rspec) Spec.next_valid_without_curr FSet.next_valid_without_curr.
Proof.
rewrite refinesE.
move=> x y [Hinv Hcols Hasc_diag Hdesc_diag Hvalid].
have Hspec_curr: [set Spec.p_curr_col x] = keep_min_op (p_valid y) 
  by admit. (* XXX: Need good spec for [keep_min_op] *)
split=> //=;
rewrite ?Spec.next_without_cols
        ?Spec.next_without_asc_diag 
        ?Spec.next_without_desc_diag 
        ?Spec.next_without_valid_cols
        ?Hspec_curr //;
 try now apply Spec.inv_next_valid_without_curr.
move/setP: Hvalid=> ->.
rewrite /inter_op/inter_fin/compl_op/compl_fin.
by rewrite setDE.
Admitted.

(*************************************************)
(** *** Machine [->] Native refinement           *)
(*************************************************)

(** From the specification of machine words to native integers. *)

Definition Rword (wp: FSet.Pos)(np: NSet.Pos): Type
  := Pos_R _ _ R.Rbitset wp np.

Global Instance Rword_init: 
  refines Rword FSet.init NSet.init.
Proof. param init_R. Qed.

Global Instance Rword_is_full: 
  refines (Rword ==> param.bool_R) FSet.is_full NSet.is_full.
Proof. param is_full_R. Qed.

Global Instance Rword_has_valid: 
  refines (Rword ==> param.bool_R) FSet.has_valid NSet.has_valid.
Proof. param has_valid_R. Qed.

Global Instance Rword_next_valid_with_curr: 
  refines (Rword ==> Rword) FSet.next_valid_with_curr NSet.next_valid_with_curr.
Proof. param next_valid_with_curr_R. 
- admit. (* XXX: refinement for [keep_min] *)
- admit. (* XXX: refinement for [succ] *)
- admit. (* XXX: refinement for [pred] *)
Admitted.

Global Instance Rword_next_valid_without_curr: 
  refines (Rword ==> Rword) FSet.next_valid_without_curr NSet.next_valid_without_curr.
Proof. param next_valid_without_curr_R. 
- admit. (* XXX: refinement for [keep_min] *)
Admitted. 

(*********** Emilio ***********)


(*************************************************)
(** *** Abstract [->] Native  refinement         *)
(*************************************************)

(** Composition of the previous refinements *)

Definition RPos: Spec.Pos -> NSet.Pos -> Type := Rspec \o Rword.


Global Instance RPos_init: 
  refines RPos Spec.init NSet.init.
Proof. eapply refines_trans; tc. Qed.

Global Instance RPos_is_full: 
  refines (RPos ==> param.bool_R) Spec.is_full NSet.is_full.
Proof. eapply refines_trans; tc. Qed.

Global Instance RPos_has_valid: 
  refines (RPos ==> param.bool_R) Spec.has_valid NSet.has_valid.
Proof. eapply refines_trans; tc. Qed.

Global Instance RPos_next_valid_with_curr: 
  refines (RPos ==> RPos) Spec.next_valid_with_curr NSet.next_valid_with_curr.
Proof. eapply refines_trans; tc. Qed.

Global Instance RPos_next_valid_without_curr: 
  refines (RPos ==> RPos) Spec.next_valid_without_curr NSet.next_valid_without_curr.
Proof. eapply refines_trans; tc. Qed.

Local Close Scope rel.

(*****************************************************************)
(** * n-queens positions                                         *)
(*****************************************************************)


Section Queen_generic.

Variable Pos: Type.

Variable init: Pos.
Variable is_full: Pos -> bool.
Variable has_valid: Pos -> bool.
Variable next_valid_with_curr: Pos -> Pos.
Variable next_valid_without_curr: Pos -> Pos.

Variable Pos_order: Pos -> Pos -> Prop.
Variable Pos_wf: well_founded Pos_order.

Hypothesis Pos_wfP : forall (P1 P2 : well_founded Pos_order), P1 = P2.

Variable next_valid_with_curr_wf   : forall p, Pos_order (next_valid_with_curr p) p.
Variable next_valid_without_curr_wf: forall p, Pos_order (next_valid_without_curr p) p.

Definition nqueens_loop: Pos -> nat ->  nat * Pos.
simple
  refine (Fix Pos_wf (fun pos => nat -> nat * Pos) 
              (fun p nqueens_loop score  =>
    (match has_valid p as b
           return b = has_valid p -> nat * Pos with
    | false => fun _ => (score, p) 
    | true => fun His_not_full => 
      let rec_result := 
          if is_full p then
            1%nat
          else
            let p' := next_valid_with_curr p in
            let (score' , _) := nqueens_loop p' _ score in
            score'
      in
      let score' := (score + rec_result)%N in
      let p' := next_valid_without_curr p in
      let total := nqueens_loop p' _ score' in
      total
     end) (Logic.eq_refl _))); 
  eauto using next_valid_with_curr_wf, next_valid_without_curr_wf.
Defined.


Definition nqueens :=
  let (res , _) := nqueens_loop init 1 in
  res.

End Queen_generic.

Parametricity Acc.
Parametricity nqueens_loop.
Parametricity nqueens.

Module Make (P: POS).

Definition nqueens 
  := nqueens P.Pos 
             P.init P.is_full P.has_valid 
             P.next_valid_with_curr P.next_valid_without_curr
             P.Pos_order P.Pos_wf
             P.next_valid_with_curr_wf P.next_valid_without_curr_wf.

End Make.

(*********************************************************)
(** ** Correctness                                       *)
(*********************************************************)

Module Prove := Make Spec.

Definition valid_board (b: Spec.board): bool :=
  [forall x, exists y, b x y && Spec.is_valid_pos b x y ].

Definition solutions :=  [set x in Spec.board | valid_board x ].

Lemma correctness_spec: Prove.nqueens = #| solutions |.
Admitted. (* XXX *)

(*********************************************************)
(** ** Extraction                                        *)
(*********************************************************)

Module Run := Make NSet.

(* XXX: drop the code to a file and check that it's efficient. *)
(* XXX: write benchmark handler *)
(* Recursive Extraction Run.nqueens. *)

Lemma eq_nqueens: Prove.nqueens = Run.nqueens.
Proof.
have Href_eq: refines Logic.eq Prove.nqueens Run.nqueens.
{
  apply refines_nat_eq.
  rewrite refinesE.
  try apply nqueens_R with (Pos_R := RPos).
  (* XXX: this smells bad.. *)
  admit.
}
by rewrite refinesE in Href_eq.
Admitted. (* XXX: complete missing instances *)

Lemma correctness: Run.nqueens = #| solutions |.
Proof. by rewrite <- correctness_spec, eq_nqueens. Qed.
