From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.
From mathcomp
Require Import choice fintype finset tuple ssralg zmodp matrix bigop mxalgebra.
From CoqEAL
Require Import hrel param refinements.

Require Import bitseq bitword notation bits bitocaml bitset.

Import Refinements.Op.
Import Logical.Op.
Import Sets.Op.



(*****************************************************************)
(** * General recursion axiom                                    *)
(*****************************************************************)

(** Parametrically justifying the termination of the algorithm is
    tricky, to say the least. To side-step this issue, we axiomatize a
    general fixpoint. Needless to say, if used carelessly (ie. in
    proofs), this axiom breaks the consistency of the logic. We can
    use [Print Assumptions proof.] to check that proofs do not depend
    on it.  *)

Section GenRec.

Variable A B: Type.

Axiom order : A -> A -> Prop.
Axiom order_wf: well_founded order.
Axiom gen_rec: forall a1 a2, order a1 a2.

Definition ffix (rec: A -> (A -> B) -> B): A -> B.
simple refine (Fix order_wf (fun a => B)
              (fun a loop  => rec a (fun a => loop a _)));
  auto using gen_rec.
Defined.

End GenRec.

Axiom ffix_rel: 
  forall (A₁ A₂ : Type)(A_R : A₁ -> A₂ -> Type) 
         (B₁ B₂ : Type)(B_R : B₁ -> B₂ -> Type) 
         (rec₁ : A₁ -> (A₁ -> B₁) -> B₁)
         (rec₂ : A₂ -> (A₂ -> B₂) -> B₂),
    (forall (H : A₁) (H0 : A₂),
        A_R H H0 ->
        forall (H1 : A₁ -> B₁) 
               (H2 : A₂ -> B₂),
          (forall (H3 : A₁) (H4 : A₂), A_R H3 H4 -> B_R (H1 H3) (H2 H4)) ->
          B_R (rec₁ H H1) (rec₂ H0 H2)) ->
    forall (H : A₁) (H0 : A₂), A_R H H0 -> B_R (ffix A₁ B₁ rec₁ H) (ffix A₂ B₂ rec₂ H0).

Realizer ffix as ffix_R := ffix_rel.

Arguments ffix [_][_] rec a.

(*****************************************************************)
(** * n-queens positions                                         *)
(*****************************************************************)

(** We offer a generic, iterator-like interface for board positions,
    together with an accessibility predicate for recursion over
    positions. *)

Module Type POS.

(** Position = board + cursor *)
Parameter pos: Type.

(** Initial position: *)
Parameter initp  : pos.

(** Board full (true = sucess): *)
Parameter fullp  : pos -> bool.

(** Board valid (false = failure): *)
Parameter validp : pos -> bool.

(** Next valid position, one row ahead: *)
Parameter nextp  : pos -> pos.

(** Next valid position on the same row: *)
Parameter altp   : pos -> pos.

End POS.


(*****************************************************************)
(** * n-queens board size                                        *)
(*****************************************************************)

(* Board size *)

Module Type BOARDSIZE.
  Variable sizep : nat.
  Definition n := sizep.+1.
End BOARDSIZE.

(*********************************************************)
(** ** Board specification                               *)
(*********************************************************)

(** This is the proof-oriented and computationally inert specification
of the board position. *)

Module Spec (B: BOARDSIZE) <: POS.

Local Open Scope ring_scope.

Import B.

Definition board := 'M[bool]_n.
Definition rowt  := 'I_n.
Definition colt  := 'I_n.

Implicit Types (b : board) (i : rowt) (j : colt).

Record pos' := mk_pos' { p_board    :> board  ;
                         p_curr_row : rowt ;
                         p_curr_col : colt ;
                       }.

Definition pos := pos'. 

Implicit Types (p : pos).

(** *** Getters *) 

Coercion to_board p : 'M_n := p_board p.

Notation "p .'i" := (p_curr_row p)
  (at level 2, left associativity, format "p .'i") : pair_scope.

Notation "p .'j" := (p_curr_col p)
  (at level 2, left associativity, format "p .'j") : pair_scope.

(** *** Setters *) 

Definition upC p j := mk_pos' p p.'i j.

Definition upC_id p : upC p p.'j = p.
Proof. by case: p. Qed.

Definition upR p i := mk_pos' p i p.'j.

Definition upR_id p j : upR p p.'i = p.
Proof. by case: p. Qed.

(** *** Validity predicates *)

Definition valC p :=
  [forall (x : rowt | x < p.'i), ~~ p x p.'j].

Definition valR p :=
  [forall (y : colt | y != p.'j), ~~ p p.'i y].

Definition valA p := 
  [forall (x : rowt | x < p.'i),
      forall (y : colt | (maxn p.'i p.'j - minn p.'i p.'j == maxn x y - minn x y)%N),
        ~~ p x y ].

Definition valD p := 
  [forall (x : rowt | x < p.'i),
      forall (y : colt | (p.'i + p.'j == x + y)%N),
        ~~ p x y].

Definition valp p :=
  [&& valC p, valR p, valA p & valD p ].

(** *** Structural invariants *)

Definition full_below p := 
  [forall (x : rowt | x < p.'i), exists j, p x j && valp p ].

Definition empty_above p :=
  [forall (x : rowt | x > p.'i), forall j, ~~ p x j].


Definition Inv p :=
  [&& 
     (* Current position is valid: *)
     valp p
   , (* One valid queen on each row below [p_curr_row]: *)
     full_below p
   & (* No queen on any row above [p_curr_row]: *)
     empty_above p ].

(** *** Sets of potential positions *)

Definition cols p: {set 'I_n} :=
  [set j in 'I_n | valC (upC p j)].

Lemma curr_col_cols: forall p, Inv p ->
    (p.(p_curr_col) : nat) = (n - #| cols p |)%N.
Proof.
case=> [b i j]; rewrite /Inv /cols /=; case/and3P => h1 h2 h3.
(* rewrite cardsE /=. *)
Admitted.

Definition asc_diag p :=
  [set j in colt | valA (upC p j) ].

Definition desc_diag p :=
  [set j in colt | valD (upC p j) ].

Definition valid_cols (p: pos): {set 'I_n} :=
  [set j in colt | (p.'j <= j) && valp (upC p p.'j)  ].

Lemma curr_col_valid  p : Inv p ->
    p.'j = [arg min_(j' < p.'j | j' \in valid_cols p ) j' ]%N.
Proof.
case/and3P=> [Hval_ij Hfull Hemp]; simpl in *.
case: arg_minP => [|x]; first by rewrite inE; apply/and3P.
rewrite !inE; case/and4P=> [H11 H12 H13 H14] H2.
have H3: (x <= p.'j) by apply H2; rewrite inE; apply/and3P.
by apply/val_inj/eqP; rewrite /= eqn_leq H12.
Qed.

(** *** Iterator implementation *)

(** **** Initial position *) 

Definition initp : pos := mk_pos' (const_mx false) ord0 ord0.

Lemma inv_initp: Inv initp.
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

(** *** Test whether the board is full *)

Definition fullp p := #| cols p | == 0%N.

(** *** Test whether the board is valid *)

Definition validp p := (#| valid_cols p | != 0)%N.

(** *** Compute the next position, after selecting the current position *)

Definition nextR i: rowt := insubd ord_max i.+1.

(* j is the column *)
Definition nextb_nosimpl p j :=
  mk_pos' (\matrix_(x , y) ([&& x == p.'i & y == p.'j] || p x y)) 
          (nextR p.'i) j.

Definition nextb := nosimpl nextb_nosimpl.

Lemma nextb_M p k (x y : 'I_n) :
  (to_board (nextb p k)) x y = [&& x == p.'i & y == p.'j] || p x y.
Proof. by rewrite mxE. Qed.

Lemma nextb_i p j : (nextb p j).'i = nextR p.'i.
Proof. by []. Qed.

Lemma nextb_j p j : (nextb p j).'j = j.
Proof. by []. Qed.

Lemma upC_nextb p j j' : upC (nextb p j) j' = nextb p j'.
Proof. by []. Qed.

Definition nextbE := (nextb_M, nextb_i, nextb_j, upC_nextb).

Definition nextC p : option colt :=
  match [pick col in colt | valp (nextb p col) ] with
  | None     => None
  | Some col => Some [arg min_(j < col | valp (nextb p j)) j ]%N
  end.

Definition nextp p :=
  match nextC p with
  | None    => p
  | Some j  => nextb p j
  end.

CoInductive nextp_spec p : pos -> Prop :=
 | NP_Same   : (forall j, ~ valp (nextb p j)) ->
                nextp_spec p p
 | NP_Update : forall j,    
                 valp (nextb p j) ->
                (forall y, valp (nextb p y) -> j <= y) ->
                nextp_spec p (nextb p j)
 .

Lemma nextpP p : nextp_spec p (nextp p).
Proof.
rewrite /nextp /nextb /nextC. case: pickP => [w /andP [hw1 hw2] |hwN].
by case arg_minP=> //; constructor 2.
by constructor 1 => j hj; have/negP := hwN j.
Qed.

Lemma inv_nextp: forall p, Inv p -> Inv (nextp p).
Admitted.

Lemma nextp_cols p (Hinv: Inv p):
    cols (nextp p) = cols p :\ p.(p_curr_col).
Proof.
case/and3P: Hinv => hi1 hi2 hi3; case: nextpP => //= [hvalN | j hval].
  rewrite /cols; apply/setP=> j0; rewrite !inE /= andb_idl //.
  move=> _; apply/negP=> _ {j0}.
  apply: (hvalN p.'j) => {hvalN}.
  move/'forall_implyP: hi2 => hi2.
  rewrite /nextb /nextb_nosimpl /=.
  admit.
move=> Hmin; rewrite /cols; apply/setP=> j0; rewrite !inE /= upC_nextb.
case: eqP => [->| hjneq] //=.
+ apply/negbTE; rewrite /valC -negb_exists_in negbK !nextbE.
  apply/existsP; exists (p.'i); rewrite !nextbE !eqxx /= andbT.
  (* Ummm. *)
  case/and4P: hval => h11 h12 h13 h14.
  admit.
rewrite /valC -!negb_exists_in; congr negb.
apply/existsP/existsP=> -[j1]; rewrite 2!nextbE /=.
  case/andP=> hj /orP[ /andP[/eqP h1 /eqP h2 //]|hp].
(*   rewrite leq_next_row in hj. *)
  exists j1.
  (* Does this mean that we need to add a side condition on p.'i ?? *)
  admit.
case/andP => hj hpj.
exists j1; rewrite mxE hpj orbT andbT.
(* by rewrite leq_next_row ltnW. *)
Admitted.
   
Lemma nextp_asc_diag: forall p, Inv p ->
    p.(p_curr_row) < n ->
    asc_diag (nextp p) = shrS (p.(p_curr_col) |: asc_diag p) (inord 1).
Admitted.

Lemma nextp_desc_diag: forall p, Inv p ->
    p.(p_curr_row) < n ->
    desc_diag (nextp p) = shlS (p.(p_curr_col) |: desc_diag p) (inord 1).
Admitted.

(*
Lemma nextp_cols': forall p,
    valid_cols (nextp p) = valid_cols p :\ p.(p_curr_col).
Admitted.
*)

Lemma nextp_valid_cols: forall p p', Inv p ->
    p' = nextp p ->
    valid_cols p' = cols p' :&: ~: (asc_diag p' :|: desc_diag p').
Admitted.


(** *** Compute an alternative, same-row/different-column position *)

Definition altC p : option colt :=
  match [pick col in colt | (p.'j < col) && valp (upC p col) ] with
  | None     => None
  | Some col => Some [arg min_(j < col | (p.'j < col) && valp (upC p j)) j ]%N
  end.

Definition altp p :=
  match altC p with
  | None => p
  | Some col => upC p col
  end.

CoInductive altp_spec p : pos -> Prop :=
 | AP_Same   : (forall j, p.'j < j -> ~ valp (upC p j)) ->
                altp_spec p p
 | AP_Update : forall j,
                 valp (upC p j) ->
                (forall y : rowt, p.'j < y -> valp (upC p y) -> j <= y) ->
                altp_spec p (upC p j)
 .

Lemma altpP p : altp_spec p (altp p).
Proof.
rewrite /altp /altC.
case: pickP=> [j /and3P [hj1 hj2 hj3] | hjN].
case: arg_minP=> [|y /andP [hy1 hy2] hlow];
    first by apply /andP.
- constructor 2=> // z hz1 hz2. 
  apply hlow. by apply/andP.
- constructor 1 => j hj.
  have/negP := hjN j.
  by rewrite hj inE.
Qed.

Lemma inv_altp: forall p, Inv p -> Inv (altp p).
Admitted.

Lemma altp_cols: forall p, Inv p ->
    cols (altp p) = cols p.
Proof.
move=> [b i j] /and3P[Hv Hf Hb] //=.
rewrite /altp /altC.
by case pickP=> [col /and3P [Hcol1 Hcol2 Hcol3]|Hempty].
Qed.

Lemma altp_asc_diag: forall p, Inv p ->
    asc_diag (altp p) = asc_diag p.
move=> [b i j] /and3P[Hv Hf Hb] //=.
rewrite /altp /altC.
by case: pickP=> [col /and3P [Hcol1 Hcol2 Hcol3]|Hempty].
Qed.

Lemma altp_desc_diag: forall p, Inv p ->
    desc_diag (altp p) = desc_diag p.
move=> [b i j] /and3P[Hv Hf Hb] //=.
rewrite /altp /altC.
by case pickP=> [col /and3P [Hcol1 Hcol2 Hcol3]|Hempty].
Qed.

Lemma altp_valid_cols: forall p, Inv p ->
    valid_cols (altp p) = valid_cols p :\ p.(p_curr_col).
Proof.
Admitted.
(*
move=> [b i j] /and3P[Hv Hf Hb].
rewrite /altp /altC.
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
(*  have := Hempty c; move/idP; apply.
  rewrite /is_valid_pos h2 h3 h4 h5 !andbT. *)
  admit.
(*   by rewrite H0 set0D. *)
Admitted.
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
Context `{succ_of int}.
Context `{pred_of int}.

Record pos := Mk_pos { p_cols: int ; 
                       p_asc_diag: int;
                       p_desc_diag: int;
                       p_valid: int }.

Definition initp := Mk_pos full_op full_op full_op full_op.
Definition fullp p := eq_op p.(p_cols) empty_op.
Definition validp p := negb (eq_op p.(p_valid) empty_op).

Definition nextp p :=
  let d := keep_min_op p.(p_valid) in
  let cols := (p.(p_cols) :&: (compl_op d))%C in
  let asc_diag := succ_op (p.(p_asc_diag) :|: d)%C in
  let desc_diag := pred_op (p.(p_desc_diag) :|: d)%C in
  let valid := (cols :&: compl_op (asc_diag :|: desc_diag))%C in
  Mk_pos cols asc_diag desc_diag valid.

Definition altp p :=
  let d := keep_min_op p.(p_valid) in
  let valid := (p.(p_valid) :&: (compl_op d))%C in
  Mk_pos p.(p_cols) p.(p_asc_diag) p.(p_desc_diag) valid.

End Machine.

Arguments Mk_pos {_} p_cols p_asc_diag p_desc_diag p_valid.
Arguments p_cols [_] p.
Arguments p_asc_diag [_] p.
Arguments p_desc_diag [_] p.
Arguments p_valid [_] p.

Parametricity pos.
Parametricity initp.
Parametricity fullp.
Parametricity validp.
Parametricity nextp.
Parametricity altp.

(*************************************************)
(** *** Abstract machine board                   *)
(*************************************************)

(** This implementation models the behavior of the machine
    representation. It is proof-oriented. *)

Module FSet (B: BOARDSIZE) <: POS.

Import B.

Definition pos := pos {set 'I_n}.

Definition initp := initp {set 'I_n}.
Definition fullp := fullp {set 'I_n}.
Definition validp := validp {set 'I_n}.
Definition nextp := nextp {set 'I_n}.
Definition altp := altp {set 'I_n}.

End FSet.

(*************************************************)
(** *** Native machine board                     *)
(*************************************************)

(** This is the extraction-oriented definition. It is purely axiomatic
    and won't execute inside Coq. *)

Module NSet (B: BOARDSIZE) <: POS.

Import B.

Definition T := [finType of 'I_n].

Module Fintype : FINTYPE with Definition T := T.
  Definition T: finType := T.
End Fintype.

Module R  := Make(Fintype).
Module Native := R.Native.

Definition pos := pos Native.Int.

Definition initp := initp Native.Int.
Definition fullp := fullp Native.Int.
Definition validp := validp Native.Int.
Definition nextp := nextp Native.Int.
Definition altp := altp Native.Int.

End NSet.

(*********************************************************)
(** ** Board refinement                                  *)
(*********************************************************)

Local Open Scope rel.

(*************************************************)
(** *** Abstract [->] Machine refinement         *)
(*************************************************)

(** From the abstract board to the machine board *)

Module Refinement (B: BOARDSIZE).

Module Spec := Spec B.
Module FSet := FSet B.
Module NSet := NSet B.
Import B.

Local Open Scope ring_scope.

Definition Rspec (p_spec: Spec.pos)(p_word: FSet.pos): Type :=
  [/\ Spec.Inv p_spec
   , Spec.cols p_spec =i p_word.(p_cols)
   , Spec.asc_diag p_spec =i p_word.(p_asc_diag)
   , Spec.desc_diag p_spec =i p_word.(p_desc_diag)
   & Spec.valid_cols p_spec =i p_word.(p_valid) ].
  
Global Instance Rspec_init: 
  refines Rspec Spec.initp FSet.initp.
Proof.
rewrite refinesE; split.
- by apply Spec.inv_initp.
- rewrite /Spec.initp/Spec.valC/Spec.cols /= /full_op/bitset.full_fin.
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
  refines (Rspec ==> param.bool_R) Spec.fullp FSet.fullp.
Proof.
rewrite refinesE.
move=> x y [Hinv Hcols Hasc_diag Hdesc_diag Hvalid].
suff ->: (Spec.fullp x = FSet.fullp y)
  by apply bool_Rxx.
rewrite /Spec.fullp/FSet.fullp/fullp
        /empty_op/bitset.empty_fin/eq_op/bitset.eq_fin.
move/setP: Hcols=> ->.
apply cards_eq0.
Qed.

Global Instance Rspec_has_valid: 
  refines (Rspec ==> param.bool_R) Spec.validp FSet.validp.
Proof.
rewrite refinesE.
move=> x y [Hinv Hcols Hasc_diag Hdesc_diag Hvalid].
suff ->: (Spec.validp x = FSet.validp y)
  by apply bool_Rxx.
rewrite /Spec.validp/FSet.validp/validp
        /empty_op/bitset.empty_fin/eq_op/bitset.eq_fin.
rewrite -lt0n.
move/setP: Hvalid=> ->.
apply card_gt0.
Qed.

Global Instance Rspec_next_valid_with_curr: 
  refines (Rspec ==> Rspec) Spec.nextp FSet.nextp.
Proof.
rewrite refinesE.
move=> x y [Hinv Hcols Hasc_diag Hdesc_diag Hvalid].
have Hspec_curr: [set Spec.p_curr_col x] = keep_min_op (p_valid y) 
  by admit. (* XXX: Need good spec for [keep_min_op] *)
split=> //=;
  first by apply Spec.inv_nextp.
- rewrite Spec.nextp_cols ?Hspec_curr //.
  move/setP: Hcols=> ->.
  by rewrite setDE.
- rewrite (Spec.nextp_asc_diag x) //.
  rewrite /succ_op/succ_fin.
  move/setP: Hasc_diag=> ->.
  by rewrite Hspec_curr setUC.
- rewrite (Spec.nextp_desc_diag x) //.
  rewrite /succ_op/succ_fin.
  move/setP: Hdesc_diag=> ->.
  by rewrite Hspec_curr setUC.
- rewrite (Spec.nextp_valid_cols x) 
          ?Spec.nextp_cols ?Hspec_curr
          ?(Spec.nextp_asc_diag x)
          ?(Spec.nextp_desc_diag x) //.
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
  refines (Rspec ==> Rspec) Spec.altp FSet.altp.
Proof.
rewrite refinesE.
move=> x y [Hinv Hcols Hasc_diag Hdesc_diag Hvalid].
have Hspec_curr: [set Spec.p_curr_col x] = keep_min_op (p_valid y) 
  by admit. (* XXX: Need good spec for [keep_min_op] *)
split=> //=;
rewrite ?Spec.altp_cols
        ?Spec.altp_asc_diag 
        ?Spec.altp_desc_diag 
        ?Spec.altp_valid_cols
        ?Hspec_curr //;
 try now apply Spec.inv_altp.
move/setP: Hvalid=> ->.
rewrite /inter_op/inter_fin/compl_op/compl_fin.
by rewrite setDE.
Admitted.

(*************************************************)
(** *** Machine [->] Native refinement           *)
(*************************************************)

(** From the specification of machine words to native integers. *)

Definition Rword (wp: FSet.pos)(np: NSet.pos): Type
  := pos_R _ _ NSet.R.Rbitset wp np.

Global Instance Rword_init: 
  refines Rword FSet.initp NSet.initp.
Proof. param initp_R. Qed.

Global Instance Rword_fullp: 
  refines (Rword ==> param.bool_R) FSet.fullp NSet.fullp.
Proof. param fullp_R. Qed.

Global Instance Rword_validp: 
  refines (Rword ==> param.bool_R) FSet.validp NSet.validp.
Proof. param validp_R. Qed.

Global Instance Rword_nextp: 
  refines (Rword ==> Rword) FSet.nextp NSet.nextp.
Proof. param nextp_R. 
- admit. (* XXX: refinement for [keep_min] *)
- admit. (* XXX: refinement for [succ] *)
- admit. (* XXX: refinement for [pred] *)
Admitted.

Global Instance Rword_altp:
  refines (Rword ==> Rword) FSet.altp NSet.altp.
Proof. param altp_R. 
- admit. (* XXX: refinement for [keep_min] *)
Admitted. 

(*************************************************)
(** *** Abstract [->] Native  refinement         *)
(*************************************************)

(** Composition of the previous refinements *)

Definition RPos: Spec.pos -> NSet.pos -> Type := Rspec \o Rword.


Global Instance RPos_initp: 
  refines RPos Spec.initp NSet.initp.
Proof. eapply refines_trans; tc. Qed.

Global Instance RPos_fullp: 
  refines (RPos ==> param.bool_R) Spec.fullp NSet.fullp.
Proof. eapply refines_trans; tc. Qed.

Global Instance RPos_validp: 
  refines (RPos ==> param.bool_R) Spec.validp NSet.validp.
Proof. eapply refines_trans; tc. Qed.

Global Instance RPos_nextp: 
  refines (RPos ==> RPos) Spec.nextp NSet.nextp.
Proof. eapply refines_trans; tc. Qed.

Global Instance RPos_altp:
  refines (RPos ==> RPos) Spec.altp NSet.altp.
Proof. eapply refines_trans; tc. Qed.

Local Close Scope rel.

End Refinement.

(*****************************************************************)
(** * n-queens positions                                         *)
(*****************************************************************)

Section Queen_generic.

Variable pos: Type.

Variable initp: pos.
Variable fullp: pos -> bool.
Variable validp: pos -> bool.
Variable nextp: pos -> pos.
Variable altp: pos -> pos.

Definition nqueens_loop: pos -> nat ->  nat :=
  ffix (fun p nqueens_loop score  =>
          match validp p with
          | false => score 
          | true => 
            let score' := 
                let p' := nextp p in
                if fullp p' then S score
                else nqueens_loop p' score            
            in
            let p' := altp p in
            nqueens_loop p' score'
          end).

Definition nqueens := nqueens_loop initp 0.

End Queen_generic.

Parametricity nqueens_loop.
Parametricity nqueens.

Module MakeQueens (P: POS).

Definition nqueens 
  := nqueens P.pos 
             P.initp P.fullp P.validp 
             P.nextp P.altp.

End MakeQueens.

(*********************************************************)
(** ** Correctness                                       *)
(*********************************************************)

Module Correctness (B: BOARDSIZE).

Module Refinement := Refinement B.
Import Refinement.

Module Prove := MakeQueens Spec.
Module Run := MakeQueens NSet.

Import B.

Definition valid_board (b: Spec.board): bool :=
  [forall x, exists y, b x y && Spec.validp (Spec.mk_pos' b x y) ].

Definition solutions :=  [set x in Spec.board | valid_board x ].

Lemma correctness_spec: Prove.nqueens = #| solutions |.
Admitted. (* XXX *)

(*********************************************************)
(** ** Equivalence spec / code                           *)
(*********************************************************)

Lemma eq_nqueens: Prove.nqueens = Run.nqueens.
Proof.
have Href_eq: refines Logic.eq Prove.nqueens Run.nqueens.
{
  apply refines_nat_eq.
  rewrite !refinesE.
  apply: nqueens_R.
  - intros. eapply refinesP.
    apply RPos_initp.
  - intros. eapply refinesP.
    eapply refines_apply; eauto.
    apply RPos_fullp. 
    rewrite refinesE. auto.
  - intros. eapply refinesP.
    eapply refines_apply; eauto.
    apply RPos_validp.
    rewrite refinesE. auto.
  - intros. eapply refinesP.
    eapply refines_apply; eauto.
    apply RPos_nextp.
    rewrite refinesE; auto.
  - intros. eapply refinesP.
    eapply refines_apply; eauto.
    apply RPos_altp.
    rewrite refinesE; auto.
}
by rewrite refinesE in Href_eq.
Qed.

Lemma correctness: Run.nqueens = #| solutions |.
Proof. by rewrite <- correctness_spec, eq_nqueens. Qed.

End Correctness.

(*********************************************************)
(** ** Extraction                                        *)
(*********************************************************)

(** Whilst, in principle, we would like to extract and compile
    [Run.nqueens], its instanciation through functors makes it
    impractical: the extracted code contains both the actual code and
    some useless proofs. To side-step this issue, we manually inline
    its defininition here. *)

Module Extractor (B: BOARDSIZE).

Import B.

Module Wordsize.
  Definition wordsize := n.
End Wordsize.

Module Nat := axioms.MakeOps(Wordsize).

Record pos := Mk_pos { p_cols      : Nat.Int ;
                       p_asc_diag  : Nat.Int ;
                       p_desc_diag : Nat.Int ;
                       p_valid     : Nat.Int }.

(* XXX: Careful, this overflows very quickly! *)
Fixpoint machine_of_nat' (n: nat)(acc: Nat.Int) :=
  match n with
  | 0 => acc
  | S n => machine_of_nat' n (Nat.add Nat.one acc)
  end.
Definition machine_of_nat (n: nat) := machine_of_nat' n Nat.zero. 

Definition machine_n := machine_of_nat n.

Definition initp := 
  let full_op := Nat.sub (Nat.lsl Nat.one machine_n) Nat.one in
  Mk_pos full_op Nat.zero Nat.zero full_op.

Definition fullp p := Nat.eq p.(p_cols) Nat.zero.
Definition validp p := negb (Nat.eq p.(p_valid) Nat.zero).
Definition keep_min bs := Nat.land bs (Nat.opp bs).

Definition nextp p :=
  let d := keep_min p.(p_valid) in
  let cols := Nat.land p.(p_cols) (Nat.lnot d) in
  let asc_diag := Nat.lsr (Nat.lor p.(p_asc_diag) d) Nat.one in
  let desc_diag := Nat.lsl (Nat.lor p.(p_desc_diag) d) Nat.one in
  let valid := Nat.land cols (Nat.lnot (Nat.lor asc_diag desc_diag)) in
  Mk_pos cols asc_diag desc_diag valid.

Definition altp p :=
  let d := keep_min p.(p_valid) in
  let valid := Nat.land p.(p_valid) (Nat.lnot d) in
  Mk_pos p.(p_cols) p.(p_asc_diag) p.(p_desc_diag) valid.

Definition nqueens_loop: pos -> nat ->  nat :=
  ffix (fun p nqueens_loop score  =>
          match validp p with
          | false => score 
          | true => 
            let score := 
                let p := nextp p in
                if fullp p then S score
                else nqueens_loop p score            
            in
            let p := altp p in
            nqueens_loop p score
          end).

Definition nqueens := nqueens_loop initp 0.

End Extractor.

Require Import ExtrOcamlIntConv.
Extraction "queens.ml" int_of_nat nat_of_int Extractor.