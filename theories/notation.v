Module Logical.
Module Op.

Class not_of int := not_op : int -> int.
Class or_of int := or_op : int -> int -> int.
Class and_of int := and_op : int -> int -> int.
Class xor_of int := xor_op : int -> int -> int.
Class shl_of idx int := shl_op : int -> idx -> int.
Class shr_of idx int := shr_op : int -> idx -> int.
(* Class size_of int := sizeof_op : int -> nat. *)

End Op.
End Logical.

Import Logical.Op.

Typeclasses Transparent not_of or_of and_of xor_of shl_of shr_of.

Notation "~%C"    := not_op.
Notation "~ x"    := (not_op x)     : computable_scope.
Notation "||%C"   := or_op.
Notation "x || y" := (or_op x y)   : computable_scope.
Notation "&&%C"   := and_op.
Notation "x && y" := (and_op x y)   : computable_scope.
Notation "^^%C"    := xor_op.
Notation "x ^^ y"  := (xor_op x y)
 (at level 30, right associativity) : computable_scope.
Notation ":>>:%C"    := shr_op.
Notation "x :>>: y"  := (shr_op x y) 
 (at level 30, right associativity) : computable_scope.
Notation ":<<:%C"    := shl_op.
Notation "x :<<: y"  := (shl_op x y) 
 (at level 30, right associativity) : computable_scope.


Module Sets.
Module Op.

Class cardinal_of n fset := cardinal_op : fset -> n.
Class compl_of fset := compl_op : fset -> fset.
Class empty_of fset := empty_op : fset.
Class full_of  fset := full_op  : fset.
Class get_of e fset := get_op   : e -> fset -> bool.
Class set_of e fset := set_op   : e -> fset -> fset.
Class inter_of fset := inter_op : fset -> fset -> fset.
Class min_of e fset := min_op : fset -> e.
Class keep_min_of fset := keep_min_op : fset -> fset.
Class remove_of e fset := remove_op : fset -> e -> fset.
Class symdiff_of fset := symdiff_op : fset -> fset -> fset.
Class union_of fset := union_op : fset -> fset -> fset.
Class singleton_of e fset := singleton_op : e -> fset.
Class subset_of fset := subset_op : fset -> fset -> bool.

Typeclasses Transparent cardinal_of compl_of empty_of full_of
  get_of set_of inter_of min_of remove_of symdiff_of union_of
  singleton_of subset_of.

From mathcomp
Require Import fintype finset.

(*
Notation "#| T |"        := (cardinal_op T)  : computable_scope.
Notation "~:%C"          := (compl_op)       : computable_scope.
Notation "'~:' T"        := (compl_op T)     : computable_scope.
*)
Notation "'SET0'"        := (empty_op)       : computable_scope.
(*
Notation "'setT'"        := (full_op)        : computable_scope.
Notation "|:%C"          := (set_op)         : computable_scope.
Notation "x '|:' T"      := (set_op x T)     : computable_scope.
Notation ":&:%C"         := and_op           : computable_scope.
*)
Notation "A :&: B"       := (inter_op A B)     : computable_scope.
(*
Notation ":\%C"          := (remove_op)      : computable_scope.
Notation "A :\ x"        := (remove_op A x)  : computable_scope.
Notation ":|:%C"         := union_op            : computable_scope.
*)
Notation "A ':|:' B"       := (union_op A B)      : computable_scope.
(*
Notation "[set]%C"       := (singleton_op)   : computable_scope.
*)
Notation "[ 'SET' x ]"  := (singleton_op x) : computable_scope.
(*
Notation "\subset%C"     := (subset_op)      : computable_scope.
Notation "A '\subset' B" := (subset_op A B)  : computable_scope.
*)

End Op.
End Sets.
