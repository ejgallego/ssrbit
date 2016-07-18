Module Logical.
Module Op.

Class not_of int := not_op : int -> int.
Class or_of int := or_op : int -> int -> int.
Class and_of int := and_op : int -> int -> int.
Class xor_of int := xor_op : int -> int -> int.
Class shl_of int := shl_op : int -> int -> int.
Class shr_of int := shr_op : int -> int -> int.
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
Notation ">>>%C"    := shr_op.
Notation "x >>> y"  := (shr_op x y) 
 (at level 30, right associativity) : computable_scope.
Notation "<<<%C"    := shl_op.
Notation "x <<< y"  := (shl_op x y) 
 (at level 30, right associativity) : computable_scope.


Module Sets.
Module Op.

Class cardinal_of n fset := cardinal_op : fset -> n.
Class compl_of fset := compl_op : fset -> fset.
Class empty_of fset := empty_op : fset.
Class full_of fset := full_op : fset.
Class get_of e fset := get_op : e -> fset -> bool.
Class set_of e fset := set_op : e -> fset -> fset.
Class inter_of fset := inter_op : fset -> fset -> fset.
Class min_of e fset := min_op : fset -> e.
Class remove_of e fset := remove_op : fset -> e -> fset.
Class symdiff_of fset := symdiff_op : fset -> fset -> fset.
Class union_of fset := union_op : fset -> fset -> fset.
Class singleton_of e fset := singleton_op : e -> fset.
Class subset_of fset := subset_op : fset -> fset -> bool.

End Op.
End Sets.

(* XXX: add notations *)