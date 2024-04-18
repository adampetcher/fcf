Require Coq.Vectors.Vector.
Export Bool Vector.VectorNotations.

Definition Bvector := Vector.t bool.
Definition Bvect_false := Vector.const false.
Definition BVxor := @Vector.map2 _ _ _ xorb.
