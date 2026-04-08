import Mathlib

example : 1 + 1 = 2 := by norm_num

/-! # Blueprint aaa: Regular graphs

The definition of a regular graph of degree `d` is already in Mathlib as
`SimpleGraph.IsRegularOfDegree`. We re-export it here for the blueprint.
-/

/-- A locally finite simple graph is regular of degree `d` if every vertex has degree `d`.
This is `SimpleGraph.IsRegularOfDegree` from Mathlib. -/
def Aaa.IsRegularOfDegree {V : Type*} (G : SimpleGraph V) [G.LocallyFinite] (d : ℕ) : Prop :=
  G.IsRegularOfDegree d
