/-
Copyright (c) 2025 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Mathlib

open Classical in
noncomputable section

/--
A locally finite simple graph is regular of degree `d` if every vertex has degree `d`.
This modified definition is used to avoid the need for the input graph to be known to be
locally finite.
-/
def SimpleGraph.IsRegularOfDegree'.{u} {V : Type u} (G : SimpleGraph V)
    (d : ℕ) : Prop :=
  ∃ _ : G.LocallyFinite, G.IsRegularOfDegree d

/- (by claude) Helper for two_factor_theorem: 0-regular graph has empty edge set -/
lemma SimpleGraph.IsRegularOfDegree'.edgeSet_empty {V : Type}
    {G : SimpleGraph V} (h : G.IsRegularOfDegree' 0) :
    G.edgeSet = ∅ := by
  rcases h with ⟨hlf, hreg⟩
  apply SimpleGraph.edgeSet_eq_empty.mpr
  ext v w
  constructor
  · intro hadj
    have hdeg0 : G.degree v = 0 := hreg.degree_eq v
    have hcard0 : G.neighborFinset v = ∅ := by
      apply Finset.card_eq_zero.mp
      rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg0]
    have hmem : w ∈ G.neighborFinset v := by
      simpa [SimpleGraph.mem_neighborFinset] using hadj
    rw [hcard0] at hmem
    simpa using hmem
  · intro h
    exfalso; exact h