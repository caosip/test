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
  haveI : G.LocallyFinite := hlf
  have hiso (v : V) : G.IsIsolated v := by
    have hdeg : G.degree v = 0 := hreg.degree_eq v
    exact ((SimpleGraph.degree_eq_zero G v).mp hdeg)
  have h_eq_bot : G = ⊥ := by
    ext v w
    constructor
    · intro hadj
      have hmem : w ∈ G.neighborSet v := hadj
      rw [hiso v |>.neighborSet_eq_empty] at hmem
      exact Set.not_mem_empty _ hmem
    · intro hadj
      cases hadj
  exact (SimpleGraph.edgeSet_eq_empty.mpr h_eq_bot)
