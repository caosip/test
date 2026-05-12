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
  ext e
  rcases e with ⟨v, w⟩
  simp only [Set.mem_edgeSet, Set.mem_setOf_eq, Sym2.forall, Set.not_mem_empty, iff_false]
  intro hadj
  have hmem : w ∈ G.neighborSet v := hadj
  have hdeg0 : G.degree v = 0 := hreg.degree_eq v
  have hcard0 : (G.neighborFinset v).card = 0 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg0]
  have hmemFinset : w ∈ G.neighborFinset v := by
    simpa [SimpleGraph.mem_neighborFinset] using hmem
  have hcard_pos : 1 ≤ (G.neighborFinset v).card :=
    Finset.one_le_card.mpr ⟨w, hmemFinset⟩
  linarith