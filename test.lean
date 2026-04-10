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
  obtain ⟨hlf, hreg⟩ := h
  rw [SimpleGraph.edgeSet_eq_empty]
  ext v w
  simp only [SimpleGraph.bot_adj]
  refine ⟨fun hadj => ?_, False.elim⟩
  have hdeg := hreg v
  have : (G.neighborFinset v).card = 0 := hdeg
  have : G.neighborFinset v = ∅ := Finset.card_eq_zero.mp this
  have : w ∈ G.neighborFinset v := by
    rw [SimpleGraph.mem_neighborFinset]
    exact hadj
  simp_all
