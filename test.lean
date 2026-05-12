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
  have h0 : ∀ v, G.degree v = 0 := hreg
  have hneigh_empty : ∀ v, G.neighborFinset v = ∅ := by
    intro v
    have hdeg := h0 v
    rw [SimpleGraph.degree] at hdeg
    exact Finset.card_eq_zero.mp hdeg
  have h_no_adj : ∀ a b, ¬ G.Adj a b := by
    intro a b h_adj
    have hmem : b ∈ G.neighborFinset a :=
      (G.mem_neighborFinset _ _).mpr h_adj
    rw [hneigh_empty a] at hmem
    simp at hmem
    exact hmem
  have h_bot : G = ⊥ := eq_bot_iff_forall_not_adj.mpr h_no_adj
  exact (SimpleGraph.edgeSet_eq_empty.mpr h_bot)
