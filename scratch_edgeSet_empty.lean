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
  obtain ⟨hfin, hreg⟩ := h
  rw [Set.eq_empty_iff_forall_notMem]
  intro e he
  rw [SimpleGraph.mem_edgeSet] at he
  obtain ⟨v, w, rfl⟩ := e.exists_eq
  rw [SimpleGraph.mk'_mem_edgeSet] at he
  have hdeg := hreg v
  have hne : @SimpleGraph.neighborFinset V G v (hfin v) = ∅ := by
    rwa [← Finset.card_eq_zero]
  have : w ∈ @SimpleGraph.neighborFinset V G v (hfin v) := by
    rw [@SimpleGraph.mem_neighborFinset]
    exact he
  rw [hne] at this
  exact absurd this (Finset.not_mem_empty _)
