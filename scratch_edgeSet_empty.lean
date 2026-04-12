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
  ext e
  simp only [Set.mem_empty_iff_false, iff_false]
  intro he
  rw [SimpleGraph.mem_edgeSet] at he
  have hadj := he
  obtain ⟨u, v, huv, rfl⟩ : ∃ u v, G.Adj u v ∧ e = ⟦(u, v)⟧ := by
    exact ⟨_, _, hadj, rfl⟩
  have : G.degree u = 0 := hreg u
  have : 0 < G.degree u := by
    rw [SimpleGraph.degree]
    exact Finset.card_pos.mpr ⟨v, by rwa [@SimpleGraph.mem_neighborFinset _ G hlf]⟩
  omega
