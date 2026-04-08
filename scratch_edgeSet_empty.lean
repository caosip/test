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
  obtain ⟨hLF, hReg⟩ := h
  ext ⟨v, w⟩
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hadj
  rw [SimpleGraph.mem_edgeSet] at hadj
  have hcard := hReg v
  simp only [SimpleGraph.IsRegularOfDegree, SimpleGraph.degree] at hcard
  have hmem : w ∈ @SimpleGraph.neighborFinset V G (hLF v) v := by
    rw [SimpleGraph.mem_neighborFinset]
    exact hadj
  have hempty : @SimpleGraph.neighborFinset V G (hLF v) v = ∅ := by
    rw [Finset.eq_empty_iff_forall_not_mem]
    intro x hx
    have : (@SimpleGraph.neighborFinset V G (hLF v) v).card = 0 := hcard
    rw [Finset.card_eq_zero] at this
    rw [this] at hx
    exact hx.elim
  rw [hempty] at hmem
  exact hmem.elim
