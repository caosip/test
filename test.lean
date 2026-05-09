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
  have h_no_adj : ∀ v w, ¬ G.Adj v w := by
    intro v w
    have hdeg0 : G.degree v = 0 := hreg v
    have h_no_ex : ¬ ∃ w', G.Adj v w' := by
      rw [← G.degree_pos_iff_exists_adj v, hdeg0]
      exact Nat.lt_irrefl 0
    exact fun hadj => h_no_ex ⟨w, hadj⟩
  rw [Set.eq_empty_iff_forall_not_mem, Sym2.forall]
  intro v w
  rw [mem_edgeSet]
  exact h_no_adj v w
