import Mathlib.LinearAlgebra.LinearIndependent.Basic
-- import MIL.Common

/-!
# Pointwise Scalar Linear Maps

Blueprint: test-blueprint
-/

section PointwiseScalar

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

/-- If `f` is a linear endomorphism such that every vector is an eigenvector,
and `u, v` are linearly independent, then `f u` and `f v` share the same eigenvalue. -/
theorem independent_vectors_determine_same_scalar
    (f : E →ₗ[K] E)
    (hf : ∀ x : E, ∃ c : K, f x = c • x)
    (u v : E)
    (huv : LinearIndependent K ![u, v]) :
    ∃ c : K, f u = c • u ∧ f v = c • v := by
  -- Extract scalars from hypothesis
  obtain ⟨c₁, hc₁⟩ := hf u
  obtain ⟨c₂, hc₂⟩ := hf v
  obtain ⟨c₃, hc₃⟩ := hf (u + v)
  -- Use linearity of f
  have h_add : f (u + v) = f u + f v := f.map_add u v
  rw [hc₃, hc₁, hc₂] at h_add
  rw [smul_add] at h_add
  -- The key insight: from h_add: c₃ • u + c₃ • v = c₁ • u + c₂ • v
  -- By rearranging: (c₁ - c₃) • u + (c₂ - c₃) • v = 0
  -- Since u, v are linearly independent, both coefficients must be zero
  -- Therefore c₁ = c₃ = c₂
  have h_eq : c₁ = c₂ := by
    have h_zero : (c₁ - c₃) • u + (c₂ - c₃) • v = 0 := by
      rw [sub_smul, sub_smul, sub_add_sub_comm, sub_eq_zero]
      exact h_add.symm
    rw [Fintype.linearIndependent_iff] at huv
    have key := huv ![c₁ - c₃, c₂ - c₃] (by simpa [Fin.sum_univ_two] using h_zero)
    have h0 := key 0; have h1 := key 1
    simp at h0 h1; linarith
  -- Now use the result
  use c₁
  exact ⟨hc₁, by rw [h_eq]; exact hc₂⟩

/-- A linear endomorphism such that every vector is an eigenvector is a scalar
multiple of the identity. -/
theorem pointwise_scalar_linear_map_is_smul_id
    (f : E →ₗ[K] E)
    (hf : ∀ x : E, ∃ c : K, f x = c • x) :
    ∃ c : K, ∀ x : E, f x = c • x := by
  -- Try to find a nonzero vector; if none exists, E is trivial
  by_cases hE : ∀ x : E, x = 0
  · exact ⟨0, fun x => by simp [hE x, map_zero]⟩
  · push_neg at hE
    obtain ⟨u, hu⟩ := hE
    obtain ⟨λ_, hλ⟩ := hf u
    use λ_
    intro y
    by_cases hlin : ∃ r : K, y = r • u
    · obtain ⟨r, rfl⟩ := hlin
      rw [f.map_smul, hλ, smul_comm]
    · -- y is not a scalar multiple of u, so {u, y} is linearly independent
      have hind : LinearIndependent K ![u, y] := by
        rw [Fintype.linearIndependent_iff]
        intro g hg i
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons] at hg
        fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        · by_contra h0
          by_cases h1 : g 1 = 0
          · rw [h1, zero_smul, add_zero] at hg
            exact hu ((smul_eq_zero.mp hg).resolve_left h0)
          · exfalso; apply hlin
            have h2 : g 1 • y = -(g 0 • u) :=
              eq_neg_of_add_eq_zero_left (show g 1 • y + g 0 • u = 0 by rwa [add_comm])
            have h3 : y = (g 1)⁻¹ • (-(g 0 • u)) := by
              rw [← h2, ← mul_smul, inv_mul_cancel₀ h1, one_smul]
            exact ⟨(g 1)⁻¹ * (-g 0), by rw [h3, mul_smul, neg_smul]⟩
        · by_contra h1; exfalso; apply hlin
          have h2 : g 1 • y = -(g 0 • u) :=
            eq_neg_of_add_eq_zero_left (show g 1 • y + g 0 • u = 0 by rwa [add_comm])
          have h3 : y = (g 1)⁻¹ • (-(g 0 • u)) := by
            rw [← h2, ← mul_smul, inv_mul_cancel₀ h1, one_smul]
          exact ⟨(g 1)⁻¹ * (-g 0), by rw [h3, mul_smul, neg_smul]⟩
      obtain ⟨c, hcu, hcy⟩ := independent_vectors_determine_same_scalar f hf u y hind
      have hceq : c = λ_ := by
        by_contra hne
        have h1 : (c - λ_) • u = 0 := by rw [sub_smul, ← hcu, hλ, sub_self]
        rw [smul_eq_zero] at h1
        exact h1.elim (fun h => hne (sub_eq_zero.mp h)) hu
      rw [hceq] at hcy; exact hcy

end PointwiseScalar