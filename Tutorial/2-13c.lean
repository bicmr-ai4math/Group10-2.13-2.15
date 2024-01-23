import «Tutorial».Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic

open Matrix GateauxDeriv
noncomputable
def f_lndet : Matrix (Fin n) (Fin n) ℝ → ℝ :=
  fun X => Real.log X.det

theorem problem_c (X : Matrix (Fin n) (Fin n) ℝ) (h : X.det > 0):
  HasGateauxDerivAt (f_lndet) X (X⁻¹)ᵀ := by
    simp [HasGateauxDerivAt]
    simp [f_lndet]
    intro V
    have h_isunitdet : IsUnit X.det := by
      simp [IsUnit]
      linarith [h]
    have h (t : ℝ) : X + t • V = X * ( 1 + t • X⁻¹ * V) := by
      simp [Matrix.mul_add]
      simp [← Matrix.mul_assoc]
      rw [mul_nonsing_inv]
      simp [Matrix.one_mul]
      assumption
    rw [Metric.tendsto_nhdsWithin_nhds]
    -- ∀  ε > 0, ∃ 0 < δ < f(ε), ....
    -- need to construct f(ε)
    simp [h]
    have none_zero_1 : det ( X ) ≠  0 := by
      linarith [h]
    have none_zero_2 (x : ℝ) : det ( 1 + x • (X⁻¹ * V) ) ≠  0 := by
      sorry
    simp [Real.log_mul, none_zero_1, none_zero_2]
    let ⟨Q, R, h3a, h3b, h3c⟩  := schur_decomposition n (X⁻¹ * V)
    rw [h3c]
    have h4 : 1 = Qᵀ * Q := by
      dsimp [Orthogonal_Matrix] at h3a
      exact symm h3a
    rw [h4]
    have h5 : Q = 1 * Q := by
      rw [Matrix.one_mul]
    nth_rewrite 2[h5]
    rw [← Matrix.mul_assoc]
    have h6: Qᵀ * R * Q = Qᵀ * (R * Q) :=by
      rw [Matrix.mul_assoc]
    rw [h6]
    have h7 (t : ℝ ) : t • (Qᵀ * (R * Q)) = Qᵀ * (t • R) * Q :=by
      rw [← Matrix.mul_assoc]
      rw[Matrix.mul_smul]
      simp
    simp only [h7]
    simp only [← Matrix.add_mul]
    simp only [← Matrix.mul_add]
    simp
    have : 1 = Q.det * Q.det := by
      have hh := congrArg Matrix.det h4 -- 将此性质引入到“假设”中
      simp at hh
      assumption
    simp only [mul_comm]
    simp only [← mul_assoc]
    simp [← this]
    have h8 (x : ℝ) : is_upper_triangle (1 + x • R) := by
      apply is_upper_triangle.add
      apply is_upper_triangle.one
      apply is_upper_triangle.smul
      exact h3b
    simp only [upper_triangle_det, h8]
    have h9 (x : ℝ) (i : Fin n): (1 + x • R) i i ≠ 0 := by
      sorry
    simp only [dist]
    intro ε
    intro ε₁
    sorry

    -- rw [Real.log_prod]
    have ha1: trace (R) = innerProductofMatrix (X⁻¹)ᵀ V :=by
      sorry
    sorry
