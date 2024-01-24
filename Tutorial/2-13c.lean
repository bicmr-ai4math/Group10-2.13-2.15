import «Tutorial».Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
-- import Mathlib.Order.Lattice

open Matrix GateauxDeriv
open InnerProductOfMatrix
open Classical
open BigOperators
noncomputable
def f_lndet : Matrix (Fin n) (Fin n) ℝ → ℝ :=
  fun X => Real.log X.det

theorem problem_c {n : Nat} (X : Matrix (Fin n) (Fin n) ℝ) (hn : 1 ≤ n) (h : X.det > 0):
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
    have none_zero_2 (x : ℝ) : det ( 1 + x • (X⁻¹ * V) ) ≠  0 := by -- 用 basic 中引入的新theorem来证明
      let ⟨δ₁, new1⟩  := det_notzero (X⁻¹ * V) x
      rcases new1
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
    have h9 (x : ℝ) (i : Fin n): (1 + x • R) i i ≠ 0 := by  -- 用 basic 中引入的新theorem来证明
      let ⟨δ₂, new2⟩  := det_notzero R x
      rcases new2
      sorry
    simp only [dist]
    intro ε
    intro ε₁
    use 2
    constructor
    · linarith
    · intro x
      intro x_nonneg x_range
      rw [Real.log_prod]
      have inv_1: Q * Qᵀ  = 1 :=by
        rw [Orthogonal_inv]
        assumption
      have ha1: trace (R) = innerProductofMatrix (X⁻¹)ᵀ V  := by
        calc
          trace (R) = trace (R * Q * Qᵀ ) :=by
            rw [Matrix.mul_assoc]
            rw [inv_1]
            simp [Matrix.mul_one]
          _ = trace (Qᵀ * R * Q) :=by
            rw [Matrix.trace_mul_cycle]
          _ = trace (X⁻¹ * V) :=by
            simp [h3c]
          _ = trace ( ((X⁻¹)ᵀ)ᵀ  * V) :=by
            simp [Matrix.transpose_transpose]
          _ = innerProductofMatrix (X⁻¹)ᵀ V := by
            simp only [traceMHDotM, iProd_eq_traceDot]
            simp
      rw [← ha1]
      have e1: trace (R) = Finset.sum Finset.univ fun i => R i i := by
        rw [trace]
        simp
      rw [e1]
      rw [Finset.sum_div]
      rw [← Finset.sum_sub_distrib]
      have h2 (i : Fin n) : |Real.log (1 + x * R i i) / x - R i i| < ε / n := -- 不可逃避的问题
        sorry
      have not_equal : n ≠ 0 := by
        linarith
      have h3 : ∑ i : Fin n, ε / n = ε := by
        rw [← Finset.sum_div]
        simp
        rw [← div_mul_eq_mul_div]
        simp [div_self, hn, not_equal]
      calc
        |Finset.sum Finset.univ fun x_1 => Real.log ((1 + x • R) x_1 x_1) / x - R x_1 x_1|
              ≤ Finset.sum Finset.univ fun x_1 => |Real.log ((1 + x • R) x_1 x_1) / x - R x_1 x_1| := by
          apply Finset.abs_sum_le_sum_abs
        _     < ε := by
          rw [← h3]
          apply Finset.sum_lt_sum_of_nonempty
          unfold Finset.Nonempty
          sorry  -- choice & use
          simp
          assumption
      specialize h9 x
      simp at h9
      simp
      assumption
