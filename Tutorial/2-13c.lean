import «Tutorial».Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
-- import Mathlib.Order.Lattice

open Matrix GateauxDeriv
open InnerProductOfMatrix
open Classical
open BigOperators
noncomputable
def f_lndet : Matrix (Fin n) (Fin n) ℝ → ℝ :=
  fun X => Real.log X.det

#check Fin.fintype 2
lemma finn_nonempty {n : Nat} (hn : n ≥ 1): (@Finset.univ (Fin n) (Fin.fintype n)).Nonempty := by
  have x : Fin n := ⟨0, by linarith⟩
  unfold Finset.Nonempty
  exact ⟨x, by simp⟩

lemma left_right_distrib_orthogonal {n : Nat} {x : ℝ} {Q R : Matrix (Fin n) (Fin n) ℝ} (h : Orthogonal_Matrix Q) :
  1 + x • (Qᵀ * R * Q) = Qᵀ * (1 + x • R) * Q := by
    rw [Matrix.mul_add, Matrix.add_mul]
    simp
    rw [Orthogonal_Matrix] at h
    exact symm h

lemma log_delta_epsilon_of_Finset {n : Nat} (hn : 1 ≤ n) (R : Matrix (Fin n) (Fin n) ℝ) :
    ∀ ε > 0, ∃ δ > 0, ∀ x ≠ 0, |x| < δ → ∀ i : Fin n, |Real.log (1 + x * R i i) / x - R i i| < ε / n := by --不可逃避的问题
  intro ε hε
  have hεdivn : ε / n > 0 := by
    apply div_pos
    · linarith
    simp; linarith
  let f := (fun i : Fin n => Exists.choose (ln_delta_epsilon (R i i) (ε / n) hεdivn))
  let f_spec := (fun i : Fin n => Exists.choose_spec (ln_delta_epsilon (R i i) (ε / n) hεdivn))
  let image_δ₃ := Finset.image f Finset.univ
  have h_image_δ₃_nonempty : image_δ₃.Nonempty := by exact Finset.image_nonempty.mpr (finn_nonempty hn)
  let δ₃  := Finset.min' image_δ₃ h_image_δ₃_nonempty
  use δ₃
  constructor
  · simp [Finset.lt_min'_iff]
    intro i
    exact (f_spec i).1
  intro y hny hy i
  simp [Finset.lt_min'_iff] at hy
  exact (f_spec i).2 y hny (hy i)

theorem problem_c {n : Nat} (X : Matrix (Fin n) (Fin n) ℝ) (hn : 1 ≤ n) (h : X.det > 0):
  HasGateauxDerivAt (f_lndet) X (X⁻¹)ᵀ := by
    simp [HasGateauxDerivAt]
    simp [f_lndet]
    intro V
    let ⟨Q, R, h3a, h3b, h3c⟩  := schur_decomposition n (X⁻¹ * V)
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
    intro ε
    intro ε₁
    -- ∀  ε > 0, ∃ 0 < δ < f(ε), ....
    -- need to construct f(ε)
    let ⟨δ₁, hδ₁, hx₁_det_nonzero⟩  := det_notzero (X⁻¹ * V)
    let ⟨δ₂, hδ₂, hx₂_det_nonzero⟩  := det_notzero R
    let ⟨δ₃, hδ₃, hx₃_log_delta_epsilon⟩ := (log_delta_epsilon_of_Finset hn R) ε ε₁
    let δ := min (min δ₁ δ₂) δ₃
    use δ
    constructor
    · simp
      exact ⟨⟨hδ₁, hδ₂⟩, hδ₃⟩
    intro x x_nonneg x_range
    simp at x_range
    simp [h]
    have none_zero_1 : det ( X ) ≠  0 := by
      linarith [h]
    have none_zero_2 : det (1 + x • (X⁻¹ * V) ) ≠ 0 := by -- 用 basic 中引入的新theorem来证明
      apply hx₁_det_nonzero
      exact x_range.1.1
    simp [Real.log_mul, none_zero_1, none_zero_2]
    rw [h3c]
    have h4 : 1 = Qᵀ * Q := by
      dsimp [Orthogonal_Matrix] at h3a
      exact symm h3a
    simp [left_right_distrib_orthogonal, h3a]
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
    have h9 (i : Fin n): (1 + x • R) i i ≠ 0 := by  -- 用 basic 中引入的新theorem来证明
      specialize hx₂_det_nonzero x
      exact (upper_nonezero (1 + x • R)) (h8 x) (hx₂_det_nonzero x_range.1.2) i
    simp only [dist]
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
    have h2 : ∀ i : Fin n, |Real.log (1 + x * R i i) / x - R i i| < ε / n := by
      exact hx₃_log_delta_epsilon x x_nonneg x_range.2
    have not_equal : n ≠ 0 := by
      linarith
    have h3 : ∑ __ : Fin n, ε / n = ε := by
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
        · exact finn_nonempty hn
        simp
        assumption
    simp at h9
    simp
    assumption
