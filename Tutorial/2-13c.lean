import «Tutorial».Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic
-- import Mathlib.Order.Lattice

open Matrix GateauxDeriv Topology
open InnerProductOfMatrix
open BigOperators

noncomputable
def f_lndet : Matrix (Fin n) (Fin n) ℝ → ℝ :=
  fun X => Real.log X.det


lemma finn_nonempty {n : Nat} (hn : n ≥ 1): (@Finset.univ (Fin n) (Fin.fintype n)).Nonempty := by
  have x : Fin n := ⟨0, by linarith⟩
  unfold Finset.Nonempty
  exact ⟨x, by simp⟩

---------------- second try ----------------


#check Matrix.det_updateRow_add
#check Matrix.updateRow
#check Matrix.row
#check Matrix.row_apply -- row n → α  to  Matrix Unit n α
#check Matrix.det_eq_sum_mul_adjugate_row
#check Matrix.adjugate
#check Matrix.inv_def

-- #check (A.det⁻¹ * ((Matrix.adjugate A) i j)

def Matrix_base {n m : Nat} (i : Fin n) (j : Fin m) : Matrix (Fin n) (Fin m) ℝ := of fun x y => if x = i ∧ y = j then 1 else 0

#check Fintype.sum_eq_single
lemma inner_product_with_matrix_base {n m : Nat} (X : Matrix (Fin n) (Fin m) ℝ) (i : Fin n) (j : Fin m) :
    innerProductofMatrix X (Matrix_base i j) = X i j := by
  unfold innerProductofMatrix
  unfold Matrix_base
  simp
  have hnotj (x: Fin n) : ∀ x' ≠ j, (if x = i ∧ x' = j then X x x' else 0) = 0 := by
    intro x' hx'; simp at hx'
    have : (x' = j) = False := by simp; intro hxi; absurd hx' hxi; exact not_false
    simp [this]
  have lem_1 (x: Fin n) := Fintype.sum_eq_single j (hnotj x)
  simp at lem_1
  have :(∑ x : Fin n, ∑ x_1 : Fin m, if x = i ∧ x_1 = j then X x x_1 else 0) =
      (∑ x : Fin n, if x = i then X x j else 0) := by
    apply Finset.sum_congr
    · rfl
    simp [lem_1]
  rw [this]
  have hnoti : ∀ x ≠ i, (if x = i then X x j else 0) = 0 := by
    intro x hx; simp at hx
    have : (x = i) = False := by simp; intro hxi; absurd hx hxi; exact not_false
    simp [this]
  have lem_2 := Fintype.sum_eq_single i hnoti
  rw [lem_2]; simp

theorem ln_tends_to (R : ℝ): Filter.Tendsto (fun t => Real.log (1 + t * R) / t) (𝓝[≠] 0) (𝓝 R) := by
  simp [Metric.tendsto_nhdsWithin_nhds]
  exact ln_delta_epsilon R

theorem tendsto_uniqueness {f : ℝ → ℝ} {y z : ℝ} (h₁ : Filter.Tendsto f (𝓝[≠] 0) (𝓝 y))
    (h₂ : Filter.Tendsto f (𝓝[≠] 0) (𝓝 z)) : y = z := by
  sorry

theorem updateColumn_twice {n m: Nat} (X : Matrix (Fin n) (Fin m) ℝ) (j : Fin m) (f₁ f₂ : Fin n → ℝ) :
    updateColumn (updateColumn X j f₁) j f₂ = updateColumn X j f₂ := by
  apply Matrix.ext
  intro i' j'
  simp [Matrix.updateColumn_apply]
  rcases (eq_or_ne j j') with (hl | hr)
  · simp [hl]
  · have hh' : (j' = j) = False := by
      simp; intro hii'; absurd hr (symm hii'); exact not_false
    simp [hh']

theorem det_of_update_row {n : Nat} (X : Matrix (Fin n) (Fin n) ℝ) (i j: Fin n) {t : ℝ}:
    det (updateRow X i fun j' => if j' = j then t else 0) = t * (X.adjugate j i) := by
  let X' := updateRow X i fun j' => if j' = j then t else 0
  rw [Matrix.det_eq_sum_mul_adjugate_row X' i]
  simp
  left
  unfold adjugate
  unfold cramer
  simp
  unfold cramerMap
  simp
  simp [← Matrix.updateColumn_transpose]
  simp [updateColumn_twice]


#check updateRow_self
lemma calculate_f_lndet_t_delta {n : Nat} (X : Matrix (Fin n) (Fin n) ℝ) (i j: Fin n) (hX : X.det > 0):
    ∃ δ > 0, ∀ t ≠ 0, |t| < δ → (f_lndet (X + t • Matrix_base i j) - f_lndet X) / t
      = Real.log (1 + t * (X.adjugate j i / det X)) / t := by
  let δ := det X / (|adjugate X j i| + 1)
  have h_pos_abs_add_one : 0 < |adjugate X j i| + 1 := by linarith [abs_nonneg (adjugate X j i)]
  have hδ_nonneg : δ > 0 := by apply div_pos; linarith; linarith;
  use δ
  constructor
  · exact hδ_nonneg
  intro t ht_nezero htleδ
  let tmulirow := (fun j' => if j' = j then t else 0)
  have hhx : X = updateRow X i (X i) := by simp
  have h1 : X + t • Matrix_base i j = updateRow X i ((X i) + tmulirow) := by
    apply Matrix.ext
    intro i' j'
    simp [Matrix.updateRow_apply, Matrix_base]
    rcases (eq_or_ne i i') with (hl | hr)
    · simp [hl]
    · have hh' : (i' = i) = False := by
        simp; intro hii'; absurd hr (symm hii'); exact not_false
      simp [hh']
  rw [h1]
  unfold f_lndet
  simp [det_updateRow_add, det_of_update_row]
  have hx1 : det X ≠ 0 := by linarith
  have hx2 : det X + t * adjugate X j i ≠ 0 := by
    rcases eq_or_ne (adjugate X j i) 0 with (heq | hne)
    · simp [heq]; linarith
    · simp at htleδ
      have hx3 := (lt_div_iff h_pos_abs_add_one).mp htleδ
      have hx4 : det X + t * adjugate X j i > 0 := by
        calc
          det X + t * adjugate X j i
            ≥ det X - |t * adjugate X j i|    := by linarith [neg_abs_le (t * adjugate X j i)]
          _ = det X - |t| * |adjugate X j i|  := by simp [abs_mul]
          _ > |t| := by simp [mul_add] at hx3; linarith [hx3]
          _ ≥ 0 := by simp [abs_nonneg]
      linarith [hx4]
  rw [← Real.log_div hx2 hx1]
  simp [add_div, hX, hx1, mul_div]


theorem pro_c {n : Nat} (X : Matrix (Fin n) (Fin n) ℝ) (hn : NeZero n) (hX : X.det > 0)
    (h : GateauxDifferentiable f_lndet X) :
      GateauxDeriv f_lndet X h = (X⁻¹)ᵀ := by
  unfold GateauxDifferentiable at h
  have hh := GateauxDeriv_spec f_lndet X h
  unfold HasGateauxDerivAt at hh
  apply Matrix.ext
  intro i j
  specialize hh (Matrix_base i j)
  rw [inner_product_with_matrix_base] at hh
  have ⟨δt, hδt, hhh⟩  := calculate_f_lndet_t_delta X i j hX
  have : (fun t => (f_lndet (X + t • Matrix_base i j) - f_lndet X) / t)
      =ᶠ[𝓝[≠] 0] (fun t => Real.log (1 + t * (X.adjugate j i/X.det) ) / t ) := by
    apply eventuallyEq_nhdsWithin_iff.mpr
    apply Metric.eventually_nhds_iff_ball.mpr
    simp
    use δt
    constructor
    · exact hδt
    intro x1 x3 x2; exact (hhh x1 x2 x3)
  have hl := (Filter.tendsto_congr' this).mp hh
  have hr := ln_tends_to (X.adjugate j i/X.det)
  have h := tendsto_uniqueness hl hr
  rw [h, ← inv_mul_eq_div]
  simp [Matrix.inv_def]
  have h1 : ((det X)⁻¹ • adjugate X) j i = (det X)⁻¹ * adjugate X j i := by
    simp [Matrix.ext_iff.mpr (Matrix.smul_of (det X)⁻¹ (adjugate X))]
  exact symm h1



---------------- first try ----------------

#check Fin.fintype 2


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
