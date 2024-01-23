import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.RowCol

import Mathlib.Data.Matrix.Reflection

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Matrix

import «Tutorial».Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Block


-- 2.13
#check Filter.Tendsto

#check DifferentiableAt

open Matrix Filter Set Topology
open BigOperators
open Finset
open Matrix


open InnerProductOfMatrix
theorem final_conclusion (n : Nat) (a b: Matrix (Fin n) (Fin n) ℝ ) :
  PosSemidef a → PosSemidef b →
    0 ≤ ⟪a, b⟫_ℝ  := by
  intro ha hb
  rcases (posSemidef_iff_eq_transpose_mul_self.mp ha) with ⟨a1, ha1⟩
  rcases (posSemidef_iff_eq_transpose_mul_self.mp hb) with ⟨b1, hb1⟩
  -- a1: Matrix (Fin n) (Fin n) ℝ
  -- ha1: a = a1ᴴ * a1
  -- b1: Matrix (Fin n) (Fin n) ℝ
  -- hb1: b = b1ᴴ * b1
  rw [ha1, hb1]
  rw [<-trace_form_of_inner_product]
  simp [traceMHDotM]
  rw [transpose_mul]
  simp
  rw [mul_assoc]
  rw [trace_mul_comm]
  rw [← mul_assoc]
  rw [mul_assoc]
  let c := b1 * a1ᵀ
  have hc : 0 ≤ trace (cᵀ * c) := by
    rw [trace_form_of_inner_product]
    exact inner_self_nonneg
  simp at hc
  exact hc



open GateauxDeriv
-- 2.13(a)

-- 计算 a^T Xb 的导数，大致思路为容易验证导数 D 应当满足 D . V = a^T V b，取 D = a^T b ，分别验证两个等式即可
-- 主要困难在于需要用开集的条件规约出tendsTo 内部的 t != 0，
-- 这里通过用 eventuallyEq_nhdsWithin_of_eqOn 证明引理引导 apply tendsto_congr' 自动匹配解决
theorem problem_a (a : Fin m → ℝ) (X : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ)
  : HasGateauxDerivAt (f_aXb a b) X (vecMulVec a b) := by
    simp [HasGateauxDerivAt]
    simp [Matrix.add_mulVec]
    simp [Matrix.smul_mulVec_assoc]
    simp [← div_mul_eq_mul_div]
    intro V
    have : innerProductofMatrix (vecMulVec a b) V = a ⬝ᵥ mulVec V b := by
      rw [<- f_aXb]
      apply Eq.symm
      apply f_aXb_eq
    rw [this]
    have : (fun t => t / t * a ⬝ᵥ mulVec V b) =ᶠ[𝓝[≠] 0] (fun _ => a ⬝ᵥ mulVec V b) := by
      apply eventuallyEq_nhdsWithin_of_eqOn
      intro x h
      simp
      rw [div_self (h), one_mul]
    apply (tendsto_congr' this).mpr
    apply tendsto_const_nhds

-- 2.13(b)
@[simp]
def f_XAX (A : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin n) ℝ → ℝ :=
  fun X => trace (Xᵀ * A * X)

theorem problem_b (A : Matrix (Fin m) (Fin m) ℝ) (X : Matrix (Fin m) (Fin n) ℝ)
  (h : ∃ f', HasGateauxDerivAt (f_XAX A) X f'):
  GateauxDeriv (f_XAX A) X h = (A + Aᵀ) * X  :=
  by
    sorry

-- 2.13(c)
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
