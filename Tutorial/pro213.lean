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
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.FiniteDimensional

-- 2.13
#check Filter.Tendsto

#check DifferentiableAt

open Matrix Filter Set Topology
open BigOperators
open Finset
open Matrix

structure Matrix' (m n : Type u) (α : Type v) [Fintype m] [Fintype n] where
  entries : m → n → α

namespace Matrix'

#check Matrix.topologicalRing
variable {x }
#check 𝓝 x
#check ℝ

-- ⟨a, b⟩ = trace (aᴴ * b)
theorem iProd_eq_traceDot (n m : Nat) (a b : Matrix (Fin n) (Fin m) ℝ) :
  innerProductofMatrix a b = traceMHDotM n m a b := by
    rw [innerProductofMatrix, traceMHDotM]
    rw [← mulᵣ_eq, mulᵣ]
    rw [trace]
    simp [dotProduct]
    exact Finset.sum_comm

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

-- define of upper triangle matrix
def is_upper_triangle (n : Nat) (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j : Fin n, j < i → A i j = 0

-- define of orthogonal matrix
def Orthogonal_Matrix (n : Nat) (A : Matrix (Fin n) (Fin n) ℝ ) : Prop :=
  A * Aᵀ = 1

-- schur decomposition theorem
theorem schur_decomposition (n: Nat) (A : Matrix (Fin n) (Fin n) ℝ) :
  ∃ U R, Orthogonal_Matrix n U ∧ is_upper_triangle n R ∧ A = Uᵀ * R * U := by
  sorry

open GateauxDeriv
-- 2.13(a)
@[simp]
def f_aXb  (a : Fin m → ℝ) (b : Fin n → ℝ): Matrix (Fin m) (Fin n) ℝ → ℝ :=
  fun X => dotProduct a (mulVec X b)

lemma f_aXb_eq (a : Fin m → ℝ) (b : Fin n → ℝ) (X : Matrix (Fin m) (Fin n) ℝ) :
  f_aXb a b X = innerProductofMatrix (vecMulVec a b) X := by
    simp [f_aXb, innerProductofMatrix, dotProduct, vecMulVec]
    dsimp [mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring


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

theorem problem_c (X : Matrix (Fin n) (Fin n) ℝ)
  (h : ∃ f', HasGateauxDerivAt (f_lndet) X f'):
  GateauxDeriv (f_lndet) X h = (X⁻¹)ᵀ  :=
  sorry
