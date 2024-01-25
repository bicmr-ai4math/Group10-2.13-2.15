-- package
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.RowCol

import Mathlib.Data.Matrix.Reflection

import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Matrix

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.FiniteDimensional

-- 环境
open BigOperators
open Finset
open Matrix
-- 矩阵内积
def innerProductofMatrix {n m : Nat} (a b : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin m, (a i j) * (b i j)

-- 定义trace
-- ⟨a, b⟩ = trace (aᴴ * b)
@[simp]
def traceMHDotM (n m : Nat) (a b: Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  trace (aᵀ   * b)

theorem iProd_eq_traceDot (n m : Nat) (a b : Matrix (Fin n) (Fin m) ℝ) :
  innerProductofMatrix a b = traceMHDotM n m a b := by
    rw [innerProductofMatrix, traceMHDotM]
    rw [← mulᵣ_eq, mulᵣ]
    rw [trace]
    simp [dotProduct]
    exact Finset.sum_comm

variable {m n : ℕ}
-- 收敛列
@[simp]
def ConvergesTo (s : ℕ → ℝ) (a : ℝ) := ∀ ε > 0, ∃ N,  ∀ n ≥ N , |s n - a| < ε

-- def ConvergesTo (s : ℕ → ℝ) (a : ℝ) := ∀ ε > 0, ∃ N, (∀ n ≥ N ∧ s n ≠ 0 ),  |s n - a| < ε
-- 定义Gateaux导数
@[simp]
def HasGateauxDerivAt (m n: ℕ) (f : Matrix (Fin m) (Fin n) ℝ → ℝ) (X : Matrix (Fin m) (Fin n) ℝ)
 (t : ℕ → ℝ)(_ : ∀ ε > 0, ∃ N,  ∀ n ≥ N , |t n - (0:ℝ)| < ε ∧ (t n ≠ 0))
   : Prop
   := ∀ V : Matrix (Fin m) (Fin n) ℝ, ∃ G : Matrix (Fin m) (Fin n) ℝ,
   ConvergesTo (fun n ↦ ((f (X + (t n)•V) - f X)/(t n) - innerProductofMatrix G V)) 0
-- 定义problem_b的函数
@[simp]
def f_XAX (A : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin n) ℝ → ℝ :=
  fun X => trace (Xᵀ * A * X)

#check mul_lt_mul_of_pos_right
section
variable (t : ℕ → ℝ) (t0 :  ∀ ε > 0, ∃ N,  ∀ n ≥ N , |t n - (0:ℝ)| < ε ∧ (t n ≠ 0))
-- 主定理证明
theorem problem_b (m n: ℕ) (A : Matrix (Fin m) (Fin m) ℝ) (X : Matrix (Fin m) (Fin n) ℝ):
HasGateauxDerivAt m n (f_XAX A) X t t0 := by
  simp
  intro V
  -- 实例化G
  have h₀ :∀k : ℕ , t k ≠ 0 → ((trace ((Xᵀ +  t k • Vᵀ) * A * (X +  t k • V)) - trace (Xᵀ * A * X)))/(t k) = trace ((A + Aᵀ) * X * Vᵀ) +  (t k) * trace (Vᵀ * A * V) := by
    intro k hk
    simp [Matrix.add_mul]
    simp [Matrix.mul_add]
    simp [mul_add]
    simp [add_assoc]
    simp [← add_assoc]
    simp [← mul_add]
    simp [← div_mul_eq_mul_div]
    have h :  trace (Xᵀ * A * V) = trace (Aᵀ * X * Vᵀ) := by
      rw [trace_mul_comm]
      rw [← trace_transpose]
      rw [Matrix.transpose_mul]
      rw [Matrix.transpose_mul]
      simp
    rw [h]

    have h1 : trace (Vᵀ * A * X) = trace (A * X * Vᵀ) := by
      rw [Matrix.mul_assoc]
      rw [trace_mul_comm]
    rw [h1]
    rw [div_self]
    simp
    rw [add_comm]
    apply hk

  use (A + Aᵀ) * X
  intro ε hε
  -- 利用 t0 假设找N
  rcases lt_trichotomy (trace (Vᵀ * A * V)) 0 with hl | he | hg

  -- trace (Vᵀ * A * V) < 0的情况
  · have h₁ : ε / |trace (Vᵀ * A * V)| > 0 := by
      apply div_pos hε
      apply abs_pos_of_neg hl
    rcases t0 (ε/|trace (Vᵀ * A * V)|) h₁ with ⟨N, h₂⟩
    use N
    intro n' h₃
    -- 换掉内积
    -- 换掉结论前半段
    rw[h₀ n']
    -- 换掉结论中的内积
    · have h₄ : innerProductofMatrix ((A + Aᵀ) * X) V = trace ((A + Aᵀ) * X * Vᵀ) := by
        rw [iProd_eq_traceDot, traceMHDotM, ← trace_transpose, Matrix.transpose_mul]
        simp
        rw [trace_mul_comm]

      rw[h₄]
      simp
      rw[abs_mul]
      -- intro h₅
      specialize h₂ n' h₃
      rcases h₂ with ⟨h₂_l, _⟩
      calc
        |t n'| * |trace (Vᵀ * A * V)| < (ε / |trace (Vᵀ * A * V)|) * |trace (Vᵀ * A * V)| := by
          have this : |trace (Vᵀ * A * V)| > 0 := by
            apply abs_pos_of_neg hl
          rw[← sub_zero (t n')]
          apply mul_lt_mul_of_pos_right h₂_l this
          -- sorry
        _ = ε :=
        by
          ring_nf
          rw [mul_assoc]
          field_simp
          rw [mul_div_assoc]
          rw [div_self]
          simp
          simp [hl]
          intro s
          absurd hl
          rw [s]
          simp
    · specialize h₂ n' h₃
      rcases h₂ with ⟨_, h_r⟩
      apply h_r


  -- trace (Vᵀ * A * V) = 0 的情况
  · rcases t0 ε hε with ⟨N, h₂⟩
    use N
    intro n'
    intro h1
    rw[h₀ n']
    rw [he]
    simp
    have h₄ : innerProductofMatrix ((A + Aᵀ) * X) V = trace ((A + Aᵀ) * X * Vᵀ) := by
      rw [iProd_eq_traceDot, traceMHDotM, ← trace_transpose, Matrix.transpose_mul]
      simp
      rw [trace_mul_comm]
    rw[h₄]
    simp
    exact hε
    · specialize h₂ n' h1
      rcases h₂ with ⟨_, h_r⟩
      apply h_r

-- trace (Vᵀ * A * V) > 0
  · have h₁ : ε / |trace (Vᵀ * A * V)| > 0 := by
      apply div_pos hε
      apply abs_pos_of_pos hg
-- #check abs_pos_of_pos
    rcases t0 (ε/|trace (Vᵀ * A * V)|) h₁ with ⟨N, h₂⟩
    use N
    intro n' h₃
    -- 换掉内积
    -- 换掉结论前半段
    rw[h₀ n']
    -- 换掉结论中的内积
    · have h₄ : innerProductofMatrix ((A + Aᵀ) * X) V = trace ((A + Aᵀ) * X * Vᵀ) := by
        rw [iProd_eq_traceDot, traceMHDotM, ← trace_transpose, Matrix.transpose_mul]
        simp
        rw [trace_mul_comm]

      rw[h₄]
      simp
      rw[abs_mul]
      -- intro h₅
      specialize h₂ n' h₃
      rcases h₂ with ⟨h₂_l, _⟩
      calc
        |t n'| * |trace (Vᵀ * A * V)| < (ε / |trace (Vᵀ * A * V)|) * |trace (Vᵀ * A * V)| := by
          have this : |trace (Vᵀ * A * V)| > 0 := by
            apply abs_pos_of_pos hg
          rw[← sub_zero (t n')]
          apply mul_lt_mul_of_pos_right h₂_l this
          -- sorry
        _ = ε :=
        by
          ring_nf
          rw [mul_assoc]
          field_simp
    · specialize h₂ n' h₃
      rcases h₂ with ⟨_, h_r⟩
      apply h_r
