import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.RowCol
import Mathlib.Data.Matrix.Reflection
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Fin.Tuple.Reflection

open BigOperators
open Finset
open Matrix

def mat : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 2;
     3, 4]

#eval dotProductᵣ ![1, 2] ![3, 4]

#check Matrix
#check Matrix (Fin 2) (Fin 2) ℝ

variable {a b : Matrix (Fin 2) (Fin 2) ℝ}

variable [Fintype m] [Fintype n] [Fintype p]

#check a 0 1
#check a * b

#check mulᵣ_eq

#check a 1 2
#check (Fin 2)


variable {c d : Matrix (Fin 2) (Fin 5) ℝ}

#check trace a
#check Matrix.transpose c
#check ((Matrix.transpose c) * d)
#check Matrix.diag
def try1 {i j : Nat}: aᵀ i j = a j i := by
  simp [transpose]
variable {v v1 v2 : (Fin 2 → ℝ)}

#check mulVec a v         -- matrix * vector
#check vecMul v a         -- vector * matrix
#check dotProduct v1 v2   -- vector * vector



--!!! definition

-- innerProductofMatrix a b -- is defined as -- ∑ i j, (a i j) * (b i j)
def innerProductofMatrix (n m : Nat) (a b : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin m, (a i j) * (b i j)

-- traceMTDotM a b -- is defined as -- trace (aᵀ * b)
def traceMTDotM (n m : Nat) (a b: Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  trace (aᵀ * b)

def is_positive_semidefinite (n : Nat) (A : Matrix (Fin n) (Fin n) ℝ) : Prop
  := ∀ (v : (Fin n → ℝ)), dotProduct v (mulVec A v) ≥ 0




-- !!! theorem

-- trace (A * B) = trace (B * A)
#check trace_mul_comm

-- ∑ i in Fin n, ∑ j in Fin m, p i j
--      = ∑ j in Fin m, ∑ i in Fin n, p i j
#check Finset.sum_comm

-- ⟨a, b⟩ = trace (aᵀ * b)
theorem iProd_eq_traceDot (n m : Nat) (a b : Matrix (Fin n) (Fin m) ℝ) :
  innerProductofMatrix n m a b = traceMTDotM n m a b := by
    rw [innerProductofMatrix, traceMTDotM]
    rw [← mulᵣ_eq, mulᵣ]
    rw [trace]
    simp [dotProduct]
    exact Finset.sum_comm

-- (aᵀ b)ᵢᵢ = ∑ j, (aᵢⱼ) * (bᵢⱼ)
private theorem MTDotM (n m : Nat) (a b : Matrix (Fin n) (Fin m) ℝ) :
  ((∀ i : Fin m,
    (aᵀ * b).diag i =
    ∑ j : Fin n, (a j i) * (b j i))) := by
    intro id
    rw [Matrix.diag]
    rw [← mulᵣ_eq, mulᵣ]
    simp [dotProduct]


#check Matrix.mulᵣ a b

-- [aᵀ * a]_ii >= 0
theorem diagPosMTDotM (n m : Nat) (a : Matrix (Fin n) (Fin m) ℝ) :
  ∀ i, 0 ≤ (aᵀ * a).diag i := by
    intro x
    rw [MTDotM]
    apply Finset.sum_nonneg
    intro _ _
    rw [← pow_two]
    apply pow_two_nonneg

-- a matrix can be decomposed into a product of a matrix and its transpose
theorem matrix_decomposition (n : Nat) (a : Matrix (Fin n) (Fin n) ℝ ) :
  is_positive_semidefinite n a → ∃ b : Matrix (Fin n) (Fin n) ℝ, a = bᵀ * b := by
  sorry


theorem final_conclusion (n : Nat) (a b: Matrix (Fin n) (Fin n) ℝ ) :
  is_positive_semidefinite n a → is_positive_semidefinite n b →
    0 ≤ innerProductofMatrix n n a b := by
  intro ha hb
  rcases ((matrix_decomposition n a) ha) with ⟨a1, ha1⟩
  rcases ((matrix_decomposition n b) hb) with ⟨b1, hb1⟩
  -- a1: Matrix (Fin n) (Fin n) ℝ
  -- ha1: a = a1ᵀ * a1
  -- b1: Matrix (Fin n) (Fin n) ℝ
  -- hb1: b = b1ᵀ * b1
  rw [ha1, hb1, iProd_eq_traceDot]
  simp [traceMTDotM]
  rw [mul_assoc]
  rw [trace_mul_comm]
  rw [← mul_assoc, mul_assoc]
  let c := b1 * a1ᵀ
  have hc : 0 ≤ trace (cᵀ * c) := by
    rw [trace]
    apply Finset.sum_nonneg
    intro _ _
    apply diagPosMTDotM
  simp at hc
  exact hc
