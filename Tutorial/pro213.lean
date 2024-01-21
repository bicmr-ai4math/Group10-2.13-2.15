import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.RowCol

import Mathlib.Data.Matrix.Reflection

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Order.Filter.Basic
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

-- 2.13
#check Filter.Tendsto

#check DifferentiableAt

open Matrix Filter Set Topology
open BigOperators
open Finset
open Matrix

def innerProductofMatrix (n m : Nat) (a b : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin m, (a i j) * (b i j)

#check Matrix.topologicalRing
variable {x }
#check 𝓝 x
#check ℝ

-- traceMHDotM a b -- is defined as -- trace (aᴴ * b)
def traceMHDotM (n m : Nat) (a b: Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  trace (aᴴ * b)

-- ⟨a, b⟩ = trace (aᴴ * b)
theorem iProd_eq_traceDot (n m : Nat) (a b : Matrix (Fin n) (Fin m) ℝ) :
  innerProductofMatrix n m a b = traceMHDotM n m a b := by
    rw [innerProductofMatrix, traceMHDotM]
    rw [← mulᵣ_eq, mulᵣ]
    rw [trace]
    simp [dotProduct]
    exact Finset.sum_comm

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

-- define f' is f's G derivative
def HasGateauxDerivAt (m n: Nat) (f : Matrix (Fin m) (Fin n) ℝ → ℝ) (X : Matrix (Fin m) (Fin n) ℝ) (f' : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ V : Matrix (Fin m) (Fin n) ℝ,
    Filter.Tendsto (fun t : ℝ ↦ (f (X + t • V) - f X ) / t)
      (𝓝[≠] 0) (𝓝 (innerProductofMatrix m n f' V))

-- define f is G differentiable
def GateauxDifferentiable (m n: Nat) (f : Matrix (Fin m) (Fin n) ℝ → ℝ) (X : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∃ G : Matrix (Fin m) (Fin n) ℝ, HasGateauxDerivAt m n f X G

-- take the derivative of the function which is differentiable
noncomputable
irreducible_def GateauxDeriv (m n: Nat) (f : Matrix (Fin m) (Fin n) ℝ → ℝ) (X : Matrix (Fin m) (Fin n) ℝ)
    (h : ∃ f', HasGateauxDerivAt m n f X f') : Matrix (Fin m) (Fin n) ℝ :=
  Classical.choose h

lemma GateauxDeriv_spec (m n: Nat) (f : Matrix (Fin m) (Fin n) ℝ → ℝ) (X : Matrix (Fin m) (Fin n) ℝ)
    (h : ∃ f', HasGateauxDerivAt m n f X f') : HasGateauxDerivAt m n f X (GateauxDeriv m n f X h) := by
  rw [GateauxDeriv_def]
  exact Classical.choose_spec h

-- 2.13(a)
@[simp]
def f_aXb  (a : Fin m → ℝ) (b : Fin n → ℝ): Matrix (Fin m) (Fin n) ℝ → ℝ :=
  fun X => dotProduct a (mulVec X b)

theorem problem_a (a : Fin m → ℝ) (X : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ)
  (h : ∃ f', HasGateauxDerivAt m n (f_aXb a b) X f'):
  GateauxDeriv m n (f_aXb a b) X h = vecMulVec a b :=
  by
    simp [HasGateauxDerivAt] at h
    simp [Matrix.add_mulVec] at h
    simp [Matrix.smul_mulVec_assoc] at h
    simp [← div_mul_eq_mul_div] at h
    replace h : ∃ f', ∀ (V : Matrix (Fin m) (Fin n) ℝ),
        Tendsto (fun t : ℝ => a ⬝ᵥ mulVec V b) (𝓝[≠] 0) (𝓝 (innerProductofMatrix m n f' V)) := by
      convert h using 3
      apply tendsto_congr'
      apply eventuallyEq_nhdsWithin_of_eqOn
      intro x hx
      dsimp
      rw [div_self (Set.mem_compl hx), one_mul]
    have hh : ∀ p q : Fin m → ℝ, dotProduct p q = trace (vecMulVec q p) :=
      by
        intro p q
        simp [dotProduct, vecMulVec, trace]
        rw [← sub_eq_zero, ← sum_sub_distrib]
        apply sum_eq_zero
        intro _ _
        ring
    sorry

-- 2.13(b)
@[simp]
def f_XAX (A : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin n) ℝ → ℝ :=
  fun X => trace (Xᵀ * A * X)

theorem problem_b (A : Matrix (Fin m) (Fin m) ℝ) (X : Matrix (Fin m) (Fin n) ℝ)
  (h : ∃ f', HasGateauxDerivAt m n (f_XAX A) X f'):
  GateauxDeriv m n (f_XAX A) X h = (A + Aᵀ) * X  :=
  by
    sorry


-- 2.13(c)
noncomputable
def f_lndet : Matrix (Fin n) (Fin n) ℝ → ℝ :=
  fun X => Real.log X.det

theorem problem_c (X : Matrix (Fin n) (Fin n) ℝ)
  (h : ∃ f', HasGateauxDerivAt n n (f_lndet) X f'):
  GateauxDeriv n n (f_lndet) X h = (X⁻¹)ᵀ  :=
  sorry
