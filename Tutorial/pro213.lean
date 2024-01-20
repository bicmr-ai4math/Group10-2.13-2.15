import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.RowCol
import Mathlib.Data.Matrix.Reflection

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Matrix

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.LinearAlgebra.Matrix.PosDef
-- import Mathlib.Analysis.Calculus.FDeriv.Basic

#check Filter.Tendsto


#check DifferentiableAt


open Matrix Filter Set Topology

variable {x : ℝ}
#check 𝓝 x

#check 𝓝

variable {mat : Matrix (Fin 2) (Fin 2) ℝ}


#check topologicalRing

--def Tendsto₁ {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :=
  --∀ V ∈ G, f ⁻¹' V ∈ F

variable {n m : ℕ}
#check Filter (Matrix (Fin n) (Fin m) ℝ)
#check 𝓝 x

variable {x₀ y₀ : ℝ}
variable {f : ℝ → ℝ}

#check DifferentiableAt ℝ f x₀
-- (h : DifferentiableAt (Matrix (Fin m) (Fin n) ℝ) f X)



def innerProductofMatrix (n m : Nat) (a b : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin m, (a i j) * (b i j)



def HasGateauxDerivAt (m n: Nat) (f : Matrix (Fin m) (Fin n) ℝ → ℝ) (X : Matrix (Fin m) (Fin n) ℝ) (f' : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ V : Matrix (Fin m) (Fin n) ℝ,
    Filter.Tendsto (fun t : ℝ ↦ (f (X + t • V) - f X ) / t)
      (𝓝[≠] 0) (𝓝 (innerProductofMatrix m n f' V))

def GateauxDifferentiable (m n: Nat) (f : Matrix (Fin m) (Fin n) ℝ → ℝ) (X : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∃ G : Matrix (Fin m) (Fin n) ℝ, HasGateauxDerivAt m n f X G

noncomputable section
def GateauxDeriv (m n: Nat) (f : Matrix (Fin m) (Fin n) ℝ → ℝ) (X : Matrix (Fin m) (Fin n) ℝ)
  (h : ∃ f', HasGateauxDerivAt m n f X f'): Matrix (Fin m) (Fin n) ℝ :=
  Classical.choose h


def f_aXb (a : Fin m → ℝ) (b : Fin n → ℝ): Matrix (Fin m) (Fin n) ℝ → ℝ :=
  fun X => dotProduct a (mulVec X b)

theorem problem_a (a : Fin m → ℝ) (X : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ)
  (h : ∃ f', HasGateauxDerivAt m n (f_aXb a b) X f'):
  GateauxDeriv m n (f_aXb a b) X h = vecMulVec a b :=
  sorry
