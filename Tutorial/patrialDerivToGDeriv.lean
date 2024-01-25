import «Tutorial».Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Reflection
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.UniformSpace.Basic
open GateauxDeriv Topology Filter Set InnerProductOfMatrix BigOperators
#check     Tendsto
@[default_instance]
noncomputable
instance matrix_topology {n m: ℕ } : TopologicalSpace (Matrix (Fin n) (Fin m) ℝ) := UniformSpace.toTopologicalSpace
def matrix_base {n m :ℕ} (i: Fin n) (j : Fin m) : Matrix (Fin n) (Fin m) ℝ := fun  i' j' => if i' = i ∧ j' = j then 1 else 0

-- G 导数是所有偏导数的和
theorem all_partial_deriv_to_GDeriv {n m:ℕ} (f : Matrix (Fin n) (Fin m) ℝ -> ℝ) (X : Matrix (Fin n) (Fin m) ℝ)
  (pf' : Fin n -> Fin m -> Matrix (Fin n) (Fin m) ℝ)
  (cond : ∀ i : Fin n, ∀ j : Fin m,  HasGateauxDerivAtDirection f X (pf' i j) (matrix_base i j)):
  HasGateauxDerivAt f X (∑ i: Fin n , ∑ j: Fin m, pf' i j ) :=
    sorry
