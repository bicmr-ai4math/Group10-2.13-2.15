
import «Tutorial».Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic

open GateauxDeriv Matrix Topology
#check eventuallyEq_nhdsWithin_of_eqOn

variable {m n a b : ℕ}



-- 2.13(b)
@[simp]
def f_XAX (A : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin n) ℝ → ℝ :=
  fun X => trace (Xᵀ * A * X)

theorem problem_b' (A : Matrix (Fin m) (Fin m) ℝ) (X : Matrix (Fin m) (Fin n) ℝ)
  :  HasGateauxDerivAt (f_XAX A) X ((A + Aᵀ) * X) :=
  by
    simp [HasGateauxDerivAt]
    intro V
    simp [Matrix.add_mul]
    simp [Matrix.mul_add]
    simp [mul_add]
    simp [add_assoc]
    simp [← add_assoc]
    simp [← mul_add]
    simp [← div_mul_eq_mul_div]
    have h :  trace (Xᵀ * A * V) = trace (Aᵀ * X * Vᵀ) := by
      rw [trace_mul_comm, ← trace_transpose, Matrix.transpose_mul, Matrix.transpose_mul]
      simp
    rw [h]

    have h1 : trace (Vᵀ * A * X) = trace (A * X * Vᵀ) := by
      rw [Matrix.mul_assoc, trace_mul_comm]
    rw [h1]
    rw [← trace_add]

    have h3 : trace (Aᵀ * X * Vᵀ + A * X * Vᵀ) = trace ((Aᵀ * X + A * X) * Vᵀ) := by
      rw [← Matrix.add_mul]
    rw [h3]

    have h4 : trace ((Aᵀ * X + A * X) * Vᵀ) = (innerProductofMatrix (Aᵀ * X + A * X) V) := by
      rw [iProd_eq_traceDot, traceMHDotM, ← trace_transpose, Matrix.transpose_mul]
      simp
      rw [trace_mul_comm]
    rw [h4]
    rw [Metric.tendsto_nhdsWithin_nhds]
    /-

    ∀ ε > 0,
    ∃ δ > 0,
    ∀ {x : ℝ},
      x ∈ {0}ᶜ →
        dist x 0 < δ →
          dist (x / x * (innerProductofMatrix (Aᵀ * X + A * X) V + x * trace (Vᵀ * A * V)))
              (innerProductofMatrix (A * X + Aᵀ * X) V) < ε
    -/

    intro ε h


    -- use δ

    sorry


    -- have h5 : Tendsto (fun t => t / t * (innerProductofMatrix (Aᵀ * X + A * X) V + t * trace (Vᵀ * A * V))) = Tendsto (fun t => t / t * (innerProductofMatrix (Aᵀ * X + A * X) V)) := by

    --   sorry
    -- rw [h5]



    -- have : (fun t => t / t * (innerProductofMatrix (Aᵀ * X + A * X) V)) =ᶠ[𝓝[≠] 0] (fun _ => innerProductofMatrix (A * X + Aᵀ * X) V) := by
    --   apply eventuallyEq_nhdsWithin_of_eqOn
    --   intro x h
    --   simp
    --   rw [div_self (h), one_mul]
    --   rw [add_comm]

    -- apply (tendsto_congr' this).mpr
    -- apply tendsto_const_nhds
