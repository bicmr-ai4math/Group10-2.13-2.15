import «Tutorial».Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

open InnerProductOfMatrix Matrix
theorem final_conclusion (n : Nat) (a b: Matrix (Fin n) (Fin n) ℝ ) :
  PosSemidef a → PosSemidef b →
    0 ≤ ⟪a, b⟫_ℝ  := by
  intro ha hb
  rcases (posSemidef_iff_eq_transpose_mul_self.mp ha) with ⟨a1, ha1⟩
  rcases (posSemidef_iff_eq_transpose_mul_self.mp hb) with ⟨b1, hb1⟩
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
