import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Reflection
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Basic
-- import Mathlib.Data.Fin.Tuple.Reflection
-- import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
-- import Mathlib.Topology.Instances.Matrix
-- import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Log
-- import Mathlib.Data.Nat.Factorization.Basic
-- import Mathlib.LinearAlgebra.Matrix.PosDef
-- import Mathlib.LinearAlgebra.Matrix.Adjugate
-- import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Analysis.InnerProductSpace.Basic
open BigOperators
open Finset
open Matrix Filter Set Topology

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
def innerProductofMatrix {n m : Nat} (a b : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin m, (a i j) * (b i j)

-- traceMHDotM a b -- is defined as -- trace (aᴴ * b)
def traceMHDotM (n m : Nat) (a b: Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  trace (aᴴ * b)

-- ⟨a, b⟩ = trace (aᴴ * b)
theorem iProd_eq_traceDot (n m : Nat) (a b : Matrix (Fin n) (Fin m) ℝ) :
  innerProductofMatrix a b = traceMHDotM n m a b := by
    rw [innerProductofMatrix, traceMHDotM]
    rw [← mulᵣ_eq, mulᵣ]
    rw [trace]
    simp [dotProduct]
    exact Finset.sum_comm

namespace GateauxDeriv

-- define f' is f's G derivative.
-- Noticing that Grandinet in Mathlib require the space is normed
-- but when we talk about Gateaux derivative of matrix, it seems we don't need to specify a norm of matrix
-- so we may redefine the definition of Gateaux derivative
def HasGateauxDerivAt {m n: Nat} (f : Matrix (Fin m) (Fin n) ℝ → ℝ) (X : Matrix (Fin m) (Fin n) ℝ) (f' : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ V : Matrix (Fin m) (Fin n) ℝ,
    Filter.Tendsto (fun t : ℝ ↦ (f (X + t • V) - f X ) / t)
      (𝓝[≠] 0) (𝓝 (innerProductofMatrix f' V))

-- define f is G differentiable
def GateauxDifferentiable {m n: Nat} (f : Matrix (Fin m) (Fin n) ℝ → ℝ) (X : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∃ G : Matrix (Fin m) (Fin n) ℝ, HasGateauxDerivAt f X G

-- take the derivative of the function which is differentiable
noncomputable
irreducible_def GateauxDeriv {m n: Nat} (f : Matrix (Fin m) (Fin n) ℝ → ℝ) (X : Matrix (Fin m) (Fin n) ℝ)
    (h : ∃ f', HasGateauxDerivAt f X f') : Matrix (Fin m) (Fin n) ℝ :=
  Classical.choose h

lemma GateauxDeriv_spec {m n: Nat} (f : Matrix (Fin m) (Fin n) ℝ → ℝ) (X : Matrix (Fin m) (Fin n) ℝ)
    (h : ∃ f', HasGateauxDerivAt f X f') : HasGateauxDerivAt f X (GateauxDeriv f X h) := by
  rw [GateauxDeriv_def]
  exact Classical.choose_spec h

end GateauxDeriv


namespace InnerProductOfMatrix
private theorem eq_of_pointwise_inner_product_and_trace_inner_product:
  ∀ {n m : Nat} (a b : Matrix (Fin n) (Fin m) ℝ),
      innerProductofMatrix a b = traceMHDotM n m a b := by
    intro n m a b
    rw [innerProductofMatrix, traceMHDotM]
    rw [← mulᵣ_eq, mulᵣ]
    rw [trace]
    simp [dotProduct]
    exact Finset.sum_comm

-- (aᴴ b)ᵢᵢ = ∑ j, (aᵢⱼ) * (bᵢⱼ)
private theorem MHDotM (n m : Nat) (a b : Matrix (Fin n) (Fin m) ℝ) :
  ((∀ i : Fin m,
    (aᴴ * b).diag i =
    ∑ j : Fin n, (a j i) * (b j i))) := by
    intro id
    rw [Matrix.diag]
    rw [← mulᵣ_eq, mulᵣ]
    simp [dotProduct]


-- [aᴴ * a]ᵢᵢ ≥ 0
theorem diagPosMHDotM (n m : Nat) (a : Matrix (Fin n) (Fin m) ℝ) :
  ∀ i, 0 ≤ (aᴴ * a).diag i := by
    intro x
    rw [MHDotM]
    apply Finset.sum_nonneg
    intro _ _
    rw [← pow_two]
    apply pow_two_nonneg


private theorem nonneg_of_inner_product_of_self_is_zero:
  ∀ {n m : Nat} (a : Matrix (Fin n) (Fin m) ℝ),
      0 ≤ innerProductofMatrix a a := by
    intro n m a
    rw [eq_of_pointwise_inner_product_and_trace_inner_product]
    simp [traceMHDotM]
    rw [trace]
    apply Finset.sum_nonneg
    intro _ _
    apply diagPosMHDotM

theorem inner_product_of_self_is_zero_infer_zero_matrix:
  ∀ {n m : Nat} (a : Matrix (Fin n) (Fin m) ℝ),
      innerProductofMatrix a a = 0 → a = 0 := by
  sorry


@[default_instance]
instance inner_product_space_of_matrix (n m : ℕ): InnerProductSpace.Core ℝ (Matrix (Fin n) (Fin m) ℝ) :=
  {
    inner := innerProductofMatrix,
    conj_symm := by
      intro x y
      simp [innerProductofMatrix]
      have : ∀ i j, (x i j) * (y i j) = (y i j) * (x i j) := by
        intros
        apply mul_comm
      simp [this]
    nonneg_re := nonneg_of_inner_product_of_self_is_zero,
    definite := inner_product_of_self_is_zero_infer_zero_matrix,
    add_left := by
      intro x y z
      simp []
      repeat rw [eq_of_pointwise_inner_product_and_trace_inner_product]
      simp [traceMHDotM]
      rw [Matrix.add_mul]
      rw [Matrix.trace_add]
    smul_left := by
      intro x y a
      simp
      repeat rw [eq_of_pointwise_inner_product_and_trace_inner_product]
      simp [traceMHDotM]
  }

@[default_instance]

noncomputable
instance norm_of_matric (n m : ℕ): NormedAddCommGroup (Matrix (Fin n) (Fin m) ℝ) := InnerProductSpace.Core.toNormedAddCommGroup

@[default_instance]
noncomputable
instance inner_product (n m : ℕ): InnerProductSpace ℝ (Matrix (Fin n) (Fin m) ℝ) := InnerProductSpace.ofCore (inner_product_space_of_matrix n m)

theorem trace_form_of_inner_product {n m : ℕ} (a b : Matrix (Fin n) (Fin m) ℝ) :
  trace (aᵀ * b) = ⟪a, b⟫_ℝ := by
  have : inner a b = innerProductofMatrix a b := by
    rfl
  rw [this]
  simp [eq_of_pointwise_inner_product_and_trace_inner_product]
  rfl

end InnerProductOfMatrix


@[simp]
def f_aXb  {m n : Nat}(a : Fin m → ℝ) (b : Fin n → ℝ): Matrix (Fin m) (Fin n) ℝ → ℝ :=
  fun X => dotProduct a (mulVec X b)

lemma f_aXb_eq {m n : Nat}(a : Fin m → ℝ) (b : Fin n → ℝ) (X : Matrix (Fin m) (Fin n) ℝ) :
  f_aXb a b X = innerProductofMatrix (vecMulVec a b) X := by
    simp [f_aXb, innerProductofMatrix, dotProduct, vecMulVec]
    dsimp [mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

-- define of upper triangle matrix
def is_upper_triangle {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Matrix.BlockTriangular A id

theorem is_upper_triangle.smul {n : Nat} {A : Matrix (Fin n) (Fin n) ℝ} {c : ℝ}
  (hA : is_upper_triangle A) : is_upper_triangle (c • A) := by
    simp [is_upper_triangle, BlockTriangular] at *
    intro _ _ hij
    exact Or.inr (hA hij)

theorem is_upper_triangle.add {n : Nat} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : is_upper_triangle A) (hB : is_upper_triangle B): is_upper_triangle (A + B) := by
  simp [is_upper_triangle] at *   -- *为将所有的标记都化简
  exact Matrix.BlockTriangular.add hA hB

theorem is_upper_triangle.one {n : Nat} : is_upper_triangle (1 : Matrix (Fin n) (Fin n) ℝ) := by
  simp [is_upper_triangle]
  exact Matrix.blockTriangular_one

theorem upper_triangle_det {n : Nat} {A : Matrix (Fin n) (Fin n) ℝ} (h : is_upper_triangle A) :
  det A = ∏ i : Fin n, A i i := by
  simp [is_upper_triangle] at h
  exact (Matrix.det_of_upperTriangular h)

-- Matrix.det_of_upperTriangular

-- define of orthogonal matrix
def Orthogonal_Matrix {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ ) : Prop :=
  Aᵀ * A = 1


-- schur decomposition theorem
theorem schur_decomposition (n: Nat) (A : Matrix (Fin n) (Fin n) ℝ) :
  ∃ U R, Orthogonal_Matrix U ∧ is_upper_triangle R ∧ A = Uᵀ * R * U := by
  sorry

theorem Orthogonal_inv {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ):
  Orthogonal_Matrix A → A * Aᵀ= 1 := by
  intro h
  sorry
