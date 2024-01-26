import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Reflection
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Polynomial.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
-- import Mathlib.Data.Fin.Tuple.Reflection
-- import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
-- import Mathlib.Topology.Instances.Matrix
-- import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
-- import Mathlib.Data.Nat.Factorization.Basic
-- import Mathlib.LinearAlgebra.Matrix.PosDef
-- import Mathlib.LinearAlgebra.Matrix.Adjugate
-- import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Matrix.Rank
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
-- def HasGateauxDerivAt {m n: Nat} (f : Matrix (Fin m) (Fin n) ℝ → ℝ) (X : Matrix (Fin m) (Fin n) ℝ) (f' : Matrix (Fin m) (Fin n) ℝ) : Prop :=
--   ∀ V : Matrix (Fin m) (Fin n) ℝ,
--     HasGateauxDerivAtDirection f X f' V

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

private lemma finsum_pos {α : Type _} [Fintype α] {f : α → ℝ} (hf : ∀ i, 0 ≤ f i) (h : ∃ i, 0 < f i) :
  0 < ∑ i, f i := by
    let ⟨i0, hi0⟩ := h
    let zero_f := fun _ : α => (0 : ℝ )
    have h1 : ∀ t : α, zero_f t ≤ f t := by
      intro t
      simp
      apply hf t
    have :  ∑ t : α, zero_f t < ∑ t : α, f t := by
      apply sum_lt_sum
      simp
      exact h1
      use i0
      simp
      exact hi0
    simp at this
    exact this


theorem inner_product_of_self_is_zero_infer_zero_matrix:
  ∀ {n m : Nat} (a : Matrix (Fin n) (Fin m) ℝ),
      innerProductofMatrix a a = 0 → a = 0 := by
    intro n m a h
    dsimp [innerProductofMatrix] at h
    contrapose! h  -- 利用h来做反证法
    have : ∃ i : Fin n, ∃ j : Fin m, a i j ≠ 0 := by
      contrapose! h
      apply Matrix.ext -- 定理：矩阵相等 当且仅当 矩阵的每个分量都相等
      simp
      exact h
    let ⟨i, ⟨j, hij⟩⟩ := this -- 把存在性的变量和结论具体的引入
    have hij' : 0 < a i j * a i j := mul_self_pos.mpr hij -- mpr为从右到左
    have h1 : ∀ t : Fin m, 0 ≤ a i t * a i t := by
      intro t
      apply mul_self_nonneg
    have : 0 < ∑ t : Fin m, a i t * a i t := by
      apply finsum_pos
      exact h1
      use j -- 把存在性的变量带入
    have : ∑ i : Fin n, ∑ j : Fin m, a i j * a i j > 0 := by
      apply finsum_pos
      intro t
      have : 0 ≤ ∑ j : Fin m, a t j * a t j := by
        apply Fintype.sum_nonneg
        intro t'
        simp
        apply mul_self_nonneg
      exact this
      use i
    simp at this
    exact ne_of_gt this


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

theorem bounded_poly {n : Nat} (p : Polynomial ℝ ) :
  ∃ M > 0, ∀ x : ℝ , |x| < 1 → |Polynomial.eval x p| < M :=by
  use 2
  constructor
  · linarith
  intro h ha
  rw [Polynomial.eval_eq_sum]
  sorry -- 只需取δ 使得每个次数项都小于 M/n即可 （需调整位置）


theorem det_limit {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ ):
  ∀ ε > 0 ,∃ δ > 0, ∀ x : ℝ, |x| < δ → |det (1 + x • A) - 1| < ε := by
  intro a ha
  use 1/3
  constructor
  · linarith
  intro b hb
  rw[ Matrix.det_one_add_smul]
  let c := min a (1)
  simp [add_sub_right_comm] -- 大部分情况还是用simp
  have this : c ≤ a := by
    simp [min_le_left]
  sorry -- 只需调整位置，取 δ = min (c / 2 * max (trace A, M)) 1即可


theorem det_notzero {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ): -- 要合适的取 δ 来证明
  ∃ δ > 0, ∀ x : ℝ, |x| < δ → det (1 + x • A) ≠ 0 := by
  have h1: ∃ δ₁ > 0, ∀ x : ℝ, |x| < δ₁ → |det (1 + x • A) - 1| < 1 :=by
    apply det_limit
    linarith
  let ⟨δ₁, h2⟩ := h1
  use δ₁
  constructor
  · simp [h2]
  rcases h2 with ⟨ha, hb⟩ -- 将and拆为两条
  intro x hx
  have hhh := hb x hx
  rw [abs_lt] at hhh
  linarith [hhh.1]

-- 用 ε,δ 语言证明 log (1 + t * R) / t 的极限为 R
-- 好在 mathlib 库里有一个 atTop 版本的证明 Real.tendsto_mul_log_one_plus_div_atTop
theorem ln_delta_epsilon (R: Real): -- 要合适的取 δ 来证明
  ∀ ε > 0, ∃ δ > 0, ∀ x ≠ 0, |x| < δ → |Real.log (1 + x * R) / x - R| < ε := by
  have hR := Real.tendsto_mul_log_one_plus_div_atTop R
  have hnR := Real.tendsto_mul_log_one_plus_div_atTop (-R)
  rw [Metric.tendsto_atTop] at hR
  rw [Metric.tendsto_atTop] at hnR
  simp [dist] at *
  intro ε' hε'
  specialize hR ε' hε'
  specialize hnR ε' hε'
  let ⟨N1, hN1⟩  := hR
  let ⟨N2, hN2⟩  := hnR
  let δ := 1 / max 1 (1 + max N1 N2)
  have hδ : N1 < 1/δ ∧ N2 < 1/δ := by
    constructor
    · simp; right;
      linarith [zero_lt_one', le_max_left N1 N2]
    · simp; right;
      linarith [zero_lt_one', le_max_right N1 N2]
  use δ
  have hpos_δ : 0 < δ := div_pos
    (by norm_num)
    (lt_of_lt_of_le (by norm_num) (le_max_left 1 (1 + max N1 N2)))
  constructor
  · exact hpos_δ
  intro x hnx hx
  rcases (Ne.lt_or_lt hnx) with (hxl | hxr)
  · let y := - 1 / x
    have hxy : x = - 1 / y := by simp [y, ← div_mul]
    rw [hxy, div_mul_eq_mul_div, neg_one_mul, ← div_mul, div_neg, div_one]
    rw [neg_mul, neg_sub_left, abs_neg, add_comm, mul_comm]
    rw [abs_of_neg hxl] at hx
    have hy : N2 ≤ y := by
      have hpos_y: 0 < y := by apply one_div_pos.mp; simp; linarith;
      rw [hxy, neg_div, neg_neg] at hx
      apply (one_div_lt hpos_y hpos_δ).mp at hx
      linarith [hx, hδ.2]
    exact hN2 y hy
  · let y := 1 / x
    have hxy : x = 1 / y := by simp [y]
    rw [mul_comm x R]
    rw [hxy, mul_one_div, ← div_mul, div_one, mul_comm]
    rw [abs_of_pos hxr] at hx
    have hy : N1 ≤ y := by
      have hpos_y: 0 < y := by apply one_div_pos.mp; linarith [hxy, hxr]
      rw [hxy] at hx
      apply (one_div_lt hpos_y hpos_δ).mp at hx
      linarith [hx, hδ.1]
    exact hN1 y hy

theorem upper_nonezero {n: Nat} (A : Matrix (Fin n) (Fin n) ℝ): -- 定理名称后的相当于是任意的条件 (∀ n: Nat,...)
  is_upper_triangle A → det (A) ≠ 0 → ∀ i : Fin n, A i i ≠ 0 := by
  intro i hi
  rw [upper_triangle_det] at hi -- 利用括号内的条件来rewrite hi
  simp [Finset.prod_ne_zero_iff.mp hi]
  assumption

-- schur decomposition theorem () -- 定理的叙述有些漏洞，因为只能sorry了，事实上是局限于数域的问题
theorem schur_decomposition (n: Nat) (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ U R, Orthogonal_Matrix U ∧ is_upper_triangle R ∧ A = Uᵀ * R * U := by  -- 抱歉，这个必须要sorry，因为结论在全局意义上有些漏洞
  sorry

theorem Orthogonal_inv {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ):
  Orthogonal_Matrix A → A * Aᵀ= 1 := by
  intro h
  simp [Orthogonal_Matrix] at h
  have this: A⁻¹ = Aᵀ:= by
    exact inv_eq_left_inv h
  rw [← this]
  have hh : ∃ B, B * A = 1 := by
    use Aᵀ
  have hhh := Matrix.vecMul_surjective_iff_exists_left_inverse.mpr hh
  have hhhh := Matrix.vecMul_surjective_iff_isUnit.mp hhh
  have hhhhh : Invertible A := by
    exact Matrix.invertibleOfIsUnitDet A ((Matrix.isUnit_iff_isUnit_det A).mp hhhh)
  simp [Matrix.mul_inv_of_invertible A] -- simple输入括号内的参数 方框内的assumption会自行寻找
-- Matrix.mulVec_surjective_iff_exists_right_inverse
