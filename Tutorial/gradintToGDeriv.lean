import «Tutorial».Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Reflection
import Mathlib.Init.Function
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Std.Tactic.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Topology.UniformSpace.Basic
open GateauxDeriv Topology Filter Set InnerProductOfMatrix Matrix BigOperators Tactic
#check     Tendsto

-- 实际执行总遇到了严重的问题，库中的 Gradient 推导出 UniformSpace.toTopologicalSpace 作为矩阵空间上的拓扑，但我们的推导使用库中已有的矩阵拓扑（似乎是乘积空间定义的）
-- 猜测可能是因为 hasGradientAt_iff_tendsto 使用了 CommpleteSpace 推导出的拓扑（mathlib 中有矩阵作为 Complete space 的 instance），自然走上了 UniformSpace 的路线
@[default_instance]
noncomputable
instance matrix_topology {n m: ℕ } : TopologicalSpace (Matrix (Fin n) (Fin m) ℝ) := UniformSpace.toTopologicalSpace


-- 证明 F 导数的梯度存在则 G 导数存在，类似于可微的函数具有所有偏导数。
-- 数学上并不困难，形式化中主要流程是写明极限换元的过程，但是过程确实繁琐
theorem gradintToGDeriv {m n : Nat}(f : Matrix (Fin m) (Fin n) ℝ → ℝ) (f' X : Matrix (Fin m) (Fin n) ℝ)
  : HasGradientAt f f' X -> HasGateauxDerivAt f X f' := by
    intro h
    let h1 :=  hasGradientAt_iff_tendsto.mp h
    simp at h1
    -- 用 x' = X + t V 进行换元
    intro V
    by_cases h2 : V = 0
    · simp [h2]
      apply Eq.symm
      have : innerProductofMatrix f' 0 = ⟪f', 0⟫_ℝ := by
        rfl
      rw [this]
      apply inner_zero_right
    have h2' : ‖V‖ ≠ 0 := by
      simp [h2]
    let sub_func (t: ℝ) := X + t • V
    have cf: (Continuous sub_func) := by
      dsimp
      -- 拼凑连续函数的计算法则
      apply@Continuous.add
      · exact continuous_const
        -- 这里很难进行自动参数推导，不知道为什么可能是类型太复杂了
      · let c1 := Continuous.smul (@continuous_id ℝ _) (@continuous_const _ _ _ _ V)
        apply Continuous.congr c1
        intro x
        rfl
    have f0 : sub_func 0 = X := by
      simp
    have : Tendsto sub_func (𝓝[≠] 0) (𝓝 X) := by
      -- 有些恼火的是这里不能直接使用连续性条件，因为滤子变小了
      -- apply Continuous.tendsto'
      apply Tendsto.mono_left (Continuous.tendsto' cf (0: ℝ) X f0)
      show 𝓝[≠] 0 ≤ 𝓝 0
      apply le_def.mpr
      intro x cond_x
      let x1 := Set.diff x {0}
      have : x1 ∈ 𝓝[≠] 0 := by
        simp
        apply diff_mem_nhdsWithin_compl
        exact cond_x
      apply mem_of_superset this
      apply diff_subset x {0}
    simp at this
    let com1 := Tendsto.comp h1 this
    simp [] at com1
    -- 慢慢化简
    have : Tendsto (abs ∘ fun t => ‖V‖⁻¹ * (f (X + t • V) - f X - inner f' (t • V) ) / t) (𝓝[≠] 0) (𝓝 0) := by
      apply (tendsto_congr' _).mp
      · exact com1
      · apply eventuallyEq_nhdsWithin_of_eqOn
        intro t _
        simp
        have : |t|⁻¹ * ‖V‖⁻¹ = ‖t • V‖⁻¹ := by
          rw [norm_smul]
          norm_num
          rw [mul_comm]
        rw [<-this]
        field_simp
        rw [mul_comm, abs_div, abs_mul]
        have : ‖V‖ >= 0 := by
          simp
        rw [abs_of_nonneg this]
    -- 去绝对值
    let h1 := (tendsto_zero_iff_abs_tendsto_zero fun t => ‖V‖⁻¹ * (f (X + t • V) - f X - inner f' (t • V)) / t).mpr this
    -- 乘以常数
    let h2 := Tendsto.mul_const ‖V‖ h1
    simp [] at h2
    -- 继续化简
    have : Tendsto (fun t => (f (X + t • V) - f X ) / t - inner f' V) (𝓝[≠] 0) (𝓝 0) := by
      apply (tendsto_congr' _).mp
      · exact h2
      · apply eventuallyEq_nhdsWithin_of_eqOn
        intro t cond_t
        field_simp []
        rw [div_mul_eq_div_mul_one_div]
        field_simp [div_self h2']
        rw [inner_smul_right, sub_div, mul_comm, <-mul_div, div_self cond_t, mul_one]
    -- 加上常数
    let this' := Tendsto.add_const (inner f' V) this
    simp [] at this'
    exact this'

theorem FDerivToGDeriv {m n : Nat}(f : Matrix (Fin m) (Fin n) ℝ → ℝ) (X : Matrix (Fin m) (Fin n) ℝ) (x : Matrix (Fin m) (Fin n) ℝ)
  : DifferentiableAt ℝ f X -> GateauxDifferentiable f X := by
    intro h
    let h1 := DifferentiableAt.hasGradientAt h
    let h2 := gradintToGDeriv f (gradient f X) X h1
    use gradient f X

lemma proj_diff {n m : ℕ} (i : Fin n) (j : Fin m) (X:  Matrix (Fin n) (Fin m) ℝ): DifferentiableAt ℝ (fun (A : Matrix (Fin n) (Fin m) ℝ) => A i j) X := by
  let proj := fun (A : Matrix (Fin n) (Fin m) ℝ) => A i j
  let base_matrix: Matrix (Fin n) (Fin m) ℝ := fun (k: Fin n) (l: Fin m) => if k = i ∧ l = j then 1 else 0
  have : HasGradientAt proj base_matrix X := by
    apply hasGradientAt_iff_tendsto.mpr
    have : (fun x' => ‖x' - X‖⁻¹ * ‖proj x' - proj X - inner base_matrix (x' - X)‖) = (fun x' => 0) := by
      funext x'
      simp
      apply Or.inr
      have (A: Matrix (Fin n) (Fin m) ℝ) : innerProductofMatrix base_matrix A = proj A := by
        simp []
        dsimp [proj, innerProductofMatrix]
        simp []
        have :
          (∑ x : Fin n, ∑ x_1 : Fin m, if x = i ∧ x_1 = j then A x x_1 else 0) =
          (∑ x : Fin n, if  x = i then A x j else 0) := by
            apply Finset.sum_congr rfl
            intro x
            simp
            by_cases h : x = i
            · simp [h]
            · simp [h]
        rw [this]
        have :∀ b: Fin n , b ≠ i → (fun x => if x = i then A x j else 0) b = 0 := by
          intro b h
          simp [h]
        let h1 := Fintype.sum_eq_single i this
        simp [h1]
      have (A: Matrix (Fin n) (Fin m) ℝ) : inner base_matrix A = proj A := by
        apply this
      rw [this]
      simp
    rw [this]
    apply tendsto_const_nhds
  exact HasGradientAt.differentiableAt this

lemma sum_map {a_2 a_3 : Type _}{n: ℕ} [AddCommMonoid a_3] (f : Fin n → a_2 -> a_3) (s : a_2) :
  ∑x: Fin n, (f x s) = (∑x: Fin n, f x) s := by
    simp

lemma proj_submatrix_diff {n : ℕ} (i : Fin (Nat.succ n)) (j : Fin (Nat.succ m)) (X : Matrix (Fin (Nat.succ n)) (Fin (Nat.succ m)) ℝ)  :
  DifferentiableAt ℝ (fun (A : Matrix (Fin (Nat.succ n)) (Fin (Nat.succ m)) ℝ) => submatrix A (Fin.succAbove i) (Fin.succAbove j)) X := by
    let base_matrix s t: Matrix (Fin n) (Fin m) ℝ := fun (k: Fin n) (l: Fin m) => if k = s ∧ l = t then 1 else 0
    have : (fun A: Matrix (Fin (Nat.succ n)) (Fin (Nat.succ m)) ℝ => submatrix A (Fin.succAbove i) (Fin.succAbove j))
            = fun A => ∑ k : Fin n, ∑ l : Fin m, A (Fin.succAbove i k) (Fin.succAbove j l) • base_matrix k l := by
      funext A
      apply Matrix.ext
      intro s t
      have : (∑ k : Fin n, ∑ l : Fin m, A (Fin.succAbove i k) (Fin.succAbove j l) • base_matrix k l) s t =
               (∑ k : Fin n, ∑ l : Fin m, A (Fin.succAbove i k) (Fin.succAbove j l) * (base_matrix k l s t)) := by
          simp
          rw [<-sum_map]
          rw [<-sum_map]
          apply congr_arg
          funext k
          rw [<-sum_map]
          rw [<-sum_map]
          apply congr_arg
          funext l
          repeat exact 1
          simp
          repeat exact 1
      rw [this]
      simp
      have : ∀ (x: Fin n), x ≠ s -> (∑ x_1 : Fin m, if s = x ∧ t = x_1 then A (Fin.succAbove i x) (Fin.succAbove j x_1) else 0) = 0 := by
        intro x h
        simp [h.symm]
      let h1 := Fintype.sum_eq_single s this
      simp [h1]
    rw [this]
    apply DifferentiableAt.sum
    intro k _
    apply DifferentiableAt.sum
    intro l _
    apply DifferentiableAt.smul
    · apply proj_diff
    · apply differentiableAt_const



--  用归纳法证明行列式可导, 思路是进行行展开并利用可导性的加法/乘法和复合
theorem detDifferentiable  {n : Nat}  (X : Matrix (Fin n) (Fin n) ℝ)  :
  DifferentiableAt ℝ (det : Matrix (Fin n) (Fin n) ℝ → ℝ) X := by
    by_cases h : n = 0
    · have : det  = fun (A: Matrix (Fin n) (Fin n) ℝ) => 1 := by
        funext A
        have : IsEmpty (Fin n) := by
          rw [h]
          exact Fin.isEmpty
        rw [det_isEmpty]
      rw [this]
      simp
    have nz: NeZero (n:ℕ) := by
      apply neZero_iff.mpr
      exact h
    let i: Fin n := Inhabited.default
    have : det  = fun (A: Matrix (Fin n) (Fin n) ℝ)
        => ∑ j : Fin n,  A i j * Matrix.adjugate A j i := by
      funext A
      apply det_eq_sum_mul_adjugate_row
    rw [this]
    have : ∀ (j : Fin n), DifferentiableAt ℝ (fun A => A i j * adjugate A j i) X := by
      intro j
      have :  (fun A => A i j * adjugate A j i) = (fun A => (fun x => x i j) A • (fun x => adjugate x j i) A) := by
        funext A
        simp
        have (a  b:ℝ) : a * b = a • b := by
          rfl
        rw [this]
      rw [this]
      apply DifferentiableAt.smul
      -- 投影可导
      · simp
        apply proj_diff i j
      · simp
        have adjugate_diff : DifferentiableAt ℝ (fun A => adjugate A j i) X := by
          cases n with
          | zero => simp
          | succ n1 =>
                have : (fun (X: Matrix (Fin (Nat.succ n1)) (Fin (Nat.succ n1)) ℝ) =>
                      adjugate X j i) = fun X => ((-1) ^ (i + j: ℕ)) * det (submatrix X (Fin.succAbove i) (Fin.succAbove j)) := by
                  funext X
                  apply adjugate_fin_succ_eq_det_submatrix X j i
                rw [this]
                apply DifferentiableAt.const_mul
                apply DifferentiableAt.comp
                ·
                    let m1 := (submatrix X (Fin.succAbove i) (Fin.succAbove j))
                    have : DifferentiableAt ℝ det m1 := by
                      apply detDifferentiable m1
                    exact this
                · apply proj_submatrix_diff
        apply adjugate_diff
    apply DifferentiableAt.sum
    intro j _
    apply this j
