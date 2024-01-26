import «Tutorial».Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Reflection
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.UniformSpace.Basic
open GateauxDeriv Topology Filter Set InnerProductOfMatrix Matrix
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
      -- 有些恼火的是这里不能直接使用连续性条件，因为滤子变小了，我们手动缩小滤子
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
-- F 导数存在则 G 导数存在
theorem FDerivToGDeriv {m n : Nat}(f : Matrix (Fin m) (Fin n) ℝ → ℝ) (X : Matrix (Fin m) (Fin n) ℝ)
  : DifferentiableAt ℝ f X -> GateauxDifferentiable f X := by
    intro h
    let h1 := DifferentiableAt.hasGradientAt h
    let h2 := gradintToGDeriv f (gradient f X) X h1
    use gradient f X
