import «Tutorial».Basic
import «Tutorial».gradintToGDeriv
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate

-- import Mathlib.Order.Lattice

open Matrix GateauxDeriv Topology
open InnerProductOfMatrix
open BigOperators

noncomputable
def f_lndet : Matrix (Fin n) (Fin n) ℝ → ℝ :=
  fun X => Real.log X.det


lemma finn_nonempty {n : Nat} (hn : n ≥ 1): (@Finset.univ (Fin n) (Fin.fintype n)).Nonempty := by
  have x : Fin n := ⟨0, by linarith⟩
  unfold Finset.Nonempty
  exact ⟨x, by simp⟩

---------------- second try ----------------


#check Matrix.det_updateRow_add
#check Matrix.updateRow
#check Matrix.row
#check Matrix.row_apply -- row n → α  to  Matrix Unit n α
#check Matrix.det_eq_sum_mul_adjugate_row
#check Matrix.adjugate
#check Matrix.inv_def

-- #check (A.det⁻¹ * ((Matrix.adjugate A) i j)

-- 矩阵的基 M i' j' = δᵢᵢ' δⱼⱼ'
def Matrix_base {n m : Nat} (i : Fin n) (j : Fin m) : Matrix (Fin n) (Fin m) ℝ := of fun x y => if x = i ∧ y = j then 1 else 0

#check Fintype.sum_eq_single

-- 矩阵 X 和 Matrix_base i j 的内积为 X i j （证明这是个投影）
-- 这里比较烦的地方是 ∑ i : Fin n, if ... then ... else ...，幸好有个 Fintype.sum_eq_single 可以用
lemma inner_product_with_matrix_base {n m : Nat} (X : Matrix (Fin n) (Fin m) ℝ) (i : Fin n) (j : Fin m) :
    innerProductofMatrix X (Matrix_base i j) = X i j := by
  unfold innerProductofMatrix
  unfold Matrix_base
  simp
  have hnotj (x: Fin n) : ∀ x' ≠ j, (if x = i ∧ x' = j then X x x' else 0) = 0 := by
    intro x' hx'; simp at hx'
    have : (x' = j) = False := by simp; intro hxi; absurd hx' hxi; exact not_false
    simp [this]
  have lem_1 (x: Fin n) := Fintype.sum_eq_single j (hnotj x)
  simp at lem_1
  have :(∑ x : Fin n, ∑ x_1 : Fin m, if x = i ∧ x_1 = j then X x x_1 else 0) =
      (∑ x : Fin n, if x = i then X x j else 0) := by
    apply Finset.sum_congr
    · rfl
    simp [lem_1]
  rw [this]
  have hnoti : ∀ x ≠ i, (if x = i then X x j else 0) = 0 := by
    intro x hx; simp at hx
    have : (x = i) = False := by simp; intro hxi; absurd hx hxi; exact not_false
    simp [this]
  have lem_2 := Fintype.sum_eq_single i hnoti
  rw [lem_2]; simp

-- 证明 log (1 + t * R) / t 的极限为 R，具体证明过程见 ln_delta_epsilon (basic 里)
theorem ln_tends_to (R : ℝ): Filter.Tendsto (fun t => Real.log (1 + t * R) / t) (𝓝[≠] 0) (𝓝 R) := by
  simp [Metric.tendsto_nhdsWithin_nhds]
  exact ln_delta_epsilon R

-- 证明极限的唯一性
theorem tendsto_uniqueness {f : ℝ → ℝ} {y z : ℝ} (h₁ : Filter.Tendsto f (𝓝[≠] 0) (𝓝 y))
    (h₂ : Filter.Tendsto f (𝓝[≠] 0) (𝓝 z)) : y = z := by
  have : (y = z) = (¬ ¬ (y = z)) := by simp
  rw [this]
  intro hyz
  simp [Metric.tendsto_nhdsWithin_nhds] at h₁
  simp [Metric.tendsto_nhdsWithin_nhds] at h₂
  let ε := 1/2 * |y - z|
  have hε : ε > 0 := by
    simp [ε]
    intro h1
    apply sub_eq_zero.mp at h1 -- 圆括号要加上引用的具体变量 箭头的定理用apply
    exact absurd h1 hyz
  specialize h₁ ε hε
  specialize h₂ ε hε
  let ⟨ δ₁, hδ₁, h₁⟩ := h₁
  let ⟨ δ₂, hδ₂, h₂⟩ := h₂
  let δ := min δ₁ δ₂
  have hδ : δ > 0 := by
    simp
    exact ⟨hδ₁, hδ₂⟩
  simp [dist] at h₁ h₂
  have h3 : ∀ x : ℝ, x ≠ 0 → |x| < δ → |f x - y| < 2⁻¹ * |y - z| := by
    intro x hx hxδ
    have h_my : |x| < δ₁ :=by
      simp at hxδ
      exact hxδ.1
    simp at hx
    exact h₁ hx h_my
  have h4 : ∀ x : ℝ, x ≠ 0 → |x| < δ → |f x - z| < 2⁻¹ * |y - z| := by
    intro x hx hxδ
    have h_my : |x| < δ₂ :=by
      simp at hxδ
      exact hxδ.2
    exact h₂ hx h_my
  have h5 : ∀ x : ℝ, x ≠ 0 → |x| < δ → |y - z| < |y - z| := by
    intro x hx hxδ
    specialize h3 x hx hxδ
    specialize h4 x hx hxδ
    have hh: |y - z| = |f x - z - (f x - y)| := by
      simp
    nth_rewrite 1 [hh]
    calc
      |f x - z - (f x - y)| ≤ |f x - z| + |f x - y| := by
        exact abs_sub (f x - z) (f x - y)
      _ < 2⁻¹ * |y - z| + |f x - y| := by
        linarith
      _ ≤ 2⁻¹ * |y - z| + 2⁻¹ * |y - z| := by
        linarith [abs_nonneg (f x - y)]
      _ = |y - z| := by
        simp [← mul_two, mul_comm 2⁻¹ |y - z|]
  specialize h5 (δ/2) (by linarith)
  have hmy: |δ / 2| = δ / 2 := by
    simp only [abs_eq_self]
    linarith [hδ]
  have hmm: δ / 2 < δ := by
    linarith [hδ]
  have := h5 (by linarith [hmy, hmm])
  linarith [this]

-- 对一个矩阵的第 j 列改两次，那么第一次对修改会被覆盖，所以等价于只改最后一次
theorem updateColumn_twice {n m: Nat} (X : Matrix (Fin n) (Fin m) ℝ) (j : Fin m) (f₁ f₂ : Fin n → ℝ) :
    updateColumn (updateColumn X j f₁) j f₂ = updateColumn X j f₂ := by
  apply Matrix.ext
  intro i' j'
  simp [Matrix.updateColumn_apply]
  rcases (eq_or_ne j j') with (hl | hr)
  · simp [hl]
  · have hh' : (j' = j) = False := by
      simp; intro hii'; absurd hr (symm hii'); exact not_false
    simp [hh']

-- 把矩阵的第 i 行改成“除了第 j 列以外全 0”，证明它的行列式可以展开为那个非零位置的代数余子式
-- 本来以为这个证明很头疼，库里找不到函数。这里直接对 updateRow 还有 cramer 还有 cramerMap 展开，没想到 simp 以后化简得特别简单
theorem det_of_update_row {n : Nat} (X : Matrix (Fin n) (Fin n) ℝ) (i j: Fin n) {t : ℝ}:
    det (updateRow X i fun j' => if j' = j then t else 0) = t * (X.adjugate j i) := by
  let X' := updateRow X i fun j' => if j' = j then t else 0
  rw [Matrix.det_eq_sum_mul_adjugate_row X' i]
  simp
  left
  unfold adjugate
  unfold cramer
  simp
  unfold cramerMap
  simp
  simp [← Matrix.updateColumn_transpose]
  simp [updateColumn_twice]


#check updateRow_self
-- 证明 (ln det (X + t Matrix_base i j) - ln det X) / t 在 δ 范围内就等于 log (1 + t * (X.adjugate j i / det X))
-- 一步步慢慢证
lemma calculate_f_lndet_t_delta {n : Nat} (X : Matrix (Fin n) (Fin n) ℝ) (i j: Fin n) (hX : X.det > 0):
    ∃ δ > 0, ∀ t ≠ 0, |t| < δ → (f_lndet (X + t • Matrix_base i j) - f_lndet X) / t
      = Real.log (1 + t * (X.adjugate j i / det X)) / t := by
  -- 直接构造一个 δ，该范围内的 t 可以保证 ln 括号内 > 0
  let δ := det X / (|adjugate X j i| + 1)
  have h_pos_abs_add_one : 0 < |adjugate X j i| + 1 := by linarith [abs_nonneg (adjugate X j i)]
  have hδ_nonneg : δ > 0 := by apply div_pos; linarith; linarith;
  use δ
  constructor
  · exact hδ_nonneg
  intro t ht_nezero htleδ
  -- 准备工作，把 X + t • Matrix_base i j 表达为 updateRow X i (X i + t • tmulirow)
  -- 这样就可以引用行列式对行作展开的性质了 （利用了 mathlib 中的 det_updateRow_add）
  let tmulirow := (fun j' => if j' = j then t else 0)
  have hhx : X = updateRow X i (X i) := by simp
  have h1 : X + t • Matrix_base i j = updateRow X i ((X i) + tmulirow) := by
    apply Matrix.ext
    intro i' j'
    simp [Matrix.updateRow_apply, Matrix_base]
    rcases (eq_or_ne i i') with (hl | hr)
    · simp [hl]
    · have hh' : (i' = i) = False := by
        simp; intro hii'; absurd hr (symm hii'); exact not_false
      simp [hh']
  rw [h1]
  unfold f_lndet
  -- 这里把行列式按行展开了，得到了等号左边 (Real.log (det X + t * adjugate X j i) - Real.log (det X)) / t
  -- 转换为了一个只涉及实数的命题
  simp [det_updateRow_add, det_of_update_row]
  -- 准备工作，得到一系列不等于 0 的条件为了后续的化简
  have hx1 : det X ≠ 0 := by linarith
  have hx2 : det X + t * adjugate X j i ≠ 0 := by
    rcases eq_or_ne (adjugate X j i) 0 with (heq | hne)
    · simp [heq]; linarith
    · simp at htleδ
      have hx3 := (lt_div_iff h_pos_abs_add_one).mp htleδ
      have hx4 : det X + t * adjugate X j i > 0 := by
        calc
          det X + t * adjugate X j i
            ≥ det X - |t * adjugate X j i|    := by linarith [neg_abs_le (t * adjugate X j i)]
          _ = det X - |t| * |adjugate X j i|  := by simp [abs_mul]
          _ > |t| := by simp [mul_add] at hx3; linarith [hx3]
          _ ≥ 0 := by simp [abs_nonneg]
      linarith [hx4]
  -- 化简 log(a/b) = log(a) - log(b), 利用了 a ≠ 0, b ≠ 0
  rw [← Real.log_div hx2 hx1]
  simp [add_div, hX, hx1, mul_div]


-- 证明矩阵元素的投影是可微的，看起来是废话但是实际上有点麻烦，主要涉及各种求和操作问题
lemma proj_diff {n m : ℕ} (i : Fin n) (j : Fin m) (X:  Matrix (Fin n) (Fin m) ℝ): DifferentiableAt ℝ (fun (A : Matrix (Fin n) (Fin m) ℝ) => A i j) X := by
  let proj := fun (A : Matrix (Fin n) (Fin m) ℝ) => A i j
  let base_matrix := Matrix_base i j
  have : HasGradientAt proj base_matrix X := by
    apply hasGradientAt_iff_tendsto.mpr
    have : (fun x' => ‖x' - X‖⁻¹ * ‖proj x' - proj X - inner base_matrix (x' - X)‖) = (fun x' => 0) := by
      funext x'
      simp
      apply Or.inr
      -- 由于沟通不畅两个人各自证明了一遍......
      --have (A: Matrix (Fin n) (Fin m) ℝ) : innerProductofMatrix base_matrix A = proj A := by
      --  simp []
      --  dsimp [proj, innerProductofMatrix, Matrix_base]
      --  simp []
      --  have :
      --    (∑ x : Fin n, ∑ x_1 : Fin m, if x = i ∧ x_1 = j then A x x_1 else 0) =
      --    (∑ x : Fin n, if  x = i then A x j else 0) := by
      --      apply Finset.sum_congr rfl
      --      intro x
      --      simp
      --      by_cases h : x = i
      --      · simp [h]
      --      · simp [h]
      --  rw [this]
      --  have :∀ b: Fin n , b ≠ i → (fun x => if x = i then A x j else 0) b = 0 := by
      --    intro b h
      --    simp [h]
      --  let h1 := Fintype.sum_eq_single i this
      --  simp [h1]
      have (A: Matrix (Fin n) (Fin m) ℝ) : inner base_matrix A = proj A := by
        simp
        rw [real_inner_comm]
        have : innerProductofMatrix A (Matrix_base i j) = inner A (Matrix_base i j) := by
          rfl
        rw [<-this]
        apply inner_product_with_matrix_base A i j
      rw [this]
      simp
    rw [this]
    apply tendsto_const_nhds
  exact HasGradientAt.differentiableAt this

-- 发现又遇到了函数应用放进求和符号里的问题，这里写了一个通用的引理
lemma sum_map {a_2 a_3 : Type _}{n: ℕ} [AddCommMonoid a_3] (f : Fin n → a_2 -> a_3) (s : a_2) :
  ∑x: Fin n, (f x s) = (∑x: Fin n, f x) s := by
    simp

-- 类似的，证明取子矩阵是可微的，事实上它就是多个元素投影乘以对应基本矩阵的和，当然是可微的
lemma proj_submatrix_diff {n : ℕ} (i : Fin (Nat.succ n)) (j : Fin (Nat.succ m)) (X : Matrix (Fin (Nat.succ n)) (Fin (Nat.succ m)) ℝ)  :
  DifferentiableAt ℝ (fun (A : Matrix (Fin (Nat.succ n)) (Fin (Nat.succ m)) ℝ) => submatrix A (Fin.succAbove i) (Fin.succAbove j)) X := by
    let base_matrix s t: Matrix (Fin n) (Fin m) ℝ := fun (k: Fin n) (l: Fin m) => if k = s ∧ l = t then 1 else 0
    have : (fun A: Matrix (Fin (Nat.succ n)) (Fin (Nat.succ m)) ℝ => submatrix A (Fin.succAbove i) (Fin.succAbove j))
            = fun A => ∑ k : Fin n, ∑ l : Fin m, A (Fin.succAbove i k) (Fin.succAbove j l) • base_matrix k l := by
      funext A
      apply Matrix.ext
      intro s t
      --  把两次函数应用放进求和符号，不知道有没有更好的方法
      have : (∑ k : Fin n, ∑ l : Fin m, A (Fin.succAbove i k) (Fin.succAbove j l) • base_matrix k l) s t =
               (∑ k : Fin n, ∑ l : Fin m, A (Fin.succAbove i k) (Fin.succAbove j l) * (base_matrix k l s t)) := by
          simp
          repeat rw [<-sum_map]
          apply congr_arg
          funext k
          repeat rw [<-sum_map]
          apply congr_arg
          funext l
          simp
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
    -- n = 0 的情形使用默认值处理
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
    -- 一般情形随便取一个 i 行进行展开
    let i: Fin n := Inhabited.default
    have : det  = fun (A: Matrix (Fin n) (Fin n) ℝ)
        => ∑ j : Fin n,  A i j * Matrix.adjugate A j i := by
      funext A
      apply det_eq_sum_mul_adjugate_row
    rw [this]
    -- 证明展开式每一项可导
    have : ∀ (j : Fin n), DifferentiableAt ℝ (fun A => A i j * adjugate A j i) X := by
      intro j
      have :  (fun A => A i j * adjugate A j i) = (fun A => (fun x => x i j) A • (fun x => adjugate x j i) A) := by
        funext A
        have (a  b:ℝ) : a * b = a • b := by
          rfl
        simp [this]
        rw [this]
      rw [this]
      apply DifferentiableAt.smul
      -- 投影到 i j 元素可导
      · simp
        apply proj_diff i j
      · simp
        have adjugate_diff : DifferentiableAt ℝ (fun A => adjugate A j i) X := by
          -- 这里我们需要使用归纳法了，因此设 n = succ n1
          cases n with
          | zero => simp
          | succ n1 =>
                have : (fun (X: Matrix (Fin (Nat.succ n1)) (Fin (Nat.succ n1)) ℝ) =>
                      adjugate X j i) = fun X => ((-1) ^ (i + j: ℕ)) * det (submatrix X (Fin.succAbove i) (Fin.succAbove j)) := by
                  funext X
                  apply adjugate_fin_succ_eq_det_submatrix X j i
                rw [this]
                apply DifferentiableAt.const_mul
                -- 将代数余子式拆穿拆成行列式函数和投影到子矩阵函数的复合
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

-- 利用 F 导数的复合证明 ln (det (A)) 是 F 可导函数，进而 G 可导
theorem differentiableOfLnDet {n: Nat} (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.det > 0) :  GateauxDifferentiable f_lndet X := by
  apply FDerivToGDeriv
  apply DifferentiableAt.comp
  · simp []
    linarith
  · exact detDifferentiable X

-- 在已知可微的情况下，证明 ln det X 的导数是 (X⁻¹)ᵀ
theorem pro_c {n : Nat} (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.det > 0)
    (h : GateauxDifferentiable f_lndet X) :
      GateauxDeriv f_lndet X h = (X⁻¹)ᵀ := by
  -- 先假设已经有这个导数
  unfold GateauxDifferentiable at h
  have hh := GateauxDeriv_spec f_lndet X h -- 那么这个导数具有性质 hh
  unfold HasGateauxDerivAt at hh
  -- 考虑第 i 行第 j 列的元素，取 Matrix_base i j，就可以得到 f' i j 的结果
  apply Matrix.ext
  intro i j
  specialize hh (Matrix_base i j)
  rw [inner_product_with_matrix_base] at hh
  -- 证明 hh 中的函数与 Real.log (1 + t * (adjugate X j i / det X)) / t 在小邻域内相等，
  -- 因此他们有相同的极限，hh 可以转换为求 log (1+tR)/t 函数的极限
  have ⟨δt, hδt, hhh⟩  := calculate_f_lndet_t_delta X i j hX
  have : (fun t => (f_lndet (X + t • Matrix_base i j) - f_lndet X) / t)
      =ᶠ[𝓝[≠] 0] (fun t => Real.log (1 + t * (X.adjugate j i/X.det) ) / t ) := by
    apply eventuallyEq_nhdsWithin_iff.mpr
    apply Metric.eventually_nhds_iff_ball.mpr
    simp
    use δt
    constructor
    · exact hδt
    intro x1 x3 x2; exact (hhh x1 x2 x3)
  -- 利用 hh 中的函数与 Log 函数在领域内相同的性质
  -- 证明 hl : log 函数的极限为 f' i j
  have hl := (Filter.tendsto_congr' this).mp hh
  -- 证明 hr : log (1+tR)/t 函数的极限为 R
  have hr := ln_tends_to (X.adjugate j i / X.det)
  -- 极限的唯一性，得到 f' i j = R = X.adjugate j i / X.det
  have h := tendsto_uniqueness hl hr
  rw [h, ← inv_mul_eq_div]
  -- 剩下的就是基本的化简
  simp [Matrix.inv_def]
  have h1 : ((det X)⁻¹ • adjugate X) j i = (det X)⁻¹ * adjugate X j i := by
    simp [Matrix.ext_iff.mpr (Matrix.smul_of (det X)⁻¹ (adjugate X))]
  exact symm h1

-- problem c 的 final 版本！
-- differentiableOfLnDet 证明了 ln det X 的可导
theorem pro_c_final {n : Nat} (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.det > 0):
    GateauxDeriv f_lndet X (differentiableOfLnDet X hX) = (X⁻¹)ᵀ := pro_c X hX (differentiableOfLnDet X hX)

---------------- first try ----------------

#check Fin.fintype 2


lemma left_right_distrib_orthogonal {n : Nat} {x : ℝ} {Q R : Matrix (Fin n) (Fin n) ℝ} (h : Orthogonal_Matrix Q) :
  1 + x • (Qᵀ * R * Q) = Qᵀ * (1 + x • R) * Q := by
    rw [Matrix.mul_add, Matrix.add_mul]
    simp
    rw [Orthogonal_Matrix] at h
    exact symm h

lemma log_delta_epsilon_of_Finset {n : Nat} (hn : 1 ≤ n) (R : Matrix (Fin n) (Fin n) ℝ) :
    ∀ ε > 0, ∃ δ > 0, ∀ x ≠ 0, |x| < δ → ∀ i : Fin n, |Real.log (1 + x * R i i) / x - R i i| < ε / n := by --不可逃避的问题
  intro ε hε
  have hεdivn : ε / n > 0 := by
    apply div_pos
    · linarith
    simp; linarith
  let f := (fun i : Fin n => Exists.choose (ln_delta_epsilon (R i i) (ε / n) hεdivn))
  let f_spec := (fun i : Fin n => Exists.choose_spec (ln_delta_epsilon (R i i) (ε / n) hεdivn))
  let image_δ₃ := Finset.image f Finset.univ
  have h_image_δ₃_nonempty : image_δ₃.Nonempty := by exact Finset.image_nonempty.mpr (finn_nonempty hn)
  let δ₃  := Finset.min' image_δ₃ h_image_δ₃_nonempty
  use δ₃
  constructor
  · simp [Finset.lt_min'_iff]
    intro i
    exact (f_spec i).1
  intro y hny hy i
  simp [Finset.lt_min'_iff] at hy
  exact (f_spec i).2 y hny (hy i)

theorem problem_c {n : Nat} (X : Matrix (Fin n) (Fin n) ℝ) (hn : 1 ≤ n) (h : X.det > 0):
  HasGateauxDerivAt (f_lndet) X (X⁻¹)ᵀ := by
    simp [HasGateauxDerivAt]
    simp [f_lndet]
    intro V
    let ⟨Q, R, h3a, h3b, h3c⟩  := schur_decomposition n (X⁻¹ * V)
    have h_isunitdet : IsUnit X.det := by
      simp [IsUnit]
      linarith [h]
    have h (t : ℝ) : X + t • V = X * ( 1 + t • X⁻¹ * V) := by
      simp [Matrix.mul_add]
      simp [← Matrix.mul_assoc]
      rw [mul_nonsing_inv]
      simp [Matrix.one_mul]
      assumption
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε
    intro ε₁
    -- ∀  ε > 0, ∃ 0 < δ < f(ε), ....
    -- need to construct f(ε)
    let ⟨δ₁, hδ₁, hx₁_det_nonzero⟩  := det_notzero (X⁻¹ * V)
    let ⟨δ₂, hδ₂, hx₂_det_nonzero⟩  := det_notzero R
    let ⟨δ₃, hδ₃, hx₃_log_delta_epsilon⟩ := (log_delta_epsilon_of_Finset hn R) ε ε₁
    let δ := min (min δ₁ δ₂) δ₃
    use δ
    constructor
    · simp
      exact ⟨⟨hδ₁, hδ₂⟩, hδ₃⟩
    intro x x_nonneg x_range
    simp at x_range
    simp [h]
    have none_zero_1 : det ( X ) ≠  0 := by
      linarith [h]
    have none_zero_2 : det (1 + x • (X⁻¹ * V) ) ≠ 0 := by -- 用 basic 中引入的新theorem来证明
      apply hx₁_det_nonzero
      exact x_range.1.1
    simp [Real.log_mul, none_zero_1, none_zero_2]
    rw [h3c]
    have h4 : 1 = Qᵀ * Q := by
      dsimp [Orthogonal_Matrix] at h3a
      exact symm h3a
    simp [left_right_distrib_orthogonal, h3a]
    have : 1 = Q.det * Q.det := by
      have hh := congrArg Matrix.det h4 -- 将此性质引入到“假设”中
      simp at hh
      assumption
    simp only [mul_comm]
    simp only [← mul_assoc]
    simp [← this]
    have h8 (x : ℝ) : is_upper_triangle (1 + x • R) := by
      apply is_upper_triangle.add
      apply is_upper_triangle.one
      apply is_upper_triangle.smul
      exact h3b
    simp only [upper_triangle_det, h8]
    have h9 (i : Fin n): (1 + x • R) i i ≠ 0 := by  -- 用 basic 中引入的新theorem来证明
      specialize hx₂_det_nonzero x
      exact (upper_nonezero (1 + x • R)) (h8 x) (hx₂_det_nonzero x_range.1.2) i
    simp only [dist]
    rw [Real.log_prod]
    have inv_1: Q * Qᵀ  = 1 :=by
      rw [Orthogonal_inv]
      assumption
    have ha1: trace (R) = innerProductofMatrix (X⁻¹)ᵀ V  := by
      calc
        trace (R) = trace (R * Q * Qᵀ ) :=by
          rw [Matrix.mul_assoc]
          rw [inv_1]
          simp [Matrix.mul_one]
        _ = trace (Qᵀ * R * Q) :=by
          rw [Matrix.trace_mul_cycle]
        _ = trace (X⁻¹ * V) :=by
          simp [h3c]
        _ = trace ( ((X⁻¹)ᵀ)ᵀ  * V) :=by
          simp [Matrix.transpose_transpose]
        _ = innerProductofMatrix (X⁻¹)ᵀ V := by
          simp only [traceMHDotM, iProd_eq_traceDot]
          simp
    rw [← ha1]
    have e1: trace (R) = Finset.sum Finset.univ fun i => R i i := by
      rw [trace]
      simp
    rw [e1]
    rw [Finset.sum_div]
    rw [← Finset.sum_sub_distrib]
    have h2 : ∀ i : Fin n, |Real.log (1 + x * R i i) / x - R i i| < ε / n := by
      exact hx₃_log_delta_epsilon x x_nonneg x_range.2
    have not_equal : n ≠ 0 := by
      linarith
    have h3 : ∑ __ : Fin n, ε / n = ε := by
      rw [← Finset.sum_div]
      simp
      rw [← div_mul_eq_mul_div]
      simp [div_self, hn, not_equal]
    calc
      |Finset.sum Finset.univ fun x_1 => Real.log ((1 + x • R) x_1 x_1) / x - R x_1 x_1|
            ≤ Finset.sum Finset.univ fun x_1 => |Real.log ((1 + x • R) x_1 x_1) / x - R x_1 x_1| := by
        apply Finset.abs_sum_le_sum_abs
      _     < ε := by
        rw [← h3]
        apply Finset.sum_lt_sum_of_nonempty
        · exact finn_nonempty hn
        simp
        assumption
    simp at h9
    simp
    assumption
