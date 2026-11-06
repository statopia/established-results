import Statlib.RandomMatrix.SampleCovariance.LeaveOneOut.OffdiagMomentBound
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_2d09ea10ba632270c6b5
import ProverJobs.ResidualE2ESupport20261106.M_f1b888dc13f117631a68
import ProverJobs.ResidualE2ESupport20261106.M_f4f836c4a38678459f2a
import ProverJobs.ResidualE2ESupport20261106.M_8b044b331a046ecc2ee8
import ProverJobs.ResidualE2ESupport20261106.M_edbc2c9a6c271a4989c1
import ProverJobs.ResidualE2ESupport20261106.ExternalNodes.Node_4e757cd702eee1ecc4cb

namespace PaperProofTasks.ResidualE2ESupport20261106



open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported
universe u

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_2072908945_35593386 : ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
        (p Kt : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1) (hKt : 0 < Kt)
        (Xi Mask : Ω → Matrix (Fin m) (Fin n) ℝ)
        (hXi_meas : ∀ i j, Measurable fun ω => Xi ω i j)
        (hXi_int : ∀ i j, Integrable (fun ω => Xi ω i j) μ)
        (hXi_sq_int : ∀ i j, Integrable (fun ω => (Xi ω i j) ^ 2) μ)
        (hXi_indep : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Xi ω ij.1 ij.2) μ)
        (hXi_mean : ∀ i j, ∫ ω, Xi ω i j ∂μ = 0)
        (hXi_var : ∀ i j, ∫ ω, (Xi ω i j) ^ 2 ∂μ = 1)
        (hXi_tail : ∀ i j (t : ℝ), 0 < t →
          μ {ω | t < |Xi ω i j|} ≤ ENNReal.ofReal (2 * Real.exp (-t / Kt)))
        (hMask_meas : ∀ i j, Measurable fun ω => Mask ω i j)
        (hMask_val : ∀ i j ω, Mask ω i j = 0 ∨ Mask ω i j = 1)
        (hMask_law : ∀ i j, μ {ω | Mask ω i j = 1} = ENNReal.ofReal p)
        (hMask_indep : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Mask ω ij.1 ij.2) μ)
        (hIndep : IndepFun (fun ω (ij : Fin m × Fin n) => Xi ω ij.1 ij.2)
          (fun ω (ij : Fin m × Fin n) => Mask ω ij.1 ij.2) μ),
      ∀ (z : ℂ), 0 < z.im →
        ‖(∫ ω, ((((m : ℝ) + (n : ℝ))⁻¹ : ℂ) *
              (((z • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) -
                (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
                  (maskedScaled p (Xi ω) (Mask ω))
                  (Matrix.transpose (maskedScaled p (Xi ω) (Mask ω)))
                  (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)⁻¹).trace) ∂μ)
          - ∫ g, ((((m : ℝ) + (n : ℝ))⁻¹ : ℂ) *
              (((z • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) -
                (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
                  (Matrix.of fun i j => g i j / Real.sqrt (m : ℝ))
                  (Matrix.transpose (Matrix.of fun i j => g i j / Real.sqrt (m : ℝ)))
                  (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)⁻¹).trace)
              ∂(stdNormalMatrixMeasure m n)‖
        ≤ C * Kt ^ 3 * Real.rpow ((m : ℝ) * p) (-(1 / 2 : ℝ)) * ((z.im) ^ 4)⁻¹ := by
  /- @proof-region region.target-node.session.c2c94ffba0fe6daa begin -/
  obtain ⟨C₀, hC₀pos, hC₀⟩ := ext_model_1.{u}
  refine ⟨48 * C₀, by positivity, ?_⟩
  intro Ω instΩ μ instμ m n hm hn p Kt hp_pos hp_le hKt Xi Mask hXi_meas hXi_int hXi_sq_int
    hXi_indep hXi_mean hXi_var hXi_tail hMask_meas hMask_val hMask_law hMask_indep hIndep z hz
  have hthird := statopia_math_node_1142199188_2b6c5b39 μ m n hm hn p Kt hp_pos hp_le hKt Xi Mask
    hXi_meas hXi_int hXi_sq_int hXi_mean hXi_var hXi_tail hMask_meas hMask_val hMask_law hIndep
  obtain ⟨hIntThird, hbudget⟩ := hthird
  have hMeasXi' : ∀ i j, Measurable fun x : Ω × (Fin m → Fin n → ℝ) => Xi x.1 i j :=
    fun i j => (hXi_meas i j).comp measurable_fst
  have hMeasMask' : ∀ i j, Measurable fun x : Ω × (Fin m → Fin n → ℝ) => Mask x.1 i j :=
    fun i j => (hMask_meas i j).comp measurable_fst
  haveI hνprob : IsProbabilityMeasure (stdNormalMatrixMeasure m n) :=
    ⟨by rw [stdNormalMatrixMeasure]; simp⟩
  have hIntThird' : ∀ i j, Integrable (fun x : Ω × (Fin m → Fin n → ℝ) =>
      |maskedScaled p (Xi x.1) (Mask x.1) i j| ^ 3)
      (μ.prod (stdNormalMatrixMeasure m n)) := by
    intro i j
    have hmp : 0 < Real.sqrt ((m : ℝ) * p) := by
      apply Real.sqrt_pos.mpr
      have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      positivity
    have hbase : Integrable (fun x : Ω × (Fin m → Fin n → ℝ) => |Xi x.1 i j| ^ 3)
        (μ.prod (stdNormalMatrixMeasure m n)) :=
      (hIntThird i j).1.comp_fst _
    have hc : Integrable (fun x : Ω × (Fin m → Fin n → ℝ) =>
        (Real.sqrt ((m : ℝ) * p))⁻¹ ^ 3 * |Xi x.1 i j| ^ 3)
        (μ.prod (stdNormalMatrixMeasure m n)) := hbase.const_mul _
    refine hc.mono' ?_ ?_
    · have hm1 : Measurable fun x : Ω × (Fin m → Fin n → ℝ) =>
          maskedScaled p (Xi x.1) (Mask x.1) i j := by
        show Measurable fun x : Ω × (Fin m → Fin n → ℝ) =>
          Mask x.1 i j * Xi x.1 i j / Real.sqrt ((m : ℝ) * p)
        exact ((hMeasMask' i j).mul (hMeasXi' i j)).div_const _
      exact ((hm1.abs).pow_const 3).aestronglyMeasurable
    · filter_upwards with x
      have hM : |Mask x.1 i j| ≤ 1 := by
        rcases hMask_val i j x.1 with h | h <;> simp [h]
      have hb : |Mask x.1 i j| ^ 3 ≤ 1 := pow_le_one₀ (abs_nonneg _) hM
      calc ‖|maskedScaled p (Xi x.1) (Mask x.1) i j| ^ 3‖
          = |maskedScaled p (Xi x.1) (Mask x.1) i j| ^ 3 := by
            rw [Real.norm_of_nonneg (by positivity)]
        _ = |Mask x.1 i j| ^ 3 * |Xi x.1 i j| ^ 3 /
              (Real.sqrt ((m : ℝ) * p)) ^ 3 := by
            simp only [maskedScaled, abs_div, abs_mul, abs_of_nonneg (le_of_lt hmp),
              div_pow, mul_pow]
        _ ≤ 1 * |Xi x.1 i j| ^ 3 / (Real.sqrt ((m : ℝ) * p)) ^ 3 := by
            gcongr
        _ = (Real.sqrt ((m : ℝ) * p))⁻¹ ^ 3 * |Xi x.1 i j| ^ 3 := by
            rw [one_mul, div_eq_inv_mul, ← inv_pow, mul_comm]
  have hIntEq : ∀ i j, ∫ x : Ω × (Fin m → Fin n → ℝ),
      |maskedScaled p (Xi x.1) (Mask x.1) i j| ^ 3
        ∂(μ.prod (stdNormalMatrixMeasure m n))
      = ∫ ω, |maskedScaled p (Xi ω) (Mask ω) i j| ^ 3 ∂μ := by
    intro i j
    refine (MeasureTheory.integral_prod
      (fun x : Ω × (Fin m → Fin n → ℝ) =>
        |maskedScaled p (Xi x.1) (Mask x.1) i j| ^ 3) (hIntThird' i j)).trans ?_
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show (∫ y : Fin m → Fin n → ℝ,
        |maskedScaled p (Xi ω) (Mask ω) i j| ^ 3 ∂(stdNormalMatrixMeasure m n))
      = |maskedScaled p (Xi ω) (Mask ω) i j| ^ 3
    rw [MeasureTheory.integral_const]
    simp
  have hbudget' : (∑ i : Fin m, ∑ j : Fin n,
      ∫ x : Ω × (Fin m → Fin n → ℝ), |maskedScaled p (Xi x.1) (Mask x.1) i j| ^ 3
        ∂(μ.prod (stdNormalMatrixMeasure m n)))
      ≤ ((m : ℝ) + (n : ℝ)) * (24 * Kt ^ 3 * (Real.sqrt ((m : ℝ) * p))⁻¹) := by
    simpa only [hIntEq] using hbudget
  have hIntThirdμ : ∀ i j, Integrable (fun ω => |maskedScaled p (Xi ω) (Mask ω) i j| ^ 3) μ := by
    intro i j
    have hmp : 0 < Real.sqrt ((m : ℝ) * p) := by
      apply Real.sqrt_pos.mpr
      have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      positivity
    have hc : Integrable (fun ω => (Real.sqrt ((m : ℝ) * p))⁻¹ ^ 3 * |Xi ω i j| ^ 3) μ :=
      (hIntThird i j).1.const_mul _
    refine hc.mono' ?_ ?_
    · have hm1 : Measurable fun ω => maskedScaled p (Xi ω) (Mask ω) i j := by
        show Measurable fun ω => Mask ω i j * Xi ω i j / Real.sqrt ((m : ℝ) * p)
        exact ((hMask_meas i j).mul (hXi_meas i j)).div_const _
      exact ((hm1.abs).pow_const 3).aestronglyMeasurable
    · filter_upwards with ω
      have hM : |Mask ω i j| ≤ 1 := by
        rcases hMask_val i j ω with h | h <;> simp [h]
      have hb : |Mask ω i j| ^ 3 ≤ 1 := pow_le_one₀ (abs_nonneg _) hM
      calc ‖|maskedScaled p (Xi ω) (Mask ω) i j| ^ 3‖
          = |maskedScaled p (Xi ω) (Mask ω) i j| ^ 3 := by
            rw [Real.norm_of_nonneg (by positivity)]
        _ = |Mask ω i j| ^ 3 * |Xi ω i j| ^ 3 / (Real.sqrt ((m : ℝ) * p)) ^ 3 := by
            simp only [maskedScaled, abs_div, abs_mul, abs_of_nonneg (le_of_lt hmp),
              div_pow, mul_pow]
        _ ≤ 1 * |Xi ω i j| ^ 3 / (Real.sqrt ((m : ℝ) * p)) ^ 3 := by
            gcongr
        _ = (Real.sqrt ((m : ℝ) * p))⁻¹ ^ 3 * |Xi ω i j| ^ 3 := by
            rw [one_mul, div_eq_inv_mul, ← inv_pow, mul_comm]
  have hZsq := statopia_math_node_2235047215_a757c0bb m n hm hn p Kt hp_pos hp_le hKt
    (μ := μ) Xi Mask hXi_meas hMask_meas hIntThirdμ hbudget
  obtain ⟨hZint, hZbudget⟩ := hZsq
  let Zfm : Fin (m * n) → Ω × (Fin m → Fin n → ℝ) → Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
    fun k x => Matrix.of fun u v =>
      ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
        (Matrix.of fun i j => if (i, j) = (finProdFinEquiv (m := m) (n := n)).symm k
          then maskedScaled p (Xi x.1) (Mask x.1) i j else 0)
        (Matrix.transpose (Matrix.of fun i j =>
          if (i, j) = (finProdFinEquiv (m := m) (n := n)).symm k
          then maskedScaled p (Xi x.1) (Mask x.1) i j else 0))
        (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)
      ((finSumFinEquiv (m := m) (n := n)).symm u)
      ((finSumFinEquiv (m := m) (n := n)).symm v)
  let Gfm : Ω × (Fin m → Fin n → ℝ) → Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
    fun x u v =>
      ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
        (Matrix.of fun i j => x.2 i j / Real.sqrt ((m : ℝ)))
        (Matrix.transpose (Matrix.of fun i j => x.2 i j / Real.sqrt ((m : ℝ))))
        (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)
      ((finSumFinEquiv (m := m) (n := n)).symm u)
      ((finSumFinEquiv (m := m) (n := n)).symm v)
  have hind := statopia_math_node_930997348_7feb7b3b (μ := μ) m n hm hn p Kt hp_pos hp_le hKt
    Xi Mask hXi_meas hXi_int hXi_sq_int hXi_indep hXi_mean hXi_var hXi_tail hMask_meas hMask_val
    hMask_law hMask_indep hIndep
  obtain ⟨hZind, hZGind⟩ := hind
  have hGpkg := statopia_math_node_3824140247_e6348683 (μ := μ) m n hm hn p Kt hp_pos hp_le hKt
    Xi Mask hXi_meas hXi_int hXi_sq_int hXi_indep hXi_mean hXi_var hXi_tail hMask_meas hMask_val
    hMask_law hMask_indep hIndep
  obtain ⟨hGherm, hGmeas, hGint, hGisGauss, hGmean, hGcov⟩ := hGpkg
  have hZpkg := statopia_math_node_4234423270_c59112bd (μ := μ) m n hm hn p hp_pos
    Xi Mask hXi_meas hXi_int hMask_meas hMask_val hMask_law hXi_mean hIndep
  obtain ⟨hZherm, hZmeas, hZint', hZmean⟩ := hZpkg
  have hd2 : 2 ≤ m + n := by
    have h := Nat.add_le_add hm hn
    simpa using h
  have hthird' : ∀ k : Fin (m * n), Integrable (fun x : Ω × (Fin m → Fin n → ℝ) =>
      ((m + n : ℕ) : ℝ)⁻¹ * ∑ t : Fin (m + n),
        ((Matrix.isHermitian_conjTranspose_mul_self (Zfm k x)).eigenvalues t) ^ ((3 : ℝ) / 2))
      (μ.prod (stdNormalMatrixMeasure m n)) := by
    intro k
    simpa only [Nat.cast_add] using hZint k
  have hZGind' : IndepFun
      ((fun Z : Fin (m * n) → Matrix (Fin (m + n)) (Fin (m + n)) ℂ =>
          fun q : Fin (m * n) × Fin (m + n) × Fin (m + n) => Z q.1 q.2.1 q.2.2) ∘
        fun x k => Zfm k x)
      ((fun G : Matrix (Fin (m + n)) (Fin (m + n)) ℂ =>
          fun q : Fin (m + n) × Fin (m + n) => G q.1 q.2) ∘ fun x => Gfm x)
      (μ.prod (stdNormalMatrixMeasure m n)) := by
    refine hZGind.comp ?_ ?_
    · exact measurable_pi_iff.2 fun q =>
        (measurable_pi_apply q.2.2).comp
          ((measurable_pi_apply q.2.1).comp (measurable_pi_apply q.1))
    · exact measurable_pi_iff.2 fun q =>
        (measurable_pi_apply q.2).comp (measurable_pi_apply q.1)
  have hmain := hC₀ (m + n) hd2 (m * n) (μ := μ.prod (stdNormalMatrixMeasure m n))
    (0 : Matrix (Fin (m + n)) (Fin (m + n)) ℂ) Matrix.isHermitian_zero Zfm Gfm
    hZind hZherm hZmeas hZint' hZmean hthird' hGherm hGmeas hGint hGisGauss hGmean hGcov
    hZGind' z hz
  have hsum : ∀ x : Ω × (Fin m → Fin n → ℝ),
      (0 : Matrix (Fin (m + n)) (Fin (m + n)) ℂ) + ∑ k : Fin (m * n), Zfm k x =
      Matrix.reindex (finSumFinEquiv) (finSumFinEquiv)
        ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
          (maskedScaled p (Xi x.1) (Mask x.1))
          (Matrix.transpose (maskedScaled p (Xi x.1) (Mask x.1)))
          (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal) := by
    intro x
    rw [zero_add]
    ext u v
    rw [Matrix.sum_apply]
    obtain ⟨a, rfl⟩ := (finSumFinEquiv (m := m) (n := n)).surjective u
    obtain ⟨b, rfl⟩ := (finSumFinEquiv (m := m) (n := n)).surjective v
    simp only [Equiv.symm_apply_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.map_apply]
    cases a with
    | inl i =>
      cases b with
      | inl j =>
        simp only [Zfm, Matrix.of_apply, Matrix.fromBlocks, Matrix.map_apply, Matrix.zero_apply,
          Complex.ofReal_zero, Sum.elim_inl, Sum.elim_inr, Equiv.symm_apply_apply]
        simp
      | inr j =>
        simp only [Zfm, Matrix.of_apply, Matrix.fromBlocks, Matrix.map_apply, Matrix.transpose_apply,
          Matrix.zero_apply, Complex.ofReal_zero, Sum.elim_inl, Sum.elim_inr,
          Equiv.symm_apply_apply]
        rw [Finset.sum_congr rfl (fun k _ =>
          show Complex.ofReal (if (i, j) = (finProdFinEquiv (m := m) (n := n)).symm k then
              maskedScaled p (Xi x.1) (Mask x.1) i j else 0) =
            (if (i, j) = (finProdFinEquiv (m := m) (n := n)).symm k then
              ((maskedScaled p (Xi x.1) (Mask x.1) i j : ℝ) : ℂ) else 0) from by
            by_cases h : (i, j) = (finProdFinEquiv (m := m) (n := n)).symm k
            · rw [if_pos h, if_pos h]
            · rw [if_neg h, if_neg h]
              simp)]
        rw [Equiv.sum_comp (finProdFinEquiv (m := m) (n := n)).symm
          (fun q : Fin m × Fin n =>
            if (i, j) = q then ((maskedScaled p (Xi x.1) (Mask x.1) i j : ℝ) : ℂ) else 0)]
        rw [Finset.sum_eq_single (i, j)]
        · simp
        · intro q _ hq
          simp [Ne.symm hq]
        · intro h
          exact absurd (Finset.mem_univ _) h
    | inr i =>
      cases b with
      | inl j =>
        simp only [Zfm, Matrix.of_apply, Matrix.fromBlocks, Matrix.map_apply, Matrix.transpose_apply,
          Matrix.zero_apply, Complex.ofReal_zero, Sum.elim_inl, Sum.elim_inr,
          Equiv.symm_apply_apply]
        rw [Finset.sum_congr rfl (fun k _ =>
          show Complex.ofReal (if (j, i) = (finProdFinEquiv (m := m) (n := n)).symm k then
              maskedScaled p (Xi x.1) (Mask x.1) j i else 0) =
            (if (j, i) = (finProdFinEquiv (m := m) (n := n)).symm k then
              ((maskedScaled p (Xi x.1) (Mask x.1) j i : ℝ) : ℂ) else 0) from by
            by_cases h : (j, i) = (finProdFinEquiv (m := m) (n := n)).symm k
            · rw [if_pos h, if_pos h]
            · rw [if_neg h, if_neg h]
              simp)]
        rw [Equiv.sum_comp (finProdFinEquiv (m := m) (n := n)).symm
          (fun q : Fin m × Fin n =>
            if (j, i) = q then ((maskedScaled p (Xi x.1) (Mask x.1) j i : ℝ) : ℂ) else 0)]
        rw [Finset.sum_eq_single (j, i)]
        · simp
        · intro q _ hq
          simp [Ne.symm hq]
        · intro h
          exact absurd (Finset.mem_univ _) h
      | inr j =>
        simp only [Zfm, Matrix.of_apply, Matrix.fromBlocks, Matrix.map_apply, Matrix.zero_apply,
          Complex.ofReal_zero, Sum.elim_inl, Sum.elim_inr, Equiv.symm_apply_apply]
        simp
  have htrace : ∀ M : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ,
      (Matrix.reindex (finSumFinEquiv) (finSumFinEquiv) M).trace = M.trace := by
    intro M
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
    exact Equiv.sum_comp (finSumFinEquiv (m := m) (n := n)).symm (fun i => M i i)
  have hbase : C₀ * (z.im ^ 4)⁻¹ * (∑ k : Fin (m * n), ∫ x : Ω × (Fin m → Fin n → ℝ),
      (↑(m + n))⁻¹ * ∑ t : Fin (m + n),
        ((Matrix.isHermitian_conjTranspose_mul_self (Zfm k x)).eigenvalues t) ^ ((3 : ℝ) / 2)
        ∂(μ.prod (stdNormalMatrixMeasure m n)))
      ≤ 48 * C₀ * Kt ^ 3 * Real.rpow ((m : ℝ) * p) (-(1 / 2)) * (z.im ^ 4)⁻¹ := by
    have hS : (∑ k : Fin (m * n), ∫ x : Ω × (Fin m → Fin n → ℝ),
        (↑(m + n))⁻¹ * ∑ t : Fin (m + n),
          ((Matrix.isHermitian_conjTranspose_mul_self (Zfm k x)).eigenvalues t) ^ ((3 : ℝ) / 2)
          ∂(μ.prod (stdNormalMatrixMeasure m n)))
        ≤ 48 * Kt ^ 3 * (Real.sqrt ((m : ℝ) * p))⁻¹ := by
      simpa only [Nat.cast_add] using hZbudget
    calc C₀ * (z.im ^ 4)⁻¹ * (∑ k : Fin (m * n), ∫ x : Ω × (Fin m → Fin n → ℝ),
          (↑(m + n))⁻¹ * ∑ t : Fin (m + n),
            ((Matrix.isHermitian_conjTranspose_mul_self (Zfm k x)).eigenvalues t) ^ ((3 : ℝ) / 2)
            ∂(μ.prod (stdNormalMatrixMeasure m n)))
        ≤ C₀ * (z.im ^ 4)⁻¹ * (48 * Kt ^ 3 * (Real.sqrt ((m : ℝ) * p))⁻¹) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
      _ = 48 * C₀ * Kt ^ 3 * ((m : ℝ) * p) ^ (-(1 / 2) : ℝ) * (z.im ^ 4)⁻¹ := by
          rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
          ring
  have htrgen : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ),
      B⁻¹.trace = Ring.inverse B.det * B.adjugate.trace := by
    intro ι _ _ B
    rw [Matrix.inv_def]
    have htr : ∀ (c : ℂ) (M : Matrix ι ι ℂ), (c • M).trace = c * M.trace := by
      intro c M
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.smul_apply, smul_eq_mul,
        Finset.mul_sum]
    exact htr _ _
  have hres_eq : ∀ A : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ,
      ((z • (1 : Matrix (Fin (m + n)) (Fin (m + n)) ℂ)) -
        Matrix.reindex (finSumFinEquiv) (finSumFinEquiv) A)⁻¹.trace
      = ((z • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) - A)⁻¹.trace := by
    intro A
    have hone : Matrix.reindex (finSumFinEquiv) (finSumFinEquiv)
        (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) = 1 := by
      ext a b
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply]
      by_cases h : a = b
      · subst h
        simp
      · have h2 : (finSumFinEquiv (m := m) (n := n)).symm a ≠
            (finSumFinEquiv (m := m) (n := n)).symm b :=
          fun hh => h ((finSumFinEquiv (m := m) (n := n)).symm.injective hh)
        simp [h, h2]
    have hsmul : ∀ (c : ℂ) (B : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ),
        Matrix.reindex (finSumFinEquiv) (finSumFinEquiv) (c • B) =
          c • Matrix.reindex (finSumFinEquiv) (finSumFinEquiv) B := by
      intro c B
      ext a b
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply]
    have hsub : ∀ B C : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ,
        Matrix.reindex (finSumFinEquiv) (finSumFinEquiv) (B - C) =
          Matrix.reindex (finSumFinEquiv) (finSumFinEquiv) B -
            Matrix.reindex (finSumFinEquiv) (finSumFinEquiv) C := by
      intro B C
      ext a b
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply]
    have haff : (z • (1 : Matrix (Fin (m + n)) (Fin (m + n)) ℂ)) -
        Matrix.reindex (finSumFinEquiv) (finSumFinEquiv) A =
          Matrix.reindex (finSumFinEquiv) (finSumFinEquiv)
            ((z • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) - A) := by
      rw [hsub, hsmul, hone]
    rw [haff]
    rw [htrgen (ι := Fin (m + n)) (Matrix.reindex (finSumFinEquiv) (finSumFinEquiv)
      ((z • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) - A))]
    rw [htrgen (ι := Fin m ⊕ Fin n)
      ((z • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) - A)]
    rw [Matrix.det_reindex_self, Matrix.adjugate_reindex, htrace]


  have hrinvmeas : Measurable fun x : ℂ => Ring.inverse x := by
    have hEq : (fun x : ℂ => Ring.inverse x) = fun x : ℂ => x⁻¹ := by
      funext x
      exact Ring.inverse_eq_inv x
    rw [hEq]
    exact measurable_inv
  have hdetmeas : ∀ {ι : Type} [Fintype ι] [DecidableEq ι],
      Measurable fun M : Matrix ι ι ℂ => M.det := by
    intro ι _ _
    have hEq : (fun M : Matrix ι ι ℂ => M.det) =
        fun M => ∑ σ : Equiv.Perm ι, ↑↑(Equiv.Perm.sign σ) * ∏ i, M (σ i) i := by
      funext M
      exact Matrix.det_apply' M
    rw [hEq]
    refine Finset.measurable_sum _ fun σ _ => ?_
    exact Measurable.const_mul
      (Finset.measurable_prod _ fun i _ =>
        (measurable_pi_apply i).comp (measurable_pi_apply (σ i))) _
  have hadjmeas : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (i j : ι),
      Measurable fun M : Matrix ι ι ℂ => M.adjugate i j := by
    intro ι _ _ i j
    have hEq : (fun M : Matrix ι ι ℂ => M.adjugate i j) =
        fun M => (M.updateRow j (Pi.single i 1)).det := by
      funext M
      exact Matrix.adjugate_apply M i j
    rw [hEq]
    refine (hdetmeas (ι := ι)).comp ?_
    refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b => ?_
    simp only [Matrix.updateRow_apply]
    by_cases hab : a = j
    · simp [hab]
    · simp only [if_neg hab]
      exact (measurable_pi_apply b).comp (measurable_pi_apply a)
  have hresmeas : ∀ {ι : Type} [Fintype ι] [DecidableEq ι],
      Measurable fun M : Matrix ι ι ℂ => ((z • (1 : Matrix ι ι ℂ) - M)⁻¹).trace := by
    intro ι _ _
    have hzM : Measurable fun M : Matrix ι ι ℂ => z • (1 : Matrix ι ι ℂ) - M := by
      refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b => ?_
      have h1 : Measurable fun M : Matrix ι ι ℂ => M a b :=
        (measurable_pi_apply b).comp (measurable_pi_apply a)
      have hEq3 : (fun M : Matrix ι ι ℂ => (z • (1 : Matrix ι ι ℂ) - M) a b) =
          fun M => z * ((1 : Matrix ι ι ℂ) a b) - M a b := by
        funext M
        simp
      rw [hEq3]
      exact measurable_const.sub h1
    have hEq4 : (fun M : Matrix ι ι ℂ => ((z • (1 : Matrix ι ι ℂ) - M)⁻¹).trace) =
        fun M => Ring.inverse (z • (1 : Matrix ι ι ℂ) - M).det *
          (z • (1 : Matrix ι ι ℂ) - M).adjugate.trace := by
      funext M
      exact htrgen ((z • (1 : Matrix ι ι ℂ)) - M)
    rw [hEq4]
    have hdetz : Measurable fun M : Matrix ι ι ℂ => (z • (1 : Matrix ι ι ℂ) - M).det :=
      (hdetmeas (ι := ι)).comp hzM
    have hadjz : Measurable fun M : Matrix ι ι ℂ =>
        (z • (1 : Matrix ι ι ℂ) - M).adjugate.trace := by
      have hEq5 : (fun M : Matrix ι ι ℂ => (z • (1 : Matrix ι ι ℂ) - M).adjugate.trace) =
          fun M => ∑ i, (z • (1 : Matrix ι ι ℂ) - M).adjugate i i := by
        funext M
        simp only [Matrix.trace, Matrix.diag_apply]
      rw [hEq5]
      exact Finset.measurable_sum _ fun i _ => (hadjmeas (ι := ι) i i).comp hzM
    exact (hrinvmeas.comp hdetz).mul hadjz

  have htrZ : (∫ ω, ((((m : ℝ) + (n : ℝ))⁻¹ : ℂ) *
        (((z • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) -
          (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
            (maskedScaled p (Xi ω) (Mask ω))
            (Matrix.transpose (maskedScaled p (Xi ω) (Mask ω)))
            (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)⁻¹).trace) ∂μ)
      = ∫ x : Ω × (Fin m → Fin n → ℝ),
          (↑(m + n) : ℂ)⁻¹ * (z • 1 - (0 + ∑ k : Fin (m * n), Zfm k x))⁻¹.trace
          ∂(μ.prod (stdNormalMatrixMeasure m n)) := by
    have hmap : (μ.prod (stdNormalMatrixMeasure m n)).map Prod.fst = μ :=
      MeasureTheory.Measure.fst_prod
    have hdilmeas : Measurable fun ω : Ω =>
        (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
          (maskedScaled p (Xi ω) (Mask ω))
          (Matrix.transpose (maskedScaled p (Xi ω) (Mask ω)))
          (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal := by
      refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b => ?_
      rcases a with i | i <;> rcases b with j | j
      · simp only [Matrix.fromBlocks, Matrix.of_apply, Matrix.map_apply, Sum.elim_inl,
          Sum.elim_inr, Matrix.zero_apply, Complex.ofReal_zero]
        exact measurable_const
      · simp only [Matrix.fromBlocks, Matrix.of_apply, Matrix.map_apply, Sum.elim_inl,
          Sum.elim_inr]
        exact Complex.continuous_ofReal.measurable.comp (by
          show Measurable fun ω => Mask ω i j * Xi ω i j / Real.sqrt ((m : ℝ) * p)
          exact ((hMask_meas i j).mul (hXi_meas i j)).div_const _)
      · simp only [Matrix.fromBlocks, Matrix.of_apply, Matrix.map_apply, Sum.elim_inl,
          Sum.elim_inr]
        exact Complex.continuous_ofReal.measurable.comp (by
          show Measurable fun ω => Mask ω j i * Xi ω j i / Real.sqrt ((m : ℝ) * p)
          exact ((hMask_meas j i).mul (hXi_meas j i)).div_const _)
      · simp only [Matrix.fromBlocks, Matrix.of_apply, Matrix.map_apply, Sum.elim_inl,
          Sum.elim_inr, Matrix.zero_apply, Complex.ofReal_zero]
        exact measurable_const
    have hstep : ∀ x : Ω × (Fin m → Fin n → ℝ),
        (↑(m + n) : ℂ)⁻¹ * (z • 1 - (0 + ∑ k : Fin (m * n), Zfm k x))⁻¹.trace
          = ((((m : ℝ) + (n : ℝ))⁻¹ : ℂ) *
              (((z • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) -
                (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
                  (maskedScaled p (Xi x.1) (Mask x.1))
                  (Matrix.transpose (maskedScaled p (Xi x.1) (Mask x.1)))
                  (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)⁻¹).trace) := by
      intro x
      rw [hsum x, hres_eq]
      have hc : ((↑(m + n) : ℂ))⁻¹ = (((m : ℝ) + (n : ℝ))⁻¹ : ℂ) := by
        push_cast
        ring
      rw [hc]
    have hmeasF : AEStronglyMeasurable (fun ω : Ω => ((((m : ℝ) + (n : ℝ))⁻¹ : ℂ) *
        (((z • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) -
          (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
            (maskedScaled p (Xi ω) (Mask ω))
            (Matrix.transpose (maskedScaled p (Xi ω) (Mask ω)))
            (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)⁻¹).trace)) μ :=
      (((hresmeas (ι := Fin m ⊕ Fin n)).comp hdilmeas).const_mul _).aestronglyMeasurable
    have h1 : (∫ x : Ω × (Fin m → Fin n → ℝ),
        ((((m : ℝ) + (n : ℝ))⁻¹ : ℂ) *
          (((z • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) -
            (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
              (maskedScaled p (Xi x.1) (Mask x.1))
              (Matrix.transpose (maskedScaled p (Xi x.1) (Mask x.1)))
              (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)⁻¹).trace)
        ∂(μ.prod (stdNormalMatrixMeasure m n)))
        = ∫ ω, ((((m : ℝ) + (n : ℝ))⁻¹ : ℂ) *
          (((z • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) -
            (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
              (maskedScaled p (Xi ω) (Mask ω))
              (Matrix.transpose (maskedScaled p (Xi ω) (Mask ω)))
              (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)⁻¹).trace) ∂μ := by
      have hm := MeasureTheory.integral_map
        (μ := μ.prod (stdNormalMatrixMeasure m n)) (φ := Prod.fst)
        (f := fun ω : Ω => ((((m : ℝ) + (n : ℝ))⁻¹ : ℂ) *
          (((z • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) -
            (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
              (maskedScaled p (Xi ω) (Mask ω))
              (Matrix.transpose (maskedScaled p (Xi ω) (Mask ω)))
              (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)⁻¹).trace))
        measurable_fst.aemeasurable (by rw [hmap]; exact hmeasF)
      rw [hmap] at hm
      exact hm.symm
    exact h1.symm.trans (MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun x => (hstep x).symm))
  have htrG : (∫ g, ((((m : ℝ) + (n : ℝ))⁻¹ : ℂ) *
        (((z • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) -
          (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
            (Matrix.of fun i j => g i j / Real.sqrt (m : ℝ))
            (Matrix.transpose (Matrix.of fun i j => g i j / Real.sqrt (m : ℝ)))
            (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)⁻¹).trace)
        ∂(stdNormalMatrixMeasure m n))
      = ∫ x : Ω × (Fin m → Fin n → ℝ),
          (↑(m + n) : ℂ)⁻¹ * (z • 1 - Gfm x)⁻¹.trace
          ∂(μ.prod (stdNormalMatrixMeasure m n)) := by
    have hmap2 : (μ.prod (stdNormalMatrixMeasure m n)).map Prod.snd = stdNormalMatrixMeasure m n :=
      MeasureTheory.Measure.snd_prod
    have hdilGmeas : Measurable fun g : Fin m → Fin n → ℝ =>
        (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
          (Matrix.of fun i j => g i j / Real.sqrt ((m : ℝ)))
          (Matrix.transpose (Matrix.of fun i j => g i j / Real.sqrt ((m : ℝ))))
          (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal := by
      refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b => ?_
      rcases a with i | i <;> rcases b with j | j
      · simp only [Matrix.fromBlocks, Matrix.of_apply, Matrix.map_apply, Sum.elim_inl,
          Sum.elim_inr, Matrix.zero_apply, Complex.ofReal_zero]
        exact measurable_const
      · simp only [Matrix.fromBlocks, Matrix.of_apply, Matrix.map_apply, Sum.elim_inl,
          Sum.elim_inr]
        exact Complex.continuous_ofReal.measurable.comp
          (((measurable_pi_apply j).comp (measurable_pi_apply i)).div_const _)
      · simp only [Matrix.fromBlocks, Matrix.of_apply, Matrix.map_apply, Matrix.transpose_apply,
          Sum.elim_inl, Sum.elim_inr]
        exact Complex.continuous_ofReal.measurable.comp
          (((measurable_pi_apply i).comp (measurable_pi_apply j)).div_const _)
      · simp only [Matrix.fromBlocks, Matrix.of_apply, Matrix.map_apply, Sum.elim_inl,
          Sum.elim_inr, Matrix.zero_apply, Complex.ofReal_zero]
        exact measurable_const
    have hstepG : ∀ x : Ω × (Fin m → Fin n → ℝ),
        (↑(m + n) : ℂ)⁻¹ * (z • 1 - Gfm x)⁻¹.trace
          = ((((m : ℝ) + (n : ℝ))⁻¹ : ℂ) *
              (((z • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) -
                (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
                  (Matrix.of fun i j => x.2 i j / Real.sqrt (m : ℝ))
                  (Matrix.transpose (Matrix.of fun i j => x.2 i j / Real.sqrt (m : ℝ)))
                  (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)⁻¹).trace) := by
      intro x
      have hG : Gfm x = Matrix.reindex (finSumFinEquiv) (finSumFinEquiv)
          ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
            (Matrix.of fun i j => x.2 i j / Real.sqrt (m : ℝ))
            (Matrix.transpose (Matrix.of fun i j => x.2 i j / Real.sqrt (m : ℝ)))
            (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal) := by
        ext u v
        rfl
      rw [hG, hres_eq]
      have hc : ((↑(m + n) : ℂ))⁻¹ = (((m : ℝ) + (n : ℝ))⁻¹ : ℂ) := by
        push_cast
        ring
      rw [hc]
    have hmeasG : AEStronglyMeasurable (fun g : Fin m → Fin n → ℝ =>
        ((((m : ℝ) + (n : ℝ))⁻¹ : ℂ) *
        (((z • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) -
          (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
            (Matrix.of fun i j => g i j / Real.sqrt ((m : ℝ)))
            (Matrix.transpose (Matrix.of fun i j => g i j / Real.sqrt ((m : ℝ))))
            (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)⁻¹).trace))
        (stdNormalMatrixMeasure m n) :=
      (((hresmeas (ι := Fin m ⊕ Fin n)).comp hdilGmeas).const_mul _).aestronglyMeasurable
    have h2 : (∫ x : Ω × (Fin m → Fin n → ℝ),
        ((((m : ℝ) + (n : ℝ))⁻¹ : ℂ) *
          (((z • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) -
            (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
              (Matrix.of fun i j => x.2 i j / Real.sqrt (m : ℝ))
              (Matrix.transpose (Matrix.of fun i j => x.2 i j / Real.sqrt (m : ℝ)))
              (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)⁻¹).trace)
        ∂(μ.prod (stdNormalMatrixMeasure m n)))
        = ∫ g : Fin m → Fin n → ℝ,
          ((((m : ℝ) + (n : ℝ))⁻¹ : ℂ) *
          (((z • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) -
            (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
              (Matrix.of fun i j => g i j / Real.sqrt (m : ℝ))
              (Matrix.transpose (Matrix.of fun i j => g i j / Real.sqrt (m : ℝ)))
              (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)⁻¹).trace)
          ∂(stdNormalMatrixMeasure m n) := by
      have hm := MeasureTheory.integral_map
        (μ := μ.prod (stdNormalMatrixMeasure m n)) (φ := Prod.snd)
        (f := fun g : Fin m → Fin n → ℝ => ((((m : ℝ) + (n : ℝ))⁻¹ : ℂ) *
          (((z • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) -
            (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
              (Matrix.of fun i j => g i j / Real.sqrt (m : ℝ))
              (Matrix.transpose (Matrix.of fun i j => g i j / Real.sqrt (m : ℝ)))
              (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)⁻¹).trace))
        measurable_snd.aemeasurable (by rw [hmap2]; exact hmeasG)
      rw [hmap2] at hm
      exact hm.symm
    exact h2.symm.trans (MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun x => (hstepG x).symm))
  rw [htrZ, htrG]
  exact le_trans hmain hbase




  /- @proof-region region.target-node.session.c2c94ffba0fe6daa end -/

end Statlib.Imported

