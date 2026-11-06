import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_4234423270_c59112bd : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (p : ℝ) (hp : 0 < p)
    (Xi Mask : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hXi_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun ω => Xi ω i j)
    (hXi_int : ∀ (i : Fin m) (j : Fin n), Integrable (fun ω => Xi ω i j) μ)
    (hMask_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun ω => Mask ω i j)
    (hMask_val : ∀ (i : Fin m) (j : Fin n) (ω : Ω), Mask ω i j = 0 ∨ Mask ω i j = 1)
    (hMask_law : ∀ (i : Fin m) (j : Fin n), μ {ω | Mask ω i j = 1} = ENNReal.ofReal p)
    (hXi_mean : ∀ (i : Fin m) (j : Fin n), ∫ ω, Xi ω i j ∂μ = 0)
    (hIndep : IndepFun (fun ω (ij : Fin m × Fin n) => Xi ω ij.1 ij.2)
      (fun ω (ij : Fin m × Fin n) => Mask ω ij.1 ij.2) μ),
    let F : Fin (m * n) → (Ω × (Fin m → Fin n → ℝ)) → Matrix (Fin m) (Fin n) ℝ :=
      fun k x i j =>
        if (i, j) = finProdFinEquiv.symm k then maskedScaled p (Xi x.1) (Mask x.1) i j else 0
    let Z : Fin (m * n) → (Ω × (Fin m → Fin n → ℝ)) → Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
      fun k x u v =>
        (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (F k x) (Matrix.transpose (F k x))
          (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal
          (finSumFinEquiv.symm u) (finSumFinEquiv.symm v)
    (∀ (k : Fin (m * n)) (x : Ω × (Fin m → Fin n → ℝ)), (Z k x).IsHermitian) ∧
    (∀ (k : Fin (m * n)) (a b : Fin (m + n)),
      Measurable fun x : Ω × (Fin m → Fin n → ℝ) => Z k x a b) ∧
    (∀ (k : Fin (m * n)) (a b : Fin (m + n)),
      Integrable (fun x : Ω × (Fin m → Fin n → ℝ) => Z k x a b)
        (μ.prod (stdNormalMatrixMeasure m n))) ∧
    (∀ (k : Fin (m * n)) (a b : Fin (m + n)),
      ∫ x, Z k x a b ∂(μ.prod (stdNormalMatrixMeasure m n)) = 0) := by
  /- @proof-region region.target-node.session.0a5c0161bde6f762 begin -/
  classical
  intro Ω _ μ _ m n hm hn p hp Xi Mask hXi_meas hXi_int hMask_meas hMask_val hMask_law hXi_mean hIndep
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k x
    have hgen : ∀ (B : Matrix (Fin m) (Fin n) ℝ),
        ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) B (Matrix.transpose B)
          (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal).IsHermitian := by
      intro B
      refine Matrix.IsHermitian.ext ?_
      intro u v
      rcases u with i | i <;> rcases v with j | j <;>
        simp [Matrix.fromBlocks, Matrix.map_apply, Matrix.transpose_apply, Complex.conj_ofReal]
    exact Matrix.IsHermitian.submatrix (hgen _) finSumFinEquiv.symm
  · intro k a b
    have hF : ∀ (i : Fin m) (j : Fin n),
        Measurable fun x : Ω × (Fin m → Fin n → ℝ) =>
          ((if (i, j) = finProdFinEquiv.symm k then
            maskedScaled p (Xi x.1) (Mask x.1) i j else 0 : ℝ) : ℂ) := by
      intro i j
      have h1 : Measurable fun x : Ω × (Fin m → Fin n → ℝ) => Mask x.1 i j :=
        (hMask_meas i j).comp measurable_fst
      have h2 : Measurable fun x : Ω × (Fin m → Fin n → ℝ) => Xi x.1 i j :=
        (hXi_meas i j).comp measurable_fst
      have hval : Measurable fun x : Ω × (Fin m → Fin n → ℝ) =>
          Complex.ofReal (maskedScaled p (Xi x.1) (Mask x.1) i j) := by
        simp only [maskedScaled]
        exact Complex.continuous_ofReal.measurable.comp ((h1.mul h2).div_const _)
      by_cases hk : (i, j) = finProdFinEquiv.symm k
      · have hfun : (fun x : Ω × (Fin m → Fin n → ℝ) =>
            ((if (i, j) = finProdFinEquiv.symm k then
              maskedScaled p (Xi x.1) (Mask x.1) i j else 0 : ℝ) : ℂ))
            = fun x => Complex.ofReal (maskedScaled p (Xi x.1) (Mask x.1) i j) := by
          funext x
          exact congrArg Complex.ofReal (if_pos hk)
        rw [hfun]
        exact hval
      · have hfun : (fun x : Ω × (Fin m → Fin n → ℝ) =>
            ((if (i, j) = finProdFinEquiv.symm k then
              maskedScaled p (Xi x.1) (Mask x.1) i j else 0 : ℝ) : ℂ))
            = fun x => (0 : ℂ) := by
          funext x
          exact congrArg Complex.ofReal (if_neg hk)
        rw [hfun]
        exact measurable_const
    obtain ⟨a', rfl⟩ := finSumFinEquiv.surjective a
    obtain ⟨b', rfl⟩ := finSumFinEquiv.surjective b
    rcases a' with i | i <;> rcases b' with j | j
    · simp [Matrix.fromBlocks, Matrix.map_apply]
    · simpa [Matrix.fromBlocks, Matrix.map_apply] using hF i j
    · simpa [Matrix.fromBlocks, Matrix.map_apply, Matrix.transpose_apply] using hF j i
    · simp [Matrix.fromBlocks, Matrix.map_apply]
  · intro k a b
    haveI hνfin : IsFiniteMeasure (stdNormalMatrixMeasure m n) := by
      haveI hνprob : IsProbabilityMeasure (stdNormalMatrixMeasure m n) := by
        unfold stdNormalMatrixMeasure
        infer_instance
      infer_instance
    have hstep : ∀ (i : Fin m) (j : Fin n),
        Integrable (fun x : Ω × (Fin m → Fin n → ℝ) =>
          ((maskedScaled p (Xi x.1) (Mask x.1) i j : ℝ) : ℂ))
          (μ.prod (stdNormalMatrixMeasure m n)) := by
      intro i j
      have h1 : Measurable fun x : Ω × (Fin m → Fin n → ℝ) => Mask x.1 i j :=
        (hMask_meas i j).comp measurable_fst
      have h2 : Measurable fun x : Ω × (Fin m → Fin n → ℝ) => Xi x.1 i j :=
        (hXi_meas i j).comp measurable_fst
      have hreal : Integrable (fun x : Ω × (Fin m → Fin n → ℝ) =>
          maskedScaled p (Xi x.1) (Mask x.1) i j) (μ.prod (stdNormalMatrixMeasure m n)) := by
        have hprod : Integrable (fun x : Ω × (Fin m → Fin n → ℝ) =>
            Mask x.1 i j * Xi x.1 i j) (μ.prod (stdNormalMatrixMeasure m n)) := by
          refine Integrable.mono' ((hXi_int i j).comp_fst (stdNormalMatrixMeasure m n)).norm
            ((h1.mul h2).aestronglyMeasurable) ?_
          filter_upwards with x
          rcases hMask_val i j x.1 with h | h <;> simp [h]
        have hdiv := hprod.div_const (Real.sqrt ((m : ℝ) * p))
        simpa only [maskedScaled] using hdiv
      refine Integrable.mono' hreal.norm
        (Complex.continuous_ofReal.measurable.comp ?_).aestronglyMeasurable ?_
      · show Measurable fun x : Ω × (Fin m → Fin n → ℝ) =>
          maskedScaled p (Xi x.1) (Mask x.1) i j
        exact (h1.mul h2).div_const (Real.sqrt ((m : ℝ) * p))
      · filter_upwards with x
        simp
    have hInt : ∀ (i : Fin m) (j : Fin n),
        Integrable (fun x : Ω × (Fin m → Fin n → ℝ) =>
          ((if (i, j) = finProdFinEquiv.symm k then
            maskedScaled p (Xi x.1) (Mask x.1) i j else 0 : ℝ) : ℂ))
          (μ.prod (stdNormalMatrixMeasure m n)) := by
      intro i j
      by_cases hk : (i, j) = finProdFinEquiv.symm k
      · have hfun : (fun x : Ω × (Fin m → Fin n → ℝ) =>
            ((if (i, j) = finProdFinEquiv.symm k then
              maskedScaled p (Xi x.1) (Mask x.1) i j else 0 : ℝ) : ℂ))
            = fun x => ((maskedScaled p (Xi x.1) (Mask x.1) i j : ℝ) : ℂ) := by
          funext x
          exact congrArg Complex.ofReal (if_pos hk)
        rw [hfun]
        exact hstep i j
      · have hfun : (fun x : Ω × (Fin m → Fin n → ℝ) =>
            ((if (i, j) = finProdFinEquiv.symm k then
              maskedScaled p (Xi x.1) (Mask x.1) i j else 0 : ℝ) : ℂ))
            = fun x => (0 : ℂ) := by
          funext x
          exact congrArg Complex.ofReal (if_neg hk)
        rw [hfun]
        simp
    obtain ⟨a', rfl⟩ := finSumFinEquiv.surjective a
    obtain ⟨b', rfl⟩ := finSumFinEquiv.surjective b
    rcases a' with i | i <;> rcases b' with j | j
    · simp [Matrix.fromBlocks, Matrix.map_apply]
    · simpa [Matrix.fromBlocks, Matrix.map_apply] using hInt i j
    · simpa [Matrix.fromBlocks, Matrix.map_apply, Matrix.transpose_apply] using hInt j i
    · simp [Matrix.fromBlocks, Matrix.map_apply]
  · intro k a b
    haveI hνfin : IsFiniteMeasure (stdNormalMatrixMeasure m n) := by
      haveI hνprob : IsProbabilityMeasure (stdNormalMatrixMeasure m n) := by
        unfold stdNormalMatrixMeasure
        infer_instance
      infer_instance
    have hfib : ∀ (i : Fin m) (j : Fin n),
        ∫ x : Ω × (Fin m → Fin n → ℝ), Mask x.1 i j * Xi x.1 i j
          ∂(μ.prod (stdNormalMatrixMeasure m n)) = 0 := by
      intro i j
      have hindep : IndepFun (fun ω : Ω => Xi ω i j) (fun ω : Ω => Mask ω i j) μ :=
        hIndep.comp (measurable_pi_apply (i, j)) (measurable_pi_apply (i, j))
      have hfac0 : ∫ ω : Ω, Xi ω i j * Mask ω i j ∂μ
          = (∫ ω : Ω, Xi ω i j ∂μ) * ∫ ω : Ω, Mask ω i j ∂μ := by
        simpa using hindep.integral_comp_mul_comp (f := id) (g := id)
          (hXi_meas i j).aemeasurable (hMask_meas i j).aemeasurable
          measurable_id.aestronglyMeasurable measurable_id.aestronglyMeasurable
      have hzero : ∫ ω : Ω, Xi ω i j * Mask ω i j ∂μ = 0 := by
        rw [hfac0, hXi_mean i j, zero_mul]
      have hzero' : (fun ω : Ω => Mask ω i j * Xi ω i j)
          = fun ω : Ω => Xi ω i j * Mask ω i j := by
        funext ω
        exact mul_comm _ _
      have hprodint : Integrable
          (fun x : Ω × (Fin m → Fin n → ℝ) => Mask x.1 i j * Xi x.1 i j)
          (μ.prod (stdNormalMatrixMeasure m n)) := by
        refine Integrable.mono' ((hXi_int i j).comp_fst (stdNormalMatrixMeasure m n)).norm
          (((hMask_meas i j).comp measurable_fst).mul
            ((hXi_meas i j).comp measurable_fst)).aestronglyMeasurable ?_
        filter_upwards with x
        rcases hMask_val i j x.1 with h | h <;> simp [h]
      calc ∫ x : Ω × (Fin m → Fin n → ℝ), Mask x.1 i j * Xi x.1 i j
            ∂(μ.prod (stdNormalMatrixMeasure m n))
          = ∫ ω : Ω, ∫ y : Fin m → Fin n → ℝ, Mask ω i j * Xi ω i j
              ∂(stdNormalMatrixMeasure m n) ∂μ :=
            MeasureTheory.integral_prod
              (fun z : Ω × (Fin m → Fin n → ℝ) => Mask z.1 i j * Xi z.1 i j) hprodint
        _ = ∫ ω : Ω,
              (stdNormalMatrixMeasure m n).real Set.univ * (Mask ω i j * Xi ω i j) ∂μ := by
            have hinner : ∀ ω : Ω, ∫ y : Fin m → Fin n → ℝ, Mask ω i j * Xi ω i j
                ∂(stdNormalMatrixMeasure m n)
                = (stdNormalMatrixMeasure m n).real Set.univ * (Mask ω i j * Xi ω i j) := by
              intro ω
              rw [MeasureTheory.integral_const]
              simp
            simp only [hinner]
        _ = (stdNormalMatrixMeasure m n).real Set.univ
              * ∫ ω : Ω, Mask ω i j * Xi ω i j ∂μ :=
            MeasureTheory.integral_const_mul _ _
        _ = 0 := by rw [hzero', hzero, mul_zero]
    have hInt : ∀ (i : Fin m) (j : Fin n),
        ∫ x : Ω × (Fin m → Fin n → ℝ),
          ((if (i, j) = finProdFinEquiv.symm k then
            maskedScaled p (Xi x.1) (Mask x.1) i j else 0 : ℝ) : ℂ)
          ∂(μ.prod (stdNormalMatrixMeasure m n)) = 0 := by
      intro i j
      have hbase : ∫ x : Ω × (Fin m → Fin n → ℝ),
          ((maskedScaled p (Xi x.1) (Mask x.1) i j : ℝ) : ℂ)
          ∂(μ.prod (stdNormalMatrixMeasure m n)) = 0 := by
        have hfun : (fun x : Ω × (Fin m → Fin n → ℝ) =>
            ((maskedScaled p (Xi x.1) (Mask x.1) i j : ℝ) : ℂ))
            = fun x => ((Mask x.1 i j * Xi x.1 i j : ℝ) : ℂ)
              * ((Real.sqrt ((m : ℝ) * p) : ℝ) : ℂ)⁻¹ := by
          funext x
          simp only [maskedScaled, div_eq_mul_inv]
          push_cast
          ring
        have h2 : ∫ x : Ω × (Fin m → Fin n → ℝ), ((Mask x.1 i j * Xi x.1 i j : ℝ) : ℂ)
            ∂(μ.prod (stdNormalMatrixMeasure m n)) = 0 := by
          calc ∫ x : Ω × (Fin m → Fin n → ℝ), ((Mask x.1 i j * Xi x.1 i j : ℝ) : ℂ)
                ∂(μ.prod (stdNormalMatrixMeasure m n))
              = ↑(∫ x : Ω × (Fin m → Fin n → ℝ), Mask x.1 i j * Xi x.1 i j
                  ∂(μ.prod (stdNormalMatrixMeasure m n))) := integral_ofReal
            _ = 0 := by rw [hfib i j]; simp
        rw [hfun, MeasureTheory.integral_mul_const, h2, zero_mul]
      by_cases hk : (i, j) = finProdFinEquiv.symm k
      · have hfun : (fun x : Ω × (Fin m → Fin n → ℝ) =>
            ((if (i, j) = finProdFinEquiv.symm k then
              maskedScaled p (Xi x.1) (Mask x.1) i j else 0 : ℝ) : ℂ))
            = fun x => ((maskedScaled p (Xi x.1) (Mask x.1) i j : ℝ) : ℂ) := by
          funext x
          exact congrArg Complex.ofReal (if_pos hk)
        rw [hfun]
        exact hbase
      · have hfun : (fun x : Ω × (Fin m → Fin n → ℝ) =>
            ((if (i, j) = finProdFinEquiv.symm k then
              maskedScaled p (Xi x.1) (Mask x.1) i j else 0 : ℝ) : ℂ))
            = fun x => (0 : ℂ) := by
          funext x
          exact congrArg Complex.ofReal (if_neg hk)
        rw [hfun]
        simp
    obtain ⟨a', rfl⟩ := finSumFinEquiv.surjective a
    obtain ⟨b', rfl⟩ := finSumFinEquiv.surjective b
    rcases a' with i | i <;> rcases b' with j | j
    · simp [Matrix.fromBlocks, Matrix.map_apply]
    · simpa [Matrix.fromBlocks, Matrix.map_apply] using hInt i j
    · simpa [Matrix.fromBlocks, Matrix.map_apply, Matrix.transpose_apply] using hInt j i
    · simp [Matrix.fromBlocks, Matrix.map_apply]
  /- @proof-region region.target-node.session.0a5c0161bde6f762 end -/

end Statlib.Imported

