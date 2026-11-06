import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import Statlib.StatFoundation.RandomVariable.Gaussian.LogSobolev
import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Statlib.StatFoundation.RandomVariable.Gaussian.Standard
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_d7e7069c8c68bdf859cd
import ProverJobs.ResidualE2ESupport20261106.M_00c1df656901ee109b3a

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
theorem statopia_math_node_187531984_414bbd93 : ∀ (n : ℕ) (hn : 1 ≤ n)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → Fin n → ℝ)
    (hU_meas : ∀ k : Fin n, Measurable fun ω => U ω k)
    (hU_gauss : ∀ a : Fin n → ℝ,
      ∃ v : NNReal,
        Measure.map (fun ω => ∑ k : Fin n, a k * U ω k) μ = gaussianReal 0 v)
    (ν' : Measure (Fin n → ℝ)) [IsProbabilityMeasure ν']
    (Φ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (hPhi_meas : Measurable fun p : (Fin n → ℝ) × (Fin n → ℝ) => Φ p.1 p.2)
    (hPhi_bdd : ∃ C : ℝ, ∀ x y : Fin n → ℝ, |Φ x y| ≤ C)
    (hPhi_diff : ∀ y : Fin n → ℝ, ContDiff ℝ 1 (fun x : Fin n → ℝ => Φ x y))
    (hPhi_deriv_int : ∀ l : Fin n,
      Integrable
        (Function.uncurry
          (fun x y : Fin n → ℝ =>
            deriv (fun s : ℝ => Φ (Function.update x l s) y) (x l)))
        ((Measure.map U μ).prod ν')),
    ∀ k : Fin n, ∀ᵐ y ∂ν',
      ∫ x, x k * Φ x y ∂(Measure.map U μ)
        = ∑ l : Fin n, (∫ ω, U ω k * U ω l ∂μ)
            * ∫ x, deriv (fun s : ℝ => Φ (Function.update x l s) y) (x l)
                ∂(Measure.map U μ) := by
  /- @proof-region region.target-node.session.c06756f3088035a4 begin -/
  intro n hn Ω _ μ _ U hU_meas hU_gauss ν' _ Φ hPhi_meas hPhi_bdd hPhi_diff hPhi_deriv_int k
  classical
  set Sig : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i j : Fin n => ∫ ω, U ω i * U ω j ∂μ) with hSig
  have hSig_apply : ∀ i j : Fin n, Sig i j = ∫ ω, U ω i * U ω j ∂μ := by
    intro i j
    rw [hSig]
    rfl
  have hSig_symm : Sig.transpose = Sig := by
    ext i j
    rw [Matrix.transpose_apply, hSig_apply, hSig_apply]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun ω => mul_comm _ _))
  set Lam : Matrix (Fin n) (Fin n) ℝ := ((2 : ℝ)⁻¹) • (Sig + Sig.transpose) with hLam
  have hLam_apply : ∀ i j : Fin n, Lam i j = ∫ ω, U ω i * U ω j ∂μ := by
    intro i j
    rw [hLam]
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, hSig_apply]
    rw [show (∫ ω, U ω j * U ω i ∂μ) = ∫ ω, U ω i * U ω j ∂μ from
      integral_congr_ae (Filter.Eventually.of_forall (fun ω => mul_comm _ _))]
    have hmul : ((2 : ℝ)⁻¹) * ((2 : ℝ) * ∫ ω, U ω i * U ω j ∂μ) = ∫ ω, U ω i * U ω j ∂μ := by
      rw [← mul_assoc, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_mul]
    calc ((2 : ℝ)⁻¹) * (∫ ω, U ω i * U ω j ∂μ + ∫ ω, U ω i * U ω j ∂μ)
        = ((2 : ℝ)⁻¹) * ((2 : ℝ) * ∫ ω, U ω i * U ω j ∂μ) := by ring
      _ = ∫ ω, U ω i * U ω j ∂μ := hmul
  have hCentered : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ U Sig := by
    refine ⟨?_, ?_, ?_⟩
    · exact measurable_pi_iff.mpr hU_meas
    · intro u
      have hf_meas : Measurable (fun ω : Ω => ∑ j : Fin n, u j * U ω j) :=
        Finset.measurable_sum Finset.univ (fun j _ => measurable_const.mul (hU_meas j))
      obtain ⟨v, hv⟩ := hU_gauss u
      have hg_meas : AEStronglyMeasurable (fun x : ℝ => Real.exp (1 * x))
          (Measure.map (fun ω : Ω => ∑ j : Fin n, u j * U ω j) μ) :=
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.aestronglyMeasurable
      have hg_int : Integrable (fun x : ℝ => Real.exp (1 * x))
          (Measure.map (fun ω : Ω => ∑ j : Fin n, u j * U ω j) μ) := by
        rw [hv]
        exact ProbabilityTheory.integrable_exp_mul_gaussianReal 1
      have hcomp := (MeasureTheory.integrable_map_measure hg_meas hf_meas.aemeasurable).mp hg_int
      simpa [Function.comp_def, one_mul] using hcomp
    · intro u
      obtain ⟨v, hv⟩ := hU_gauss u
      have hm : ∫ ω, Real.exp (∑ j : Fin n, u j * U ω j) ∂μ = Real.exp ((v : ℝ) / 2) := by
        have h1 := ProbabilityTheory.mgf_gaussianReal (p := μ)
          (X := fun ω : Ω => ∑ j : Fin n, u j * U ω j) hv 1
        simpa only [ProbabilityTheory.mgf, zero_mul, one_pow, mul_one, zero_add, one_mul] using h1
      have hvr : (v : ℝ) = ∑ i : Fin n, ∑ j : Fin n, u i * Sig i j * u j := by
        have hSqG : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) := by
          refine MeasureTheory.Integrable.mono'
            (MeasureTheory.Integrable.const_mul
              (Statlib.StatFoundation.RandomVariable.Gaussian.integrable_exp_abs_gaussianReal 0 v 1) 2)
            ((continuous_id.pow 2).measurable.aestronglyMeasurable) ?_
          filter_upwards with x
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x), one_mul]
          have h₁ : |x| ^ 2 / 2 ≤ Real.exp |x| :=
            Real.pow_div_factorial_le_exp |x| (abs_nonneg x) 2
          nlinarith [h₁, sq_abs x]
        have hmom : ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 v) = (v : ℝ) := by
          have h2 : ProbabilityTheory.variance (fun x : ℝ => x) (gaussianReal 0 v)
              = ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 v) := by
            rw [ProbabilityTheory.variance_eq_integral (X := fun x : ℝ => x)
              (μ := gaussianReal 0 v) measurable_id.aemeasurable,
              ProbabilityTheory.integral_id_gaussianReal]
            simp
          rw [← h2, ProbabilityTheory.variance_fun_id_gaussianReal]
        have hSqInt : ∀ a : Fin n → ℝ,
            Integrable (fun ω : Ω => (∑ j : Fin n, a j * U ω j) ^ 2) μ := by
          intro a
          obtain ⟨w, hw⟩ := hU_gauss a
          have hwSq : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 w) := by
            refine MeasureTheory.Integrable.mono'
              (MeasureTheory.Integrable.const_mul
                (Statlib.StatFoundation.RandomVariable.Gaussian.integrable_exp_abs_gaussianReal 0 w 1) 2)
              ((continuous_id.pow 2).measurable.aestronglyMeasurable) ?_
            filter_upwards with x
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x), one_mul]
            have h₂ : |x| ^ 2 / 2 ≤ Real.exp |x| :=
              Real.pow_div_factorial_le_exp |x| (abs_nonneg x) 2
            nlinarith [h₂, sq_abs x]
          have hfm : AEMeasurable (fun ω : Ω => ∑ j : Fin n, a j * U ω j) μ := by
            have h : Measurable (fun ω : Ω => ∑ j : Fin n, a j * U ω j) :=
              Finset.measurable_sum Finset.univ (fun j _ => measurable_const.mul (hU_meas j))
            exact h.aemeasurable
          have hsq_meas : AEStronglyMeasurable (fun x : ℝ => x ^ 2)
              (Measure.map (fun ω : Ω => ∑ j : Fin n, a j * U ω j) μ) :=
            (continuous_id.pow 2).measurable.aestronglyMeasurable
          have hmain := (MeasureTheory.integrable_map_measure hsq_meas hfm).mp (by rw [hw]; exact hwSq)
          simpa [Function.comp_def] using hmain
        have hprod_int : ∀ i j : Fin n, Integrable (fun ω : Ω => U ω i * U ω j) μ := by
          intro i j
          have hi : Integrable (fun ω : Ω => (U ω i) ^ 2) μ := by
            have h := hSqInt (Pi.single i (1 : ℝ) : Fin n → ℝ)
            have h1 : (fun ω : Ω => (∑ l : Fin n,
                (Pi.single i (1 : ℝ) : Fin n → ℝ) l * U ω l) ^ 2)
                = fun ω => (U ω i) ^ 2 := by
              funext ω
              simp [Pi.single_apply]
            rw [h1] at h
            exact h
          have hj : Integrable (fun ω : Ω => (U ω j) ^ 2) μ := by
            have h := hSqInt (Pi.single j (1 : ℝ) : Fin n → ℝ)
            have h1 : (fun ω : Ω => (∑ l : Fin n,
                (Pi.single j (1 : ℝ) : Fin n → ℝ) l * U ω l) ^ 2)
                = fun ω => (U ω j) ^ 2 := by
              funext ω
              simp [Pi.single_apply]
            rw [h1] at h
            exact h
          have hij : Integrable (fun ω : Ω => (U ω i + U ω j) ^ 2) μ := by
            have h := hSqInt (fun l : Fin n =>
              (Pi.single i (1 : ℝ) : Fin n → ℝ) l + (Pi.single j (1 : ℝ) : Fin n → ℝ) l)
            have h1 : (fun ω : Ω => (∑ l : Fin n,
                ((Pi.single i (1 : ℝ) : Fin n → ℝ) l + (Pi.single j (1 : ℝ) : Fin n → ℝ) l) * U ω l) ^ 2)
                = fun ω => (U ω i + U ω j) ^ 2 := by
              funext ω
              have hdist : (∑ l : Fin n,
                  ((Pi.single i (1 : ℝ) : Fin n → ℝ) l + (Pi.single j (1 : ℝ) : Fin n → ℝ) l) * U ω l)
                  = U ω i + U ω j := by
                rw [Finset.sum_congr rfl (fun l (_ : l ∈ Finset.univ) =>
                  add_mul ((Pi.single i (1 : ℝ) : Fin n → ℝ) l)
                    ((Pi.single j (1 : ℝ) : Fin n → ℝ) l) (U ω l))]
                rw [Finset.sum_add_distrib]
                congr 1
                · simp [Pi.single_apply]
                · simp [Pi.single_apply]
              rw [hdist]
            rw [h1] at h
            exact h
          have hdiff : Integrable (fun ω : Ω =>
              (U ω i + U ω j) ^ 2 - (U ω i) ^ 2 - (U ω j) ^ 2) μ :=
            (hij.sub hi).sub hj
          have heq : (fun ω : Ω => U ω i * U ω j)
              = fun ω => ((2 : ℝ)⁻¹) * ((U ω i + U ω j) ^ 2 - (U ω i) ^ 2 - (U ω j) ^ 2) := by
            funext ω
            field_simp
            ring
          rw [heq]
          exact MeasureTheory.Integrable.const_mul hdiff ((2 : ℝ)⁻¹)
        have hterm : ∀ i j : Fin n,
            Integrable (fun ω : Ω => (u i * U ω i) * (u j * U ω j)) μ := by
          intro i j
          have h := hprod_int i j
          have heq : (fun ω : Ω => (u i * U ω i) * (u j * U ω j))
              = fun ω => (u i * u j) * (U ω i * U ω j) := by
            funext ω
            ring
          rw [heq]
          exact MeasureTheory.Integrable.const_mul h (u i * u j)
        have hexp : ∫ ω, (∑ j : Fin n, u j * U ω j) ^ 2 ∂μ
            = ∑ i : Fin n, ∑ j : Fin n, u i * Sig i j * u j := by
          have hpt : (fun ω : Ω => (∑ j : Fin n, u j * U ω j) ^ 2)
              = fun ω => ∑ i : Fin n, ∑ j : Fin n, (u i * U ω i) * (u j * U ω j) := by
            funext ω
            rw [sq, Finset.sum_mul_sum]
          rw [hpt]
          rw [MeasureTheory.integral_finset_sum Finset.univ]
          · refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [MeasureTheory.integral_finset_sum Finset.univ]
            · refine Finset.sum_congr rfl (fun j _ => ?_)
              rw [show (fun ω : Ω => (u i * U ω i) * (u j * U ω j))
                  = fun ω => (U ω i * U ω j) * (u i * u j) from by
                funext ω
                ring]
              rw [MeasureTheory.integral_mul_const (u i * u j) (fun ω : Ω => U ω i * U ω j)]
              rw [hSig_apply i j]
              ring
            · intro j _
              exact hterm i j
          · intro i _
            exact MeasureTheory.integrable_finset_sum Finset.univ (fun j _ => hterm i j)
        have hF : AEMeasurable (fun ω : Ω => ∑ j : Fin n, u j * U ω j) μ := by
          have hfm : Measurable (fun ω : Ω => ∑ j : Fin n, u j * U ω j) :=
            Finset.measurable_sum Finset.univ (fun j _ => measurable_const.mul (hU_meas j))
          exact hfm.aemeasurable
        have hsq : AEStronglyMeasurable (fun x : ℝ => x ^ 2)
            (Measure.map (fun ω : Ω => ∑ j : Fin n, u j * U ω j) μ) :=
          (continuous_id.pow 2).measurable.aestronglyMeasurable
        rw [← hmom]
        rw [← hv]
        rw [MeasureTheory.integral_map hF hsq]
        exact hexp
      rw [hm, hvr]
  have hLambda_psd : Lam.PosSemidef := by
    rw [hLam]
    exact Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.posSemidef_symmetrizedCovariance hCentered hn
  have hPush : Measure.map U μ =
      Measure.map (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Lam)
        (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi n) := by
    rw [hLam]
    exact Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.map_eq_canonicalGaussianVector hCentered hn
  have hcv_meas : AEMeasurable
      (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Lam)
      (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi n) := by
    obtain ⟨hcvmeas, hcvint, hcvmom⟩ :=
      Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector_isCenteredGaussianVector
        (lt_of_lt_of_le Nat.zero_lt_one hn) Lam hLambda_psd
    exact hcvmeas.aemeasurable
  have hmeas1 : ∀ y : Fin n → ℝ,
      AEStronglyMeasurable (fun x : Fin n → ℝ => x k * Φ x y) (Measure.map U μ) := by
    intro y
    have hΦ : Measurable (fun x : Fin n → ℝ => Φ x y) := by
      have h1 : Measurable (fun x : Fin n → ℝ => (x, y)) :=
        Measurable.prodMk measurable_id measurable_const
      simpa [Function.comp_def] using hPhi_meas.comp h1
    exact ((measurable_pi_apply k).mul hΦ).aestronglyMeasurable
  have hmeas2 : ∀ y : Fin n → ℝ, ∀ l : Fin n, AEStronglyMeasurable (fun x : Fin n → ℝ =>
      deriv (fun s : ℝ => Φ (Function.update x l s) y) (x l)) (Measure.map U μ) := by
    intro y l
    have hderiv : (fun x : Fin n → ℝ => deriv (fun s : ℝ => Φ (Function.update x l s) y) (x l))
        = fun x => fderiv ℝ (fun z : Fin n → ℝ => Φ z y) x (Pi.single l (1 : ℝ)) := by
      funext x
      have hupd : Function.update x l (x l) = x := by
        funext i
        by_cases hi : i = l
        · subst hi
          simp
        · simp [Function.update_apply, hi]
      have hF : HasFDerivAt (fun z : Fin n → ℝ => Φ z y)
          (fderiv ℝ (fun z : Fin n → ℝ => Φ z y) x) x :=
        ((hPhi_diff y).differentiable (by decide)).differentiableAt.hasFDerivAt
      have hstep := (hupd.symm ▸ hF).comp_hasDerivAt (x l) (hasDerivAt_update x l (x l))
      simpa using hstep.deriv
    have hcont : Continuous (fun x : Fin n → ℝ =>
        fderiv ℝ (fun z : Fin n → ℝ => Φ z y) x (Pi.single l (1 : ℝ))) :=
      ((hPhi_diff y).continuous_fderiv (by decide)).clm_apply continuous_const
    rw [hderiv]
    exact hcont.measurable.aestronglyMeasurable
  have hΦy : ∀ y : Fin n → ℝ, Measurable (fun x : Fin n → ℝ => Φ x y) := by
    intro y
    have h1 : Measurable (fun x : Fin n → ℝ => (x, y)) :=
      Measurable.prodMk measurable_id measurable_const
    simpa [Function.comp_def] using hPhi_meas.comp h1
  have hint1 : ∀ y : Fin n → ℝ, ∀ j : Fin n, Integrable (fun z : Fin n → ℝ =>
      z j * Φ (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Lam z) y)
      (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi n) := by
    intro y j
    have hproj : Integrable (fun z : Fin n → ℝ => z j)
        (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi n) := by
      refine MeasureTheory.Integrable.mono'
        (MeasureTheory.Integrable.norm
          (Statlib.StatFoundation.RandomVariable.Gaussian.integrable_id_standardPi n))
        (measurable_pi_apply j).aestronglyMeasurable ?_
      filter_upwards with z
      exact norm_le_pi_norm z j
    have hbdd_meas : AEStronglyMeasurable (fun z : Fin n → ℝ =>
        Φ (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Lam z) y)
        (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi n) := by
      have h1 : AEMeasurable (fun z : Fin n → ℝ =>
          Φ (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Lam z) y)
          (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi n) := by
        have h2 := (hΦy y).comp_aemeasurable hcv_meas
        simpa [Function.comp_def] using h2
      exact h1.aestronglyMeasurable
    obtain ⟨C, hC⟩ := hPhi_bdd
    have hprod : Integrable (fun z : Fin n → ℝ =>
        Φ (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Lam z) y * z j)
        (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi n) := by
      refine MeasureTheory.Integrable.bdd_mul (c := C) hproj hbdd_meas ?_
      filter_upwards with z
      rw [Real.norm_eq_abs]
      exact hC _ _
    have hcomm : (fun z : Fin n → ℝ =>
        Φ (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Lam z) y * z j)
        = fun z => z j * Φ (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Lam z) y := by
      funext z
      exact mul_comm _ _
    rw [hcomm] at hprod
    exact hprod
  have hint2' : ∀ᵐ y ∂ν', ∀ l : Fin n, Integrable (fun x : Fin n → ℝ =>
      deriv (fun s : ℝ => Φ (Function.update x l s) y) (x l)) (Measure.map U μ) := by
    have hUm : Measurable U := measurable_pi_iff.mpr hU_meas
    haveI : IsProbabilityMeasure (Measure.map U μ) := by
      refine ⟨?_⟩
      rw [Measure.map_apply hUm MeasurableSet.univ]
      simpa using measure_univ
    exact statopia_math_node_3931290992_decd810a (μ := Measure.map U μ) (ν := ν') (ι := Fin n)
      (f := fun l x y => deriv (fun s : ℝ => Φ (Function.update x l s) y) (x l))
      hPhi_deriv_int
  have hint2 : ∀ᵐ y ∂ν', ∀ l : Fin n, Integrable (fun z : Fin n → ℝ =>
      deriv (fun s : ℝ => Φ (Function.update
        (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Lam z) l s) y)
        ((Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Lam z) l))
      (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi n) := by
    filter_upwards [hint2'] with y hy
    intro l
    have h := (MeasureTheory.integrable_map_measure (hPush ▸ hmeas2 y l) hcv_meas).mp
      (hPush ▸ hy l)
    simpa [Function.comp_def] using h
  have hgood : ∀ᵐ y ∂ν',
      (∀ j : Fin n, Integrable (fun z : Fin n → ℝ =>
        z j * Φ (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Lam z) y)
        (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi n)) ∧
      (∀ l : Fin n, Integrable (fun z : Fin n → ℝ =>
        deriv (fun s : ℝ => Φ (Function.update
          (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Lam z) l s) y)
          ((Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Lam z) l))
        (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi n)) := by
    filter_upwards [hint2] with y hy2
    exact ⟨hint1 y, hy2⟩
  filter_upwards [hgood] with y hy
  calc ∫ x, x k * Φ x y ∂(Measure.map U μ)
      = ∫ z, (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Lam z) k *
          Φ (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Lam z) y
          ∂(Statlib.StatFoundation.RandomVariable.Gaussian.standardPi n) := by
        rw [hPush]
        exact integral_map hcv_meas (hPush ▸ hmeas1 y)
    _ = ∑ l : Fin n, Lam k l *
          ∫ z, deriv (fun s : ℝ => Φ (Function.update
              (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Lam z) l s) y)
            ((Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Lam z) l)
            ∂(Statlib.StatFoundation.RandomVariable.Gaussian.standardPi n) :=
        statopia_math_node_3953135755_4b3e498f n hn Lam hLambda_psd Φ hPhi_meas hPhi_bdd
          hPhi_diff y hy.1 hy.2 k
    _ = ∑ l : Fin n, (∫ ω, U ω k * U ω l ∂μ) *
          ∫ z, deriv (fun s : ℝ => Φ (Function.update
              (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Lam z) l s) y)
            ((Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Lam z) l)
            ∂(Statlib.StatFoundation.RandomVariable.Gaussian.standardPi n) :=
        Finset.sum_congr rfl (fun l _ => by rw [hLam_apply k l])
    _ = ∑ l : Fin n, (∫ ω, U ω k * U ω l ∂μ) *
          ∫ x, deriv (fun s : ℝ => Φ (Function.update x l s) y) (x l) ∂(Measure.map U μ) := by
        refine Finset.sum_congr rfl (fun l _ => ?_)
        congr 1
        rw [hPush]
        exact (integral_map hcv_meas (hPush ▸ hmeas2 y l)).symm
  /- @proof-region region.target-node.session.c06756f3088035a4 end -/

end Statlib.Imported

