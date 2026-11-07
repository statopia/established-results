import Statlib.HighDim.MatrixAnalysis.AndoVocabulary
import Statlib.StatFoundation.BasicAnalysis.ENNRealBridge
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Statlib.StatFoundation.RandomVariable.Gaussian.Standard
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base

namespace PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Statlib.StatFoundation.RandomVariable.Gaussian
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Statlib.StatFoundation.RandomVariable.Gaussian
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_4215527874_039d8d35 : ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {m : ℕ} (Sigma : Matrix (Fin m) (Fin m) ℝ) (X : Ω → Fin m → ℝ)
    (hX : ∀ j : Fin m, Measurable (fun ω => X ω j))
    (hGauss : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector P X Sigma)
    (hm : 1 ≤ m) (u : Fin m → ℝ),
    ∫ ω, (∑ j, u j * X ω j) ^ 2 ∂P =
      ∑ a, ∑ b, u a * (((2 : ℝ)⁻¹) • (Sigma + Sigma.transpose)) a b * u b := by
  /- @proof-region region.target-node.session.9e1e3c495abb2c60 begin -/
  intro Ω _inst P _instP m Sigma X hX hGauss hm u
  let S : Matrix (Fin m) (Fin m) ℝ := (2⁻¹ : ℝ) • (Sigma + Sigma.transpose)
  have hPSD : S.PosSemidef := IsCenteredGaussianVector.posSemidef_symmetrizedCovariance hGauss hm
  have hne : 0 < m := by omega
  haveI : IsProbabilityMeasure (standardPi m) := Slepian.standardPi_probability m
  have hcanon : IsCenteredGaussianVector (standardPi m) (Slepian.canonicalGaussianVector S) S :=
    Slepian.canonicalGaussianVector_isCenteredGaussianVector hne S hPSD
  have hmap : Measure.map X P = Measure.map (Slepian.canonicalGaussianVector S) (standardPi m) :=
    IsCenteredGaussianVector.map_eq_canonicalGaussianVector hGauss hm
  have hX_meas : Measurable X := measurable_pi_iff.mpr hX
  have hcanon_meas : Measurable (Slepian.canonicalGaussianVector S) := by
    rw [measurable_pi_iff]
    intro i
    have key : (fun z : Fin m → ℝ => Slepian.canonicalGaussianVector S z i) =
        (fun z : Fin m → ℝ =>
          ∑ j, (CFC.sqrt S).mulVec (fun k => if k = i then (1 : ℝ) else 0) j * z j) := by
      funext z
      have h := Slepian.canonicalGaussianVector_linearCombination S hPSD
        (fun k => if k = i then (1 : ℝ) else 0) z
      simp only [ite_mul, one_mul, zero_mul] at h
      have h3 := Finset.sum_eq_single (s := Finset.univ)
          (f := fun x => if x = i then Slepian.canonicalGaussianVector S z x else 0) i
          (fun b _ hb => by simp only [if_neg hb])
          (fun hi => absurd (Finset.mem_univ i) hi)
      have h2 : (∑ x, if x = i then Slepian.canonicalGaussianVector S z x else 0)
          = Slepian.canonicalGaussianVector S z i := by
        simpa using h3
      rw [h2] at h
      exact h
    rw [key]
    apply Finset.measurable_sum
    intro j _
    exact Measurable.const_mul (measurable_pi_apply j) _
  have hg_meas : Measurable (fun y : Fin m → ℝ => ∑ j, u j * y j) := by
    measurability
  have hZ_meas : Measurable (fun ω : Ω => ∑ j, u j * X ω j) := by
    apply Finset.measurable_sum
    intro j _
    exact Measurable.const_mul (hX j) (u j)
  have hQ : 0 ≤ ∑ i, ∑ j, u i * S i j * u j := by
    rw [← Slepian.canonicalGaussianVector_quadratic S hPSD u]
    exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
  let q : NNReal := ⟨∑ i, ∑ j, u i * S i j * u j, hQ⟩
  have hmap_lc :
      Measure.map (fun y : Fin m → ℝ => ∑ j, u j * Slepian.canonicalGaussianVector S y j)
          (standardPi m) = gaussianReal 0 q :=
    (IsCenteredGaussianVector.map_linearCombination (standardPi m)
      (Slepian.canonicalGaussianVector S) S hcanon hPSD u).trans
      (congrArg (gaussianReal 0) (Subtype.ext rfl))
  have hdist :
      Measure.map (fun ω : Ω => ∑ j, u j * X ω j) P = gaussianReal 0 q := by
    calc Measure.map (fun ω : Ω => ∑ j, u j * X ω j) P
        = Measure.map (fun y : Fin m → ℝ => ∑ j, u j * y j) (Measure.map X P) := by
            rw [Measure.map_map hg_meas hX_meas]; rfl
      _ = Measure.map (fun y : Fin m → ℝ => ∑ j, u j * y j)
            (Measure.map (Slepian.canonicalGaussianVector S) (standardPi m)) := by rw [hmap]
      _ = Measure.map (fun y : Fin m → ℝ => ∑ j, u j * Slepian.canonicalGaussianVector S y j)
            (standardPi m) := by
            rw [Measure.map_map hg_meas hcanon_meas]; rfl
      _ = gaussianReal 0 q := hmap_lc
  have hsq : ∫ x : ℝ, x ^ 2 ∂(gaussianReal (0 : ℝ) q) = (q : ℝ) := by
    have hint : Integrable (fun x : ℝ => x ^ 2) (gaussianReal (0 : ℝ) q) :=
      MeasureTheory.memLp_one_iff_integrable.mp
        (Statlib.StatFoundation.RandomVariable.Gaussian.memLp_pow_id_gaussianReal 2 1 (by simp))
    have hnn : 0 ≤ᵐ[gaussianReal (0 : ℝ) q] (fun x : ℝ => x ^ 2) :=
      Filter.Eventually.of_forall (fun x => sq_nonneg x)
    have h1 : (∫⁻ x : ℝ, ENNReal.ofReal (x ^ 2) ∂(gaussianReal (0 : ℝ) q)).toReal
        = ∫ x : ℝ, x ^ 2 ∂(gaussianReal (0 : ℝ) q) :=
      Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.lintegral_toReal_eq_integral_of_nonneg hnn hint
    rw [← h1]
    have hvar := ProbabilityTheory.variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := q)
    unfold ProbabilityTheory.variance at hvar
    rw [ProbabilityTheory.evariance_eq_lintegral_ofReal] at hvar
    simp only [ProbabilityTheory.integral_id_gaussianReal, sub_zero] at hvar
    exact hvar
  have hintegral :
      ∫ ω, (∑ j, u j * X ω j) ^ 2 ∂P = ∫ x : ℝ, x ^ 2 ∂(gaussianReal (0 : ℝ) q) := by
    rw [← hdist]
    exact (MeasureTheory.integral_map (f := fun x : ℝ => x ^ 2)
      (φ := fun ω => ∑ j, u j * X ω j) hZ_meas.aemeasurable (by measurability)).symm
  rw [hintegral, hsq]
  rfl
  /- @proof-region region.target-node.session.9e1e3c495abb2c60 end -/

end

end Statlib.Imported

