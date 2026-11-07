import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import Statlib.StatFoundation.BasicAnalysis.ENNRealBridge
import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Statlib.StatFoundation.RandomVariable.Gaussian.Standard
import Lean
import ProverJobs.paper_fresh_20261101t120354916065z_dcf.Vocabulary
import ProverJobs.paper_fresh_20261101t120354916065z_dcf.Base

namespace PaperProofTasks.paper_fresh_20261101t120354916065z_dcf

open MeasureTheory ProbabilityTheory
open Statlib.StatFoundation.RandomVariable.Gaussian
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261101t120354916065z_dcf.Statlib.Imported

open MeasureTheory ProbabilityTheory
open Statlib.StatFoundation.RandomVariable.Gaussian
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_3590859496_cde24528 : ∀ (p : ℕ) (hp : 1 ≤ p)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → Fin p → ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (hZ : ∀ j : Fin p, Measurable (fun ω => Z ω j))
    (hG : IsCenteredGaussianVector P Z Sigma)
    (hSymm : ∀ j k : Fin p, Sigma j k = Sigma k j)
    (h2 : ∀ j k : Fin p, Integrable (fun ω => Z ω j * Z ω k) P),
    (∀ j : Fin p, Integrable (fun ω => Z ω j) P) ∧
    (∀ j : Fin p, ∫ (ω : Ω), Z ω j ∂P = 0) ∧
    (∀ j : Fin p, Integrable (fun ω => Z ω j ^ 2) P) ∧
    (∀ j : Fin p, ∫ (ω : Ω), Z ω j ^ 2 ∂P = Sigma j j) ∧
    (∀ j : Fin p, Integrable (fun ω => |Z ω j| ^ 3) P) ∧
    (∀ j : Fin p, ∃ v : NNReal, (v : ℝ) = Sigma j j ∧
      Measure.map (fun ω => Z ω j) P = ProbabilityTheory.gaussianReal 0 v) ∧
    ProbabilityTheory.IsGaussian (Measure.map Z P) := by
  /- @proof-region region.target-node.session.5f37d35c1ebc80ed begin -/
  intro p hp Ω _ P _ Z Sigma hZ hG hSymm h2
  have hSigma : Sigma.PosSemidef := by
    have h1 := hG.posSemidef_symmetrizedCovariance hp
    have hmat : ((2⁻¹ : ℝ) • (Sigma + Sigma.transpose)) = Sigma := by
      ext a b
      simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
      rw [hSymm b a, ← two_mul, ← mul_assoc, inv_mul_cancel₀ (by norm_num : (2:ℝ) ≠ 0), one_mul]
    exact hmat ▸ h1
  have hmarg : ∀ j : Fin p, ∃ v : NNReal, (v : ℝ) = Sigma j j ∧
      Measure.map (fun ω => Z ω j) P = ProbabilityTheory.gaussianReal 0 v := by
    intro j
    let u : Fin p → ℝ := fun k => if k = j then 1 else 0
    have hsum : (fun ω => ∑ k, u k * Z ω k) = (fun ω => Z ω j) := by
      funext ω
      simp [u]
    have hquad : (∑ i, ∑ k, u i * Sigma i k * u k) = Sigma j j := by
      simp [u]
    have hlaw := hG.map_linearCombination P Z Sigma hSigma u
    rw [hsum] at hlaw
    obtain ⟨v, hvdef, hvm⟩ : ∃ v : NNReal, (v : ℝ) = ∑ i, ∑ k, u i * Sigma i k * u k ∧
        Measure.map (fun ω => Z ω j) P = gaussianReal 0 v := ⟨_, rfl, hlaw⟩
    exact ⟨v, hvdef.trans hquad, hvm⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, hmarg, ?_⟩
  · intro j
    have hg : Integrable (fun ω => 1 + Z ω j ^ 2) P :=
      (integrable_const (1 : ℝ)).add (by simpa [pow_two] using h2 j j)
    refine hg.mono' (hZ j).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (|Z ω j| - 1), abs_nonneg (Z ω j), sq_abs (Z ω j)]
  · intro j
    obtain ⟨v, hvdef, hvm⟩ := hmarg j
    have htr : ∫ (y : ℝ), y ∂Measure.map (fun ω => Z ω j) P = ∫ (ω : Ω), Z ω j ∂P :=
      MeasureTheory.integral_map_of_stronglyMeasurable (μ := P) (φ := fun ω => Z ω j) (hZ j)
        (f := fun y : ℝ => y) measurable_id.stronglyMeasurable
    rw [← htr, hvm]
    simpa using ProbabilityTheory.integral_id_gaussianReal (μ := (0:ℝ)) (v := v)
  · intro j
    simpa [pow_two] using h2 j j
  · intro j
    obtain ⟨v, hvdef, hvm⟩ := hmarg j
    have htr : ∫ (y : ℝ), y ^ 2 ∂Measure.map (fun ω => Z ω j) P = ∫ (ω : Ω), Z ω j ^ 2 ∂P :=
      MeasureTheory.integral_map_of_stronglyMeasurable (μ := P) (φ := fun ω => Z ω j) (hZ j)
        (f := fun y : ℝ => y ^ 2)
        (by simpa [pow_two] using (measurable_id.mul measurable_id).stronglyMeasurable)
    have hmon : ∫ (y : ℝ), y ^ 2 ∂gaussianReal 0 v = (v : ℝ) := by
      have hInt : Integrable (fun y : ℝ => y ^ 2) (gaussianReal 0 v) :=
        MeasureTheory.memLp_one_iff_integrable.mp
          (memLp_pow_id_gaussianReal (μ₀ := (0 : ℝ)) (v := v) 2 1 ENNReal.one_ne_top)
      have hnn : 0 ≤ᶠ[ae (gaussianReal 0 v)] (fun y : ℝ => y ^ 2) := by
        filter_upwards with y
        exact sq_nonneg y
      calc ∫ (y : ℝ), y ^ 2 ∂gaussianReal 0 v
          = (∫⁻ (y : ℝ), ENNReal.ofReal (y ^ 2) ∂gaussianReal 0 v).toReal :=
            Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.integral_eq_lintegral_toReal_of_nonneg hnn hInt
        _ = (eVar[id; gaussianReal 0 v]).toReal := by
            rw [ProbabilityTheory.evariance_eq_lintegral_ofReal]
            simp [ProbabilityTheory.integral_id_gaussianReal]
        _ = (v : ℝ) := ProbabilityTheory.variance_id_gaussianReal (μ := (0 : ℝ)) (v := v)
    rw [← htr, hvm, hmon, hvdef]
  · intro j
    obtain ⟨v, hvdef, hvm⟩ := hmarg j
    haveI : IsGaussian (gaussianReal 0 v) := isGaussian_gaussianReal 0 v
    have hsrc : MemLp (fun x : ℝ => x) 3 (gaussianReal 0 v) :=
      IsGaussian.memLp_id (gaussianReal 0 v) 3 (by norm_num)
    have hmap : MemLp (fun x : ℝ => x) 3 (Measure.map (fun ω => Z ω j) P) := by
      rw [hvm]
      exact hsrc
    have hcomp : MemLp (fun ω => Z ω j) 3 P := hmap.comp_of_map (hZ j).aemeasurable
    have h3 := hcomp.integrable_norm_pow (p := 3) (by norm_num)
    simpa [Real.norm_eq_abs] using h3
  · exact hG.pushforward_isGaussian P Z Sigma hSigma
  /- @proof-region region.target-node.session.5f37d35c1ebc80ed end -/

end Statlib.Imported

