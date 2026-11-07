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
theorem statopia_math_node_343663452_95962ec5 : ∀ (p : ℕ) (hp : 1 ≤ p) (Ω : Type) [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → Fin p → ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (hZ : ∀ j : Fin p, Measurable (fun ω : Ω => Z ω j))
    (hG : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector P Z Sigma)
    (hSymm : ∀ j k : Fin p, Sigma j k = Sigma k j)
    (h2 : ∀ j k : Fin p, Integrable (fun ω : Ω => Z ω j * Z ω k) P),
    ∀ j k : Fin p, ∫ (ω : Ω), Z ω j * Z ω k ∂P = Sigma j k := by
  /- @proof-region region.target-node.session.aa9e2b41c52f49a6 begin -/
  intro p hp Ω _ P _ Z Sigma hZ hG hSymm h2 j k
  have hmoment : ∀ v : NNReal, ∫ (x : ℝ), x ^ 2 ∂(gaussianReal (0 : ℝ) v) = (v : ℝ) := by
    intro v
    have hInt : Integrable (fun x : ℝ => x ^ 2) (gaussianReal (0 : ℝ) v) :=
      MeasureTheory.memLp_one_iff_integrable.mp
        (memLp_pow_id_gaussianReal (μ₀ := (0 : ℝ)) (v := v) 2 1 (by simp))
    have hnn : ∀ᵐ x ∂(gaussianReal (0 : ℝ) v), 0 ≤ x ^ 2 :=
      Filter.Eventually.of_forall fun x => sq_nonneg x
    have hbr :=
      Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.integral_eq_lintegral_toReal_of_nonneg hnn hInt
    have hev : ProbabilityTheory.evariance (fun x : ℝ => x) (gaussianReal (0 : ℝ) v)
        = ∫⁻ (x : ℝ), ENNReal.ofReal (x ^ 2) ∂(gaussianReal (0 : ℝ) v) := by
      rw [ProbabilityTheory.evariance_eq_lintegral_ofReal]
      have h0 : ∫ (x : ℝ), x ∂(gaussianReal (0 : ℝ) v) = 0 := by
        simpa using ProbabilityTheory.integral_id_gaussianReal (μ := (0 : ℝ)) (v := v)
      rw [h0]
      simp
    have hvar : (ProbabilityTheory.evariance (fun x : ℝ => x) (gaussianReal (0 : ℝ) v)).toReal = (v : ℝ) :=
      ProbabilityTheory.variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := v)
    calc ∫ (x : ℝ), x ^ 2 ∂(gaussianReal (0 : ℝ) v)
        = (∫⁻ (x : ℝ), ENNReal.ofReal (x ^ 2) ∂(gaussianReal (0 : ℝ) v)).toReal := hbr
      _ = (ProbabilityTheory.evariance (fun x : ℝ => x) (gaussianReal (0 : ℝ) v)).toReal := by rw [hev]
      _ = (v : ℝ) := hvar
  have hPSD : Sigma.PosSemidef := by
    have h1 := hG.posSemidef_symmetrizedCovariance hp
    have heq : ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose) : Matrix (Fin p) (Fin p) ℝ) = Sigma := by
      ext a b
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
      rw [hSymm b a, ← two_mul, ← mul_assoc, inv_mul_cancel₀ two_ne_zero, one_mul]
    rwa [heq] at h1
  have hcollapse : ∀ (i : Fin p) (ω : Ω), ∑ a, (if a = i then (1 : ℝ) else 0) * Z ω a = Z ω i := by
    intro i ω
    calc ∑ a, (if a = i then (1 : ℝ) else 0) * Z ω a
        = (if i = i then (1 : ℝ) else 0) * Z ω i := by
          refine Finset.sum_eq_single i ?_ ?_
          · intro b _ hb
            simp [hb]
          · intro hmem
            exact absurd (Finset.mem_univ i) hmem
      _ = Z ω i := by simp
  have hcollapseS : ∀ s t : Fin p,
      ∑ a, ∑ b, (if a = s then (1 : ℝ) else 0) * Sigma a b * (if b = t then (1 : ℝ) else 0) = Sigma s t := by
    intro s t
    calc ∑ a, ∑ b, (if a = s then (1 : ℝ) else 0) * Sigma a b * (if b = t then (1 : ℝ) else 0)
        = ∑ b, (if s = s then (1 : ℝ) else 0) * Sigma s b * (if b = t then (1 : ℝ) else 0) := by
          refine Finset.sum_eq_single s ?_ ?_
          · intro a _ ha
            simp [ha]
          · intro hmem
            exact absurd (Finset.mem_univ s) hmem
      _ = (if s = s then (1 : ℝ) else 0) * Sigma s t * (if t = t then (1 : ℝ) else 0) := by
          refine Finset.sum_eq_single t ?_ ?_
          · intro b _ hb
            simp [hb]
          · intro hmem
            exact absurd (Finset.mem_univ t) hmem
      _ = Sigma s t := by simp
  have hsecond : ∀ u : Fin p → ℝ,
      ∫ (ω : Ω), (∑ a, u a * Z ω a) ^ 2 ∂P = ∑ a, ∑ b, u a * Sigma a b * u b := by
    intro u
    have hmap := IsCenteredGaussianVector.map_linearCombination P Z Sigma hG hPSD u
    have hmeas : Measurable (fun ω : Ω => ∑ a, u a * Z ω a) :=
      Finset.measurable_sum Finset.univ fun a _ => (hZ a).const_mul (u a)
    have hint : ∫ (x : ℝ), x ^ 2 ∂(Measure.map (fun ω : Ω => ∑ a, u a * Z ω a) P)
        = ∫ (ω : Ω), (∑ a, u a * Z ω a) ^ 2 ∂P :=
      MeasureTheory.integral_map_of_stronglyMeasurable (f := fun x : ℝ => x ^ 2) hmeas
        (continuous_pow 2).stronglyMeasurable
    rw [hmap] at hint
    rw [← hint]
    simpa using hmoment _
  have hdiag : ∀ i : Fin p, ∫ (ω : Ω), Z ω i ^ 2 ∂P = Sigma i i := by
    intro i
    have h := hsecond (fun a => if a = i then (1 : ℝ) else 0)
    simpa only [hcollapse, hcollapseS] using h
  have hpair : ∫ (ω : Ω), (Z ω j + Z ω k) ^ 2 ∂P = Sigma j j + 2 * Sigma j k + Sigma k k := by
    have h := hsecond (fun a => (if a = j then (1 : ℝ) else 0) + (if a = k then (1 : ℝ) else 0))
    have hinner : ∀ ω : Ω,
        ∑ a, ((if a = j then (1 : ℝ) else 0) + (if a = k then (1 : ℝ) else 0)) * Z ω a = Z ω j + Z ω k := by
      intro ω
      calc ∑ a, ((if a = j then (1 : ℝ) else 0) + (if a = k then (1 : ℝ) else 0)) * Z ω a
          = ∑ a, ((if a = j then (1 : ℝ) else 0) * Z ω a + (if a = k then (1 : ℝ) else 0) * Z ω a) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [add_mul]
        _ = (∑ a, (if a = j then (1 : ℝ) else 0) * Z ω a) + ∑ a, (if a = k then (1 : ℝ) else 0) * Z ω a :=
            Finset.sum_add_distrib
        _ = Z ω j + Z ω k := by rw [hcollapse j ω, hcollapse k ω]
    have hS : (∑ a, ∑ b, ((if a = j then (1 : ℝ) else 0) + (if a = k then (1 : ℝ) else 0)) * Sigma a b
          * ((if b = j then (1 : ℝ) else 0) + (if b = k then (1 : ℝ) else 0)))
        = Sigma j j + 2 * Sigma j k + Sigma k k := by
      have hexp : ∀ a b : Fin p,
          ((if a = j then (1 : ℝ) else 0) + (if a = k then (1 : ℝ) else 0)) * Sigma a b
            * ((if b = j then (1 : ℝ) else 0) + (if b = k then (1 : ℝ) else 0))
          = (if a = j then (1 : ℝ) else 0) * Sigma a b * (if b = j then (1 : ℝ) else 0)
            + (if a = j then (1 : ℝ) else 0) * Sigma a b * (if b = k then (1 : ℝ) else 0)
            + (if a = k then (1 : ℝ) else 0) * Sigma a b * (if b = j then (1 : ℝ) else 0)
            + (if a = k then (1 : ℝ) else 0) * Sigma a b * (if b = k then (1 : ℝ) else 0) := by
        intro a b
        ring
      simp only [hexp, Finset.sum_add_distrib, hcollapseS]
      rw [hSymm k j]
      ring
    simpa only [hinner, hS] using h
  have hexpand : ∫ (ω : Ω), (Z ω j + Z ω k) ^ 2 ∂P
      = ∫ (ω : Ω), Z ω j ^ 2 ∂P + 2 * ∫ (ω : Ω), Z ω j * Z ω k ∂P + ∫ (ω : Ω), Z ω k ^ 2 ∂P := by
    have hpt : ∀ ω : Ω, (Z ω j + Z ω k) ^ 2 = Z ω j ^ 2 + 2 * (Z ω j * Z ω k) + Z ω k ^ 2 :=
      fun ω => by ring
    have hZj2 : Integrable (fun ω : Ω => Z ω j ^ 2) P := by
      simpa only [pow_two] using h2 j j
    have hZk2 : Integrable (fun ω : Ω => Z ω k ^ 2) P := by
      simpa only [pow_two] using h2 k k
    have hmix2 : Integrable (fun ω : Ω => 2 * (Z ω j * Z ω k)) P := by
      simpa only [smul_eq_mul] using (h2 j k).const_mul (2 : ℝ)
    have e1 : ∫ (ω : Ω), (Z ω j + Z ω k) ^ 2 ∂P
        = ∫ (ω : Ω), Z ω j ^ 2 + 2 * (Z ω j * Z ω k) + Z ω k ^ 2 ∂P := by
      simp only [hpt]
    have e2 : ∫ (ω : Ω), Z ω j ^ 2 + 2 * (Z ω j * Z ω k) + Z ω k ^ 2 ∂P
        = (∫ (ω : Ω), Z ω j ^ 2 + 2 * (Z ω j * Z ω k) ∂P) + ∫ (ω : Ω), Z ω k ^ 2 ∂P := by
      refine integral_add ?_ ?_
      · exact hZj2.add hmix2
      · exact hZk2
    have e3 : ∫ (ω : Ω), Z ω j ^ 2 + 2 * (Z ω j * Z ω k) ∂P
        = ∫ (ω : Ω), Z ω j ^ 2 ∂P + ∫ (ω : Ω), 2 * (Z ω j * Z ω k) ∂P := by
      refine integral_add ?_ ?_
      · exact hZj2
      · exact hmix2
    have e4 : ∫ (ω : Ω), 2 * (Z ω j * Z ω k) ∂P = 2 * ∫ (ω : Ω), Z ω j * Z ω k ∂P := by
      rw [integral_const_mul]
    rw [e1, e2, e3, e4]
  have hcross : ∫ (ω : Ω), Z ω j * Z ω k ∂P = Sigma j k := by
    have h1 := hpair
    rw [hexpand, hdiag j, hdiag k] at h1
    have h2' : 2 * ∫ (ω : Ω), Z ω j * Z ω k ∂P = 2 * Sigma j k := by linarith
    exact mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) h2'
  exact hcross
  /- @proof-region region.target-node.session.aa9e2b41c52f49a6 end -/

end Statlib.Imported

