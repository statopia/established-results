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
theorem statopia_math_node_1861729969_f0cb78c5 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {p : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (Y : Ω → Fin p → ℝ)
    (hY : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector P Y Sigma)
    (hSigma : Sigma.PosSemidef),
    ∀ j k : Fin p, ∫ ω, Y ω j * Y ω k ∂P = Sigma j k := by
  /- @proof-region region.target-node.session.ec34f8523ce8c62c begin -/
  intro Ω hΩ P hP p Sigma Y hY hSigma j k
  have hsq : ∀ v : NNReal, ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 v) = (v : ℝ) := by
    intro v
    have h := ProbabilityTheory.variance_fun_id_gaussianReal (μ := 0) (v := v)
    simp only [ProbabilityTheory.variance, evariance, ProbabilityTheory.integral_id_gaussianReal,
      sub_zero] at h
    have hML : MemLp (fun x : ℝ => x ^ 2) 2 (gaussianReal 0 v) :=
      Statlib.StatFoundation.RandomVariable.Gaussian.memLp_pow_id_gaussianReal (v := v) 2 2
        (by norm_num)
    have hnn : 0 ≤ᵐ[gaussianReal 0 v] fun x : ℝ => x ^ 2 := by
      filter_upwards with x
      positivity
    rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnn hML.aestronglyMeasurable]
    have hpt : ∀ x : ℝ, ENNReal.ofReal (x ^ 2) = (enorm x) ^ 2 := by
      intro x
      have hc : ((‖x‖₊ : NNReal) : ℝ) = ‖x‖ := rfl
      have hsq3 : ((‖x‖₊ * ‖x‖₊ : NNReal) : ℝ) = x * x := by
        rw [NNReal.coe_mul, hc, Real.norm_eq_abs, ← pow_two, sq_abs, pow_two]
      have hp : ((‖x‖₊ : NNReal) : ℝ≥0∞) ^ 2 = ((‖x‖₊ * ‖x‖₊ : NNReal) : ℝ≥0∞) := by
        rw [pow_two, ← ENNReal.coe_mul]
      rw [show (enorm x) = ((‖x‖₊ : NNReal) : ℝ≥0∞) from rfl, hp,
        ← ENNReal.ofReal_coe_nnreal, hsq3, pow_two]
    simp only [hpt]
    exact h
  haveI hGauss : IsGaussian (Measure.map Y P) := hY.pushforward_isGaussian P Y Sigma hSigma
  have hmemLp : ∀ i : Fin p, MemLp (fun ω => Y ω i) 2 P := by
    intro i
    have h2 : MemLp Y 2 P :=
      (ProbabilityTheory.IsGaussian.memLp_two_fun_id (μ := Measure.map Y P)).comp_of_map
        hY.measurable.aemeasurable
    exact MeasureTheory.memLp_pi_iff.mp h2 i
  have hkey : ∀ u : Fin p → ℝ,
      ∫ ω, (∑ m, u m * Y ω m) ^ 2 ∂P = ∑ a, ∑ b, u a * Sigma a b * u b := by
    intro u
    have hmap := hY.map_linearCombination P Y Sigma hSigma u
    have hmeasM : Measurable (fun ω => ∑ m, u m * Y ω m) :=
      Finset.measurable_sum Finset.univ
        (fun m _ => measurable_const.mul (hY.measurable.eval (a := m)))
    have hIm : ∫ y : ℝ, y ^ 2 ∂(Measure.map (fun ω => ∑ m, u m * Y ω m) P)
        = ∫ ω, (∑ m, u m * Y ω m) ^ 2 ∂P :=
      MeasureTheory.integral_map hmeasM.aemeasurable
        ((by fun_prop : Measurable fun y : ℝ => y ^ 2).aestronglyMeasurable)
    rw [← hIm, hmap]
    exact hsq _
  set uj : Fin p → ℝ := Pi.single j (1 : ℝ) with huj
  set uk : Fin p → ℝ := Pi.single k (1 : ℝ) with huk
  have hj : ∀ ω : Ω, ∑ m, uj m * Y ω m = Y ω j := by
    intro ω
    rw [Finset.sum_eq_single j (fun b _ hb => by simp [huj, hb, Ne.symm hb])
      (fun hmem => absurd (Finset.mem_univ j) hmem)]
    simp [huj]
  have hk : ∀ ω : Ω, ∑ m, uk m * Y ω m = Y ω k := by
    intro ω
    rw [Finset.sum_eq_single k (fun b _ hb => by simp [huk, hb, Ne.symm hb])
      (fun hmem => absurd (Finset.mem_univ k) hmem)]
    simp [huk]
  have hsplit : ∀ (ω : Ω) (m : Fin p),
      (uj + uk) m * Y ω m = uj m * Y ω m + uk m * Y ω m := by
    intro ω m
    rw [Pi.add_apply, add_mul]
  have hjk : ∀ ω : Ω, ∑ m, (uj + uk) m * Y ω m = Y ω j + Y ω k := by
    intro ω
    simp only [hsplit ω, Finset.sum_add_distrib, hj, hk]
  have hQj : ∑ a, ∑ b, uj a * Sigma a b * uj b = Sigma j j := by
    have hinner : ∀ a : Fin p, (∑ b, uj a * Sigma a b * uj b) = uj a * Sigma a j * uj j := by
      intro a
      exact Finset.sum_eq_single j (fun b _ hb => by simp [huj, hb, Ne.symm hb])
        (fun hmem => absurd (Finset.mem_univ j) hmem)
    simp only [hinner]
    rw [Finset.sum_eq_single j (fun b _ hb => by simp [huj, hb, Ne.symm hb])
      (fun hmem => absurd (Finset.mem_univ j) hmem)]
    simp [huj]
  have hQk : ∑ a, ∑ b, uk a * Sigma a b * uk b = Sigma k k := by
    have hinner : ∀ a : Fin p, (∑ b, uk a * Sigma a b * uk b) = uk a * Sigma a k * uk k := by
      intro a
      exact Finset.sum_eq_single k (fun b _ hb => by simp [huk, hb, Ne.symm hb])
        (fun hmem => absurd (Finset.mem_univ k) hmem)
    simp only [hinner]
    rw [Finset.sum_eq_single k (fun b _ hb => by simp [huk, hb, Ne.symm hb])
      (fun hmem => absurd (Finset.mem_univ k) hmem)]
    simp [huk]
  have hBjk : ∑ a, ∑ b, uj a * Sigma a b * uk b = Sigma j k := by
    have hinner : ∀ a : Fin p, (∑ b, uj a * Sigma a b * uk b) = uj a * Sigma a k * uk k := by
      intro a
      exact Finset.sum_eq_single k (fun b _ hb => by simp [huk, hb, Ne.symm hb])
        (fun hmem => absurd (Finset.mem_univ k) hmem)
    simp only [hinner]
    rw [Finset.sum_eq_single j (fun b _ hb => by simp [huj, hb, Ne.symm hb])
      (fun hmem => absurd (Finset.mem_univ j) hmem)]
    simp [huj, huk]
  have hBkj : ∑ a, ∑ b, uk a * Sigma a b * uj b = Sigma k j := by
    have hinner : ∀ a : Fin p, (∑ b, uk a * Sigma a b * uj b) = uk a * Sigma a j * uj j := by
      intro a
      exact Finset.sum_eq_single j (fun b _ hb => by simp [huj, hb, Ne.symm hb])
        (fun hmem => absurd (Finset.mem_univ j) hmem)
    simp only [hinner]
    rw [Finset.sum_eq_single k (fun b _ hb => by simp [huk, hb, Ne.symm hb])
      (fun hmem => absurd (Finset.mem_univ k) hmem)]
    simp [huj, huk]
  have hQjk : ∑ a, ∑ b, (uj + uk) a * Sigma a b * (uj + uk) b
      = Sigma j j + Sigma j k + Sigma k j + Sigma k k := by
    have hpt2 : ∀ a b : Fin p, (uj + uk) a * Sigma a b * (uj + uk) b
        = uj a * Sigma a b * uj b + uj a * Sigma a b * uk b
          + uk a * Sigma a b * uj b + uk a * Sigma a b * uk b := by
      intro a b
      rw [Pi.add_apply, Pi.add_apply]
      ring
    simp only [hpt2, Finset.sum_add_distrib, hQj, hBjk, hBkj, hQk]
  have hint_j : Integrable (fun ω => Y ω j ^ 2) P := (hmemLp j).integrable_sq
  have hint_k : Integrable (fun ω => Y ω k ^ 2) P := (hmemLp k).integrable_sq
  have hint_jk : Integrable (fun ω => Y ω j * Y ω k) P := (hmemLp j).integrable_mul (hmemLp k)
  have Ij : ∫ ω, Y ω j ^ 2 ∂P = Sigma j j := by
    have h := hkey uj
    simp only [hj, hQj] at h
    exact h
  have Ik : ∫ ω, Y ω k ^ 2 ∂P = Sigma k k := by
    have h := hkey uk
    simp only [hk, hQk] at h
    exact h
  have Ijk : ∫ ω, (Y ω j + Y ω k) ^ 2 ∂P = Sigma j j + Sigma j k + Sigma k j + Sigma k k := by
    have h := hkey (uj + uk)
    simp only [hjk, hQjk] at h
    exact h
  have hexp : ∫ ω, (Y ω j + Y ω k) ^ 2 ∂P
      = ∫ ω, Y ω j ^ 2 ∂P + 2 * ∫ ω, Y ω j * Y ω k ∂P + ∫ ω, Y ω k ^ 2 ∂P := by
    have hpt3 : ∀ ω : Ω, (Y ω j + Y ω k) ^ 2
        = Y ω j ^ 2 + 2 * (Y ω j * Y ω k) + Y ω k ^ 2 := by
      intro ω
      ring
    have h1 : ∫ ω, (Y ω j ^ 2 + 2 * (Y ω j * Y ω k)) + Y ω k ^ 2 ∂P
        = ∫ ω, (Y ω j ^ 2 + 2 * (Y ω j * Y ω k)) ∂P + ∫ ω, Y ω k ^ 2 ∂P :=
      MeasureTheory.integral_add (hint_j.add (hint_jk.const_mul 2)) hint_k
    have h2 : ∫ ω, Y ω j ^ 2 + 2 * (Y ω j * Y ω k) ∂P
        = ∫ ω, Y ω j ^ 2 ∂P + ∫ ω, 2 * (Y ω j * Y ω k) ∂P :=
      MeasureTheory.integral_add hint_j (hint_jk.const_mul 2)
    have h3 : ∫ ω, 2 * (Y ω j * Y ω k) ∂P = 2 * ∫ ω, Y ω j * Y ω k ∂P := by
      have hp : ∀ ω : Ω, 2 * (Y ω j * Y ω k) = Y ω j * Y ω k + Y ω j * Y ω k := by
        intro ω
        ring
      have key : ∫ ω, Y ω j * Y ω k + Y ω j * Y ω k ∂P
          = ∫ ω, Y ω j * Y ω k ∂P + ∫ ω, Y ω j * Y ω k ∂P :=
        MeasureTheory.integral_add hint_jk hint_jk
      rw [show (fun ω => 2 * (Y ω j * Y ω k))
          = (fun ω => Y ω j * Y ω k + Y ω j * Y ω k) from funext hp]
      rw [key]
      ring
    simp only [hpt3]
    rw [h1, h2, h3]
  have hsymm : Sigma j k = Sigma k j := by
    have h' : Matrix.conjTranspose Sigma = Sigma := hSigma.isHermitian
    have h2 : star (Sigma j k) = Sigma k j := by
      rw [← Matrix.conjTranspose_apply]
      exact congrFun (congrFun h' k) j
    simpa using h2
  linarith [Ijk, hexp, Ij, Ik, hsymm]
  /- @proof-region region.target-node.session.ec34f8523ce8c62c end -/

end

end Statlib.Imported

