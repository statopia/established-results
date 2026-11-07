import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
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
theorem statopia_math_node_2024687868_9ec8273d : ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℕ) (hp : 1 ≤ p) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (U : Ω → Fin p → ℝ) (hUmeas : Measurable U)
    (hU : IsCenteredGaussianVector P U Sigma)
    (b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hbc : b ^ 2 + c ^ 2 = d ^ 2),
    Measure.map
        (fun q : (Fin p → ℝ) × (Fin p → ℝ) => fun j : Fin p => b * q.1 j + c * q.2 j)
        ((Measure.map U P).prod (Measure.map U P))
      = Measure.map (fun g : Fin p → ℝ => fun j : Fin p => d * g j) (Measure.map U P) := by
  /- @proof-region region.target-node.session.d941d4b56d353774 begin -/
  intro Ω _ P _ p hp Sigma U hUmeas hU b c d hb hc hd hbc
  let Z : Ω × Ω → Fin p → ℝ := fun x j => b * U x.1 j + c * U x.2 j
  have hpair_meas : Measurable fun x : Ω × Ω => (U x.1, U x.2) := by
    measurability
  have hT_meas : Measurable fun q : (Fin p → ℝ) × (Fin p → ℝ) => fun j : Fin p => b * q.1 j + c * q.2 j := by
    measurability
  have hsc_meas : Measurable fun g : Fin p → ℝ => fun j : Fin p => d * g j := by
    measurability
  have hleft :
      Measure.map (fun q : (Fin p → ℝ) × (Fin p → ℝ) => fun j : Fin p => b * q.1 j + c * q.2 j)
          ((Measure.map U P).prod (Measure.map U P))
        = Measure.map Z (P.prod P) := by
    rw [Measure.map_prod_map (μa := P) (μc := P) (hf := hUmeas) (hg := hUmeas)]
    rw [Measure.map_map (f := Prod.map U U)
      (g := fun q : (Fin p → ℝ) × (Fin p → ℝ) => fun j : Fin p => b * q.1 j + c * q.2 j)
      (μ := P.prod P) (hg := hT_meas) (hf := hpair_meas)]
    rfl
  have hright :
      Measure.map (fun g : Fin p → ℝ => fun j : Fin p => d * g j) (Measure.map U P)
        = Measure.map (fun ω j => d * U ω j) P := by
    rw [Measure.map_map (f := U) (g := fun g : Fin p → ℝ => fun j : Fin p => d * g j) (μ := P)
      (hg := hsc_meas) (hf := hUmeas)]
    rfl
  have hdU : IsCenteredGaussianVector P (fun ω j => d * U ω j) (d ^ 2 • Sigma) := by
    have h0 :=
      IsCenteredGaussianVector.linearImage P U Sigma hU (d • (1 : Matrix (Fin p) (Fin p) ℝ))
    have hmat :
        (d • (1 : Matrix (Fin p) (Fin p) ℝ)) * Sigma
            * (d • (1 : Matrix (Fin p) (Fin p) ℝ)).transpose
          = d ^ 2 • Sigma := by
      rw [Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul,
        Matrix.mul_smul, Matrix.mul_one, smul_smul, pow_two]
    rw [hmat] at h0
    simpa only [Matrix.smul_mulVec, Matrix.one_mulVec] using h0
  have hZ : IsCenteredGaussianVector (P.prod P) Z (d ^ 2 • Sigma) := by
    have hsplit :
        ∀ (u : Fin p → ℝ) (x : Ω × Ω),
          (∑ j, u j * Z x j)
            = (∑ j, (b * u j) * U x.1 j) + (∑ j, (c * u j) * U x.2 j) := by
      intro u x
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hQ :
        ∀ (t : ℝ) (u : Fin p → ℝ),
          (∑ i, ∑ j, (t * u i) * Sigma i j * (t * u j))
            = t ^ 2 * (∑ i, ∑ j, u i * Sigma i j * u j) := by
      intro t u
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hQd :
        ∀ u : Fin p → ℝ,
          (∑ i, ∑ j, u i * (d ^ 2 • Sigma) i j * u j)
            = d ^ 2 * (∑ i, ∑ j, u i * Sigma i j * u j) := by
      intro u
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Matrix.smul_apply, smul_eq_mul]
      ring
    refine ⟨?_, ?_, ?_⟩
    · measurability
    · intro u
      have hfac :
          Integrable (fun x : Ω × Ω => Real.exp (∑ j, (b * u j) * U x.1 j)
            * Real.exp (∑ j, (c * u j) * U x.2 j)) (P.prod P) :=
        MeasureTheory.Integrable.mul_prod (hU.integrable_exp (fun j => b * u j))
          (hU.integrable_exp (fun j => c * u j))
      refine MeasureTheory.Integrable.congr hfac ?_
      filter_upwards with x
      rw [← Real.exp_add, hsplit u x]
    · intro u
      have hb_eq :
          ∫ y, Real.exp (∑ j, (b * u j) * U y j) ∂P
            = Real.exp ((∑ i, ∑ j, (b * u i) * Sigma i j * (b * u j)) / 2) := by
        simpa only [] using hU.mgf_eq (fun j => b * u j)
      have hc_eq :
          ∫ y, Real.exp (∑ j, (c * u j) * U y j) ∂P
            = Real.exp ((∑ i, ∑ j, (c * u i) * Sigma i j * (c * u j)) / 2) := by
        simpa only [] using hU.mgf_eq (fun j => c * u j)
      have hexp :
          ∀ x : Ω × Ω,
            Real.exp (∑ j, u j * Z x j)
              = Real.exp (∑ j, (b * u j) * U x.1 j)
                * Real.exp (∑ j, (c * u j) * U x.2 j) := by
        intro x
        rw [hsplit u x, Real.exp_add]
      calc
        ∫ x : Ω × Ω, Real.exp (∑ j, u j * Z x j) ∂(P.prod P)
            = ∫ x : Ω × Ω,
                Real.exp (∑ j, (b * u j) * U x.1 j)
                  * Real.exp (∑ j, (c * u j) * U x.2 j) ∂(P.prod P) := by
              simp only [hexp]
        _ = (∫ y, Real.exp (∑ j, (b * u j) * U y j) ∂P)
              * (∫ y, Real.exp (∑ j, (c * u j) * U y j) ∂P) :=
              MeasureTheory.integral_prod_mul
                (f := fun y : Ω => Real.exp (∑ j, (b * u j) * U y j))
                (g := fun y : Ω => Real.exp (∑ j, (c * u j) * U y j))
        _ = Real.exp ((∑ i, ∑ j, (b * u i) * Sigma i j * (b * u j)) / 2)
              * Real.exp ((∑ i, ∑ j, (c * u i) * Sigma i j * (c * u j)) / 2) := by
              rw [hb_eq, hc_eq]
        _ = Real.exp ((∑ i, ∑ j, u i * (d ^ 2 • Sigma) i j * u j) / 2) := by
              rw [← Real.exp_add, hQ b u, hQ c u, hQd u, ← hbc]
              congr 1
              ring
  have h1 := hZ.map_eq_canonicalGaussianVector hp
  have h2 := hdU.map_eq_canonicalGaussianVector hp
  exact hleft.trans (h1.trans (h2.symm.trans hright.symm))
  /- @proof-region region.target-node.session.d941d4b56d353774 end -/

end

end Statlib.Imported

