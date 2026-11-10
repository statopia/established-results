import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base

namespace PaperProofTasks.paper_fresh_20261108t120211266248z_prior_learning33

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261108t120211266248z_prior_learning33.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_2535765968_adf0fe99 : ∀ (F : Type) [Fintype F] (v : F → NNReal)
    (hv : ∀ k : F, v k ≠ 0) (a b : F → ℝ),
    MeasureTheory.Measure.pi (fun k : F => ProbabilityTheory.gaussianReal (b k) (v k))
      = (MeasureTheory.Measure.pi (fun k : F => ProbabilityTheory.gaussianReal (a k) (v k))).withDensity
          (fun x : F → ℝ => ENNReal.ofReal
            (Real.exp
              ((∑ k : F, ((b k - a k) * (x k - a k)) / (v k : ℝ))
                - (∑ k : F, (b k - a k) ^ 2 / (2 * (v k : ℝ)))))) := by
  /- @proof-region region.target-node.session.95a9703b90de0e6c begin -/
  intro F _ v hv a b
  have hbr : ∀ (f : (F → ℝ) → ℝ), Integrable f (Measure.pi (fun k => gaussianReal (a k) (v k))) →
      0 ≤ᵐ[Measure.pi (fun k => gaussianReal (a k) (v k))] f →
      ENNReal.ofReal (∫ x, f x ∂(Measure.pi (fun k => gaussianReal (a k) (v k)))) =
        ∫⁻ x, ENNReal.ofReal (f x) ∂(Measure.pi (fun k => gaussianReal (a k) (v k))) := by
    intro f hf h0
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf h0
  have h1d : ∀ k : F, gaussianReal (b k) (v k) = (gaussianReal (a k) (v k)).withDensity
      (fun y : ℝ => ENNReal.ofReal (Real.exp (((b k - a k) * (y - a k)) / (v k : ℝ) - (b k - a k) ^ 2 / (2 * (v k : ℝ))))) := by
    intro k
    have hvk : (v k : ℝ) ≠ 0 := by simpa using hv k
    have hq : gaussianReal (b k) (v k) = volume.withDensity (gaussianPDF (b k) (v k)) :=
      gaussianReal_of_var_ne_zero _ (hv k)
    have hp : gaussianReal (a k) (v k) = volume.withDensity (gaussianPDF (a k) (v k)) :=
      gaussianReal_of_var_ne_zero _ (hv k)
    have hφm : Measurable (fun y : ℝ => ENNReal.ofReal (Real.exp (((b k - a k) * (y - a k)) / (v k : ℝ) - (b k - a k) ^ 2 / (2 * (v k : ℝ))))) :=
      Measurable.ennreal_ofReal (by fun_prop)
    have hgm : Measurable (gaussianPDF (a k) (v k)) := by
      unfold ProbabilityTheory.gaussianPDF
      exact Measurable.ennreal_ofReal (measurable_gaussianPDFReal (a k) (v k))
    have hkey : gaussianPDF (b k) (v k) = gaussianPDF (a k) (v k) *
        (fun y : ℝ => ENNReal.ofReal (Real.exp (((b k - a k) * (y - a k)) / (v k : ℝ) - (b k - a k) ^ 2 / (2 * (v k : ℝ))))) := by
      funext y
      have hexp : Real.exp (-(y - a k) ^ 2 / (2 * (v k : ℝ))) *
          Real.exp (((b k - a k) * (y - a k)) / (v k : ℝ) - (b k - a k) ^ 2 / (2 * (v k : ℝ))) =
          Real.exp (-(y - b k) ^ 2 / (2 * (v k : ℝ))) := by
        rw [← Real.exp_add]
        congr 1
        field_simp
        ring
      have hreal : gaussianPDFReal (a k) (v k) y *
          Real.exp (((b k - a k) * (y - a k)) / (v k : ℝ) - (b k - a k) ^ 2 / (2 * (v k : ℝ))) =
          gaussianPDFReal (b k) (v k) y := by
        simp only [ProbabilityTheory.gaussianPDFReal]
        rw [mul_assoc, hexp]
      simp only [ProbabilityTheory.gaussianPDF, Pi.mul_apply]
      rw [← hreal, mul_comm (gaussianPDFReal (a k) (v k) y),
        ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _)), mul_comm]
    rw [hq, hp, hkey]
    exact MeasureTheory.withDensity_mul volume hgm hφm
  refine Measure.pi_eq (fun s hs => ?_)
  have hbox : MeasurableSet (Set.univ.pi s) := MeasurableSet.pi Set.countable_univ (fun i _ => hs i)
  have hxiff : ∀ x : F → ℝ, (x ∈ Set.univ.pi s ↔ ∀ k : F, x k ∈ s k) := fun x => by simp
  have hind : (Set.univ.pi s).indicator (fun x : F → ℝ => ENNReal.ofReal (Real.exp ((∑ k : F, ((b k - a k) * (x k - a k)) / (v k : ℝ)) - (∑ k : F, (b k - a k) ^ 2 / (2 * (v k : ℝ))))))
      = fun x : F → ℝ => ∏ k : F, (s k).indicator (fun y : ℝ => ENNReal.ofReal (Real.exp (((b k - a k) * (y - a k)) / (v k : ℝ) - (b k - a k) ^ 2 / (2 * (v k : ℝ))))) (x k) := by
    funext x
    by_cases hx : ∀ k : F, x k ∈ s k
    · rw [Set.indicator_of_mem ((hxiff x).mpr hx),
        Finset.prod_congr rfl (fun k _ => Set.indicator_of_mem (hx k) (fun y : ℝ => ENNReal.ofReal (Real.exp (((b k - a k) * (y - a k)) / (v k : ℝ) - (b k - a k) ^ 2 / (2 * (v k : ℝ))))))]
      rw [← ENNReal.ofReal_prod_of_nonneg (fun k _ => (Real.exp_pos _).le),
        ← Real.exp_sum, Finset.sum_sub_distrib]
    · rw [Set.indicator_of_notMem (fun h => hx ((hxiff x).mp h))]
      obtain ⟨k, hk⟩ := not_forall.mp hx
      have hz : (s k).indicator (fun y : ℝ => ENNReal.ofReal (Real.exp (((b k - a k) * (y - a k)) / (v k : ℝ) - (b k - a k) ^ 2 / (2 * (v k : ℝ))))) (x k) = 0 := by
        rw [Set.indicator_of_notMem hk]
      rw [Finset.prod_eq_zero_iff.mpr ⟨k, Finset.mem_univ k, hz⟩]
  rw [MeasureTheory.withDensity_apply _ hbox, ← MeasureTheory.lintegral_indicator hbox, hind]
  have hpt : ∀ x : F → ℝ, (∏ k : F, (s k).indicator (fun y : ℝ => ENNReal.ofReal (Real.exp (((b k - a k) * (y - a k)) / (v k : ℝ) - (b k - a k) ^ 2 / (2 * (v k : ℝ))))) (x k))
      = ENNReal.ofReal (∏ k : F, (s k).indicator (fun y : ℝ => Real.exp (((b k - a k) * (y - a k)) / (v k : ℝ) - (b k - a k) ^ 2 / (2 * (v k : ℝ)))) (x k)) := by
    intro x
    have hptk : ∀ k : F, (s k).indicator (fun y : ℝ => ENNReal.ofReal (Real.exp (((b k - a k) * (y - a k)) / (v k : ℝ) - (b k - a k) ^ 2 / (2 * (v k : ℝ))))) (x k)
        = ENNReal.ofReal ((s k).indicator (fun y : ℝ => Real.exp (((b k - a k) * (y - a k)) / (v k : ℝ) - (b k - a k) ^ 2 / (2 * (v k : ℝ)))) (x k)) := by
      intro k
      by_cases h : x k ∈ s k
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, ENNReal.ofReal_zero]
    rw [Finset.prod_congr rfl (fun k _ => hptk k),
      ← ENNReal.ofReal_prod_of_nonneg (fun k _ => by
        by_cases h : x k ∈ s k
        · rw [Set.indicator_of_mem h]; exact (Real.exp_pos _).le
        · simp [Set.indicator_of_notMem h])]
  have hIk : ∀ k : F, Integrable (fun y : ℝ => (s k).indicator (fun y : ℝ => Real.exp (((b k - a k) * (y - a k)) / (v k : ℝ) - (b k - a k) ^ 2 / (2 * (v k : ℝ)))) y) (gaussianReal (a k) (v k)) := by
    intro k
    have hexpint : Integrable (fun y : ℝ => Real.exp (((b k - a k) * (y - a k)) / (v k : ℝ) - (b k - a k) ^ 2 / (2 * (v k : ℝ)))) (gaussianReal (a k) (v k)) := by
      have hfun : (fun y : ℝ => Real.exp (((b k - a k) * (y - a k)) / (v k : ℝ) - (b k - a k) ^ 2 / (2 * (v k : ℝ))))
          = fun y : ℝ => Real.exp (-((b k - a k) * a k / (v k : ℝ) + (b k - a k) ^ 2 / (2 * (v k : ℝ)))) * Real.exp (((b k - a k) / (v k : ℝ)) * y) := by
        funext y
        have hvk : (v k : ℝ) ≠ 0 := by simpa using hv k
        rw [← Real.exp_add]
        congr 1
        field_simp
        ring
      rw [hfun]
      exact (ProbabilityTheory.integrable_exp_mul_gaussianReal ((b k - a k) / (v k : ℝ))).const_mul _
    exact hexpint.indicator (hs k)
  have hIprod : Integrable (fun x : F → ℝ => ∏ k : F, (s k).indicator (fun y : ℝ => Real.exp (((b k - a k) * (y - a k)) / (v k : ℝ) - (b k - a k) ^ 2 / (2 * (v k : ℝ)))) (x k)) (Measure.pi (fun k => gaussianReal (a k) (v k))) :=
    MeasureTheory.Integrable.fintype_prod hIk
  have hnn : 0 ≤ᵐ[Measure.pi (fun k => gaussianReal (a k) (v k))] fun x : F → ℝ => ∏ k : F, (s k).indicator (fun y : ℝ => Real.exp (((b k - a k) * (y - a k)) / (v k : ℝ) - (b k - a k) ^ 2 / (2 * (v k : ℝ)))) (x k) :=
    Filter.Eventually.of_forall (fun x => Finset.prod_nonneg (fun k _ => by
      by_cases h : x k ∈ s k
      · rw [Set.indicator_of_mem h]; exact (Real.exp_pos _).le
      · simp [Set.indicator_of_notMem h]))
  calc ∫⁻ x, ∏ k : F, (s k).indicator (fun y : ℝ => ENNReal.ofReal (Real.exp (((b k - a k) * (y - a k)) / (v k : ℝ) - (b k - a k) ^ 2 / (2 * (v k : ℝ))))) (x k) ∂(Measure.pi (fun k => gaussianReal (a k) (v k)))
      = ∫⁻ x, ENNReal.ofReal (∏ k : F, (s k).indicator (fun y : ℝ => Real.exp (((b k - a k) * (y - a k)) / (v k : ℝ) - (b k - a k) ^ 2 / (2 * (v k : ℝ)))) (x k)) ∂(Measure.pi (fun k => gaussianReal (a k) (v k))) := MeasureTheory.lintegral_congr hpt
    _ = ENNReal.ofReal (∫ x, ∏ k : F, (s k).indicator (fun y : ℝ => Real.exp (((b k - a k) * (y - a k)) / (v k : ℝ) - (b k - a k) ^ 2 / (2 * (v k : ℝ)))) (x k) ∂(Measure.pi (fun k => gaussianReal (a k) (v k)))) := (hbr _ hIprod hnn).symm
    _ = ENNReal.ofReal (∏ k : F, ∫ y, (s k).indicator (fun y : ℝ => Real.exp (((b k - a k) * (y - a k)) / (v k : ℝ) - (b k - a k) ^ 2 / (2 * (v k : ℝ)))) y ∂(gaussianReal (a k) (v k))) := by
        rw [MeasureTheory.integral_fintype_prod_eq_prod]
    _ = ∏ k : F, ENNReal.ofReal (∫ y, (s k).indicator (fun y : ℝ => Real.exp (((b k - a k) * (y - a k)) / (v k : ℝ) - (b k - a k) ^ 2 / (2 * (v k : ℝ)))) y ∂(gaussianReal (a k) (v k))) := by
        rw [ENNReal.ofReal_prod_of_nonneg (fun k _ => MeasureTheory.integral_nonneg (fun y => by
          by_cases h : y ∈ s k
          · rw [Set.indicator_of_mem h]; exact (Real.exp_pos _).le
          · simp [Set.indicator_of_notMem h]))]
    _ = ∏ k : F, gaussianReal (b k) (v k) (s k) := by
        refine Finset.prod_congr rfl (fun k _ => ?_)
        have h1 : ENNReal.ofReal (∫ y, (s k).indicator (fun y : ℝ => Real.exp (((b k - a k) * (y - a k)) / (v k : ℝ) - (b k - a k) ^ 2 / (2 * (v k : ℝ)))) y ∂(gaussianReal (a k) (v k)))
            = ∫⁻ y, ENNReal.ofReal ((s k).indicator (fun y : ℝ => Real.exp (((b k - a k) * (y - a k)) / (v k : ℝ) - (b k - a k) ^ 2 / (2 * (v k : ℝ)))) y) ∂(gaussianReal (a k) (v k)) :=
          MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hIk k) (Filter.Eventually.of_forall (fun y => by
            by_cases h : y ∈ s k
            · rw [Set.indicator_of_mem h]; exact (Real.exp_pos _).le
            · simp [Set.indicator_of_notMem h]))
        have h2 : ∀ y : ℝ, ENNReal.ofReal ((s k).indicator (fun y : ℝ => Real.exp (((b k - a k) * (y - a k)) / (v k : ℝ) - (b k - a k) ^ 2 / (2 * (v k : ℝ)))) y)
            = (s k).indicator (fun y : ℝ => ENNReal.ofReal (Real.exp (((b k - a k) * (y - a k)) / (v k : ℝ) - (b k - a k) ^ 2 / (2 * (v k : ℝ))))) y := by
          intro y
          by_cases h : y ∈ s k
          · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
          · simp [Set.indicator_of_notMem h]
        rw [h1, MeasureTheory.lintegral_congr h2, MeasureTheory.lintegral_indicator (hs k),
          ← MeasureTheory.withDensity_apply _ (hs k), ← h1d k]
  /- @proof-region region.target-node.session.95a9703b90de0e6c end -/

end Statlib.Imported
end

