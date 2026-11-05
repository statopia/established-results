import ProverJobs.jobea4701a9720de21f681f2da3.Vocabulary
import ProverJobs.jobea4701a9720de21f681f2da3.Base
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_4165839269_5bb0fb68_cbf17518
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
open Statlib.Imported
open Statlib.Imported.T24
open T24

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
namespace Statlib.Imported
noncomputable section
open T24

set_option autoImplicit false in
theorem statopia_math_node_224186213_92110505 : ∀ {U : Type*} [MeasurableSpace U] (n : ℕ)
    (kap lam : Fin n → Measure U)
    (hkap_prob : ∀ i : Fin n, IsProbabilityMeasure (kap i))
    (hlam_prob : ∀ i : Fin n, IsProbabilityMeasure (lam i)),
    (Measure.pi kap ≪ Measure.pi lam ↔ ∀ i : Fin n, kap i ≪ lam i) := by
  /- @proof-region region.target-node.session.5a7629fe9b6c811d begin -/
  intro U inst n kap lam hkap_prob hlam_prob
  haveI hk : ∀ i : Fin n, IsProbabilityMeasure (kap i) := hkap_prob
  haveI hl : ∀ i : Fin n, IsProbabilityMeasure (lam i) := hlam_prob
  have hbox : ∀ (i : Fin n) (μ : Fin n → Measure U) [∀ j : Fin n, IsProbabilityMeasure (μ j)]
      (t : Set U), MeasurableSet t → Measure.pi μ (Function.eval i ⁻¹' t) = μ i t := by
    intro i μ hμ t ht
    haveI := hμ
    have hmeas :
        ∀ j : Fin n, MeasurableSet ((Function.update (fun _ : Fin n => Set.univ) i t) j) := by
      intro j
      by_cases hji : j = i
      · subst hji
        simpa using ht
      · simpa [Function.update, hji] using MeasurableSet.univ
    have hpi : Measure.pi μ (Function.eval i ⁻¹' t)
        = ∏ j : Fin n, μ j ((Function.update (fun _ : Fin n => Set.univ) i t) j) := by
      rw [Set.eval_preimage]
      exact Measure.pi_pi μ (Function.update (fun _ : Fin n => Set.univ) i t)
    have hprod : (∏ j : Fin n, μ j ((Function.update (fun _ : Fin n => Set.univ) i t) j))
        = μ i ((Function.update (fun _ : Fin n => Set.univ) i t) i) := by
      refine Finset.prod_eq_single (s := Finset.univ) i ?_ ?_
      · intro j _ hji
        simp [Function.update, hji, (hμ j).measure_univ]
      · intro h
        exact absurd (Finset.mem_univ i) h
    have hsame : μ i ((Function.update (fun _ : Fin n => Set.univ) i t) i) = μ i t := by
      simp
    exact hpi.trans (hprod.trans hsame)
  constructor
  · intro hac i s hs
    have hms : MeasurableSet (toMeasurable (lam i) s) := measurableSet_toMeasurable _ _
    have hple : Measure.pi lam (Function.eval i ⁻¹' toMeasurable (lam i) s) = 0 := by
      rw [hbox i lam (toMeasurable (lam i) s) hms, measure_toMeasurable]
      exact hs
    have hpkap : Measure.pi kap (Function.eval i ⁻¹' toMeasurable (lam i) s) = 0 := hac hple
    have hkbox := hbox i kap (toMeasurable (lam i) s) hms
    rw [hkbox] at hpkap
    refine le_antisymm ?_ (zero_le _)
    exact le_trans (measure_mono (subset_toMeasurable (lam i) s)) (le_of_eq hpkap)
  · intro h
    exact statopia_math_node_4165839269_5bb0fb68 n kap lam hkap_prob hlam_prob h
  /- @proof-region region.target-node.session.5a7629fe9b6c811d end -/

end
end Statlib.Imported
