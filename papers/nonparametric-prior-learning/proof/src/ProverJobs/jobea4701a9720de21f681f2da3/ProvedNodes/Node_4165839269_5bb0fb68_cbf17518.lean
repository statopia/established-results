import ProverJobs.jobea4701a9720de21f681f2da3.Vocabulary
import ProverJobs.jobea4701a9720de21f681f2da3.Base

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
theorem statopia_math_node_4165839269_5bb0fb68 : ∀ {U : Type*} [MeasurableSpace U] (n : ℕ)
    (kap lam : Fin n → Measure U)
    (hkap_prob : ∀ i : Fin n, IsProbabilityMeasure (kap i))
    (hlam_prob : ∀ i : Fin n, IsProbabilityMeasure (lam i))
    (hac : ∀ i : Fin n, kap i ≪ lam i),
    Measure.pi kap ≪ Measure.pi lam := by
  /- @proof-region region.target-node.session.236463e174a63407 begin -/
  intro U inst n
  induction n with
  | zero =>
    intro kap lam hkap hlam hac
    haveI := hlam
    have hpi : Measure.pi lam Set.univ = 1 := by
      rw [← Set.pi_univ (Set.univ : Set (Fin 0)), Measure.pi_pi]
      exact Finset.prod_eq_one fun i _ => measure_univ
    intro s hs
    by_cases hex : ∃ x : Fin 0 → U, x ∈ s
    · obtain ⟨x, hx⟩ := hex
      have huniv : s = Set.univ :=
        Set.eq_univ_of_forall fun y => by
          have hyx : y = x := funext fun i => i.elim0
          rw [hyx]
          exact hx
      rw [huniv, hpi] at hs
      exact absurd hs one_ne_zero
    · refine measure_mono_null ?_ measure_empty
      intro y hy
      exact absurd ⟨y, hy⟩ hex
  | succ n ih =>
    intro kap lam hkap hlam hac
    haveI := hkap
    haveI := hlam
    let F : (Fin (n + 1) → U) ≃ᵐ (U × (Fin n → U)) :=
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => U) 0
    have back : ∀ (a b : Measure (Fin (n + 1) → U)),
        Measure.map (⇑F) a ≪ Measure.map (⇑F) b → a ≪ b := by
      intro a b hab s hs
      have hmeas : MeasurableSet (toMeasurable b s) := measurableSet_toMeasurable b s
      have hpre : MeasurableSet (⇑F.symm ⁻¹' toMeasurable b s) := F.symm.measurable hmeas
      have hcomp : (⇑F) ⁻¹' (⇑F.symm ⁻¹' toMeasurable b s) = toMeasurable b s := by
        ext x
        simp
      have hzero : Measure.map (⇑F) b (⇑F.symm ⁻¹' toMeasurable b s) = 0 := by
        rw [Measure.map_apply F.measurable hpre, hcomp, measure_toMeasurable]
        exact hs
      have hz2 : Measure.map (⇑F) a (⇑F.symm ⁻¹' toMeasurable b s) = 0 := hab hzero
      have hle : a s ≤ 0 := by
        calc a s ≤ a (toMeasurable b s) := measure_mono (subset_toMeasurable b s)
          _ = Measure.map (⇑F) a (⇑F.symm ⁻¹' toMeasurable b s) := by
                rw [Measure.map_apply F.measurable hpre, hcomp]
          _ = 0 := hz2
      exact le_antisymm hle (zero_le (a s))
    have htail : Measure.pi (fun j : Fin n => kap (Fin.succAbove 0 j)) ≪
        Measure.pi (fun j : Fin n => lam (Fin.succAbove 0 j)) :=
      ih _ _ (fun j => hkap (Fin.succAbove 0 j)) (fun j => hlam (Fin.succAbove 0 j))
        (fun j => hac (Fin.succAbove 0 j))
    have hprod : (kap 0).prod (Measure.pi (fun j : Fin n => kap (Fin.succAbove 0 j))) ≪
        (lam 0).prod (Measure.pi (fun j : Fin n => lam (Fin.succAbove 0 j))) :=
      MeasureTheory.Measure.AbsolutelyContinuous.prod (hac 0) htail
    have hmapac : Measure.map (⇑F) (Measure.pi kap) ≪ Measure.map (⇑F) (Measure.pi lam) := by
      rw [(measurePreserving_piFinSuccAbove (fun i : Fin (n + 1) => kap i) 0).map_eq,
        (measurePreserving_piFinSuccAbove (fun i : Fin (n + 1) => lam i) 0).map_eq]
      exact hprod
    exact back _ _ hmapac
  /- @proof-region region.target-node.session.236463e174a63407 end -/

end
end Statlib.Imported
