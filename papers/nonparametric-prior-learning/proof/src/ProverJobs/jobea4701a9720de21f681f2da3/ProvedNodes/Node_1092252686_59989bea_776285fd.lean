import ProverJobs.jobea4701a9720de21f681f2da3.Vocabulary
import ProverJobs.jobea4701a9720de21f681f2da3.Base
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_315826285_30cc4431_c46d0e4c
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_980129684_7aca482a_b9568c94

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
theorem statopia_math_node_1092252686_59989bea : ∀ {U : Type*} [MeasurableSpace U] (n : ℕ) (kap lam : Fin n → Measure U)
    (hkap : ∀ i : Fin n, IsProbabilityMeasure (kap i))
    (hlam : ∀ i : Fin n, IsProbabilityMeasure (lam i))
    (hac : ∀ i : Fin n, kap i ≪ lam i)
    (hprod : (Measure.pi lam).withDensity
      (fun u : Fin n → U => ∏ i : Fin n, (kap i).rnDeriv (lam i) (u i)) = Measure.pi kap),
    (llr (Measure.pi kap) (Measure.pi lam) =ᵐ[Measure.pi kap]
        (fun u : Fin n → U => ∑ i : Fin n, llr (kap i) (lam i) (u i)))
      ∧ (Integrable (llr (Measure.pi kap) (Measure.pi lam)) (Measure.pi kap)
          ↔ ∀ i : Fin n, Integrable (llr (kap i) (lam i)) (kap i))
      ∧ ((∀ i : Fin n, Integrable (llr (kap i) (lam i)) (kap i)) →
          (∫ u : (Fin n → U), llr (Measure.pi kap) (Measure.pi lam) u ∂(Measure.pi kap))
            = ∑ i : Fin n, ∫ x : U, llr (kap i) (lam i) x ∂(kap i)) := by
  /- @proof-region region.target-node.session.6635287bc54b0490 begin -/
  intro U _ n kap lam hkap hlam hac hprod
  haveI : ∀ i : Fin n, IsProbabilityMeasure (kap i) := hkap
  haveI : ∀ i : Fin n, IsProbabilityMeasure (lam i) := hlam
  let d : Fin n → U → ℝ≥0∞ := fun i => (kap i).rnDeriv (lam i)
  let ρ : (Fin n → U) → ℝ≥0∞ := fun u => ∏ i, d i (u i)
  have hρ_meas : Measurable ρ :=
    Finset.measurable_prod Finset.univ (f := fun (i : Fin n) (u : Fin n → U) => d i (u i))
      (fun i _ => (Measure.measurable_rnDeriv (kap i) (lam i)).comp (measurable_pi_apply i))
  have hwit : ∀ i : Fin n, (lam i).withDensity (d i) = kap i :=
    fun i => Measure.withDensity_rnDeriv_eq (kap i) (lam i) (hac i)
  have hP : (Measure.pi lam).withDensity ρ = Measure.pi kap := hprod
  have hacpi : Measure.pi kap ≪ Measure.pi lam :=
    hP ▸ withDensity_absolutelyContinuous (Measure.pi lam) ρ
  have hmapP : ∀ i : Fin n, Measure.map (Function.eval i) (Measure.pi kap) = kap i := by
    intro i
    rw [Measure.pi_map_eval]
    have h1 : ∏ j ∈ Finset.univ.erase i, (kap j) Set.univ = 1 := by simp
    rw [h1, one_smul]
  have hmapL : ∀ i : Fin n, Measure.map (Function.eval i) (Measure.pi lam) = lam i := by
    intro i
    rw [Measure.pi_map_eval]
    have h1 : ∏ j ∈ Finset.univ.erase i, (lam j) Set.univ = 1 := by simp
    rw [h1, one_smul]
  have hmeas_d : ∀ i : Fin n, Measurable (d i) :=
    fun i => Measure.measurable_rnDeriv (kap i) (lam i)
  have hrnP : (Measure.pi kap).rnDeriv (Measure.pi lam) =ᵐ[Measure.pi kap] ρ := by
    have h : (Measure.pi kap).rnDeriv (Measure.pi lam) =ᵐ[Measure.pi lam] ρ := by
      have h' := Measure.rnDeriv_withDensity (Measure.pi lam) hρ_meas
      rwa [hP] at h'
    exact hacpi.ae_eq h
  have hzero : ∀ i : Fin n, (Measure.pi kap) {u : Fin n → U | d i (u i) = 0} = 0 := by
    intro i
    have hms : MeasurableSet {u : Fin n → U | d i (u i) = 0} :=
      (hmeas_d i).comp (measurable_pi_apply i) (measurableSet_singleton 0)
    have hρ0 : ∀ u : Fin n → U, u ∈ {u : Fin n → U | d i (u i) = 0} → ρ u = 0 :=
      fun u hu => Finset.prod_eq_zero (Finset.mem_univ i) hu
    have hmain := MeasureTheory.setLIntegral_withDensity_eq_lintegral_mul₀ (μ := Measure.pi lam)
      (f := ρ) (g := fun _ => (1 : ℝ≥0∞)) hρ_meas.aemeasurable measurable_const.aemeasurable
      (s := {u : Fin n → U | d i (u i) = 0}) hms
    rw [hP] at hmain
    have hmain' : ∫⁻ a in {u : Fin n → U | d i (u i) = 0}, (1 : ℝ≥0∞) ∂(Measure.pi kap)
        = ∫⁻ a in {u : Fin n → U | d i (u i) = 0}, ρ a ∂(Measure.pi lam) := by
      simpa using hmain
    have hLHS : (Measure.pi kap) {u : Fin n → U | d i (u i) = 0}
        = ∫⁻ a in {u : Fin n → U | d i (u i) = 0}, (1 : ℝ≥0∞) ∂(Measure.pi kap) := by
      rw [lintegral_one, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    have hRHS : ∫⁻ a in {u : Fin n → U | d i (u i) = 0},
        ρ a ∂(Measure.pi lam) = 0 := by
      rw [← MeasureTheory.lintegral_indicator hms]
      have hind : Set.indicator {u : Fin n → U | d i (u i) = 0} ρ
          = (0 : (Fin n → U) → ℝ≥0∞) := by
        funext u
        rw [Set.indicator_apply]
        by_cases hu : u ∈ {u : Fin n → U | d i (u i) = 0}
        · rw [if_pos hu]
          exact hρ0 u hu
        · rw [if_neg hu]
          simp
      rw [hind]
      simp
    calc (Measure.pi kap) {u : Fin n → U | d i (u i) = 0}
        = ∫⁻ a in {u : Fin n → U | d i (u i) = 0}, (1 : ℝ≥0∞) ∂(Measure.pi kap) := hLHS
      _ = ∫⁻ a in {u : Fin n → U | d i (u i) = 0},
            ρ a ∂(Measure.pi lam) := hmain'
      _ = 0 := hRHS
  have hne0 : ∀ᵐ u ∂(Measure.pi kap), ∀ i : Fin n, d i (u i) ≠ 0 := by
    rw [Filter.eventually_all]
    intro i
    rw [MeasureTheory.ae_iff]
    simpa using hzero i
  have hntop_lam : ∀ i : Fin n, (lam i) {x : U | d i x = ⊤} = 0 := by
    intro i
    have hint_d : ∫⁻ x, d i x ∂(lam i) = 1 := by
      have h := MeasureTheory.lintegral_withDensity_eq_lintegral_mul (lam i) (hmeas_d i)
        (g := fun _ => (1 : ℝ≥0∞)) measurable_const
      rw [hwit i] at h
      simp only [Pi.mul_apply, mul_one] at h
      rw [← h]
      simp
    have hne : ∫⁻ x, d i x ∂(lam i) ≠ ⊤ := by
      rw [hint_d]
      exact ENNReal.one_ne_top
    have h := MeasureTheory.ae_lt_top (hmeas_d i) hne
    rw [MeasureTheory.ae_iff] at h
    simpa using h
  have hntop : ∀ᵐ u ∂(Measure.pi kap), ∀ i : Fin n, d i (u i) ≠ ⊤ := by
    rw [Filter.eventually_all]
    intro i
    have hmsi : MeasurableSet {x : U | d i x = ⊤} := (hmeas_d i) (measurableSet_singleton ⊤)
    have hms : MeasurableSet {u : Fin n → U | d i (u i) = ⊤} :=
      (hmeas_d i).comp (measurable_pi_apply i) (measurableSet_singleton ⊤)
    have hL : (Measure.pi lam) {u : Fin n → U | d i (u i) = ⊤} = 0 := by
      have heq : {u : Fin n → U | d i (u i) = ⊤} = (Function.eval i) ⁻¹' {x : U | d i x = ⊤} :=
        rfl
      rw [heq, ← Measure.map_apply (measurable_pi_apply i) hmsi, hmapL i]
      exact hntop_lam i
    have hP0 : (Measure.pi kap) {u : Fin n → U | d i (u i) = ⊤} = 0 := hacpi hL
    rw [MeasureTheory.ae_iff]
    simpa using hP0
  have hllr : llr (Measure.pi kap) (Measure.pi lam) =ᵐ[Measure.pi kap]
      (fun u : Fin n → U => ∑ i : Fin n, llr (kap i) (lam i) (u i)) := by
    filter_upwards [hrnP, hne0, hntop] with u hrn hu0 hut
    simp only [MeasureTheory.llr_def]
    rw [hrn]
    change Real.log ((∏ i : Fin n, d i (u i)).toReal)
      = ∑ i : Fin n, Real.log ((d i (u i)).toReal)
    rw [ENNReal.toReal_prod,
      Real.log_prod (fun i _ => ne_of_gt (ENNReal.toReal_pos (hu0 i) (hut i)))]
  have hIntFwd : Integrable (llr (Measure.pi kap) (Measure.pi lam)) (Measure.pi kap) →
      ∀ i : Fin n, Integrable (llr (kap i) (lam i)) (kap i) :=
    fun h => statopia_math_node_980129684_7aca482a n kap lam hkap hlam hac hprod hllr h
  have hmpP : ∀ i : Fin n, MeasurePreserving (Function.eval i) (Measure.pi kap) (kap i) :=
    fun i => ⟨measurable_pi_apply i, hmapP i⟩
  have hIntSummand : (∀ i : Fin n, Integrable (llr (kap i) (lam i)) (kap i)) →
      ∀ i : Fin n, Integrable (fun u : Fin n → U => llr (kap i) (lam i) (u i)) (Measure.pi kap) := by
    intro hinter i
    exact ((hmpP i).integrable_comp (measurable_llr (kap i) (lam i)).aestronglyMeasurable).mpr
      (hinter i)
  have hIntBack : (∀ i : Fin n, Integrable (llr (kap i) (lam i)) (kap i)) →
      Integrable (llr (Measure.pi kap) (Measure.pi lam)) (Measure.pi kap) := by
    intro hinter
    have hsum : Integrable
        (fun u : Fin n → U => ∑ i : Fin n, llr (kap i) (lam i) (u i)) (Measure.pi kap) :=
      integrable_finset_sum Finset.univ
        (f := fun (i : Fin n) (u : Fin n → U) => llr (kap i) (lam i) (u i))
        (fun i _ => hIntSummand hinter i)
    exact hsum.congr hllr.symm
  have hint : (∀ i : Fin n, Integrable (llr (kap i) (lam i)) (kap i)) →
      (∫ u : (Fin n → U), llr (Measure.pi kap) (Measure.pi lam) u ∂(Measure.pi kap))
        = ∑ i : Fin n, ∫ x : U, llr (kap i) (lam i) x ∂(kap i) := by
    intro hinter
    have hcongr : (∫ u : (Fin n → U), llr (Measure.pi kap) (Measure.pi lam) u ∂(Measure.pi kap))
        = ∫ u : (Fin n → U), ∑ i : Fin n, llr (kap i) (lam i) (u i) ∂(Measure.pi kap) :=
      integral_congr_ae hllr
    rw [hcongr, integral_finset_sum Finset.univ
      (f := fun (i : Fin n) (u : Fin n → U) => llr (kap i) (lam i) (u i))
      (fun i _ => hIntSummand hinter i)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have h1 : (∫ x : U, llr (kap i) (lam i) x ∂(Measure.map (Function.eval i) (Measure.pi kap)))
        = ∫ u : Fin n → U, llr (kap i) (lam i) (u i) ∂(Measure.pi kap) :=
      integral_map (measurable_pi_apply i).aemeasurable
        (measurable_llr (kap i) (lam i)).aestronglyMeasurable
    rw [hmapP i] at h1
    exact h1.symm
  exact ⟨hllr, ⟨hIntFwd, hIntBack⟩, hint⟩
  /- @proof-region region.target-node.session.6635287bc54b0490 end -/

end
end Statlib.Imported
