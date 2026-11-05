import ProverJobs.jobea4701a9720de21f681f2da3.Vocabulary
import ProverJobs.jobea4701a9720de21f681f2da3.Base
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_1092252686_59989bea_776285fd
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_315826285_30cc4431_c46d0e4c
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
theorem statopia_math_node_4070022191_35653aaa : ∀ {U : Type*} [MeasurableSpace U] (n : ℕ) (kap lam : Fin n → Measure U)
    (hkap : ∀ i : Fin n, IsProbabilityMeasure (kap i))
    (hlam : ∀ i : Fin n, IsProbabilityMeasure (lam i))
    (hac : ∀ i : Fin n, kap i ≪ lam i),
    InformationTheory.klDiv (Measure.pi kap) (Measure.pi lam)
      = ∑ i : Fin n, InformationTheory.klDiv (kap i) (lam i) := by
  /- @proof-region region.target-node.session.5f153af65daef357 begin -/
  intro U _ n kap lam hkap hlam hac
  classical
  haveI : ∀ i : Fin n, IsProbabilityMeasure (kap i) := hkap
  haveI : ∀ i : Fin n, IsProbabilityMeasure (lam i) := hlam
  let d : Fin n → U → ℝ≥0∞ := fun i => (kap i).rnDeriv (lam i)
  have hdmeas : ∀ i : Fin n, Measurable (d i) :=
    fun i => Measure.measurable_rnDeriv (kap i) (lam i)
  have hwit : ∀ i : Fin n, (lam i).withDensity (d i) = kap i :=
    fun i => Measure.withDensity_rnDeriv_eq (kap i) (lam i) (hac i)
  have hprod : (Measure.pi lam).withDensity (fun u : Fin n → U => ∏ i, d i (u i))
      = Measure.pi kap := by
    have hbox : ∀ (s : Fin n → Set U), (∀ i, MeasurableSet (s i)) →
        ((Measure.pi lam).withDensity (fun u : Fin n → U => ∏ i, d i (u i)))
            (Set.univ.pi s) = ∏ i, kap i (s i) := by
      intro s hs
      have hbm : MeasurableSet (Set.univ.pi s) := by
        have hEq : Set.univ.pi s
            = ⋂ i, (fun u : Fin n → U => u i) ⁻¹' (s i) := by
          ext u
          simp [Set.mem_univ_pi]
        rw [hEq]
        exact MeasurableSet.iInter (fun i => measurable_pi_apply i (hs i))
      have hwd : ((Measure.pi lam).withDensity (fun u : Fin n → U => ∏ i, d i (u i)))
          (Set.univ.pi s) = ∫⁻ u in Set.univ.pi s, ∏ i, d i (u i) ∂(Measure.pi lam) :=
        withDensity_apply _ hbm
      rw [hwd]
      rw [← lintegral_indicator hbm]
      have hB : ∀ u : Fin n → U,
          (Set.univ.pi s).indicator (fun v => ∏ i, d i (v i)) u
            = ∏ i, (s i).indicator (d i) (u i) := by
        intro u
        by_cases hu : u ∈ Set.univ.pi s
        · have hmem : ∀ i, u i ∈ s i := fun i => Set.mem_univ_pi.mp hu i
          rw [Set.indicator_of_mem hu]
          exact Finset.prod_congr rfl
            (fun i _ => (Set.indicator_of_mem (hmem i) (d i)).symm)
        · have hex : ∃ i, u i ∉ s i := by
            by_contra hcon
            exact hu (Set.mem_univ_pi.mpr (fun i => by
              by_contra h'
              exact hcon ⟨i, h'⟩))
          obtain ⟨i0, hi0⟩ := hex
          rw [Set.indicator_of_notMem hu]
          exact (Finset.prod_eq_zero (Finset.mem_univ i0)
            (Set.indicator_of_notMem hi0 (d i0))).symm
      simp only [hB]
      have hchild := statopia_math_node_315826285_30cc4431 n lam hlam
        (fun i => (s i).indicator (d i))
        (fun i => by measurability)
      exact hchild.trans (Finset.prod_congr rfl (fun i _ => by
        rw [lintegral_indicator (hs i), ← hwit i, withDensity_apply _ (hs i)]))
    exact (Measure.pi_eq hbox).symm
  have hacpi : Measure.pi kap ≪ Measure.pi lam := by
    rw [← hprod]
    exact withDensity_absolutelyContinuous _ _
  have hrn : (Measure.pi kap).rnDeriv (Measure.pi lam)
      =ᵐ[Measure.pi lam] fun u : Fin n → U => ∏ i, d i (u i) := by
    have hmeas : Measurable (fun u : Fin n → U => ∏ i, d i (u i)) :=
      Finset.measurable_prod Finset.univ
        (fun i _ => (hdmeas i).comp (measurable_pi_apply i))
    have h := Measure.rnDeriv_withDensity (Measure.pi lam) hmeas
    rwa [hprod] at h
  have hstep := statopia_math_node_1092252686_59989bea n kap lam hkap hlam hac hprod
  have hllr : llr (Measure.pi kap) (Measure.pi lam)
      =ᵐ[Measure.pi kap]
        fun u : Fin n → U => ∑ i, llr (kap i) (lam i) (u i) := hstep.1
  have hint2 : (∀ i, Integrable (llr (kap i) (lam i)) (kap i)) →
      (∫ u, llr (Measure.pi kap) (Measure.pi lam) u ∂(Measure.pi kap))
        = ∑ i, ∫ x, llr (kap i) (lam i) x ∂(kap i) := hstep.2.2
  have hIntTransfer : Integrable (llr (Measure.pi kap) (Measure.pi lam)) (Measure.pi kap)
      ↔ ∀ i, Integrable (llr (kap i) (lam i)) (kap i) := hstep.2.1
  have hpuniv : (Measure.pi kap) Set.univ = 1 := by
    rw [Measure.pi_univ]
    simp
  have hluniv : (Measure.pi lam) Set.univ = 1 := by
    rw [Measure.pi_univ]
    simp
  have hPr : Measure.real (Measure.pi kap) Set.univ = 1 := by
    simp [Measure.real, hpuniv]
  have hLr : Measure.real (Measure.pi lam) Set.univ = 1 := by
    simp [Measure.real, hluniv]
  have hlamr : ∀ i : Fin n, Measure.real (lam i) Set.univ = 1 := by
    intro i
    simp [Measure.real]
  have hkapr : ∀ i : Fin n, Measure.real (kap i) Set.univ = 1 := by
    intro i
    simp [Measure.real]
  by_cases hfin : ∀ i : Fin n, InformationTheory.klDiv (kap i) (lam i) ≠ ⊤
  · have hinter : ∀ i, Integrable (llr (kap i) (lam i)) (kap i) :=
      fun i => (InformationTheory.klDiv_ne_top_iff.mp (hfin i)).2
    have hIntP : Integrable (llr (Measure.pi kap) (Measure.pi lam)) (Measure.pi kap) :=
      hIntTransfer.mpr hinter
    have hPne : InformationTheory.klDiv (Measure.pi kap) (Measure.pi lam) ≠ ⊤ :=
      InformationTheory.klDiv_ne_top_iff.mpr ⟨hacpi, hIntP⟩
    have hsumne : (∑ i : Fin n, InformationTheory.klDiv (kap i) (lam i)) ≠ ⊤ := by
      have h1 : (∑ i : Fin n, InformationTheory.klDiv (kap i) (lam i))
          = ∑ i : Fin n,
              ENNReal.ofReal ((InformationTheory.klDiv (kap i) (lam i))).toReal :=
        Finset.sum_congr rfl (fun i _ => (ENNReal.ofReal_toReal (hfin i)).symm)
      rw [h1, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => ENNReal.toReal_nonneg)]
      exact ENNReal.ofReal_ne_top
    refine (ENNReal.toReal_eq_toReal hPne hsumne).mp ?_
    rw [InformationTheory.toReal_klDiv hacpi hIntP]
    rw [ENNReal.toReal_sum (fun i _ => hfin i)]
    have hterm : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        (InformationTheory.klDiv (kap i) (lam i)).toReal
          = ∫ x, llr (kap i) (lam i) x ∂(kap i)
            + Measure.real (lam i) Set.univ - Measure.real (kap i) Set.univ :=
      fun i _ => InformationTheory.toReal_klDiv (hac i) (hinter i)
    rw [Finset.sum_congr rfl hterm]
    have h2 := hint2 hinter
    simp only [hPr, hLr, hlamr, hkapr]
    rw [h2]
    simp
  · push_neg at hfin
    obtain ⟨i, hi⟩ := hfin
    have hni : ¬ Integrable (llr (kap i) (lam i)) (kap i) := by
      intro h
      exact (InformationTheory.klDiv_ne_top_iff.mpr ⟨hac i, h⟩) hi
    have hsumtop : (∑ j : Fin n, InformationTheory.klDiv (kap j) (lam j)) = ⊤ := by
      have hle : InformationTheory.klDiv (kap i) (lam i)
          ≤ ∑ j : Fin n, InformationTheory.klDiv (kap j) (lam j) :=
        Finset.single_le_sum
          (f := fun j : Fin n => InformationTheory.klDiv (kap j) (lam j))
          (fun j _ => zero_le _) (Finset.mem_univ i)
      simp only at hle
      rw [hi] at hle
      exact top_le_iff.mp hle
    rw [hsumtop]
    by_contra hne
    exact hni (hIntTransfer.mp (InformationTheory.klDiv_ne_top_iff.mp hne).2 i)

  /- @proof-region region.target-node.session.5f153af65daef357 end -/

end
end Statlib.Imported
