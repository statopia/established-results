import ProverJobs.jobea4701a9720de21f681f2da3.Vocabulary
import ProverJobs.jobea4701a9720de21f681f2da3.Base
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_3721294497_2acf13ef_ff5cf613
import ProverJobs.jobea4701a9720de21f681f2da3.ExternalNodes.Node_a26b2b509ee15a62f52b

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
theorem statopia_math_node_35798353_6c7e7779 : ∀ (Ω : Type*) [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    (mu nu : ProbabilityMeasure Ω)
    (h : Ω → ℝ) (hh : Measurable h)
    (C : ℝ) (hC : ∀ x : Ω, |h x| ≤ C),
    (((∫ x, h x ∂(nu : Measure Ω)) : ℝ) : EReal)
      ≤ ENNReal.toEReal (InformationTheory.klDiv (nu : Measure Ω) (mu : Measure Ω))
        + (((Real.log (∫ x, Real.exp (h x) ∂(mu : Measure Ω))) : ℝ) : EReal) := by
  /- @proof-region region.target-node.session.abc3189cfeec117e begin -/
  intro H _ _ _ _ μ ν h hh_meas C hC
  have hB0 : ∀ x : H, |h x| ≤ max C 0 := fun x => (hC x).trans (le_max_left C 0)
  have happrox : ∃ (Θ : ℕ → H → ℝ), (∀ n, Continuous (Θ n)) ∧ (∀ n, Bornology.IsBounded (Set.range (Θ n))) ∧
      Filter.Tendsto (fun n => ∫ x, Θ n x ∂(ν : Measure H)) Filter.atTop (nhds (∫ x, h x ∂(ν : Measure H))) ∧
      Filter.Tendsto (fun n => ∫ x, Real.exp (Θ n x) ∂(μ : Measure H)) Filter.atTop (nhds (∫ x, Real.exp (h x) ∂(μ : Measure H))) :=
    statopia_math_node_3721294497_2acf13ef μ ν h hh_meas C hC
  obtain ⟨Θ, hΘcont, hΘbdd, hΘν, hΘμ⟩ := happrox
  have hpos : 0 < ∫ x, Real.exp (h x) ∂(μ : Measure H) := by
    have hint : Integrable (fun x => Real.exp (h x)) (μ : Measure H) :=
      Integrable.of_bound (Real.measurable_exp.comp hh_meas).aestronglyMeasurable (Real.exp (max C 0))
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact Real.exp_le_exp.mpr (abs_le.mp (hB0 x)).2)
    have hc : ∫ x, Real.exp (-(max C 0)) ∂(μ : Measure H) = Real.exp (-(max C 0)) := by
      rw [integral_const]
      simp [Measure.real, measure_univ]
    calc 0 < Real.exp (-(max C 0)) := Real.exp_pos _
      _ = ∫ x, Real.exp (-(max C 0)) ∂(μ : Measure H) := hc.symm
      _ ≤ ∫ x, Real.exp (h x) ∂(μ : Measure H) :=
          integral_mono (integrable_const _) hint (fun x => Real.exp_le_exp.mpr (abs_le.mp (hB0 x)).1)
  have hFlim : Filter.Tendsto (fun n => (∫ x, Θ n x ∂(ν : Measure H)) - Real.log (∫ x, Real.exp (Θ n x) ∂(μ : Measure H))) Filter.atTop
      (nhds ((∫ x, h x ∂(ν : Measure H)) - Real.log (∫ x, Real.exp (h x) ∂(μ : Measure H)))) :=
    hΘν.sub ((Real.continuousAt_log hpos.ne').tendsto.comp hΘμ)
  have hadd : ∀ a b : ℝ, (((a : ℝ) : EReal) + ((b : ℝ) : EReal)) = (((a + b : ℝ)) : EReal) :=
    fun a b => EReal.coe_add a b
  have hsub : ∀ a b : ℝ, (((a : ℝ) : EReal) - ((b : ℝ) : EReal)) = (((a - b : ℝ)) : EReal) :=
    fun a b => EReal.coe_sub a b
  have hsup : ENNReal.toEReal (InformationTheory.klDiv (ν : Measure H) (μ : Measure H))
      = ⨆ (Theta : H → ℝ), ⨆ (_ : Continuous Theta) (_ : Bornology.IsBounded (Set.range Theta)),
          (((∫ x, Theta x ∂(ν : Measure H)) : ℝ) : EReal) - (((Real.log (∫ x, Real.exp (Theta x) ∂(μ : Measure H))) : ℝ) : EReal) :=
    ExternalRevision_5d5e44994e1bd0d7755f1cc92bfd67e5640cab3ee11d2f6e18ce338046e89096.citation μ ν
  have key : ∀ (Theta : H → ℝ), Continuous Theta → Bornology.IsBounded (Set.range Theta) →
      (((∫ x, Theta x ∂(ν : Measure H)) : ℝ) : EReal) - (((Real.log (∫ x, Real.exp (Theta x) ∂(μ : Measure H))) : ℝ) : EReal)
        ≤ ENNReal.toEReal (InformationTheory.klDiv (ν : Measure H) (μ : Measure H)) := by
    intro Theta hcT hbT
    rw [hsup]
    refine le_trans (le_iSup (fun _ : Bornology.IsBounded (Set.range Theta) =>
      (((∫ x, Theta x ∂(ν : Measure H)) : ℝ) : EReal) - (((Real.log (∫ x, Real.exp (Theta x) ∂(μ : Measure H))) : ℝ) : EReal)) hbT) ?_
    refine le_trans (le_iSup (fun _ : Continuous Theta =>
      ⨆ (_ : Bornology.IsBounded (Set.range Theta)),
        (((∫ x, Theta x ∂(ν : Measure H)) : ℝ) : EReal) - (((Real.log (∫ x, Real.exp (Theta x) ∂(μ : Measure H))) : ℝ) : EReal)) hcT) ?_
    exact le_iSup (fun T : H → ℝ => ⨆ (_ : Continuous T) (_ : Bornology.IsBounded (Set.range T)),
      (((∫ x, T x ∂(ν : Measure H)) : ℝ) : EReal) - (((Real.log (∫ x, Real.exp (T x) ∂(μ : Measure H))) : ℝ) : EReal)) Theta
  have hub : ∀ (y : EReal),
      (∀ (Theta : H → ℝ) (hc : Continuous Theta) (hb : Bornology.IsBounded (Set.range Theta)),
        (((∫ x, Theta x ∂(ν : Measure H)) : ℝ) : EReal) - (((Real.log (∫ x, Real.exp (Theta x) ∂(μ : Measure H))) : ℝ) : EReal) ≤ y) →
      (((∫ x, h x ∂(ν : Measure H)) - Real.log (∫ x, Real.exp (h x) ∂(μ : Measure H)) : ℝ) : EReal) ≤ y := by
    intro y hy
    rcases y with _ | y'
    · have h3 : (((∫ x, Θ 0 x ∂(ν : Measure H)) - Real.log (∫ x, Real.exp (Θ 0 x) ∂(μ : Measure H)) : ℝ) : EReal) = (⊥ : EReal) :=
        (hsub (∫ x, Θ 0 x ∂(ν : Measure H)) (Real.log (∫ x, Real.exp (Θ 0 x) ∂(μ : Measure H)))).symm.trans
          (le_antisymm (hy (Θ 0) (hΘcont 0) (hΘbdd 0)) bot_le)
      have h1 : ((((∫ x, Θ 0 x ∂(ν : Measure H)) - Real.log (∫ x, Real.exp (Θ 0 x) ∂(μ : Measure H)) : ℝ) - 1 : ℝ) : EReal)
          < (((∫ x, Θ 0 x ∂(ν : Measure H)) - Real.log (∫ x, Real.exp (Θ 0 x) ∂(μ : Measure H)) : ℝ) : EReal) := by
        exact_mod_cast (show (∫ x, Θ 0 x ∂(ν : Measure H)) - Real.log (∫ x, Real.exp (Θ 0 x) ∂(μ : Measure H)) - 1
          < (∫ x, Θ 0 x ∂(ν : Measure H)) - Real.log (∫ x, Real.exp (Θ 0 x) ∂(μ : Measure H)) by linarith)
      rw [h3] at h1
      exact absurd h1 (not_lt.mpr bot_le)
    · rcases y' with _ | k
      · exact le_top
      · have h1 : ∀ n, (∫ x, Θ n x ∂(ν : Measure H)) - Real.log (∫ x, Real.exp (Θ n x) ∂(μ : Measure H)) ≤ k := by
          intro n
          have h2 : (((∫ x, Θ n x ∂(ν : Measure H)) - Real.log (∫ x, Real.exp (Θ n x) ∂(μ : Measure H)) : ℝ) : EReal) ≤ (((k : ℝ)) : EReal) := by
            calc (((∫ x, Θ n x ∂(ν : Measure H)) - Real.log (∫ x, Real.exp (Θ n x) ∂(μ : Measure H)) : ℝ) : EReal)
                = (((∫ x, Θ n x ∂(ν : Measure H)) : ℝ) : EReal) - (((Real.log (∫ x, Real.exp (Θ n x) ∂(μ : Measure H))) : ℝ) : EReal) := (hsub _ _).symm
              _ ≤ (((k : ℝ)) : EReal) := hy (Θ n) (hΘcont n) (hΘbdd n)
          exact_mod_cast h2
        have h3 : (∫ x, h x ∂(ν : Measure H)) - Real.log (∫ x, Real.exp (h x) ∂(μ : Measure H)) ≤ k :=
          le_of_tendsto_of_tendsto hFlim tendsto_const_nhds (Filter.Eventually.of_forall h1)
        have h4 : (((∫ x, h x ∂(ν : Measure H)) - Real.log (∫ x, Real.exp (h x) ∂(μ : Measure H)) : ℝ) : EReal) ≤ (((k : ℝ)) : EReal) := by
          exact_mod_cast h3
        exact h4
  have hFL : (((∫ x, h x ∂(ν : Measure H)) - Real.log (∫ x, Real.exp (h x) ∂(μ : Measure H)) : ℝ) : EReal)
      ≤ ENNReal.toEReal (InformationTheory.klDiv (ν : Measure H) (μ : Measure H)) :=
    hub _ key
  calc (((∫ x, h x ∂(ν : Measure H)) : ℝ) : EReal)
      = (((∫ x, h x ∂(ν : Measure H)) - Real.log (∫ x, Real.exp (h x) ∂(μ : Measure H)) : ℝ) : EReal)
          + (((Real.log (∫ x, Real.exp (h x) ∂(μ : Measure H))) : ℝ) : EReal) := by
        rw [hadd]
        congr 1
        ring
    _ ≤ ENNReal.toEReal (InformationTheory.klDiv (ν : Measure H) (μ : Measure H))
          + (((Real.log (∫ x, Real.exp (h x) ∂(μ : Measure H))) : ℝ) : EReal) := add_le_add_left hFL _
  /- @proof-region region.target-node.session.abc3189cfeec117e end -/

end
end Statlib.Imported
