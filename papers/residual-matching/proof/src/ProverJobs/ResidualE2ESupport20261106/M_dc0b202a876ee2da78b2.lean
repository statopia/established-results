import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_3574194610_c2928622 : ∀ (n : ℕ) (l : Fin n)
    (Phi : (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (hPhi_meas : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => Phi p.1 p.2))
    (hPhi_diff : ∀ y : Fin n → ℝ, ContDiff ℝ 1 (fun x : Fin n → ℝ => Phi x y)),
    Measurable
        (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
          deriv (fun s : ℝ => Phi (Function.update p.1 l s) p.2) (p.1 l)) ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (U W : Ω → Fin n → ℝ),
        Measurable U → Measurable W →
        Integrable
            (fun ω => deriv (fun s : ℝ => Phi (Function.update (U ω) l s) (W ω)) (U ω l)) μ →
        Measure.map (fun ω => (U ω, W ω)) μ
            = (Measure.map U μ).prod (Measure.map W μ) →
        Integrable
            (Function.uncurry
              (fun x y => deriv (fun s : ℝ => Phi (Function.update x l s) y) (x l)))
            ((Measure.map U μ).prod (Measure.map W μ)) ∧
          AEStronglyMeasurable
            (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
              deriv (fun s : ℝ => Phi (Function.update p.1 l s) p.2) (p.1 l))
            ((Measure.map U μ).prod (Measure.map W μ)) := by
  /- @proof-region region.target-node.session.bd7d9d9c8f44168d begin -/
  intro n l Phi hPhi_meas hPhi_diff
  have hcontA : ∀ c : ℝ, Continuous (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      Function.update p.1 l (p.1 l + c)) := by
    intro c
    apply continuous_pi
    intro i
    by_cases hi : i = l
    · simpa [Function.update_apply, hi] using
        ((continuous_apply l).comp continuous_fst).add continuous_const
    · simpa [Function.update_apply, hi] using (continuous_apply i).comp continuous_fst
  have hcontB : Continuous (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      Function.update p.1 l (p.1 l)) := by
    apply continuous_pi
    intro i
    by_cases hi : i = l
    · simpa [Function.update_apply, hi] using (continuous_apply l).comp continuous_fst
    · simpa [Function.update_apply, hi] using (continuous_apply i).comp continuous_fst
  have hstep : ∀ m : ℕ, Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      (Phi (Function.update p.1 l (p.1 l + 1 / ((m : ℝ) + 1))) p.2
        - Phi (Function.update p.1 l (p.1 l)) p.2) / (1 / ((m : ℝ) + 1))) := by
    intro m
    have h1 : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        Phi (Function.update p.1 l (p.1 l + 1 / ((m : ℝ) + 1))) p.2) :=
      hPhi_meas.comp
        (Measurable.prodMk (hcontA (1 / ((m : ℝ) + 1))).measurable measurable_snd)
    have h2 : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        Phi (Function.update p.1 l (p.1 l)) p.2) :=
      hPhi_meas.comp (Measurable.prodMk hcontB.measurable measurable_snd)
    exact (h1.sub h2).div_const _
  have hconv : ∀ (x y : Fin n → ℝ),
      Filter.Tendsto (fun m : ℕ =>
        (Phi (Function.update x l (x l + 1 / ((m : ℝ) + 1))) y
          - Phi (Function.update x l (x l)) y) / (1 / ((m : ℝ) + 1)))
        Filter.atTop (nhds (deriv (fun s : ℝ => Phi (Function.update x l s) y) (x l))) := by
    intro x y
    have hue : Function.update x l (x l) = x := by
      funext i
      by_cases hi : i = l <;> simp [Function.update_apply, hi]
    have hd : DifferentiableAt ℝ (fun z : Fin n → ℝ => Phi z y) (Function.update x l (x l)) := by
      rw [hue]
      exact ((hPhi_diff y).differentiable one_ne_zero).differentiableAt
    have hc : DifferentiableAt ℝ (fun s : ℝ => Function.update x l s) (x l) := by
      refine differentiableAt_pi.mpr ?_
      intro i
      by_cases hi : i = l
      · simpa [Function.update_apply, hi] using differentiableAt_id
      · simpa [Function.update_apply, hi] using differentiableAt_const (x i)
    have hD : DifferentiableAt ℝ (fun s : ℝ => Phi (Function.update x l s) y) (x l) :=
      DifferentiableAt.comp (x l) hd hc
    have hslope := hasDerivAt_iff_tendsto_slope_zero.mp hD.hasDerivAt
    have hseq : Filter.Tendsto (fun m : ℕ => (1 / ((m : ℝ) + 1) : ℝ)) Filter.atTop
        (nhdsWithin (0 : ℝ) {0}ᶜ) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
      filter_upwards with m
      have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have hne : (1 : ℝ) / ((m : ℝ) + 1) ≠ 0 := div_ne_zero one_ne_zero hpos.ne'
      simpa using hne
    refine Filter.Tendsto.congr (fun m => ?_) (hslope.comp hseq)
    simp only [Function.comp_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hmeasD : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      deriv (fun s : ℝ => Phi (Function.update p.1 l s) p.2) (p.1 l)) := by
    refine measurable_of_tendsto_metrizable
      (f := fun m p => (Phi (Function.update p.1 l (p.1 l + 1 / ((m : ℝ) + 1))) p.2
        - Phi (Function.update p.1 l (p.1 l)) p.2) / (1 / ((m : ℝ) + 1))) (fun m => ?_) ?_
    · exact hstep m
    · rw [tendsto_pi_nhds]
      rintro ⟨x, y⟩
      exact hconv x y
  refine ⟨hmeasD, ?_⟩
  intro Ω _ μ U W hU hW hint hpair
  have hpair_meas : AEMeasurable (fun ω => (U ω, W ω)) μ := (hU.prodMk hW).aemeasurable
  have hInt : Integrable
      (Function.uncurry (fun x y => deriv (fun s : ℝ => Phi (Function.update x l s) y) (x l)))
      (Measure.map (fun ω => (U ω, W ω)) μ) := by
    refine (MeasureTheory.integrable_map_measure ?_ hpair_meas).mpr ?_
    · rw [hpair]
      exact hmeasD.aestronglyMeasurable
    · exact hint
  refine ⟨?_, ?_⟩
  · simpa only [hpair] using hInt
  · rw [← hpair]
    exact hmeasD.aestronglyMeasurable
  /- @proof-region region.target-node.session.bd7d9d9c8f44168d end -/

end Statlib.Imported

