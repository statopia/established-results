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
theorem statopia_math_node_2395645464_8193eae1 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [MeasurableSpace U] [BorelSpace U]
    (e : HilbertBasis ℕ ℝ U) (lam : ℕ → ℝ) (hlam_pos : ∀ k : ℕ, 0 < lam k)
    (s0 st : ℝ) (hs0_nonneg : 0 ≤ s0) (hs0_lt : s0 < 1)
    (hst_gt : s0 < st) (hst_le : st ≤ 1)
    (M1 : ℝ → ℝ) (hM1_mono : Monotone M1) (hM1_nonneg : ∀ r : ℝ, 0 ≤ M1 r)
    (P : Measure U) [IsProbabilityMeasure P]
    (hdelta : ∃ d0 : ℝ, 0 < d0 ∧ ∀ delta : ℝ, 0 ≤ delta → delta < d0 →
      (∫⁻ u : U, momentExpENN M1 delta (UScaleDist e lam (1 - st) u 0) ∂P) ≠ ⊤),
    ∃ delta0 : ℝ, 0 < delta0 ∧
      P (UScale e lam (1 - st)) = 1 ∧
      ∀ delta : ℝ, 0 ≤ delta → delta < delta0 →
        Integrable ((UScale e lam (1 - st)).indicator
          (fun u : U =>
            Real.exp (delta * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2))) P := by
  /- @proof-region region.target-node.session.5b734af21017717b begin -/
  intro U hNAG hIPS hMS hBS e lam hlam_pos s0 st hs0_nonneg hs0_lt hst_gt hst_le M1 hM1_mono
    hM1_nonneg P hPprob hdelta
  haveI := hPprob
  have hmeas_inner : ∀ k : ℕ, Measurable fun u : U => inner ℝ (e k) u := by
    intro k
    have hc : Continuous fun u : U => inner ℝ (e k) u :=
      Continuous.inner continuous_const continuous_id
    exact hc.measurable
  have hterm : ∀ k : ℕ, Measurable fun u : U =>
      ENNReal.ofReal (Real.rpow (lam k) (-(1 - st)) * (inner ℝ (e k) u) ^ 2) := by
    intro k
    have hsq : Measurable fun u : U => (inner ℝ (e k) u) ^ 2 := by
      simpa [pow_two] using (hmeas_inner k).mul (hmeas_inner k)
    exact ENNReal.measurable_ofReal.comp (measurable_const.mul hsq)
  have hmeasNorm : Measurable fun u : U => UScaleNorm e lam (1 - st) u := by
    unfold UScaleNorm
    exact Measurable.ennreal_tsum hterm
  have hmeasSet : MeasurableSet (UScale e lam (1 - st)) := by
    unfold UScale
    exact hmeasNorm.stronglyMeasurable.measurableSet_lt
      (stronglyMeasurable_const : StronglyMeasurable fun _ : U => (⊤ : ℝ≥0∞))
  have hmem_iff : ∀ u : U,
      UScaleDist e lam (1 - st) u 0 < ⊤ ↔ u ∈ UScale e lam (1 - st) := by
    intro u
    simp only [UScaleDist, UScale, Set.mem_setOf_eq, sub_zero]
    exact ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
  have hmoment_top : ∀ (d : ℝ) (u : U), ¬ UScaleDist e lam (1 - st) u 0 < ⊤ →
      momentExpENN M1 d (UScaleDist e lam (1 - st) u 0) = ⊤ := by
    intro d u hu
    unfold momentExpENN
    exact dif_neg hu
  obtain ⟨d0, hd0_pos, hd0_mom⟩ := hdelta
  have hcomp : P (UScale e lam (1 - st))ᶜ = 0 := by
    by_contra hne
    have hle : ∫⁻ u : U, (UScale e lam (1 - st))ᶜ.indicator (fun _ => (⊤ : ℝ≥0∞)) u ∂P
        ≤ ∫⁻ u : U, momentExpENN M1 (d0 / 2) (UScaleDist e lam (1 - st) u 0) ∂P := by
      refine lintegral_mono fun u => ?_
      by_cases hu : u ∈ UScale e lam (1 - st)
      · have hz : (UScale e lam (1 - st))ᶜ.indicator (fun _ => (⊤ : ℝ≥0∞)) u = 0 := by
          simp [Set.indicator, hu]
        rw [hz]
        exact zero_le _
      · have hmem : u ∈ (UScale e lam (1 - st))ᶜ := by simpa using hu
        have htop : ¬ UScaleDist e lam (1 - st) u 0 < ⊤ := by
          rw [hmem_iff u]
          exact hu
        rw [Set.indicator_of_mem hmem, hmoment_top (d0 / 2) u htop]
    have htop : ∫⁻ u : U, (UScale e lam (1 - st))ᶜ.indicator (fun _ => (⊤ : ℝ≥0∞)) u ∂P = ⊤ := by
      rw [MeasureTheory.lintegral_indicator_const hmeasSet.compl (⊤ : ℝ≥0∞)]
      exact ENNReal.top_mul hne
    exact hd0_mom (d0 / 2) (by linarith) (by linarith)
      (top_le_iff.mp (by rw [← htop]; exact hle))
  have hPs : P (UScale e lam (1 - st)) = 1 := by
    have hle1 : P (UScale e lam (1 - st)) ≤ 1 := by
      calc P (UScale e lam (1 - st)) ≤ P Set.univ :=
            MeasureTheory.measure_mono (Set.subset_univ (UScale e lam (1 - st)))
        _ = 1 := measure_univ
    have hunion : 1 ≤ P (UScale e lam (1 - st)) + P (UScale e lam (1 - st))ᶜ := by
      have h := MeasureTheory.measure_union_le (μ := P) (UScale e lam (1 - st))
        (UScale e lam (1 - st))ᶜ
      have huniv : (UScale e lam (1 - st)) ∪ (UScale e lam (1 - st))ᶜ = Set.univ := by
        ext x
        simp
      rw [huniv, measure_univ] at h
      exact h
    rw [hcomp, add_zero] at hunion
    exact le_antisymm hle1 hunion
  refine ⟨d0, hd0_pos, hPs, ?_⟩
  intro d hd0 hdlt
  have hmom := hd0_mom d hd0 hdlt
  have hmeas_rpow : Measurable fun x : ℝ≥0∞ => x.toReal ^ (1 / 2 : ℝ) :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)).measurable.comp
      ENNReal.measurable_toReal
  have harg0 : Measurable fun u : U =>
      M1 ((UScaleNorm e lam (1 - st) u).toReal ^ (1 / 2 : ℝ)) :=
    hM1_mono.measurable.comp (hmeas_rpow.comp hmeasNorm)
  have hmeas_arg : Measurable fun u : U =>
      (M1 ((UScaleNorm e lam (1 - st) u).toReal ^ (1 / 2 : ℝ))) ^ 2 := by
    simpa [pow_two] using harg0.mul harg0
  have hbase : Measurable fun u : U =>
      Real.exp (d * (M1 ((UScaleNorm e lam (1 - st) u).toReal ^ (1 / 2 : ℝ))) ^ 2) :=
    Real.continuous_exp.measurable.comp (measurable_const.mul hmeas_arg)
  have hcongr : (fun u : U =>
        Real.exp (d * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2))
      = fun u : U =>
        Real.exp (d * (M1 ((UScaleNorm e lam (1 - st) u).toReal ^ (1 / 2 : ℝ))) ^ 2) := by
    funext u
    rw [UScaleDist, sub_zero, ENNReal.toReal_rpow]
  have hmeas_g : Measurable ((UScale e lam (1 - st)).indicator
      (fun v : U =>
        Real.exp (d * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2))) := by
    rw [hcongr]
    exact hbase.indicator hmeasSet
  have hge : 0 ≤ᶠ[ae P] ((UScale e lam (1 - st)).indicator
      (fun v : U =>
        Real.exp (d * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2))) := by
    filter_upwards with u
    by_cases hu : u ∈ UScale e lam (1 - st)
    · rw [Set.indicator_of_mem hu]
      exact (Real.exp_pos _).le
    · have hz : (UScale e lam (1 - st)).indicator
          (fun v : U =>
            Real.exp (d * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)) u = 0 := by
        simp [Set.indicator, hu]
      rw [hz]
      exact le_rfl
  have hbound : ∀ u : U, ENNReal.ofReal (((UScale e lam (1 - st)).indicator
      (fun v : U =>
        Real.exp (d * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2))) u)
      ≤ momentExpENN M1 d (UScaleDist e lam (1 - st) u 0) := by
    intro u
    by_cases hu : u ∈ UScale e lam (1 - st)
    · have hfin : UScaleDist e lam (1 - st) u 0 < ⊤ := (hmem_iff u).2 hu
      rw [Set.indicator_of_mem hu]
      unfold momentExpENN
      rw [dif_pos hfin]
    · have htop : ¬ UScaleDist e lam (1 - st) u 0 < ⊤ := by
        rw [hmem_iff u]
        exact hu
      have hz : (UScale e lam (1 - st)).indicator
          (fun v : U =>
            Real.exp (d * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)) u = 0 := by
        simp [Set.indicator, hu]
      rw [hz, hmoment_top d u htop]
      exact le_top
  have hint_ne : ∫⁻ u : U, ENNReal.ofReal (((UScale e lam (1 - st)).indicator
      (fun v : U =>
        Real.exp (d * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2))) u) ∂P
      ≠ ⊤ := by
    have hle := lintegral_mono (μ := P) hbound
    intro htop
    exact hmom (le_antisymm le_top (htop ▸ hle))
  exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
    hmeas_g.aestronglyMeasurable hge).mp hint_ne
  /- @proof-region region.target-node.session.5b734af21017717b end -/

end Statlib.Imported
end

