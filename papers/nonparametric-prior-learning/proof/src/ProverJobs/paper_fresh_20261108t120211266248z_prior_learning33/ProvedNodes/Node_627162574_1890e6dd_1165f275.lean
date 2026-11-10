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
theorem statopia_math_node_627162574_1890e6dd : ∀ (U : Type*) [MeasurableSpace U] (P : Measure U) [IsProbabilityMeasure P]
    (f : U → ℝ) (rho : ℕ → U → ℝ≥0∞)
    (hf_meas : AEMeasurable f P)
    (hf_nonneg : ∀ u : U, 0 ≤ f u)
    (hf_sq_lt_top : (∫⁻ u : U, ENNReal.ofReal (f u ^ 2) ∂P) < ⊤)
    (hrho_meas : ∀ n : ℕ, Measurable (rho n))
    (hrho_conv : Tendsto
      (fun n : ℕ => ∫⁻ u : U, ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) ∂P)
      Filter.atTop (𝓝 0)),
    Tendsto (fun n : ℕ => ∫ u : U, f u * (Real.sqrt ((rho n u).toReal) - 1) ^ 2 ∂P)
      Filter.atTop (𝓝 0) := by
  /- @proof-region region.target-node.session.c20db78a541a431d begin -/
  intro U _ P _ f rho hf_meas hf_nonneg hf_sq_lt_top hrho_meas hrho_conv
  have htr : ∀ n : ℕ, Measurable (fun u : U => (rho n u).toReal) :=
    fun n => (hrho_meas n).ennreal_toReal
  have hsqrtm : Measurable (fun x : ℝ => Real.sqrt x) := Real.continuous_sqrt.measurable
  have hsqrt_nn : ∀ n : ℕ, Measurable (fun u : U => Real.sqrt ((rho n u).toReal)) :=
    fun n => hsqrtm.comp (htr n)
  have hhm : ∀ n : ℕ, Measurable (fun u : U => ((rho n u).toReal - 1) ^ 2) := by
    intro n
    have h2 : Measurable (fun u : U => (rho n u).toReal - 1) := (htr n).sub measurable_const
    have h3 : Measurable (fun u : U => ((rho n u).toReal - 1) * ((rho n u).toReal - 1)) :=
      h2.mul h2
    simpa [pow_two] using h3
  have hgm : ∀ n : ℕ, Measurable (fun u : U => (Real.sqrt ((rho n u).toReal) - 1) ^ 2) := by
    intro n
    have h2 : Measurable (fun u : U => Real.sqrt ((rho n u).toReal) - 1) :=
      (hsqrt_nn n).sub measurable_const
    have h3 : Measurable (fun u : U =>
        (Real.sqrt ((rho n u).toReal) - 1) * (Real.sqrt ((rho n u).toReal) - 1)) := h2.mul h2
    simpa [pow_two] using h3
  have hg2m : ∀ n : ℕ, Measurable (fun u : U => ((Real.sqrt ((rho n u).toReal) - 1) ^ 2) ^ 2) := by
    intro n
    have h2 : Measurable (fun u : U => (Real.sqrt ((rho n u).toReal) - 1) ^ 2) := hgm n
    have h3 : Measurable (fun u : U =>
        (Real.sqrt ((rho n u).toReal) - 1) ^ 2 * (Real.sqrt ((rho n u).toReal) - 1) ^ 2) :=
      h2.mul h2
    simpa [pow_two] using h3
  have hf2_meas : AEMeasurable (fun u : U => f u ^ 2) P := by
    have h' := hf_meas.mul hf_meas
    simpa [pow_two] using h'
  have hf2_enn : AEMeasurable (fun u : U => ENNReal.ofReal (f u ^ 2)) P :=
    hf2_meas.ennreal_ofReal
  have hf_int_eq : ∫ u : U, f u ^ 2 ∂P = (∫⁻ u : U, ENNReal.ofReal (f u ^ 2) ∂P).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun u => sq_nonneg (f u)))
      hf2_meas.aestronglyMeasurable
  have hh_int_eq : ∀ n : ℕ, ∫ u : U, ((rho n u).toReal - 1) ^ 2 ∂P
      = (∫⁻ u : U, ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) ∂P).toReal :=
    fun n => integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun u => sq_nonneg _))
      (hhm n).aestronglyMeasurable
  have hg_int_eq : ∀ n : ℕ, ∫ u : U, ((Real.sqrt ((rho n u).toReal) - 1) ^ 2) ^ 2 ∂P
      = (∫⁻ u : U, ENNReal.ofReal (((Real.sqrt ((rho n u).toReal) - 1) ^ 2) ^ 2) ∂P).toReal :=
    fun n => integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun u => sq_nonneg _))
      (hg2m n).aestronglyMeasurable
  have hfg_int_eq : ∀ n : ℕ, ∫ u : U, f u * (Real.sqrt ((rho n u).toReal) - 1) ^ 2 ∂P
      = (∫⁻ u : U, ENNReal.ofReal (f u * (Real.sqrt ((rho n u).toReal) - 1) ^ 2) ∂P).toReal :=
    fun n => integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun u => mul_nonneg (hf_nonneg u) (sq_nonneg _)))
      ((hf_meas.mul (hgm n).aemeasurable).aestronglyMeasurable)
  have key : ∀ x : ℝ, 0 ≤ x → ((Real.sqrt x - 1) ^ 2) ^ 2 ≤ (x - 1) ^ 2 := by
    intro x hx
    have hs : (Real.sqrt x - 1) ^ 2 ≤ (Real.sqrt x + 1) ^ 2 := by
      nlinarith [Real.sqrt_nonneg x]
    have hfac : (x - 1) ^ 2 = (Real.sqrt x + 1) ^ 2 * (Real.sqrt x - 1) ^ 2 := by
      have h : x - 1 = (Real.sqrt x - 1) * (Real.sqrt x + 1) := by
        nlinarith [Real.sq_sqrt hx]
      rw [h]; ring
    calc ((Real.sqrt x - 1) ^ 2) ^ 2
        = (Real.sqrt x - 1) ^ 2 * (Real.sqrt x - 1) ^ 2 := by ring
      _ ≤ (Real.sqrt x - 1) ^ 2 * (Real.sqrt x + 1) ^ 2 :=
          mul_le_mul_of_nonneg_left hs (sq_nonneg _)
      _ = (x - 1) ^ 2 := by rw [hfac]; ring
  have hsq_le : ∀ n : ℕ,
      (∫⁻ u : U, ENNReal.ofReal (((Real.sqrt ((rho n u).toReal) - 1) ^ 2) ^ 2) ∂P)
        ≤ (∫⁻ u : U, ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) ∂P) := by
    intro n
    exact lintegral_mono (fun u => ENNReal.ofReal_le_ofReal (key _ ENNReal.toReal_nonneg))
  have hsmall : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      (∫⁻ u : U, ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) ∂P) ≠ ⊤ ∧
      (∫ u : U, ((rho n u).toReal - 1) ^ 2 ∂P) ≤ δ ∧
      (∫ u : U, ((Real.sqrt ((rho n u).toReal) - 1) ^ 2) ^ 2 ∂P) ≤ δ := by
    intro δ hδ
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (δ / 2) := ENNReal.ofReal_pos.mpr (by linarith)
    have hev : ∀ᶠ n : ℕ in atTop,
        (∫⁻ u : U, ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) ∂P) < ENNReal.ofReal (δ / 2) :=
      hrho_conv.eventually (Iio_mem_nhds hpos)
    filter_upwards [hev] with n hn
    have hne : (∫⁻ u : U, ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) ∂P) ≠ ⊤ :=
      ne_of_lt (lt_of_lt_of_le hn le_top)
    have hLh_le : (∫⁻ u : U, ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) ∂P).toReal ≤ δ / 2 := by
      calc (∫⁻ u : U, ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) ∂P).toReal
          ≤ (ENNReal.ofReal (δ / 2)).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top (le_of_lt hn)
        _ = δ / 2 := ENNReal.toReal_ofReal (by linarith)
    refine ⟨hne, ?_, ?_⟩
    · rw [hh_int_eq n]; linarith
    · rw [hg_int_eq n]
      have h2 : (∫⁻ u : U,
            ENNReal.ofReal (((Real.sqrt ((rho n u).toReal) - 1) ^ 2) ^ 2) ∂P).toReal
          ≤ (∫⁻ u : U, ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) ∂P).toReal :=
        ENNReal.toReal_mono hne (hsq_le n)
      linarith
  have young : ∀ (n : ℕ) (t : ℝ), 0 < t →
      (∫⁻ u : U, ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) ∂P) ≠ ⊤ →
      (∫ u : U, f u * (Real.sqrt ((rho n u).toReal) - 1) ^ 2 ∂P)
        ≤ t / 2 * (∫ u : U, f u ^ 2 ∂P)
          + 1 / (2 * t) * (∫ u : U, ((Real.sqrt ((rho n u).toReal) - 1) ^ 2) ^ 2 ∂P) := by
    intro n t ht hne
    have hLh_lt : (∫⁻ u : U, ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) ∂P) < ⊤ :=
      lt_of_le_of_ne le_top hne
    have hLg_lt : (∫⁻ u : U, ENNReal.ofReal (((Real.sqrt ((rho n u).toReal) - 1) ^ 2) ^ 2) ∂P) < ⊤ :=
      lt_of_le_of_lt (hsq_le n) hLh_lt
    have hae_g2 : AEMeasurable
        (fun u : U => ENNReal.ofReal (((Real.sqrt ((rho n u).toReal) - 1) ^ 2) ^ 2)) P := by
      have h : Measurable
          (fun u : U => ENNReal.ofReal (((Real.sqrt ((rho n u).toReal) - 1) ^ 2) ^ 2)) :=
        ENNReal.measurable_ofReal.comp (hg2m n)
      exact h.aemeasurable
    have hcoef1 : (0:ℝ) < t / 2 := by linarith
    have hcoef2 : (0:ℝ) < 1 / (2 * t) := one_div_pos.mpr (by linarith)
    have hpt : ∀ u : U, ENNReal.ofReal (f u * (Real.sqrt ((rho n u).toReal) - 1) ^ 2)
        ≤ ENNReal.ofReal
            (t / 2 * f u ^ 2 + 1 / (2 * t) * ((Real.sqrt ((rho n u).toReal) - 1) ^ 2) ^ 2) := by
      intro u
      apply ENNReal.ofReal_le_ofReal
      have hkey : t / 2 * f u ^ 2 + 1 / (2 * t) * ((Real.sqrt ((rho n u).toReal) - 1) ^ 2) ^ 2
          - f u * (Real.sqrt ((rho n u).toReal) - 1) ^ 2
          = (t * f u - (Real.sqrt ((rho n u).toReal) - 1) ^ 2) ^ 2 / (2 * t) := by
        have h2t : (2 * t) ≠ 0 := ne_of_gt (by linarith)
        field_simp [h2t]
        ring
      have hnn : 0 ≤ (t * f u - (Real.sqrt ((rho n u).toReal) - 1) ^ 2) ^ 2 / (2 * t) :=
        div_nonneg (sq_nonneg _) (by linarith)
      linarith
    have hsplit : ∀ u : U,
        ENNReal.ofReal (t / 2 * f u ^ 2 + 1 / (2 * t) * ((Real.sqrt ((rho n u).toReal) - 1) ^ 2) ^ 2)
          = ENNReal.ofReal (t / 2) * ENNReal.ofReal (f u ^ 2)
            + ENNReal.ofReal (1 / (2 * t)) * ENNReal.ofReal (((Real.sqrt ((rho n u).toReal) - 1) ^ 2) ^ 2) := by
      intro u
      rw [ENNReal.ofReal_add (mul_nonneg (le_of_lt hcoef1) (sq_nonneg (f u)))
            (mul_nonneg (le_of_lt hcoef2) (sq_nonneg _)),
          ENNReal.ofReal_mul (le_of_lt hcoef1), ENNReal.ofReal_mul (le_of_lt hcoef2)]
    have hRHS : (∫⁻ u : U,
          ENNReal.ofReal (t / 2 * f u ^ 2 + 1 / (2 * t) * ((Real.sqrt ((rho n u).toReal) - 1) ^ 2) ^ 2) ∂P)
        = ENNReal.ofReal (t / 2) * (∫⁻ u : U, ENNReal.ofReal (f u ^ 2) ∂P)
          + ENNReal.ofReal (1 / (2 * t)) *
              (∫⁻ u : U, ENNReal.ofReal (((Real.sqrt ((rho n u).toReal) - 1) ^ 2) ^ 2) ∂P) := by
      simp only [hsplit]
      rw [lintegral_add_left' (hf2_enn.const_mul (ENNReal.ofReal (t / 2))),
        lintegral_const_mul'' (ENNReal.ofReal (t / 2)) hf2_enn,
        lintegral_const_mul'' (ENNReal.ofReal (1 / (2 * t))) hae_g2]
    have hRHS_ne : (∫⁻ u : U,
          ENNReal.ofReal (t / 2 * f u ^ 2 + 1 / (2 * t) * ((Real.sqrt ((rho n u).toReal) - 1) ^ 2) ^ 2) ∂P) ≠ ⊤ := by
      rw [hRHS]
      exact ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_of_lt hf_sq_lt_top),
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_of_lt hLg_lt)⟩
    have htot : (ENNReal.ofReal (t / 2) * (∫⁻ u : U, ENNReal.ofReal (f u ^ 2) ∂P)
          + ENNReal.ofReal (1 / (2 * t)) *
              (∫⁻ u : U, ENNReal.ofReal (((Real.sqrt ((rho n u).toReal) - 1) ^ 2) ^ 2) ∂P)).toReal
        = t / 2 * (∫⁻ u : U, ENNReal.ofReal (f u ^ 2) ∂P).toReal
          + 1 / (2 * t) *
              (∫⁻ u : U, ENNReal.ofReal (((Real.sqrt ((rho n u).toReal) - 1) ^ 2) ^ 2) ∂P).toReal := by
      rw [ENNReal.toReal_add
            (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_of_lt hf_sq_lt_top))
            (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_of_lt hLg_lt)),
        ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (le_of_lt hcoef1), ENNReal.toReal_ofReal (le_of_lt hcoef2)]
    calc ∫ u : U, f u * (Real.sqrt ((rho n u).toReal) - 1) ^ 2 ∂P
        = (∫⁻ u : U, ENNReal.ofReal (f u * (Real.sqrt ((rho n u).toReal) - 1) ^ 2) ∂P).toReal :=
          hfg_int_eq n
      _ ≤ (∫⁻ u : U,
            ENNReal.ofReal (t / 2 * f u ^ 2 + 1 / (2 * t) * ((Real.sqrt ((rho n u).toReal) - 1) ^ 2) ^ 2) ∂P).toReal :=
          ENNReal.toReal_mono hRHS_ne (lintegral_mono hpt)
      _ = t / 2 * (∫⁻ u : U, ENNReal.ofReal (f u ^ 2) ∂P).toReal
            + 1 / (2 * t) *
                (∫⁻ u : U, ENNReal.ofReal (((Real.sqrt ((rho n u).toReal) - 1) ^ 2) ^ 2) ∂P).toReal := by
          rw [hRHS, htot]
      _ = t / 2 * (∫ u : U, f u ^ 2 ∂P)
            + 1 / (2 * t) * (∫ u : U, ((Real.sqrt ((rho n u).toReal) - 1) ^ 2) ^ 2 ∂P) := by
          rw [hf_int_eq, hg_int_eq n]
  have hCnn : (0:ℝ) ≤ ∫ u : U, f u ^ 2 ∂P := integral_nonneg (fun u => sq_nonneg (f u))
  rw [tendsto_order]
  constructor
  · intro b hb
    filter_upwards with n
    exact lt_of_lt_of_le hb
      (integral_nonneg (fun u => mul_nonneg (hf_nonneg u) (sq_nonneg _)))
  · intro a ha
    have hC1 : (0:ℝ) < ∫ u : U, f u ^ 2 ∂P + 1 := by linarith
    have hd : 0 < a * a / (2 * (∫ u : U, f u ^ 2 ∂P + 1)) :=
      div_pos (mul_pos ha ha) (by linarith)
    have ht : 0 < a / (2 * (∫ u : U, f u ^ 2 ∂P + 1)) := div_pos ha (by linarith)
    have hδeq : a / (2 * (∫ u : U, f u ^ 2 ∂P + 1)) * a
        = a * a / (2 * (∫ u : U, f u ^ 2 ∂P + 1)) := by
      field_simp
    filter_upwards [hsmall (a * a / (2 * (∫ u : U, f u ^ 2 ∂P + 1))) hd] with n hn
    obtain ⟨hne, hhle, hgle⟩ := hn
    have hy := young n (a / (2 * (∫ u : U, f u ^ 2 ∂P + 1))) ht hne
    have hcoef : (0:ℝ) ≤ 1 / (2 * (a / (2 * (∫ u : U, f u ^ 2 ∂P + 1)))) :=
      le_of_lt (one_div_pos.mpr (by linarith))
    have hmul := mul_le_mul_of_nonneg_left hgle hcoef
    have hδ : 1 / (2 * (a / (2 * (∫ u : U, f u ^ 2 ∂P + 1))))
        * (a * a / (2 * (∫ u : U, f u ^ 2 ∂P + 1))) = a / 2 := by
      field_simp
    have htb : a / (2 * (∫ u : U, f u ^ 2 ∂P + 1)) / 2 * (∫ u : U, f u ^ 2 ∂P) < a / 2 := by
      field_simp
      nlinarith
    linarith [hy, hmul, hδ, htb]
  /- @proof-region region.target-node.session.c20db78a541a431d end -/

end Statlib.Imported
end

