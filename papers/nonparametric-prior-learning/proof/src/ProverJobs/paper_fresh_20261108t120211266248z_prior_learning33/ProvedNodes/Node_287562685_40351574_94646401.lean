import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_2103907506_2297e1dc_fe47e4b0
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3091194290_4509a8b7_27a85c1e
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3551296407_58969dcf_1b749c74
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3916768571_a9930ecf_948a7b8d

namespace PaperProofTasks.paper_fresh_20261108t120211266248z_prior_learning33




open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261108t120211266248z_prior_learning33.Statlib.Imported

set_option maxRecDepth 10000
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
theorem statopia_math_node_287562685_40351574 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [MeasurableSpace U] [BorelSpace U]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (X : Type*) [TopologicalSpace X]
    (m : ℕ) (hm : 0 < m)
    (e : HilbertBasis ℕ ℝ U) (lam : ℕ → ℝ)
    (hlam_pos : ∀ k : ℕ, 0 < lam k) (hlam_anti : Antitone lam)
    (iotaH : Type*) [Preorder iotaH] (bH : HilbertBasis iotaH ℝ H) (mu : iotaH → ℝ)
    (hmu_pos : ∀ i : iotaH, 0 < mu i) (hmu_anti : Antitone mu)
    (s st alpha : ℝ)
    (Nc : ℕ) (hNc : 0 < Nc)
    (Theta1 : Type*) [NormedAddCommGroup Theta1] [InnerProductSpace ℝ Theta1] [CompleteSpace Theta1]
    (Ptheta : (Fin m → X × H) → (Theta1 × (Fin Nc → ℝ)) → Measure U)
    (hPtheta_isProb : ∀ (S : Fin m → X × H) (theta : Theta1 × (Fin Nc → ℝ)),
      IsProbabilityMeasure (Ptheta S theta))
    (R_u : ℝ) (hR_u : 0 < R_u)
    (beta : ℝ) (hbeta : 0 < beta)
    (M1 : ℝ → ℝ) (hM1_mono : Monotone M1) (hM1_nonneg : ∀ r : ℝ, 0 ≤ M1 r)
    (theta : Theta1 × (Fin Nc → ℝ)) (S : Fin m → X × H)
    (mubar : ℝ) (hmubar : 1 ≤ mubar)
    (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (delta0 : ℝ) (hdelta0 : 0 < delta0)
    (hmoment : ∀ delta : ℝ, 0 ≤ delta → delta < delta0 →
      (∫⁻ u : U, momentExpENN M1 delta (UScaleDist e lam (1 - st) u 0)
        ∂(Ptheta S theta)) ≠ ⊤)
    (Lambda : ℝ)
    (hLambda : Lambda =
      max 1 (sSup {r : ℝ | ∃ k : Fin Nc, r = lam (k : ℕ) / priorEigen lam Nc theta.2 (k : ℕ)}))
    (Bbar : ℝ) (hBbar : Bbar = Real.exp (Lambda * lam 0 * (2 * R_u) ^ 2))
    (hpriorShift : ∀ D : Fin m → X × H,
      Ptheta D theta =
          (Ptheta S theta).withDensity
            (fun u : U => ((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ∧
        (∫⁻ u : U, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ^ 2
            ∂(Ptheta S theta)) ≤ ENNReal.ofReal Bbar),
    let E : ℝ → U → ℝ :=
      fun eta u => (momentExpENN M1 eta (UScaleDist e lam (1 - st) u 0)).toReal
    let rho : (Fin m → X × H) → U → ℝ≥0∞ :=
      fun D u => ((Ptheta D theta).rnDeriv (Ptheta S theta)) u
    let Km : ℝ → ℝ :=
      fun eta => Real.sqrt (∫ u : U, E (2 * eta) u ∂(Ptheta S theta)) * Real.sqrt Bbar
    (∀ (D : Fin m → X × H) (c delta : ℝ),
        0 < 2 * c → 2 * c < delta0 → 0 ≤ delta → delta < delta0 / 2 →
        Integrable (fun u : U => E c u) (Ptheta D theta) ∧
          Integrable (fun u : U => E delta u) (Ptheta D theta) ∧
          (∫ u : U, E c u ∂(Ptheta D theta) ≤
              Real.sqrt (∫ u : U, E (2 * c) u ∂(Ptheta S theta)) *
                Real.sqrt ((∫⁻ u : U, rho D u ^ 2 ∂(Ptheta S theta)).toReal) ∧
            Real.sqrt (∫ u : U, E (2 * c) u ∂(Ptheta S theta)) *
                Real.sqrt ((∫⁻ u : U, rho D u ^ 2 ∂(Ptheta S theta)).toReal) ≤
              Km c)) ∧
      (∀ (delta1 r : ℝ) (D : Fin m → X × H),
        0 < delta1 → 8 * delta1 < delta0 → 0 ≤ r →
        (∀ j : Fin m,
          (HScaleNorm bH mu (alpha - s) (D j).2) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal r) →
        Integrable
            (fun u : U => Real.exp (2 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
              delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2)))
            (Ptheta D theta) ∧
          (∫ u : U, Real.exp (2 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
                delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2))
              ∂(Ptheta D theta)
            ≤ Real.exp ((beta * kappa * r) ^ 2 / (2 * delta1)) * Km (2 * delta1))) := by
  /- @proof-region region.target-node.session.0a8c73c34c8f34cf begin -/
  intro U _ _ _ _ H _ _ X _ m hm e lam hlam_pos hlam_anti iotaH _ bH mu hmu_pos hmu_anti
    s st alpha Nc hNc Theta1 _ _ _ Ptheta hPtheta_isProb R_u hR_u beta hbeta M1 hM1_mono
    hM1_nonneg theta S mubar hmubar kappa hkappa delta0 hdelta0 hmoment Lambda hLambda
    Bbar hBbar hpriorShift
  have hM1m : Measurable M1 := hM1_mono.measurable
  have hterm : ∀ k : ℕ, Measurable (fun u : U =>
      ENNReal.ofReal (Real.rpow (lam k) (-(1 - st)) * (inner ℝ (e k) u) ^ 2)) := by
    intro k
    have hk : Measurable fun u : U => inner ℝ (e k) u := (innerSL ℝ (e k)).measurable
    have hmul : Measurable fun u : U =>
        Real.rpow (lam k) (-(1 - st)) * (inner ℝ (e k) u * inner ℝ (e k) u) :=
      measurable_const.mul (hk.mul hk)
    have hof : Measurable fun u : U => ENNReal.ofReal
        (Real.rpow (lam k) (-(1 - st)) * (inner ℝ (e k) u * inner ℝ (e k) u)) :=
      ENNReal.measurable_ofReal.comp hmul
    simpa only [pow_two] using hof
  have hSN : Measurable (fun u : U => UScaleNorm e lam (1 - st) u) := by
    unfold UScaleNorm
    exact Measurable.ennreal_tsum hterm
  have hrpow : Measurable (fun x : ℝ≥0∞ => x ^ (1 / 2 : ℝ)) :=
    ENNReal.continuous_rpow_const.measurable
  have hDfun : Measurable (fun u : U => UScaleDist e lam (1 - st) u 0) := by
    have hS' : Measurable (fun u : U => UScaleNorm e lam (1 - st) (u - 0)) := by
      simpa only [sub_zero] using hSN
    unfold UScaleDist
    exact hrpow.comp hS'
  have hmoment_meas : ∀ eta : ℝ, Measurable (fun r : ℝ≥0∞ => momentExpENN M1 eta r) := by
    intro eta
    have hg : Measurable (fun r : ℝ≥0∞ =>
        ENNReal.ofReal (Real.exp (eta * (M1 r.toReal) ^ 2))) := by
      have h1 : Measurable fun r : ℝ≥0∞ => M1 r.toReal :=
        hM1m.comp ENNReal.measurable_toReal
      have h2 : Measurable fun r : ℝ≥0∞ => M1 r.toReal * M1 r.toReal := h1.mul h1
      have h3 : Measurable fun r : ℝ≥0∞ => eta * (M1 r.toReal * M1 r.toReal) :=
        measurable_const.mul h2
      have h4 : Measurable fun r : ℝ≥0∞ => Real.exp (eta * (M1 r.toReal * M1 r.toReal)) :=
        Real.continuous_exp.measurable.comp h3
      have h5 : Measurable fun r : ℝ≥0∞ =>
          ENNReal.ofReal (Real.exp (eta * (M1 r.toReal * M1 r.toReal))) :=
        ENNReal.measurable_ofReal.comp h4
      simpa only [pow_two] using h5
    have hset : MeasurableSet {r : ℝ≥0∞ | r < ⊤} :=
      measurableSet_lt measurable_id measurable_const
    have heq : (fun r : ℝ≥0∞ => momentExpENN M1 eta r)
        = fun r : ℝ≥0∞ =>
          if r < ⊤ then ENNReal.ofReal (Real.exp (eta * (M1 r.toReal) ^ 2)) else ⊤ := by
      funext r
      unfold momentExpENN
      by_cases hr : r < ⊤
      · rw [dif_pos hr, if_pos hr]
      · rw [dif_neg hr, if_neg hr]
    rw [heq]
    exact Measurable.ite hset hg measurable_const
  have hmm : ∀ eta : ℝ, Measurable
      (fun u : U => momentExpENN M1 eta (UScaleDist e lam (1 - st) u 0)) :=
    fun eta => (hmoment_meas eta).comp hDfun
  have hKfun : Measurable
      (fun u : U => M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) :=
    hM1m.comp (ENNReal.measurable_toReal.comp hDfun)
  have hgsq : ∀ (eta : ℝ) (r : ℝ≥0∞),
      momentExpENN M1 eta r ^ (2 : ℝ) = momentExpENN M1 (2 * eta) r := by
    intro eta r
    rw [ENNReal.rpow_two, pow_two]
    unfold momentExpENN
    by_cases hr : r < ⊤
    · rw [dif_pos hr, dif_pos hr]
      have hX : Real.exp (eta * (M1 r.toReal) ^ 2) * Real.exp (eta * (M1 r.toReal) ^ 2)
          = Real.exp ((2 * eta) * (M1 r.toReal) ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, hX]
    · rw [dif_neg hr, dif_neg hr]
      exact ENNReal.top_mul ENNReal.top_ne_zero
  have hscale : ∀ᵐ u ∂(Ptheta S theta), UScaleDist e lam (1 - st) u 0 < ⊤ := by
    rw [MeasureTheory.ae_iff]
    by_contra hne
    have h0 : ∫⁻ u, momentExpENN M1 0 (UScaleDist e lam (1 - st) u 0)
        ∂(Ptheta S theta) ≠ ⊤ := hmoment 0 le_rfl hdelta0
    refine h0 ?_
    have hset : MeasurableSet {u : U | ¬ (UScaleDist e lam (1 - st) u 0 < ⊤)} :=
      (measurableSet_lt hDfun measurable_const).compl
    have hmono : ∫⁻ u, {u : U | ¬ (UScaleDist e lam (1 - st) u 0 < ⊤)}.indicator
          (fun _ => ⊤) u ∂(Ptheta S theta)
        ≤ ∫⁻ u, momentExpENN M1 0 (UScaleDist e lam (1 - st) u 0)
            ∂(Ptheta S theta) := by
      refine MeasureTheory.lintegral_mono (fun u => ?_)
      by_cases hu : UScaleDist e lam (1 - st) u 0 < ⊤
      · rw [Set.indicator_of_notMem (not_not_intro hu)]
        exact zero_le _
      · rw [Set.indicator_of_mem (by simpa using hu)]
        unfold momentExpENN
        rw [dif_neg hu]
    have hval : ∫⁻ u, {u : U | ¬ (UScaleDist e lam (1 - st) u 0 < ⊤)}.indicator
          (fun _ => ⊤) u ∂(Ptheta S theta) = ⊤ := by
      rw [MeasureTheory.lintegral_indicator hset, MeasureTheory.lintegral_const,
        show (Ptheta S theta).restrict
              {u : U | ¬ (UScaleDist e lam (1 - st) u 0 < ⊤)} Set.univ
            = (Ptheta S theta) {u : U | ¬ (UScaleDist e lam (1 - st) u 0 < ⊤)} from by
          rw [Measure.restrict_apply MeasurableSet.univ]
          simp]
      exact ENNReal.top_mul hne
    exact top_unique (hval ▸ hmono)
  have hρ_meas_all : ∀ D : Fin m → X × H,
      AEMeasurable (fun u : U => ((Ptheta D theta).rnDeriv (Ptheta S theta)) u)
        (Ptheta S theta) := fun D => (Measure.measurable_rnDeriv _ _).aemeasurable
  have htransfer_all : ∀ (D : Fin m → X × H) (g : U → ℝ≥0∞),
      AEMeasurable g (Ptheta S theta) →
      ∫⁻ u, g u ∂(Ptheta D theta)
        = ∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) * g u
            ∂(Ptheta S theta) := by
    intro D g hg
    have hgen : ∀ (f : U → ℝ≥0∞), AEMeasurable f (Ptheta S theta) →
        ∫⁻ u, g u ∂((Ptheta S theta).withDensity f)
          = ∫⁻ u, f u * g u ∂(Ptheta S theta) := by
      intro f hf
      simpa using (MeasureTheory.setLIntegral_withDensity_eq_lintegral_mul₀
        (μ := Ptheta S theta) (s := Set.univ) (f := f) (g := g) hf hg)
    calc ∫⁻ u, g u ∂(Ptheta D theta)
        = ∫⁻ u, g u ∂((Ptheta S theta).withDensity
            (fun u => ((Ptheta D theta).rnDeriv (Ptheta S theta)) u)) := by
          conv_lhs => rw [(hpriorShift D).1]
      _ = ∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) * g u
            ∂(Ptheta S theta) := hgen _ (hρ_meas_all D)
  have hρ2_all : ∀ D : Fin m → X × H,
      ∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ^ (2 : ℝ)
        ∂(Ptheta S theta) ≠ ⊤ := by
    intro D
    have hle := (hpriorShift D).2
    rw [← MeasureTheory.lintegral_congr (fun u => ENNReal.rpow_two _)] at hle
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hfin_all : ∀ (D : Fin m → X × H) (eta : ℝ), 0 ≤ 2 * eta → 2 * eta < delta0 →
      ∫⁻ u, momentExpENN M1 eta (UScaleDist e lam (1 - st) u 0)
        ∂(Ptheta D theta) ≠ ⊤ := by
    intro D eta h2eta h2eta'
    have hρ2 := hρ2_all D
    have hg2 : ∫⁻ u, (momentExpENN M1 eta (UScaleDist e lam (1 - st) u 0)) ^ (2 : ℝ)
        ∂(Ptheta S theta) ≠ ⊤ := by
      rw [MeasureTheory.lintegral_congr (fun u => hgsq eta _)]
      exact hmoment (2 * eta) h2eta h2eta'
    have hfac1 : (∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ^ (2 : ℝ)
          ∂(Ptheta S theta)) ^ (1 / 2 : ℝ) ≠ ⊤ := by
      have hlt : (∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ^ (2 : ℝ)
            ∂(Ptheta S theta)) ^ (1 / 2 : ℝ) < ⊤ := by
        rw [ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        exact lt_top_iff_ne_top.mpr hρ2
      exact ne_of_lt hlt
    have hfac2 : (∫⁻ u, (momentExpENN M1 eta (UScaleDist e lam (1 - st) u 0)) ^ (2 : ℝ)
          ∂(Ptheta S theta)) ^ (1 / 2 : ℝ) ≠ ⊤ := by
      have hlt : (∫⁻ u, (momentExpENN M1 eta (UScaleDist e lam (1 - st) u 0)) ^ (2 : ℝ)
            ∂(Ptheta S theta)) ^ (1 / 2 : ℝ) < ⊤ := by
        rw [ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        exact lt_top_iff_ne_top.mpr hg2
      exact ne_of_lt hlt
    have hbd : ∫⁻ u, momentExpENN M1 eta (UScaleDist e lam (1 - st) u 0)
          ∂(Ptheta D theta)
        ≤ (∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ^ (2 : ℝ)
            ∂(Ptheta S theta)) ^ (1 / 2 : ℝ) *
          (∫⁻ u, (momentExpENN M1 eta (UScaleDist e lam (1 - st) u 0)) ^ (2 : ℝ)
            ∂(Ptheta S theta)) ^ (1 / 2 : ℝ) := by
      rw [htransfer_all D _ ((hmm eta).aemeasurable)]
      exact ENNReal.lintegral_mul_le_Lp_mul_Lq (Ptheta S theta) (p := 2) (q := 2)
        Real.HolderConjugate.two_two (hρ_meas_all D) ((hmm eta).aemeasurable)
    exact ne_of_lt (lt_of_le_of_lt hbd
      (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top hfac1 hfac2)))
  have hρ2bd_all : ∀ D : Fin m → X × H,
      (∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ^ 2
        ∂(Ptheta S theta)).toReal ≤ Bbar := by
    intro D
    have hB : (0 : ℝ) ≤ Bbar := by
      rw [hBbar]
      exact (Real.exp_pos _).le
    have h1 := ENNReal.toReal_mono (ENNReal.ofReal_ne_top (r := Bbar)) (hpriorShift D).2
    rwa [ENNReal.toReal_ofReal hB] at h1
  have hmain_all : ∀ (D : Fin m → X × H) (c : ℝ), 0 ≤ 2 * c → 2 * c < delta0 →
      (∫ u : U, (momentExpENN M1 c (UScaleDist e lam (1 - st) u 0)).toReal
          ∂(Ptheta D theta))
        ≤ Real.sqrt (∫ u : U, (momentExpENN M1 (2 * c)
            (UScaleDist e lam (1 - st) u 0)).toReal ∂(Ptheta S theta)) *
          Real.sqrt ((∫⁻ u : U, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ^ 2
            ∂(Ptheta S theta)).toReal) := by
    intro D c h2c0 h2c1
    have hIntC : Integrable (fun u : U =>
        (momentExpENN M1 c (UScaleDist e lam (1 - st) u 0)).toReal) (Ptheta D theta) :=
      MeasureTheory.integrable_toReal_of_lintegral_ne_top ((hmm c).aemeasurable)
        (hfin_all D c h2c0 h2c1)
    have hg2' : ∫⁻ u, (momentExpENN M1 c (UScaleDist e lam (1 - st) u 0)) ^ (2 : ℝ)
        ∂(Ptheta S theta) ≠ ⊤ := by
      rw [MeasureTheory.lintegral_congr (fun u => hgsq c _)]
      exact hmoment (2 * c) h2c0 h2c1
    have hbd : ∫⁻ u, momentExpENN M1 c (UScaleDist e lam (1 - st) u 0)
          ∂(Ptheta D theta)
        ≤ (∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ^ (2 : ℝ)
            ∂(Ptheta S theta)) ^ (1 / 2 : ℝ) *
          (∫⁻ u, (momentExpENN M1 c (UScaleDist e lam (1 - st) u 0)) ^ (2 : ℝ)
            ∂(Ptheta S theta)) ^ (1 / 2 : ℝ) := by
      rw [htransfer_all D _ ((hmm c).aemeasurable)]
      exact ENNReal.lintegral_mul_le_Lp_mul_Lq (Ptheta S theta) (p := 2) (q := 2)
        Real.HolderConjugate.two_two (hρ_meas_all D) ((hmm c).aemeasurable)
    have hleE : ∫⁻ u, ENNReal.ofReal
          ((momentExpENN M1 c (UScaleDist e lam (1 - st) u 0)).toReal)
          ∂(Ptheta D theta)
        ≤ ∫⁻ u, momentExpENN M1 c (UScaleDist e lam (1 - st) u 0)
            ∂(Ptheta D theta) := by
      refine MeasureTheory.lintegral_mono (fun u => ?_)
      by_cases htop : momentExpENN M1 c (UScaleDist e lam (1 - st) u 0) = ⊤
      · rw [htop]
        simp
      · rw [ENNReal.ofReal_toReal htop]
    have hstep : (∫ u, (momentExpENN M1 c (UScaleDist e lam (1 - st) u 0)).toReal
          ∂(Ptheta D theta))
        = (∫⁻ u, ENNReal.ofReal
            ((momentExpENN M1 c (UScaleDist e lam (1 - st) u 0)).toReal)
            ∂(Ptheta D theta)).toReal := by
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntC
          (Filter.Eventually.of_forall (fun u => ENNReal.toReal_nonneg)),
        ENNReal.toReal_ofReal
          (MeasureTheory.integral_nonneg (fun u => ENNReal.toReal_nonneg))]
    have hf1 : (∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ^ (2 : ℝ)
          ∂(Ptheta S theta)) ^ (1 / 2 : ℝ) ≠ ⊤ := by
      have hlt : (∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ^ (2 : ℝ)
            ∂(Ptheta S theta)) ^ (1 / 2 : ℝ) < ⊤ := by
        rw [ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        exact lt_top_iff_ne_top.mpr (hρ2_all D)
      exact ne_of_lt hlt
    have hf2 : (∫⁻ u, (momentExpENN M1 c (UScaleDist e lam (1 - st) u 0)) ^ (2 : ℝ)
          ∂(Ptheta S theta)) ^ (1 / 2 : ℝ) ≠ ⊤ := by
      have hlt : (∫⁻ u, (momentExpENN M1 c (UScaleDist e lam (1 - st) u 0)) ^ (2 : ℝ)
            ∂(Ptheta S theta)) ^ (1 / 2 : ℝ) < ⊤ := by
        rw [ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        exact lt_top_iff_ne_top.mpr hg2'
      exact ne_of_lt hlt
    have hFac1 : (∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ^ (2 : ℝ)
          ∂(Ptheta S theta))
        = ∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ^ 2
            ∂(Ptheta S theta) :=
      MeasureTheory.lintegral_congr (fun u => ENNReal.rpow_two _)
    have hFac2 : (∫⁻ u, (momentExpENN M1 c (UScaleDist e lam (1 - st) u 0)) ^ (2 : ℝ)
          ∂(Ptheta S theta))
        = ENNReal.ofReal (∫ u, (momentExpENN M1 (2 * c)
            (UScaleDist e lam (1 - st) u 0)).toReal ∂(Ptheta S theta)) := by
      rw [MeasureTheory.lintegral_congr (fun u => hgsq c _)]
      have h2c_int : Integrable (fun u : U =>
          (momentExpENN M1 (2 * c) (UScaleDist e lam (1 - st) u 0)).toReal)
          (Ptheta S theta) :=
        MeasureTheory.integrable_toReal_of_lintegral_ne_top ((hmm (2 * c)).aemeasurable)
          (hmoment (2 * c) (by linarith) h2c1)
      have hae : (fun u : U => ENNReal.ofReal
            ((momentExpENN M1 (2 * c) (UScaleDist e lam (1 - st) u 0)).toReal))
          =ᵐ[Ptheta S theta]
          (fun u : U => momentExpENN M1 (2 * c) (UScaleDist e lam (1 - st) u 0)) := by
        filter_upwards [hscale] with u hu
        have hval : momentExpENN M1 (2 * c) (UScaleDist e lam (1 - st) u 0)
            = ENNReal.ofReal
              (Real.exp ((2 * c) * (M1 (UScaleDist e lam (1 - st) u 0).toReal) ^ 2)) := by
          unfold momentExpENN
          rw [dif_pos hu]
        rw [hval, ENNReal.ofReal_toReal ENNReal.ofReal_ne_top]
      rw [← MeasureTheory.lintegral_congr_ae hae]
      exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal h2c_int
        (Filter.Eventually.of_forall (fun u => ENNReal.toReal_nonneg))).symm
    have hnn2 : (0 : ℝ) ≤ ∫ u : U, (momentExpENN M1 (2 * c)
        (UScaleDist e lam (1 - st) u 0)).toReal ∂(Ptheta S theta) :=
      integral_nonneg (fun u => ENNReal.toReal_nonneg)
    have hsqrt1 : ((∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ^ (2 : ℝ)
          ∂(Ptheta S theta)) ^ (1 / 2 : ℝ)).toReal
        = Real.sqrt ((∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ^ 2
          ∂(Ptheta S theta)).toReal) := by
      rw [← ENNReal.toReal_rpow, hFac1, ← Real.sqrt_eq_rpow]
    have hsqrt2 : ((∫⁻ u, (momentExpENN M1 c (UScaleDist e lam (1 - st) u 0)) ^ (2 : ℝ)
          ∂(Ptheta S theta)) ^ (1 / 2 : ℝ)).toReal
        = Real.sqrt (∫ u, (momentExpENN M1 (2 * c)
            (UScaleDist e lam (1 - st) u 0)).toReal ∂(Ptheta S theta)) := by
      rw [← ENNReal.toReal_rpow, hFac2, ENNReal.toReal_ofReal hnn2, ← Real.sqrt_eq_rpow]
    have hprod : ((∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ^ (2 : ℝ)
            ∂(Ptheta S theta)) ^ (1 / 2 : ℝ) *
          (∫⁻ u, (momentExpENN M1 c (UScaleDist e lam (1 - st) u 0)) ^ (2 : ℝ)
            ∂(Ptheta S theta)) ^ (1 / 2 : ℝ)).toReal
        = Real.sqrt (∫ u, (momentExpENN M1 (2 * c)
            (UScaleDist e lam (1 - st) u 0)).toReal ∂(Ptheta S theta)) *
          Real.sqrt ((∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ^ 2
            ∂(Ptheta S theta)).toReal) := by
      rw [ENNReal.toReal_mul, hsqrt1, hsqrt2]
      exact mul_comm _ _
    calc (∫ u, (momentExpENN M1 c (UScaleDist e lam (1 - st) u 0)).toReal
            ∂(Ptheta D theta))
        = (∫⁻ u, ENNReal.ofReal
            ((momentExpENN M1 c (UScaleDist e lam (1 - st) u 0)).toReal)
            ∂(Ptheta D theta)).toReal := hstep
      _ ≤ (∫⁻ u, momentExpENN M1 c (UScaleDist e lam (1 - st) u 0)
            ∂(Ptheta D theta)).toReal :=
          ENNReal.toReal_mono (hfin_all D c h2c0 h2c1) hleE
      _ ≤ ((∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ^ (2 : ℝ)
              ∂(Ptheta S theta)) ^ (1 / 2 : ℝ) *
            (∫⁻ u, (momentExpENN M1 c (UScaleDist e lam (1 - st) u 0)) ^ (2 : ℝ)
              ∂(Ptheta S theta)) ^ (1 / 2 : ℝ)).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top hf1 hf2) hbd
      _ = Real.sqrt (∫ u, (momentExpENN M1 (2 * c)
            (UScaleDist e lam (1 - st) u 0)).toReal ∂(Ptheta S theta)) *
          Real.sqrt ((∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ^ 2
            ∂(Ptheta S theta)).toReal) := hprod


  refine ⟨?_, ?_⟩
  · intro D c delta h2c h2cdelta hdelta_nn hdelta_lt
    have hM1m : Measurable M1 := hM1_mono.measurable
    have hterm : ∀ k : ℕ, Measurable (fun u : U =>
        ENNReal.ofReal (Real.rpow (lam k) (-(1 - st)) * (inner ℝ (e k) u) ^ 2)) := by
      intro k
      have hk : Measurable fun u : U => inner ℝ (e k) u := (innerSL ℝ (e k)).measurable
      have hmul : Measurable fun u : U =>
          Real.rpow (lam k) (-(1 - st)) * (inner ℝ (e k) u * inner ℝ (e k) u) :=
        measurable_const.mul (hk.mul hk)
      have hof : Measurable fun u : U => ENNReal.ofReal
          (Real.rpow (lam k) (-(1 - st)) * (inner ℝ (e k) u * inner ℝ (e k) u)) :=
        ENNReal.measurable_ofReal.comp hmul
      simpa only [pow_two] using hof
    have hSN : Measurable (fun u : U => UScaleNorm e lam (1 - st) u) := by
      unfold UScaleNorm
      exact Measurable.ennreal_tsum hterm
    have hrpow : Measurable (fun x : ℝ≥0∞ => x ^ (1 / 2 : ℝ)) :=
      ENNReal.continuous_rpow_const.measurable
    have hDfun : Measurable (fun u : U => UScaleDist e lam (1 - st) u 0) := by
      have hS' : Measurable (fun u : U => UScaleNorm e lam (1 - st) (u - 0)) := by
        simpa only [sub_zero] using hSN
      unfold UScaleDist
      exact hrpow.comp hS'
    have hmoment_meas : ∀ eta : ℝ, Measurable (fun r : ℝ≥0∞ => momentExpENN M1 eta r) := by
      intro eta
      have hg : Measurable (fun r : ℝ≥0∞ =>
          ENNReal.ofReal (Real.exp (eta * (M1 r.toReal) ^ 2))) := by
        have h1 : Measurable fun r : ℝ≥0∞ => M1 r.toReal :=
          hM1m.comp ENNReal.measurable_toReal
        have h2 : Measurable fun r : ℝ≥0∞ => M1 r.toReal * M1 r.toReal := h1.mul h1
        have h3 : Measurable fun r : ℝ≥0∞ => eta * (M1 r.toReal * M1 r.toReal) :=
          measurable_const.mul h2
        have h4 : Measurable fun r : ℝ≥0∞ => Real.exp (eta * (M1 r.toReal * M1 r.toReal)) :=
          Real.continuous_exp.measurable.comp h3
        have h5 : Measurable fun r : ℝ≥0∞ =>
            ENNReal.ofReal (Real.exp (eta * (M1 r.toReal * M1 r.toReal))) :=
          ENNReal.measurable_ofReal.comp h4
        simpa only [pow_two] using h5
      have hset : MeasurableSet {r : ℝ≥0∞ | r < ⊤} :=
        measurableSet_lt measurable_id measurable_const
      have heq : (fun r : ℝ≥0∞ => momentExpENN M1 eta r)
          = fun r : ℝ≥0∞ =>
            if r < ⊤ then ENNReal.ofReal (Real.exp (eta * (M1 r.toReal) ^ 2)) else ⊤ := by
        funext r
        unfold momentExpENN
        by_cases hr : r < ⊤
        · rw [dif_pos hr, if_pos hr]
        · rw [dif_neg hr, if_neg hr]
      rw [heq]
      exact Measurable.ite hset hg measurable_const
    have hmm : ∀ eta : ℝ, Measurable
        (fun u : U => momentExpENN M1 eta (UScaleDist e lam (1 - st) u 0)) :=
      fun eta => (hmoment_meas eta).comp hDfun
    have hKfun : Measurable
        (fun u : U => M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) :=
      hM1m.comp (ENNReal.measurable_toReal.comp hDfun)
    have hρ_meas : AEMeasurable (fun u : U => ((Ptheta D theta).rnDeriv (Ptheta S theta)) u)
        (Ptheta S theta) := (Measure.measurable_rnDeriv _ _).aemeasurable
    have htransfer : ∀ (g : U → ℝ≥0∞), AEMeasurable g (Ptheta S theta) →
        ∫⁻ u, g u ∂(Ptheta D theta)
          = ∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) * g u
              ∂(Ptheta S theta) := by
      intro g hg
      have hgen : ∀ (f : U → ℝ≥0∞), AEMeasurable f (Ptheta S theta) →
          ∫⁻ u, g u ∂((Ptheta S theta).withDensity f)
            = ∫⁻ u, f u * g u ∂(Ptheta S theta) := by
        intro f hf
        simpa using (MeasureTheory.setLIntegral_withDensity_eq_lintegral_mul₀
          (μ := Ptheta S theta) (s := Set.univ) (f := f) (g := g) hf hg)
      calc ∫⁻ u, g u ∂(Ptheta D theta)
          = ∫⁻ u, g u ∂((Ptheta S theta).withDensity
              (fun u => ((Ptheta D theta).rnDeriv (Ptheta S theta)) u)) := by
            conv_lhs => rw [(hpriorShift D).1]
        _ = ∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) * g u
              ∂(Ptheta S theta) := hgen _ hρ_meas
    have hgsq : ∀ (eta : ℝ) (r : ℝ≥0∞),
        momentExpENN M1 eta r ^ (2 : ℝ) = momentExpENN M1 (2 * eta) r := by
      intro eta r
      rw [ENNReal.rpow_two, pow_two]
      unfold momentExpENN
      by_cases hr : r < ⊤
      · rw [dif_pos hr, dif_pos hr]
        have hX : Real.exp (eta * (M1 r.toReal) ^ 2) * Real.exp (eta * (M1 r.toReal) ^ 2)
            = Real.exp ((2 * eta) * (M1 r.toReal) ^ 2) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, hX]
      · rw [dif_neg hr, dif_neg hr]
        exact ENNReal.top_mul ENNReal.top_ne_zero
    have hρ2 : ∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ^ (2 : ℝ)
        ∂(Ptheta S theta) ≠ ⊤ := by
      have hle := (hpriorShift D).2
      rw [← MeasureTheory.lintegral_congr (fun u => ENNReal.rpow_two _)] at hle
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
    have hfin : ∀ (eta : ℝ), 0 ≤ 2 * eta → 2 * eta < delta0 →
        ∫⁻ u, momentExpENN M1 eta (UScaleDist e lam (1 - st) u 0)
          ∂(Ptheta D theta) ≠ ⊤ := by
      intro eta h2eta h2eta'
      have hg2 : ∫⁻ u, (momentExpENN M1 eta (UScaleDist e lam (1 - st) u 0)) ^ (2 : ℝ)
          ∂(Ptheta S theta) ≠ ⊤ := by
        rw [MeasureTheory.lintegral_congr (fun u => hgsq eta _)]
        exact hmoment (2 * eta) h2eta h2eta'
      have hfac1 : (∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ^ (2 : ℝ)
            ∂(Ptheta S theta)) ^ (1 / 2 : ℝ) ≠ ⊤ := by
        have hlt : (∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ^ (2 : ℝ)
              ∂(Ptheta S theta)) ^ (1 / 2 : ℝ) < ⊤ := by
          rw [ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          exact lt_top_iff_ne_top.mpr hρ2
        exact ne_of_lt hlt
      have hfac2 : (∫⁻ u, (momentExpENN M1 eta (UScaleDist e lam (1 - st) u 0)) ^ (2 : ℝ)
            ∂(Ptheta S theta)) ^ (1 / 2 : ℝ) ≠ ⊤ := by
        have hlt : (∫⁻ u, (momentExpENN M1 eta (UScaleDist e lam (1 - st) u 0)) ^ (2 : ℝ)
              ∂(Ptheta S theta)) ^ (1 / 2 : ℝ) < ⊤ := by
          rw [ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          exact lt_top_iff_ne_top.mpr hg2
        exact ne_of_lt hlt
      have hbd : ∫⁻ u, momentExpENN M1 eta (UScaleDist e lam (1 - st) u 0)
            ∂(Ptheta D theta)
          ≤ (∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ^ (2 : ℝ)
              ∂(Ptheta S theta)) ^ (1 / 2 : ℝ) *
            (∫⁻ u, (momentExpENN M1 eta (UScaleDist e lam (1 - st) u 0)) ^ (2 : ℝ)
              ∂(Ptheta S theta)) ^ (1 / 2 : ℝ) := by
        rw [htransfer _ ((hmm eta).aemeasurable)]
        exact ENNReal.lintegral_mul_le_Lp_mul_Lq (Ptheta S theta) (p := 2) (q := 2)
          Real.HolderConjugate.two_two hρ_meas ((hmm eta).aemeasurable)
      exact ne_of_lt (lt_of_le_of_lt hbd
        (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top hfac1 hfac2)))
    have hscale : ∀ᵐ u ∂(Ptheta S theta), UScaleDist e lam (1 - st) u 0 < ⊤ := by
      rw [MeasureTheory.ae_iff]
      by_contra hne
      have h0 : ∫⁻ u, momentExpENN M1 0 (UScaleDist e lam (1 - st) u 0)
          ∂(Ptheta S theta) ≠ ⊤ := hmoment 0 le_rfl hdelta0
      refine h0 ?_
      have hset : MeasurableSet {u : U | ¬ (UScaleDist e lam (1 - st) u 0 < ⊤)} :=
        (measurableSet_lt hDfun measurable_const).compl
      have hmono : ∫⁻ u, {u : U | ¬ (UScaleDist e lam (1 - st) u 0 < ⊤)}.indicator
            (fun _ => ⊤) u ∂(Ptheta S theta)
          ≤ ∫⁻ u, momentExpENN M1 0 (UScaleDist e lam (1 - st) u 0)
              ∂(Ptheta S theta) := by
        refine MeasureTheory.lintegral_mono (fun u => ?_)
        by_cases hu : UScaleDist e lam (1 - st) u 0 < ⊤
        · rw [Set.indicator_of_notMem (not_not_intro hu)]
          exact zero_le _
        · rw [Set.indicator_of_mem (by simpa using hu)]
          unfold momentExpENN
          rw [dif_neg hu]
      have hval : ∫⁻ u, {u : U | ¬ (UScaleDist e lam (1 - st) u 0 < ⊤)}.indicator
            (fun _ => ⊤) u ∂(Ptheta S theta) = ⊤ := by
        rw [MeasureTheory.lintegral_indicator hset, MeasureTheory.lintegral_const,
          show (Ptheta S theta).restrict
                {u : U | ¬ (UScaleDist e lam (1 - st) u 0 < ⊤)} Set.univ
              = (Ptheta S theta) {u : U | ¬ (UScaleDist e lam (1 - st) u 0 < ⊤)} from by
            rw [Measure.restrict_apply MeasurableSet.univ]
            simp]
        exact ENNReal.top_mul hne
      exact top_unique (hval ▸ hmono)
    have hIntC : Integrable (fun u : U =>
        (momentExpENN M1 c (UScaleDist e lam (1 - st) u 0)).toReal) (Ptheta D theta) :=
      MeasureTheory.integrable_toReal_of_lintegral_ne_top ((hmm c).aemeasurable)
        (hfin c (le_of_lt h2c) h2cdelta)
    have hIntD : Integrable (fun u : U =>
        (momentExpENN M1 delta (UScaleDist e lam (1 - st) u 0)).toReal)
        (Ptheta D theta) :=
      MeasureTheory.integrable_toReal_of_lintegral_ne_top ((hmm delta).aemeasurable)
        (hfin delta (by linarith) (by linarith))
    refine ⟨hIntC, hIntD, ?_, ?_⟩
    · have hg2' : ∫⁻ u, (momentExpENN M1 c (UScaleDist e lam (1 - st) u 0)) ^ (2 : ℝ)
          ∂(Ptheta S theta) ≠ ⊤ := by
        rw [MeasureTheory.lintegral_congr (fun u => hgsq c _)]
        exact hmoment (2 * c) (le_of_lt h2c) h2cdelta
      have hbd : ∫⁻ u, momentExpENN M1 c (UScaleDist e lam (1 - st) u 0)
            ∂(Ptheta D theta)
          ≤ (∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ^ (2 : ℝ)
              ∂(Ptheta S theta)) ^ (1 / 2 : ℝ) *
            (∫⁻ u, (momentExpENN M1 c (UScaleDist e lam (1 - st) u 0)) ^ (2 : ℝ)
              ∂(Ptheta S theta)) ^ (1 / 2 : ℝ) := by
        rw [htransfer _ ((hmm c).aemeasurable)]
        exact ENNReal.lintegral_mul_le_Lp_mul_Lq (Ptheta S theta) (p := 2) (q := 2)
          Real.HolderConjugate.two_two hρ_meas ((hmm c).aemeasurable)
      have hleE : ∫⁻ u, ENNReal.ofReal
            ((momentExpENN M1 c (UScaleDist e lam (1 - st) u 0)).toReal)
            ∂(Ptheta D theta)
          ≤ ∫⁻ u, momentExpENN M1 c (UScaleDist e lam (1 - st) u 0)
              ∂(Ptheta D theta) := by
        refine MeasureTheory.lintegral_mono (fun u => ?_)
        by_cases htop : momentExpENN M1 c (UScaleDist e lam (1 - st) u 0) = ⊤
        · rw [htop]
          simp
        · rw [ENNReal.ofReal_toReal htop]
      have hstep : (∫ u, (momentExpENN M1 c (UScaleDist e lam (1 - st) u 0)).toReal
            ∂(Ptheta D theta))
          = (∫⁻ u, ENNReal.ofReal
              ((momentExpENN M1 c (UScaleDist e lam (1 - st) u 0)).toReal)
              ∂(Ptheta D theta)).toReal := by
        rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntC
            (Filter.Eventually.of_forall (fun u => ENNReal.toReal_nonneg)),
          ENNReal.toReal_ofReal
            (MeasureTheory.integral_nonneg (fun u => ENNReal.toReal_nonneg))]
      have hf1 : (∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ^ (2 : ℝ)
            ∂(Ptheta S theta)) ^ (1 / 2 : ℝ) ≠ ⊤ := by
        have hlt : (∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ^ (2 : ℝ)
              ∂(Ptheta S theta)) ^ (1 / 2 : ℝ) < ⊤ := by
          rw [ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          exact lt_top_iff_ne_top.mpr hρ2
        exact ne_of_lt hlt
      have hf2 : (∫⁻ u, (momentExpENN M1 c (UScaleDist e lam (1 - st) u 0)) ^ (2 : ℝ)
            ∂(Ptheta S theta)) ^ (1 / 2 : ℝ) ≠ ⊤ := by
        have hlt : (∫⁻ u, (momentExpENN M1 c (UScaleDist e lam (1 - st) u 0)) ^ (2 : ℝ)
              ∂(Ptheta S theta)) ^ (1 / 2 : ℝ) < ⊤ := by
          rw [ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          exact lt_top_iff_ne_top.mpr hg2'
        exact ne_of_lt hlt
      have hFac1 : (∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ^ (2 : ℝ)
            ∂(Ptheta S theta))
          = ∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ^ 2
              ∂(Ptheta S theta) :=
        MeasureTheory.lintegral_congr (fun u => ENNReal.rpow_two _)
      have hFac2 : (∫⁻ u, (momentExpENN M1 c (UScaleDist e lam (1 - st) u 0)) ^ (2 : ℝ)
            ∂(Ptheta S theta))
          = ENNReal.ofReal (∫ u, (momentExpENN M1 (2 * c)
              (UScaleDist e lam (1 - st) u 0)).toReal ∂(Ptheta S theta)) := by
        rw [MeasureTheory.lintegral_congr (fun u => hgsq c _)]
        have h2c_int : Integrable (fun u : U =>
            (momentExpENN M1 (2 * c) (UScaleDist e lam (1 - st) u 0)).toReal)
            (Ptheta S theta) :=
          MeasureTheory.integrable_toReal_of_lintegral_ne_top ((hmm (2 * c)).aemeasurable)
            (hmoment (2 * c) (by linarith) h2cdelta)
        have hae : (fun u : U => ENNReal.ofReal
              ((momentExpENN M1 (2 * c) (UScaleDist e lam (1 - st) u 0)).toReal))
            =ᵐ[Ptheta S theta]
            (fun u : U => momentExpENN M1 (2 * c) (UScaleDist e lam (1 - st) u 0)) := by
          filter_upwards [hscale] with u hu
          have hval : momentExpENN M1 (2 * c) (UScaleDist e lam (1 - st) u 0)
              = ENNReal.ofReal
                (Real.exp ((2 * c) * (M1 (UScaleDist e lam (1 - st) u 0).toReal) ^ 2)) := by
            unfold momentExpENN
            rw [dif_pos hu]
          rw [hval, ENNReal.ofReal_toReal ENNReal.ofReal_ne_top]
        rw [← MeasureTheory.lintegral_congr_ae hae]
        exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal h2c_int
          (Filter.Eventually.of_forall (fun u => ENNReal.toReal_nonneg))).symm
      have hnn2 : (0 : ℝ) ≤ ∫ u : U, (momentExpENN M1 (2 * c)
          (UScaleDist e lam (1 - st) u 0)).toReal ∂(Ptheta S theta) :=
        integral_nonneg (fun u => ENNReal.toReal_nonneg)
      have hsqrt1 : ((∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ^ (2 : ℝ)
            ∂(Ptheta S theta)) ^ (1 / 2 : ℝ)).toReal
          = Real.sqrt ((∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ^ 2
            ∂(Ptheta S theta)).toReal) := by
        rw [← ENNReal.toReal_rpow, hFac1, ← Real.sqrt_eq_rpow]
      have hsqrt2 : ((∫⁻ u, (momentExpENN M1 c (UScaleDist e lam (1 - st) u 0)) ^ (2 : ℝ)
            ∂(Ptheta S theta)) ^ (1 / 2 : ℝ)).toReal
          = Real.sqrt (∫ u, (momentExpENN M1 (2 * c)
              (UScaleDist e lam (1 - st) u 0)).toReal ∂(Ptheta S theta)) := by
        rw [← ENNReal.toReal_rpow, hFac2, ENNReal.toReal_ofReal hnn2, ← Real.sqrt_eq_rpow]
      have hprod : ((∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ^ (2 : ℝ)
              ∂(Ptheta S theta)) ^ (1 / 2 : ℝ) *
            (∫⁻ u, (momentExpENN M1 c (UScaleDist e lam (1 - st) u 0)) ^ (2 : ℝ)
              ∂(Ptheta S theta)) ^ (1 / 2 : ℝ)).toReal
          = Real.sqrt (∫ u, (momentExpENN M1 (2 * c)
              (UScaleDist e lam (1 - st) u 0)).toReal ∂(Ptheta S theta)) *
            Real.sqrt ((∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ^ 2
              ∂(Ptheta S theta)).toReal) := by
        rw [ENNReal.toReal_mul, hsqrt1, hsqrt2]
        exact mul_comm _ _
      calc (∫ u, (momentExpENN M1 c (UScaleDist e lam (1 - st) u 0)).toReal
              ∂(Ptheta D theta))
          = (∫⁻ u, ENNReal.ofReal
              ((momentExpENN M1 c (UScaleDist e lam (1 - st) u 0)).toReal)
              ∂(Ptheta D theta)).toReal := hstep
        _ ≤ (∫⁻ u, momentExpENN M1 c (UScaleDist e lam (1 - st) u 0)
              ∂(Ptheta D theta)).toReal :=
            ENNReal.toReal_mono (hfin c (le_of_lt h2c) h2cdelta) hleE
        _ ≤ ((∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ^ (2 : ℝ)
                ∂(Ptheta S theta)) ^ (1 / 2 : ℝ) *
              (∫⁻ u, (momentExpENN M1 c (UScaleDist e lam (1 - st) u 0)) ^ (2 : ℝ)
                ∂(Ptheta S theta)) ^ (1 / 2 : ℝ)).toReal :=
            ENNReal.toReal_mono (ENNReal.mul_ne_top hf1 hf2) hbd
        _ = Real.sqrt (∫ u, (momentExpENN M1 (2 * c)
              (UScaleDist e lam (1 - st) u 0)).toReal ∂(Ptheta S theta)) *
            Real.sqrt ((∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ^ 2
              ∂(Ptheta S theta)).toReal) := hprod
    · have hB : (0 : ℝ) ≤ Bbar := by
        rw [hBbar]
        exact (Real.exp_pos _).le
      have hle : (∫⁻ u : U, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ^ 2
            ∂(Ptheta S theta)).toReal ≤ Bbar := by
        have h1 := ENNReal.toReal_mono (ENNReal.ofReal_ne_top (r := Bbar)) (hpriorShift D).2
        rwa [ENNReal.toReal_ofReal hB] at h1
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hle) (Real.sqrt_nonneg _)
  · intro delta1 r D hd1 h8 hr hD
    have hs_neg : MeasurableSet {u : U | ¬ (UScaleDist e lam (1 - st) u 0 < ⊤)} :=
      (measurableSet_lt hDfun measurable_const).compl
    have hbase_zero : (Ptheta S theta) {u : U | ¬ (UScaleDist e lam (1 - st) u 0 < ⊤)} = 0 := by
      rw [← MeasureTheory.ae_iff]
      exact hscale
    have hPD_zero : (Ptheta D theta) {u : U | ¬ (UScaleDist e lam (1 - st) u 0 < ⊤)} = 0 := by
      have hind : AEMeasurable
          ({u : U | ¬ (UScaleDist e lam (1 - st) u 0 < ⊤)}.indicator (fun _ => (1 : ℝ≥0∞)))
          (Ptheta S theta) :=
        (Measurable.ite hs_neg measurable_const measurable_const).aemeasurable
      have h1 : (Ptheta D theta) {u : U | ¬ (UScaleDist e lam (1 - st) u 0 < ⊤)}
          = ∫⁻ u, {u : U | ¬ (UScaleDist e lam (1 - st) u 0 < ⊤)}.indicator
              (fun _ => (1 : ℝ≥0∞)) u ∂(Ptheta D theta) := by
        rw [MeasureTheory.lintegral_indicator hs_neg, MeasureTheory.lintegral_const,
          show (Ptheta D theta).restrict
                {u : U | ¬ (UScaleDist e lam (1 - st) u 0 < ⊤)} Set.univ
              = (Ptheta D theta) {u : U | ¬ (UScaleDist e lam (1 - st) u 0 < ⊤)} from by
            rw [Measure.restrict_apply MeasurableSet.univ]
            simp]
        rw [one_mul]
      rw [h1, htransfer_all D _ hind]
      refine le_antisymm ?_ (zero_le _)
      calc ∫⁻ u, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) *
              {u : U | ¬ (UScaleDist e lam (1 - st) u 0 < ⊤)}.indicator
                (fun _ => (1 : ℝ≥0∞)) u ∂(Ptheta S theta)
          ≤ ∫⁻ u, {u : U | ¬ (UScaleDist e lam (1 - st) u 0 < ⊤)}.indicator
              (fun _ => (⊤ : ℝ≥0∞)) u ∂(Ptheta S theta) := by
            refine MeasureTheory.lintegral_mono (fun u => ?_)
            by_cases hu : u ∈ {u : U | ¬ (UScaleDist e lam (1 - st) u 0 < ⊤)}
            · rw [Set.indicator_of_mem hu]
              rw [Set.indicator_of_mem hu]
              exact le_top
            · rw [Set.indicator_of_notMem hu]
              rw [Set.indicator_of_notMem hu, mul_zero]
        _ = ⊤ * (Ptheta S theta) {u : U | ¬ (UScaleDist e lam (1 - st) u 0 < ⊤)} := by
            rw [MeasureTheory.lintegral_indicator hs_neg, MeasureTheory.lintegral_const,
              show (Ptheta S theta).restrict
                    {u : U | ¬ (UScaleDist e lam (1 - st) u 0 < ⊤)} Set.univ
                  = (Ptheta S theta) {u : U | ¬ (UScaleDist e lam (1 - st) u 0 < ⊤)} from by
                rw [Measure.restrict_apply MeasurableSet.univ]
                simp]
        _ = 0 := by rw [hbase_zero, mul_zero]
    have hscalePD : ∀ᵐ u ∂(Ptheta D theta), UScaleDist e lam (1 - st) u 0 < ⊤ := by
      rw [MeasureTheory.ae_iff]
      exact hPD_zero
    have hpt : (fun u : U => Real.exp (2 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
          delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2)))
        =ᵐ[Ptheta D theta] (fun u : U =>
          Real.exp (2 * ((beta * kappa * r) ^ 2 / (4 * delta1))) *
            (momentExpENN M1 (2 * delta1) (UScaleDist e lam (1 - st) u 0)).toReal) := by
      filter_upwards [hscalePD] with u hu
      have hval : (momentExpENN M1 (2 * delta1) (UScaleDist e lam (1 - st) u 0)).toReal
          = Real.exp ((2 * delta1) *
              (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2) := by
        unfold momentExpENN
        rw [dif_pos hu, ENNReal.toReal_ofReal (Real.exp_pos _).le]
      rw [hval, ← Real.exp_add]
      congr 1
      ring
    have hInt : Integrable (fun u : U => Real.exp (2 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
        delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2)))
        (Ptheta D theta) := by
      have hfin2 : ∫⁻ u, momentExpENN M1 (2 * delta1) (UScaleDist e lam (1 - st) u 0)
          ∂(Ptheta D theta) ≠ ⊤ :=
        hfin_all D (2 * delta1) (by linarith) (by linarith)
      have hbase : Integrable (fun u : U =>
          (momentExpENN M1 (2 * delta1) (UScaleDist e lam (1 - st) u 0)).toReal)
          (Ptheta D theta) :=
        MeasureTheory.integrable_toReal_of_lintegral_ne_top
          ((hmm (2 * delta1)).aemeasurable) hfin2
      exact (hbase.const_mul (Real.exp (2 * ((beta * kappa * r) ^ 2 / (4 * delta1))))).congr
        hpt.symm
    have hArg : 2 * ((beta * kappa * r) ^ 2 / (4 * delta1)) =
        (beta * kappa * r) ^ 2 / (2 * delta1) := by
      have hd : (2 * delta1 : ℝ) ≠ 0 := by positivity
      have hd4 : (4 * delta1 : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    refine ⟨hInt, ?_⟩
    calc ∫ u, Real.exp (2 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
          delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2))
          ∂(Ptheta D theta)
        = ∫ u, Real.exp (2 * ((beta * kappa * r) ^ 2 / (4 * delta1))) *
            (momentExpENN M1 (2 * delta1) (UScaleDist e lam (1 - st) u 0)).toReal
            ∂(Ptheta D theta) := MeasureTheory.integral_congr_ae hpt
      _ = Real.exp (2 * ((beta * kappa * r) ^ 2 / (4 * delta1))) *
            ∫ u, (momentExpENN M1 (2 * delta1) (UScaleDist e lam (1 - st) u 0)).toReal
              ∂(Ptheta D theta) := by
          rw [MeasureTheory.integral_const_mul]
      _ ≤ Real.exp (2 * ((beta * kappa * r) ^ 2 / (4 * delta1))) *
            (Real.sqrt (∫ u : U, (momentExpENN M1 (2 * (2 * delta1))
              (UScaleDist e lam (1 - st) u 0)).toReal ∂(Ptheta S theta)) *
              Real.sqrt ((∫⁻ u : U, (((Ptheta D theta).rnDeriv (Ptheta S theta)) u) ^ 2
                ∂(Ptheta S theta)).toReal)) :=
          mul_le_mul_of_nonneg_left (hmain_all D (2 * delta1) (by linarith) (by linarith))
            (Real.exp_pos _).le
      _ ≤ Real.exp (2 * ((beta * kappa * r) ^ 2 / (4 * delta1))) *
            (Real.sqrt (∫ u : U, (momentExpENN M1 (2 * (2 * delta1))
              (UScaleDist e lam (1 - st) u 0)).toReal ∂(Ptheta S theta)) *
              Real.sqrt Bbar) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hρ2bd_all D)) (Real.sqrt_nonneg _))
            (Real.exp_pos _).le
      _ = Real.exp ((beta * kappa * r) ^ 2 / (2 * delta1)) *
            (Real.sqrt (∫ u : U, (momentExpENN M1 (2 * (2 * delta1))
              (UScaleDist e lam (1 - st) u 0)).toReal ∂(Ptheta S theta)) *
              Real.sqrt Bbar) := by
          rw [hArg]
  /- @proof-region region.target-node.session.0a8c73c34c8f34cf end -/

end Statlib.Imported
end

