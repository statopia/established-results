import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_2035098161_9f60db94_bdde90c8
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3916768571_a9930ecf_948a7b8d
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3975929643_b00873c3_38223545
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_480728362_b0f6f73a_9160e5b6

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
theorem statopia_math_node_3191669108_71ceb7f7 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [MeasurableSpace U] [BorelSpace U]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (X : Type*) [TopologicalSpace X]
    (e : HilbertBasis ℕ ℝ U) (lam : ℕ → ℝ)
    (hlam_pos : ∀ k : ℕ, 0 < lam k) (hlam_anti : Antitone lam)
    (Gamma : H →L[ℝ] H) (hGamma_pos : Gamma.IsPositive)
    (hGamma_inj : ∀ v : H, Gamma v = 0 → v = 0)
    (Gammah : H →ₗ[ℝ] H)
    (hGammah_symm : ∀ v w : H, inner ℝ (Gammah v) w = inner ℝ v (Gammah w))
    (hGammah_pos : ∀ v : H, 0 ≤ inner ℝ v (Gammah v))
    (hGammah_sq : ∀ v : H, Gammah (Gammah v) = Gamma v)
    (Gammaih : H → H) (hGammaih_left : ∀ v : H, Gammaih (Gammah v) = v)
    (iotaH : Type*) [Preorder iotaH] (bH : HilbertBasis iotaH ℝ H) (mu : iotaH → ℝ)
    (hmu_pos : ∀ i : iotaH, 0 < mu i) (hmu_anti : Antitone mu)
    (C1 : H →L[ℝ] H) (hC1_pos : C1.IsPositive)
    (hC1_inj : ∀ v : H, C1 v = 0 → v = 0)
    (hC1_eigen : ∀ i : iotaH, C1 (bH i) = mu i • bH i)
    (LG : X → U → H)
    (s0 s1 s st alpha : ℝ)
    (hs0_nonneg : 0 ≤ s0) (hs0_lt : s0 < 1)
    (hs1_nonneg : 0 ≤ s1) (hs1_lt : s1 < 1)
    (hs_gt : s1 < s) (hs_le : s ≤ 1)
    (hst_gt : s0 < st) (hst_le : st ≤ 1) (halpha : 0 ≤ alpha)
    (C1c C2c : ℝ) (hC1c : 0 < C1c) (hC2c : 0 < C2c)
    (M1 : ℝ → ℝ) (hM1_mono : Monotone M1) (hM1_nonneg : ∀ r : ℝ, 0 ≤ M1 r)
    (M2 : ℝ → ℝ → ℝ) (hM2_nonneg : ∀ r1 r2 : ℝ, 0 ≤ M2 r1 r2)
    (hM2_mono_fst : ∀ r2 : ℝ, Monotone (fun r : ℝ => M2 r r2))
    (hM2_mono_snd : ∀ r1 : ℝ, Monotone (fun r : ℝ => M2 r1 r))
    (hA1 : (¬ FiniteDimensional ℝ H) → ∀ (w : H) (rho : ℝ),
      HScale bH mu (alpha - s) w → ((Int.floor (alpha - s1 - 1) : ℤ) : ℝ) ≤ rho →
      rho < alpha - s1 →
      HScale bH mu (-st) (Gammaih w) ∧ HScale bH mu st (Gammah w) ∧
        HScale bH mu (rho - alpha) w ∧
      (HScaleNorm bH mu (-st) (Gammaih w)) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal C1c * (HScaleNorm bH mu (alpha - s) w) ^ (1 / 2 : ℝ) ∧
      (HScaleNorm bH mu st (Gammah w)) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal C2c * (HScaleNorm bH mu (rho - alpha) w) ^ (1 / 2 : ℝ))
    (hA2 : ∀ (x : X) (u : U), UScale e lam (1 - st) u →
      (HScaleNorm bH mu st (Gammaih (LG x u))) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))))
    (hA3 : ∀ (x : X) (u1 u2 : U), UScale e lam (1 - st) u1 → UScale e lam (1 - st) u2 →
      UScale e lam (1 - st) (u1 - u2) →
      (HScaleNorm bH mu st (Gammaih (LG x u1 - LG x u2))) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (M2 (ENNReal.toReal (UScaleDist e lam (1 - st) u1 0))
            (ENNReal.toReal (UScaleDist e lam (1 - st) u2 0))) *
          UScaleDist e lam (1 - st) (u1 - u2) 0)
    (hA4 : ∀ (x' : X) (u : U), UScale e lam (1 - st) u →
      Tendsto (fun x : X => (HScaleNorm bH mu st (Gammaih (LG x u - LG x' u))) ^ (1 / 2 : ℝ))
        (𝓝 x') (𝓝 0))
    (hLG_all_range : ∀ (x : X) (u : U), UScale e lam (1 - st) u → ∃ w : H, Gammah w = LG x u)
    (beta : ℝ) (hbeta : 0 < beta)
    (m : ℕ) (hm : 0 < m)
    (Nc : ℕ) (hNc : 0 < Nc)
    (Theta1 : Type*) [NormedAddCommGroup Theta1] [InnerProductSpace ℝ Theta1]
      [CompleteSpace Theta1] [TopologicalSpace.SeparableSpace Theta1] [MeasurableSpace Theta1]
    (Ptheta : (Fin m → X × H) → (Theta1 × (Fin Nc → ℝ)) → Measure U)
    (hPtheta_isProb : ∀ (S : Fin m → X × H) (theta : Theta1 × (Fin Nc → ℝ)),
      IsProbabilityMeasure (Ptheta S theta))
    (theta : Theta1 × (Fin Nc → ℝ))
    (S : Fin m → X × H)
    (mubar : ℝ) (hmubar : 1 ≤ mubar)
    (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (h6 : ∀ (x x' : X) (y y' : H), HScale bH mu (alpha - s) y → HScale bH mu (alpha - s) y' →
      ∀ u : U, UScale e lam (1 - st) u →
      |Phi Gammaih LG u x y - Phi Gammaih LG u x y'| ≤
        kappa * ENNReal.toReal (HScaleDist bH mu (alpha - s) y y') *
          M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)))
    (h7 : ∀ (x x' : X) (y y' : H), HScale bH mu (alpha - s) y → HScale bH mu (alpha - s) y' →
      ∀ u : U, UScale e lam (1 - st) u →
      |Phi Gammaih LG u x y - Phi Gammaih LG u x' y| ≤
        (Real.rpow mubar st * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) +
          kappa * ENNReal.toReal (HScaleDist bH mu (alpha - s) y 0)) *
          ENNReal.toReal (HScaleDist bH mu st (Gammaih (LG x u - LG x' u)) 0))
    (h8 : ∀ (x x' : X) (y y' : H), HScale bH mu (alpha - s) y → HScale bH mu (alpha - s) y' →
      ∀ u : U, UScale e lam (1 - st) u →
      ENNReal.toReal (HScaleDist bH mu st (Gammaih (LG x u - LG x' u)) 0) ≤
        2 * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)))
    (delta0 : ℝ) (hdelta0 : 0 < delta0)
    (hmoment : ∀ delta : ℝ, 0 ≤ delta → delta < delta0 →
      Integrable
        (fun u : U => Real.exp (delta * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2))
        (Ptheta S theta))
    (hdelta_meas : ∀ delta : ℝ,
      AEMeasurable ((UScale e lam (1 - st)).indicator
        (fun v : U =>
          Real.exp (delta * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)))
        (Ptheta S theta))
    (hP_scale : (Ptheta S theta) (UScale e lam (1 - st)) = 1)
    (delta1 : ℝ) (hdelta1 : 0 < delta1) (hdelta1_bound : 8 * delta1 < delta0)
    (r : ℝ) (hr : 0 ≤ r)
    (D : Fin m → X × H) (Dn : ℕ → Fin m → X × H)
    (hD_scale : ∀ j : Fin m, HScale bH mu (alpha - s) (D j).2)
    (hDn_scale : ∀ (n : ℕ) (j : Fin m), HScale bH mu (alpha - s) ((Dn n j).2))
    (hD_rad : ∀ j : Fin m, HScaleDist bH mu (alpha - s) (D j).2 0 ≤ ENNReal.ofReal r)
    (hDn_rad : ∀ (n : ℕ) (j : Fin m),
      HScaleDist bH mu (alpha - s) ((Dn n j).2) 0 ≤ ENNReal.ofReal r)
    (hDn_tendsto : Tendsto Dn atTop
      (dataNhds (fun z : H => (HScaleNorm bH mu (alpha - s) z) ^ (1 / 2 : ℝ))
        (HScale bH mu (alpha - s)) D))
    (Bbar : ℝ) (hBbar : 0 ≤ Bbar)
    (rho : ℕ → U → ℝ≥0∞) (hrho_meas : ∀ n : ℕ, Measurable (rho n))
    (hrho_dens : ∀ n : ℕ, Ptheta (Dn n) theta = (Ptheta S theta).withDensity (rho n))
    (hrhon_scale : ∀ n : ℕ, (Ptheta (Dn n) theta) (UScale e lam (1 - st)) = 1)
    (hrho_bound : ∀ n : ℕ, ∫⁻ u : U, (rho n u) ^ 2 ∂(Ptheta S theta) ≤ ENNReal.ofReal Bbar)
    (eta : ℝ) (heta_pos : 0 < eta) (heta_le : eta ≤ 2),
    Tendsto
        (fun n : ℕ => ∫ u : U,
          |(beta / (m : ℝ)) * potSum Gammaih LG (Dn n) u -
              (beta / (m : ℝ)) * potSum Gammaih LG D u| ^ 2 *
            (UScale e lam (1 - st)).indicator
              (fun v : U =>
                Real.exp (eta * ((beta * kappa * r) ^ 2 / (4 * delta1) +
                  delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2))) u
          ∂(Ptheta (Dn n) theta))
        atTop (𝓝 0) := by
  /- @proof-region region.target-node.session.7d05da0fe13fea02 begin -/
  intro U _ _ _ _ _ H _ _ _ X _ e lam hlam_pos hlam_anti Gamma hGamma_pos hGamma_inj Gammah
    hGammah_symm hGammah_pos hGammah_sq Gammaih hGammaih_left iotaH _ bH mu hmu_pos hmu_anti C1
    hC1_pos hC1_inj hC1_eigen LG s0 s1 s st alpha hs0_nonneg hs0_lt hs1_nonneg hs1_lt hs_gt hs_le
    hst_gt hst_le halpha C1c C2c hC1c hC2c M1 hM1_mono hM1_nonneg M2 hM2_nonneg hM2_mono_fst
    hM2_mono_snd hA1 hA2 hA3 hA4 hLG_all_range beta hbeta m hm Nc hNc Theta1 _ _ _ _ _ Ptheta
    hPtheta_isProb theta S mubar hmubar kappa hkappa h6 h7 h8 delta0 hdelta0 hmoment hdelta_meas
    hP_scale delta1 hdelta1 hdelta1_bound r hr D Dn hD_scale hDn_scale hD_rad hDn_rad hDn_tendsto
    Bbar hBbar rho hrho_meas hrho_dens hrhon_scale hrho_bound eta heta_pos heta_le
  classical
  let P : Measure U := Ptheta S theta
  let Pn : ℕ → Measure U := fun n => Ptheta (Dn n) theta
  let Nn : U → ℝ := fun u => M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))
  let A0 : ℝ := (beta * kappa * r) ^ 2 / (4 * delta1)
  let Kc : ℝ := beta * (4 * kappa * r + 2 * Real.rpow mubar st)
  let C4 : ℝ := 16 + 4096 / delta1 ^ 4
  let Cd : ℝ := Kc ^ 4 * C4 * Real.exp (4 * A0)
  let Sc : Set U := UScale e lam (1 - st)
  let Δ : ℕ → U → ℝ := fun n u =>
    (beta / (m : ℝ)) * potSum Gammaih LG (Dn n) u - (beta / (m : ℝ)) * potSum Gammaih LG D u
  let av : U → ℝ := fun u => A0 + delta1 * Nn u ^ 2
  let IdE : U → ℝ := fun v => Real.exp (eta * av v)
  let F : ℕ → U → ℝ := fun n u =>
    |Δ n u| ^ 4 * Sc.indicator (fun v : U => Real.exp ((2 * eta) * av v)) u
  haveI hPprob : IsProbabilityMeasure P := hPtheta_isProb S theta
  have hPs : P Sc = 1 := hP_scale
  have hNn_nonneg : ∀ u : U, 0 ≤ Nn u := fun u => hM1_nonneg _
  have hrpow_nonneg : (0 : ℝ) ≤ Real.rpow mubar st := Real.rpow_nonneg (by linarith) st
  have hKc_nonneg : 0 ≤ Kc := by
    show (0 : ℝ) ≤ beta * (4 * kappa * r + 2 * Real.rpow mubar st)
    have h2 : (0 : ℝ) ≤ 4 * kappa * r + 2 * Real.rpow mubar st := by
      nlinarith [hkappa, hr, hrpow_nonneg]
    exact mul_nonneg hbeta.le h2
  have hA0_nonneg : 0 ≤ A0 := by
    show (0 : ℝ) ≤ (beta * kappa * r) ^ 2 / (4 * delta1)
    positivity
  have hC4_pos : 0 < C4 := by
    show (0 : ℝ) < 16 + 4096 / delta1 ^ 4
    have h1 : (0 : ℝ) < delta1 ^ 4 := by positivity
    have h2 : (0 : ℝ) < 4096 / delta1 ^ 4 := by positivity
    linarith
  have hSc_meas : MeasurableSet Sc := by
    have hnorm : Measurable (fun u : U => UScaleNorm e lam (1 - st) u) := by
      have hsummand : ∀ k : ℕ, Measurable (fun u : U =>
          ENNReal.ofReal (Real.rpow (lam k) (-(1 - st)) * (inner ℝ (e k) u) ^ 2)) := by
        intro k
        have hi : Measurable (fun u : U => inner ℝ (e k) u) :=
          (continuous_const.inner continuous_id).measurable
        exact ENNReal.measurable_ofReal.comp (measurable_const.mul (hi.pow_const 2))
      simpa [UScaleNorm] using Measurable.ennreal_tsum hsummand
    have hpre : MeasurableSet (UScaleNorm e lam (1 - st) ⁻¹' {(⊤ : ℝ≥0∞)}) :=
      (measurableSet_singleton (⊤ : ℝ≥0∞)).preimage hnorm
    have hneq : Sc = (UScaleNorm e lam (1 - st) ⁻¹' {(⊤ : ℝ≥0∞)})ᶜ := by
      ext u
      simp only [Sc, UScale, Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_setOf_eq, lt_top_iff_ne_top]
    rw [hneq]
    exact hpre.compl
  have hPc : P Scᶜ = 0 := by
    have huniv : P Set.univ = 1 := measure_univ
    have hne : P Sc ≠ ⊤ := by
      rw [hPs]
      exact ENNReal.one_ne_top
    rw [measure_compl hSc_meas hne, huniv, hPs]
    simp
  have hEmeas : ∀ w : ℝ, AEMeasurable (Sc.indicator (fun v : U => Real.exp (w * av v))) P := by
    intro w
    have hbase : AEMeasurable (Sc.indicator (fun v : U => Real.exp ((w * delta1) * Nn v ^ 2))) P :=
      hdelta_meas (w * delta1)
    have hfun : (Sc.indicator (fun v : U => Real.exp (w * av v))) =
        fun u : U => Real.exp (w * A0) *
          Sc.indicator (fun v : U => Real.exp ((w * delta1) * Nn v ^ 2)) u := by
      funext u
      by_cases hu : u ∈ Sc
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, ← Real.exp_add]
        congr 1
        simp only [av]
        ring
      · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, mul_zero]
    rw [hfun]
    exact hbase.const_mul _
  have h391 := statopia_math_node_3916768571_a9930ecf U H X e lam hlam_pos hlam_anti Gamma
    hGamma_pos hGamma_inj Gammah hGammah_symm hGammah_pos hGammah_sq Gammaih hGammaih_left iotaH
    bH mu hmu_pos hmu_anti C1 hC1_pos hC1_inj hC1_eigen LG s0 s1 s st alpha hs0_nonneg hs0_lt
    hs1_nonneg hs1_lt hs_gt hs_le hst_gt hst_le halpha C1c C2c hC1c hC2c M1 hM1_mono hM1_nonneg
    M2 hM2_nonneg hM2_mono_fst hM2_mono_snd hA1 hA2 hA3 hA4 hLG_all_range beta hbeta m hm
  have hAE_delta : ∀ n : ℕ, AEMeasurable (Δ n) P := by
    intro n
    have hDn : AEMeasurable (fun u : U => potSum Gammaih LG (Dn n) u) P :=
      ((h391.2.2 (Dn n) ((Dn n ⟨0, hm⟩).1) ((Dn n ⟨0, hm⟩).2) P hP_scale hPc).2.1)
    have hD : AEMeasurable (fun u : U => potSum Gammaih LG D u) P :=
      ((h391.2.2 D ((D ⟨0, hm⟩).1) ((D ⟨0, hm⟩).2) P hP_scale hPc).2.1)
    exact (hDn.const_mul (beta / (m : ℝ))).sub (hD.const_mul (beta / (m : ℝ)))
  have hAE_F : ∀ n : ℕ, AEMeasurable (F n) P := by
    intro n
    have h1 : AEMeasurable (fun u : U => |Δ n u| ^ 4) P :=
      (continuous_abs.pow 4).measurable.comp_aemeasurable (hAE_delta n)
    exact h1.mul (hEmeas (2 * eta))
  have hAE_sqrtF : ∀ n : ℕ, AEMeasurable (fun u : U => Real.sqrt (F n u)) P := by
    intro n
    exact Real.continuous_sqrt.measurable.comp_aemeasurable (hAE_F n)
  have hpot_bound : ∀ (n : ℕ) (u : U), u ∈ Sc → |Δ n u| ≤ Kc * (1 + Nn u ^ 2) := by
    intro n u hu
    have hmain := (statopia_math_node_3975929643_b00873c3 U H X Gammaih LG e lam iotaH bH mu
      hmu_pos M1 hM1_mono hM1_nonneg s st alpha m hm beta hbeta mubar kappa hmubar hkappa h6 h7
      h8).2.1 r hr (Dn n) D (hDn_scale n) hD_scale (hDn_rad n) hD_rad u hu
    simpa [Δ, Kc, Nn] using hmain
  have hscalar : ∀ Y : ℝ, 0 ≤ Y → (1 + Y) ^ 4 ≤ C4 * Real.exp (delta1 * Y) := by
    intro Y hY
    have ht : (0 : ℝ) ≤ delta1 * Y := mul_nonneg hdelta1.le hY
    have hs : (0 : ℝ) ≤ delta1 * Y / 4 := by linarith only [ht]
    have hexp4 : (Real.exp (delta1 * Y / 4)) ^ 4 = Real.exp (delta1 * Y) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hstep : delta1 * Y / 4 ≤ Real.exp (delta1 * Y / 4) := by
      have h := Real.add_one_le_exp (delta1 * Y / 4)
      linarith only [h]
    have hes : (0 : ℝ) ≤ Real.exp (delta1 * Y / 4) := (Real.exp_pos _).le
    have hsq : (delta1 * Y / 4) * (delta1 * Y / 4) ≤
        Real.exp (delta1 * Y / 4) * Real.exp (delta1 * Y / 4) :=
      mul_le_mul hstep hstep hs hes
    have hpow : (delta1 * Y / 4) ^ 4 ≤ (Real.exp (delta1 * Y / 4)) ^ 4 := by
      have h2 : (delta1 * Y / 4) * (delta1 * Y / 4) * ((delta1 * Y / 4) * (delta1 * Y / 4))
          ≤ (Real.exp (delta1 * Y / 4) * Real.exp (delta1 * Y / 4)) *
            (Real.exp (delta1 * Y / 4) * Real.exp (delta1 * Y / 4)) :=
        mul_le_mul hsq hsq (by positivity) (by positivity)
      calc (delta1 * Y / 4) ^ 4
            = (delta1 * Y / 4) * (delta1 * Y / 4) *
              ((delta1 * Y / 4) * (delta1 * Y / 4)) := by ring
        _ ≤ (Real.exp (delta1 * Y / 4) * Real.exp (delta1 * Y / 4)) *
              (Real.exp (delta1 * Y / 4) * Real.exp (delta1 * Y / 4)) := h2
        _ = (Real.exp (delta1 * Y / 4)) ^ 4 := by ring
    have hexpbound : (delta1 * Y / 4) ^ 4 ≤ Real.exp (delta1 * Y) := by
      rw [← hexp4]
      exact hpow
    have hd4 : (0 : ℝ) < delta1 ^ 4 := by positivity
    have hY4 : Y ^ 4 ≤ 256 / delta1 ^ 4 * Real.exp (delta1 * Y) := by
      have hmul : delta1 ^ 4 * Y ^ 4 ≤ 256 * Real.exp (delta1 * Y) := by
        nlinarith only [hexpbound, hd4]
      rw [div_mul_eq_mul_div, le_div_iff₀ hd4]
      nlinarith only [hmul]
    have h2a : (1 + Y) ^ 2 ≤ 2 * (1 + Y ^ 2) := by
      nlinarith only [sq_nonneg (1 - Y)]
    have h2b : (1 + Y ^ 2) ^ 2 ≤ 2 * (1 + Y ^ 4) := by
      nlinarith only [sq_nonneg (1 - Y ^ 2)]
    have hsq1 : ((1 + Y) ^ 2) * ((1 + Y) ^ 2) ≤
        (2 * (1 + Y ^ 2)) * (2 * (1 + Y ^ 2)) :=
      mul_le_mul h2a h2a (by positivity) (by positivity)
    have hsq2 : (2 * (1 + Y ^ 2)) * (2 * (1 + Y ^ 2)) ≤ 16 * (1 + Y ^ 4) := by
      have h4 : (2 * (1 + Y ^ 2)) * (2 * (1 + Y ^ 2)) = 4 * (1 + Y ^ 2) ^ 2 := by ring
      have hY4nn : (0 : ℝ) ≤ 1 + Y ^ 4 := by positivity
      nlinarith only [h4, h2b, hY4nn]
    have h16 : (1 + Y) ^ 4 ≤ 16 * (1 + Y ^ 4) := by
      calc (1 + Y) ^ 4 = ((1 + Y) ^ 2) * ((1 + Y) ^ 2) := by ring
        _ ≤ (2 * (1 + Y ^ 2)) * (2 * (1 + Y ^ 2)) := hsq1
        _ ≤ 16 * (1 + Y ^ 4) := hsq2
    have he1 : (1 : ℝ) ≤ Real.exp (delta1 * Y) := by
      have h := Real.exp_le_exp.mpr ht
      rwa [Real.exp_zero] at h
    have h16E : (16 : ℝ) ≤ 16 * Real.exp (delta1 * Y) := by linarith only [he1]
    have hlast : 16 + 4096 / delta1 ^ 4 * Real.exp (delta1 * Y)
        ≤ (16 + 4096 / delta1 ^ 4) * Real.exp (delta1 * Y) := by
      have h := h16E
      calc 16 + 4096 / delta1 ^ 4 * Real.exp (delta1 * Y)
          ≤ 16 * Real.exp (delta1 * Y) + 4096 / delta1 ^ 4 * Real.exp (delta1 * Y) := by
            linarith only [h]
        _ = (16 + 4096 / delta1 ^ 4) * Real.exp (delta1 * Y) := by ring
    have hstep2 : 16 * (1 + Y ^ 4)
        ≤ 16 * (1 + 256 / delta1 ^ 4 * Real.exp (delta1 * Y)) := by
      have h : 1 + Y ^ 4 ≤ 1 + 256 / delta1 ^ 4 * Real.exp (delta1 * Y) := by
        linarith only [hY4]
      linarith only [h]
    calc (1 + Y) ^ 4 ≤ 16 * (1 + Y ^ 4) := h16
      _ ≤ 16 * (1 + 256 / delta1 ^ 4 * Real.exp (delta1 * Y)) := hstep2
      _ = 16 + 4096 / delta1 ^ 4 * Real.exp (delta1 * Y) := by ring
      _ ≤ (16 + 4096 / delta1 ^ 4) * Real.exp (delta1 * Y) := hlast
  have hF_bound : ∀ (n : ℕ) (u : U), F n u ≤ Cd * Real.exp ((8 * delta1) * Nn u ^ 2) := by
    intro n u
    have hY : (0 : ℝ) ≤ Nn u ^ 2 := sq_nonneg _
    have hX : (0 : ℝ) ≤ delta1 * Nn u ^ 2 := mul_nonneg hdelta1.le hY
    by_cases hu : u ∈ Sc
    · simp only [F, Set.indicator_of_mem hu]
      have hb := hpot_bound n u hu
      have h1 : |Δ n u| ^ 4 ≤ (Kc * (1 + Nn u ^ 2)) ^ 4 :=
        pow_le_pow_left₀ (abs_nonneg _) hb 4
      have h3 : (1 + Nn u ^ 2) ^ 4 ≤ C4 * Real.exp (delta1 * Nn u ^ 2) := hscalar _ hY
      have hexp : Real.exp ((2 * eta) * av u)
          ≤ Real.exp (4 * A0) * Real.exp (4 * (delta1 * Nn u ^ 2)) := by
        have hsplit : Real.exp ((2 * eta) * av u)
            = Real.exp ((2 * eta) * A0) * Real.exp ((2 * eta) * (delta1 * Nn u ^ 2)) := by
          rw [← Real.exp_add]
          congr 1
          simp only [av]
          ring
        rw [hsplit]
        exact mul_le_mul
          (Real.exp_le_exp.mpr (by nlinarith only [hA0_nonneg, heta_le]))
          (Real.exp_le_exp.mpr (by nlinarith only [hX, heta_le]))
          (Real.exp_pos _).le (Real.exp_pos _).le
      have h4 : |Δ n u| ^ 4 * Real.exp ((2 * eta) * av u)
          ≤ (Kc * (1 + Nn u ^ 2)) ^ 4 *
            (Real.exp (4 * A0) * Real.exp (4 * (delta1 * Nn u ^ 2))) :=
        mul_le_mul h1 hexp (Real.exp_pos _).le (by positivity)
      have h5 : (Kc * (1 + Nn u ^ 2)) ^ 4 *
            (Real.exp (4 * A0) * Real.exp (4 * (delta1 * Nn u ^ 2)))
          ≤ (Kc ^ 4 * (C4 * Real.exp (delta1 * Nn u ^ 2))) *
            (Real.exp (4 * A0) * Real.exp (4 * (delta1 * Nn u ^ 2))) := by
        have hbase : (Kc * (1 + Nn u ^ 2)) ^ 4 = Kc ^ 4 * (1 + Nn u ^ 2) ^ 4 := by ring
        rw [hbase]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h3 (by positivity)) (by positivity)
      have h6 : (Kc ^ 4 * (C4 * Real.exp (delta1 * Nn u ^ 2))) *
            (Real.exp (4 * A0) * Real.exp (4 * (delta1 * Nn u ^ 2)))
          = Kc ^ 4 * C4 * Real.exp (4 * A0) *
            (Real.exp (delta1 * Nn u ^ 2) * Real.exp (4 * (delta1 * Nn u ^ 2))) := by ring
      have h7 : Real.exp (delta1 * Nn u ^ 2) * Real.exp (4 * (delta1 * Nn u ^ 2))
          ≤ Real.exp ((8 * delta1) * Nn u ^ 2) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by nlinarith only [hX])
      calc |Δ n u| ^ 4 * Real.exp ((2 * eta) * av u)
          ≤ (Kc * (1 + Nn u ^ 2)) ^ 4 *
              (Real.exp (4 * A0) * Real.exp (4 * (delta1 * Nn u ^ 2))) := h4
        _ ≤ (Kc ^ 4 * (C4 * Real.exp (delta1 * Nn u ^ 2))) *
              (Real.exp (4 * A0) * Real.exp (4 * (delta1 * Nn u ^ 2))) := h5
        _ = Kc ^ 4 * C4 * Real.exp (4 * A0) *
              (Real.exp (delta1 * Nn u ^ 2) * Real.exp (4 * (delta1 * Nn u ^ 2))) := h6
        _ ≤ Kc ^ 4 * C4 * Real.exp (4 * A0) * Real.exp ((8 * delta1) * Nn u ^ 2) :=
            mul_le_mul_of_nonneg_left h7 (by positivity)
    · simp only [F, Set.indicator_of_notMem hu, mul_zero]
      have hCd : (0 : ℝ) ≤ Cd := by
        show (0 : ℝ) ≤ Kc ^ 4 * C4 * Real.exp (4 * A0)
        have h1 : (0 : ℝ) ≤ Kc ^ 4 := by positivity
        have h2 : (0 : ℝ) ≤ C4 := hC4_pos.le
        have h3 : (0 : ℝ) ≤ Real.exp (4 * A0) := (Real.exp_pos _).le
        exact mul_nonneg (mul_nonneg h1 h2) h3
      exact mul_nonneg hCd (Real.exp_pos _).le
  have hFnn : ∀ (n : ℕ) (u : U), 0 ≤ F n u := by
    intro n u
    by_cases hu : u ∈ Sc
    · simp only [F, Set.indicator_of_mem hu]
      positivity
    · simp only [F, Set.indicator_of_notMem hu, mul_zero]
      exact le_refl 0
  have hmono_int : Integrable (fun u : U => Real.exp ((8 * delta1) * Nn u ^ 2)) P :=
    hmoment (8 * delta1) (by linarith) hdelta1_bound
  have hFint : ∀ n : ℕ, Integrable (F n) P := by
    intro n
    have hbound : ∀ u : U, |F n u| ≤ Cd * Real.exp ((8 * delta1) * Nn u ^ 2) := by
      intro u
      rw [abs_of_nonneg (hFnn n u)]
      exact hF_bound n u
    exact Integrable.mono' (hmono_int.const_mul Cd) (hAE_F n).aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  have hFsqrtint : ∀ n : ℕ, Integrable (fun u : U => Real.sqrt (F n u)) P := by
    intro n
    have hbound : ∀ u : U,
        |Real.sqrt (F n u)| ≤ (1 + Cd) * Real.exp ((8 * delta1) * Nn u ^ 2) := by
      intro u
      have ht : (0 : ℝ) ≤ F n u := hFnn n u
      have hc : (0 : ℝ) ≤ 1 + F n u := by linarith only [ht]
      have ht1 : F n u ≤ (1 + F n u) ^ 2 := by nlinarith only [ht]
      have hsq : Real.sqrt (F n u) ≤ 1 + F n u := by
        have h1 : Real.sqrt (F n u) ≤ Real.sqrt ((1 + F n u) ^ 2) := Real.sqrt_le_sqrt ht1
        rwa [Real.sqrt_sq hc] at h1
      have hE1 : (1 : ℝ) ≤ Real.exp ((8 * delta1) * Nn u ^ 2) := by
        have hpos : (0 : ℝ) ≤ (8 * delta1) * Nn u ^ 2 := by
          have h2 : (0 : ℝ) ≤ 8 * delta1 := by linarith only [hdelta1.le]
          exact mul_nonneg h2 (sq_nonneg _)
        have h := Real.exp_le_exp.mpr hpos
        rwa [Real.exp_zero] at h
      have hb1 : 1 + F n u ≤ 1 + Cd * Real.exp ((8 * delta1) * Nn u ^ 2) := by
        have h := hF_bound n u
        linarith only [h]
      have hb2 : 1 + Cd * Real.exp ((8 * delta1) * Nn u ^ 2)
          ≤ (1 + Cd) * Real.exp ((8 * delta1) * Nn u ^ 2) := by
        linarith only [hE1]
      have hfinal : Real.sqrt (F n u) ≤ (1 + Cd) * Real.exp ((8 * delta1) * Nn u ^ 2) := by
        linarith only [hsq, hb1, hb2]
      rwa [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Integrable.mono' (hmono_int.const_mul (1 + Cd))
      (hAE_sqrtF n).aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  have hFlim : Tendsto (fun n : ℕ => ∫ u : U, F n u ∂P) atTop (𝓝 0) :=
    (statopia_math_node_480728362_b0f6f73a U H X e lam hlam_pos hlam_anti Gamma hGamma_pos
      hGamma_inj Gammah hGammah_symm hGammah_pos hGammah_sq Gammaih hGammaih_left iotaH bH mu
      hmu_pos hmu_anti C1 hC1_pos hC1_inj hC1_eigen LG s0 s1 s st alpha hs0_nonneg hs0_lt
      hs1_nonneg hs1_lt hs_gt hs_le hst_gt hst_le halpha C1c C2c hC1c hC2c M1 hM1_mono
      hM1_nonneg M2 hM2_nonneg hM2_mono_fst hM2_mono_snd hA1 hA2 hA3 hA4 hLG_all_range beta
      hbeta m hm Nc hNc Theta1 Ptheta hPtheta_isProb theta S mubar hmubar kappa hkappa h6 h7 h8
      delta0 hdelta0 hmoment hdelta_meas hP_scale delta1 hdelta1 hdelta1_bound r hr D Dn
      hD_scale hDn_scale hD_rad hDn_rad hDn_tendsto Bbar hBbar rho hrho_meas hrho_dens
      hrhon_scale hrho_bound eta heta_pos heta_le).1
  have hsqrt_eq : ∀ (n : ℕ) (u : U), Real.sqrt (F n u) = |Δ n u| ^ 2 * Sc.indicator IdE u := by
    intro n u
    by_cases hu : u ∈ Sc
    · simp only [F, IdE, Set.indicator_of_mem hu]
      have h1 : |Δ n u| ^ 4 = (|Δ n u| ^ 2) ^ 2 := by ring
      have h2 : Real.exp ((2 * eta) * av u) = (Real.exp (eta * av u)) ^ 2 := by
        have hsplit : (2 * eta) * av u = (2 : ℕ) * (eta * av u) := by
          push_cast
          ring
        rw [hsplit, Real.exp_nat_mul]
      rw [h1, h2, ← mul_pow, Real.sqrt_sq (by positivity)]
    · simp only [F, IdE, Set.indicator_of_notMem hu, mul_zero, Real.sqrt_zero]
  have hlim_sqrt : Tendsto (fun n : ℕ => ∫ u : U, Real.sqrt (F n u) ∂Pn n) atTop (𝓝 0) :=
    statopia_math_node_2035098161_9f60db94 U P Pn rho hrho_meas hrho_dens Bbar hBbar hrho_bound
      F hFint hFsqrtint hFnn hFlim
  have hgoal : Tendsto (fun n : ℕ => ∫ u : U, |Δ n u| ^ 2 * Sc.indicator IdE u ∂Pn n) atTop (𝓝 0) := by
    simpa only [hsqrt_eq] using hlim_sqrt
  change Tendsto (fun n : ℕ => ∫ u : U, |Δ n u| ^ 2 * Sc.indicator IdE u ∂Pn n) atTop (𝓝 0)
  exact hgoal

  /- @proof-region region.target-node.session.7d05da0fe13fea02 end -/

end Statlib.Imported
end

