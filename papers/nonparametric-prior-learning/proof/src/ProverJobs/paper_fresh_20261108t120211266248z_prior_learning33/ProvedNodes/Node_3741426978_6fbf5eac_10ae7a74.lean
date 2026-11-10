import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_1220214867_7bace56e_4839d7d8
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_1524419607_fd93d37d_e884b403
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_2045408823_ad3ced10_a3540a44
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_2103907506_2297e1dc_fe47e4b0
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3091194290_4509a8b7_27a85c1e
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3916768571_a9930ecf_948a7b8d
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_4026486579_064ccf6a_a9e6ae7a
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_4147388267_4d56357b_aae526a8
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_934913505_908353c8_30b2122d

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
theorem statopia_math_node_3741426978_6fbf5eac : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [MeasurableSpace U] [BorelSpace U]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H]
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X] [MeasurableSpace X]
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
    (C0th : (Fin Nc → ℝ) → U →L[ℝ] U)
    (hC0th_basis : ∀ (theta2 : Fin Nc → ℝ) (k : ℕ),
      C0th theta2 (e k) = priorEigen lam Nc theta2 k • e k)
    (hC0th_expand : ∀ (theta2 : Fin Nc → ℝ) (u : U),
      HasSum (fun k : ℕ => (priorEigen lam Nc theta2 k * inner ℝ (e k) u) • e k) (C0th theta2 u))
    (R_u : ℝ) (hR_u : 0 < R_u)
    (fm : (Fin m → X × H) → Theta1 → U)
    (Ptheta : (Fin m → X × H) → (Theta1 × (Fin Nc → ℝ)) → Measure U)
    (hPtheta_isProb : ∀ (S : Fin m → X × H) (theta : Theta1 × (Fin Nc → ℝ)),
      IsProbabilityMeasure (Ptheta S theta))
    (hPtheta_gauss : ∀ (S : Fin m → X × H) (theta : Theta1 × (Fin Nc → ℝ)),
      ProbabilityTheory.IsGaussian (Ptheta S theta))
    (hPtheta_mean : ∀ (S : Fin m → X × H) (theta : Theta1 × (Fin Nc → ℝ)) (v : U),
      ∫ u, inner ℝ v u ∂(Ptheta S theta) = inner ℝ v (fm S theta.1))
    (hPtheta_cov : ∀ (S : Fin m → X × H) (theta : Theta1 × (Fin Nc → ℝ)) (v w : U),
      ∫ u, (inner ℝ v u - inner ℝ v (fm S theta.1)) * (inner ℝ w u - inner ℝ w (fm S theta.1))
        ∂(Ptheta S theta) = inner ℝ v (C0th theta.2 w))
    (hPtheta_int1 : ∀ (S : Fin m → X × H) (theta : Theta1 × (Fin Nc → ℝ)) (v : U),
      Integrable (fun u : U => inner ℝ v u) (Ptheta S theta))
    (hPtheta_int2 : ∀ (S : Fin m → X × H) (theta : Theta1 × (Fin Nc → ℝ)) (v w : U),
      Integrable (fun u : U =>
        (inner ℝ v u - inner ℝ v (fm S theta.1)) * (inner ℝ w u - inner ℝ w (fm S theta.1)))
        (Ptheta S theta))
    (hfm_ball : ∀ (S : Fin m → X × H) (theta : Theta1 × (Fin Nc → ℝ)),
      UScale e lam 2 (fm S theta.1) ∧
      (UScaleNorm e lam 2 (fm S theta.1)) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal R_u)
    (theta : Theta1 × (Fin Nc → ℝ))
    (S : Fin m → X × H)
    (mubar : ℝ) (hmubar : 1 ≤ mubar)
    (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hPhi_lower : ∀ (x : X) (y : H) (u : U), HScale bH mu (alpha - s) y →
      UScale e lam (1 - st) u →
      Phi Gammaih LG u x y ≥
        - (kappa * ENNReal.toReal (HScaleDist bH mu (alpha - s) y 0) *
            M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))))
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
        (fun u : U =>
          Real.exp (delta * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2))
        (Ptheta S theta))
    (hdelta_meas : ∀ delta : ℝ,
      AEMeasurable ((UScale e lam (1 - st)).indicator
        (fun v : U =>
          Real.exp (delta * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)))
        (Ptheta S theta))
    (hP_scale : (Ptheta S theta) (UScale e lam (1 - st)) = 1)
    (delta1 : ℝ) (hdelta1 : 0 < delta1) (hdelta1_bound : 8 * delta1 < delta0)
    (r : ℝ) (hr : 0 ≤ r)
    (hS_scale : ∀ j : Fin m, HScale bH mu (alpha - s) (S j).2)
    (hS_rad : ∀ j : Fin m,
      (HScaleNorm bH mu (alpha - s) (S j).2) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal r)
    (Dn : ℕ → Fin m → X × H)
    (hDn_scale : ∀ (n : ℕ) (j : Fin m), HScale bH mu (alpha - s) ((Dn n j).2))
    (hDn_rad : ∀ (n : ℕ) (j : Fin m),
      (HScaleNorm bH mu (alpha - s) ((Dn n j).2)) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal r)
    (hDn_tendsto : Tendsto Dn atTop
      (dataNhds (fun z : H => (HScaleNorm bH mu (alpha - s) z) ^ (1 / 2 : ℝ))
        (HScale bH mu (alpha - s)) S))
    (hfm_cont : Tendsto (fun S' : Fin m → X × H =>
        UScaleDist e lam (1 + st) (fm S' theta.1) (fm S theta.1))
      (dataNhds (fun z : H => (HScaleNorm bH mu (alpha - s) z) ^ (1 / 2 : ℝ))
        (HScale bH mu (alpha - s)) S) (𝓝 0)),
    Tendsto (fun n : ℕ =>
      hellingerDist (Qpost beta m Gammaih LG (Ptheta S theta) S)
        (Qpost beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n))) atTop (𝓝 0) := by
  /- @proof-region region.target-node.session.45d7ff6a81eb7586 begin -/
  intro U _ _ _ _ _ _
  intro H _ _ _ _ _ _
  intro X _ _ _ _ _
  intro e lam
  intro hlam_pos hlam_anti
  intro Gamma hGamma_pos hGamma_inj
  intro Gammah hGammah_symm hGammah_pos hGammah_sq
  intro Gammaih hGammaih_left
  intro iotaH _ bH mu
  intro hmu_pos hmu_anti
  intro C1 hC1_pos hC1_inj hC1_eigen
  intro LG
  intro s0 s1 s st alpha
  intro hs0_nonneg hs0_lt hs1_nonneg hs1_lt hs_gt hs_le hst_gt hst_le halpha
  intro C1c C2c hC1c hC2c
  intro M1 hM1_mono hM1_nonneg
  intro M2 hM2_nonneg hM2_mono_fst hM2_mono_snd
  intro hA1 hA2 hA3 hA4 hLG_all_range
  intro beta hbeta
  intro m hm
  intro Nc hNc
  intro Theta1 _ _ _ _ _
  intro C0th hC0th_basis hC0th_expand
  intro R_u hR_u
  intro fm
  intro Ptheta hPtheta_isProb
  intro hPtheta_gauss hPtheta_mean hPtheta_cov hPtheta_int1 hPtheta_int2 hfm_ball
  intro theta
  intro D
  intro mubar hmubar kappa hkappa
  intro _
  intro h6 h7 h8
  intro delta0 hdelta0 hmoment hdelta_meas hP_scale
  intro delta1 hdelta1 hdelta1_bound
  intro r hr
  intro hS_scale hS_rad
  intro Dn hDn_scale hDn_rad hDn_tendsto
  intro hfm_cont
  have hD_scale : ∀ j : Fin m, HScale bH mu (alpha - s) (D j).2 := hS_scale
  have hD_rad : ∀ j : Fin m, HScaleDist bH mu (alpha - s) (D j).2 0 ≤ ENNReal.ofReal r :=
    fun j => by simpa [HScaleDist] using hS_rad j
  have hBund := statopia_math_node_2103907506_2297e1dc U H X m hm e lam hlam_pos hlam_anti iotaH
    bH mu s alpha st (le_trans hs0_nonneg (le_of_lt hst_gt)) Nc hNc Theta1 C0th hC0th_basis
    hC0th_expand fm Ptheta hPtheta_isProb hPtheta_gauss hPtheta_mean hPtheta_cov hPtheta_int1
    hPtheta_int2 R_u hR_u hfm_ball theta D hfm_cont
  obtain ⟨hc_pos, hc_exp, hc_lam, hc_basis, hLambda, hDens, hSqB, hLim⟩ := hBund
  set rho : ℕ → U → ℝ≥0∞ :=
    fun n => Measure.rnDeriv (Ptheta (Dn n) theta) (Ptheta D theta) with hrho_def
  have hrho_meas : ∀ n : ℕ, Measurable (rho n) := by
    intro n
    rw [hrho_def]
    exact MeasureTheory.Measure.measurable_rnDeriv (Ptheta (Dn n) theta) (Ptheta D theta)
  have hrho_ac : ∀ n : ℕ,
      MeasureTheory.Measure.AbsolutelyContinuous (Ptheta (Dn n) theta) (Ptheta D theta) :=
    fun n => (hDens (Dn n)).2.2.2.2.2.2.1
  have hrho_dens : ∀ n : ℕ, Ptheta (Dn n) theta = (Ptheta D theta).withDensity (rho n) := by
    intro n
    rw [hrho_def]
    exact ((MeasureTheory.Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq
      (μ := Ptheta (Dn n) theta) (ν := Ptheta D theta)).mp (hrho_ac n)).symm
  have hrho_rnDeriv : ∀ n : ℕ,
      (Ptheta (Dn n) theta).rnDeriv (Ptheta D theta) =ᵐ[Ptheta D theta] rho n := by
    intro n
    rw [hrho_def]
  set sigma2 : (Fin m → X × H) → ℝ := fun Dd => tsum (fun k : ℕ =>
    (priorEigen lam Nc theta.2 k)⁻¹ *
      (inner ℝ (e k) (fm Dd theta.1 - fm D theta.1)) ^ 2) with hsigma2_set
  have hsigma2_def : ∀ Dd : Fin m → X × H, sigma2 Dd = tsum (fun k : ℕ =>
      (priorEigen lam Nc theta.2 k)⁻¹ *
        (inner ℝ (e k) (fm Dd theta.1 - fm D theta.1)) ^ 2) := by
    intro Dd
    rw [hsigma2_set]
  have hsigma2_summable : ∀ Dd : Fin m → X × H, Summable (fun k : ℕ =>
      (priorEigen lam Nc theta.2 k)⁻¹ *
        (inner ℝ (e k) (fm Dd theta.1 - fm D theta.1)) ^ 2) :=
    fun Dd => (hDens Dd).1
  have hsigma2_tendsto : Tendsto (fun n : ℕ => sigma2 (Dn n)) atTop (𝓝 0) :=
    (hLim Dn hDn_tendsto).1
  have hexp_sigma2_tendsto : Tendsto (fun n : ℕ => Real.exp (sigma2 (Dn n)) - 1) atTop (𝓝 0) :=
    (hLim Dn hDn_tendsto).2.2
  have hkey_sq : ∀ (Φ : ℝ≥0∞ → ℝ≥0∞) (f g : U → ℝ≥0∞), f =ᵐ[Ptheta D theta] g →
      (∫⁻ u : U, Φ (f u) ∂(Ptheta D theta))
        = ∫⁻ u : U, Φ (g u) ∂(Ptheta D theta) := by
    intro Φ f g hfg
    refine le_antisymm ?_ ?_
    · refine MeasureTheory.lintegral_mono_ae ?_
      filter_upwards [hfg] with u hu
      rw [hu]
    · refine MeasureTheory.lintegral_mono_ae ?_
      filter_upwards [hfg] with u hu
      rw [← hu]
  obtain ⟨Bfund, hBfund⟩ : ∃ B : ℝ, ∀ n : ℕ,
      (∫⁻ u : U, ENNReal.rpow (rho n u) (2 : ℝ) ∂(Ptheta D theta)) ≤ ENNReal.ofReal B :=
    ⟨_, fun n => (hkey_sq (fun x : ℝ≥0∞ => ENNReal.rpow x (2 : ℝ)) (rho n) _
      ((hrho_rnDeriv n).symm.trans ((hDens (Dn n)).2.2.2.2.2.2.2))).trans_le
        ((hSqB (Dn n)).2.2.2)⟩
  set Bbar : ℝ := max Bfund 0 with hBbar_def
  have hBbar : 0 ≤ Bbar := by
    rw [hBbar_def]
    exact le_max_right Bfund 0
  have hrho_bound_rpow : ∀ n : ℕ,
      (∫⁻ u : U, ENNReal.rpow (rho n u) (2 : ℝ) ∂(Ptheta D theta)) ≤ ENNReal.ofReal Bbar := by
    intro n
    refine (hBfund n).trans ?_
    rw [hBbar_def]
    exact ENNReal.ofReal_le_ofReal (le_max_left Bfund 0)
  have hrho_bound : ∀ n : ℕ,
      (∫⁻ u : U, (rho n u) ^ 2 ∂(Ptheta D theta)) ≤ ENNReal.ofReal Bbar := by
    intro n
    refine (le_of_eq ?_).trans (hrho_bound_rpow n)
    exact MeasureTheory.lintegral_congr
      (fun u => (ENNReal.rpow_natCast (rho n u) 2).symm)
  have hrho_moment : ∀ (n : ℕ) (q : ℝ), 0 < q →
      (∫⁻ u : U, ENNReal.rpow (rho n u) q ∂(Ptheta D theta))
        = ENNReal.ofReal (Real.exp (q * (q - 1) / 2 * sigma2 (Dn n))) := by
    intro n q hq
    have hb := (hDens (Dn n)).2.2.1 q hq
    have hρ := (hrho_rnDeriv n).symm.trans ((hDens (Dn n)).2.2.2.2.2.2.2)
    have hcongr : ∀ (f g : U → ℝ≥0∞), f =ᵐ[Ptheta D theta] g →
        (∫⁻ u : U, ENNReal.rpow (f u) q ∂(Ptheta D theta))
          = ∫⁻ u : U, ENNReal.rpow (g u) q ∂(Ptheta D theta) := by
      intro f g hfg
      refine le_antisymm ?_ ?_
      · refine MeasureTheory.lintegral_mono_ae ?_
        filter_upwards [hfg] with u hu
        rw [hu]
      · refine MeasureTheory.lintegral_mono_ae ?_
        filter_upwards [hfg] with u hu
        rw [← hu]
    exact (hcongr _ _ hρ).trans hb
  have hrho_change : ∀ (n : ℕ) (g : U → ℝ), Measurable g → (∀ u : U, 0 ≤ g u) →
      (∫ u : U, g u ∂(Ptheta (Dn n) theta))
        = ∫ u : U, g u * (rho n u).toReal ∂(Ptheta D theta) := by
    intro n g hg hgnn
    have hb := (hDens (Dn n)).2.2.2.2.2.1 g hg hgnn
    have hρ := ((hDens (Dn n)).2.2.2.2.2.2.2).symm.trans (hrho_rnDeriv n)
    refine hb.trans ?_
    exact MeasureTheory.integral_congr_ae (by
      filter_upwards [hρ] with u hu
      rw [hu])
  have hUSS_meas_set : MeasurableSet (UScale e lam (1 - st)) := by
    have hterm : ∀ k : ℕ, Measurable (fun u : U =>
        ENNReal.ofReal (Real.rpow (lam k) (-(1 - st)) * (inner ℝ (e k) u) ^ 2)) := by
      intro k
      have hin : Measurable (fun u : U => inner ℝ (e k) u) :=
        (continuous_const.inner continuous_id).measurable
      exact ENNReal.measurable_ofReal.comp (measurable_const.mul (hin.pow_const 2))
    have hnorm : Measurable (UScaleNorm e lam (1 - st)) := Measurable.ennreal_tsum hterm
    show MeasurableSet (UScaleNorm e lam (1 - st) ⁻¹' (Set.Iio ⊤))
    exact measurableSet_Iio.preimage hnorm
  have hrhon_scale : ∀ n : ℕ, (Ptheta (Dn n) theta) (UScale e lam (1 - st)) = 1 := by
    have hcompP : (Ptheta D theta) (UScale e lam (1 - st))ᶜ = 0 := by
      haveI : IsProbabilityMeasure (Ptheta D theta) := hPtheta_isProb D theta
      exact MeasureTheory.mem_ae_iff.mp
        ((MeasureTheory.mem_ae_iff_prob_eq_one hUSS_meas_set).mpr hP_scale)
    intro n
    haveI : IsProbabilityMeasure (Ptheta (Dn n) theta) := hPtheta_isProb (Dn n) theta
    exact (MeasureTheory.mem_ae_iff_prob_eq_one hUSS_meas_set).mp
      (MeasureTheory.mem_ae_iff.mpr (hrho_ac n hcompP))
  have hrho_sq_tendsto : Tendsto
      (fun n : ℕ => ∫⁻ u : U, ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) ∂(Ptheta D theta))
      atTop (𝓝 0) := by
    refine Filter.Tendsto.congr' ?_ ((hLim Dn hDn_tendsto).2.1)
    refine Filter.Eventually.of_forall (fun n => ?_)
    exact hkey_sq (fun x : ℝ≥0∞ => ENNReal.ofReal ((x.toReal - 1) ^ 2)) _ _
      (((hDens (Dn n)).2.2.2.2.2.2.2).symm.trans (hrho_rnDeriv n))
  have hGamma_ih_zero : Gammaih (0 : H) = 0 := by
    simpa using hGammaih_left (0 : H)
  have hPhi_lower : ∀ (x : X) (y : H) (u : U), HScale bH mu (alpha - s) y →
      UScale e lam (1 - st) u →
      Phi Gammaih LG u x y ≥
        - (kappa * ENNReal.toReal (HScaleDist bH mu (alpha - s) y 0) *
            M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) := by
    intro x y u hy hu
    have h5 : HScale bH mu (alpha - s) (0 : H) := by
      show HScaleNorm bH mu (alpha - s) (0 : H) < ⊤
      simp [HScaleNorm]
    have hb := h6 x x y 0 hy h5 u hu
    have hX : -(kappa * ENNReal.toReal (HScaleDist bH mu (alpha - s) y 0) *
        M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ≤
        Phi Gammaih LG u x y - Phi Gammaih LG u x 0 := by
      by_cases hpos : 0 ≤ Phi Gammaih LG u x y - Phi Gammaih LG u x 0
      · rw [abs_of_nonneg hpos] at hb
        linarith
      · rw [abs_of_neg (lt_of_not_ge hpos)] at hb
        linarith
    have hge : (0 : ℝ) ≤ Phi Gammaih LG u x 0 := by
      simp [Phi, hGamma_ih_zero] <;> positivity
    linarith

  have hMeasNode :
      ∀ (Dd : Fin m → X × H) (x : X) (y : H) (Q : Measure U),
        Q (UScale e lam (1 - st)) = 1 → Q (UScale e lam (1 - st))ᶜ = 0 →
        AEMeasurable (fun u : U => Phi Gammaih LG u x y) Q ∧
          AEMeasurable (fun u : U => potSum Gammaih LG Dd u) Q ∧
          AEMeasurable (fun u : U => temperedDens beta m Gammaih LG Dd u) Q :=
    (statopia_math_node_3916768571_a9930ecf U H X e lam hlam_pos hlam_anti Gamma hGamma_pos
      hGamma_inj Gammah hGammah_symm hGammah_pos hGammah_sq Gammaih hGammaih_left iotaH bH mu
      hmu_pos hmu_anti C1 hC1_pos hC1_inj hC1_eigen LG s0 s1 s st alpha hs0_nonneg hs0_lt
      hs1_nonneg hs1_lt hs_gt hs_le hst_gt hst_le halpha C1c C2c hC1c hC2c M1 hM1_mono
      hM1_nonneg M2 hM2_nonneg hM2_mono_fst hM2_mono_snd hA1 hA2 hA3 hA4 hLG_all_range beta
      hbeta m hm).2.2
  have hcompl : (Ptheta D theta) (UScale e lam (1 - st))ᶜ = 0 := by
    haveI : IsProbabilityMeasure (Ptheta D theta) := hPtheta_isProb D theta
    exact MeasureTheory.mem_ae_iff.mp
      ((MeasureTheory.mem_ae_iff_prob_eq_one hUSS_meas_set).mpr hP_scale)
  have hcompl_n : ∀ n : ℕ, (Ptheta (Dn n) theta) (UScale e lam (1 - st))ᶜ = 0 := by
    intro n
    haveI : IsProbabilityMeasure (Ptheta (Dn n) theta) := hPtheta_isProb (Dn n) theta
    exact MeasureTheory.mem_ae_iff.mp
      ((MeasureTheory.mem_ae_iff_prob_eq_one hUSS_meas_set).mpr (hrhon_scale n))

  have hmeas_f : AEMeasurable (fun u : U => temperedDens beta m Gammaih LG D u) (Ptheta D theta) :=
    (hMeasNode D (D ⟨0, hm⟩).1 (D ⟨0, hm⟩).2 (Ptheta D theta) hP_scale hcompl).2.2
  have hmeas_fn : ∀ n : ℕ,
      AEMeasurable (fun u : U => temperedDens beta m Gammaih LG (Dn n) u) (Ptheta D theta) := by
    intro n
    exact (hMeasNode (Dn n) (D ⟨0, hm⟩).1 (D ⟨0, hm⟩).2 (Ptheta D theta) hP_scale hcompl).2.2
  have hmeas_pot : AEMeasurable (fun u : U => potSum Gammaih LG D u) (Ptheta D theta) :=
    (hMeasNode D (D ⟨0, hm⟩).1 (D ⟨0, hm⟩).2 (Ptheta D theta) hP_scale hcompl).2.1
  have hmeas_potn : ∀ n : ℕ,
      AEMeasurable (fun u : U => potSum Gammaih LG (Dn n) u) (Ptheta D theta) := by
    intro n
    exact (hMeasNode (Dn n) (D ⟨0, hm⟩).1 (D ⟨0, hm⟩).2 (Ptheta D theta) hP_scale hcompl).2.1
  have hmeas_Phi : ∀ (x : X) (y : H),
      AEMeasurable (fun u : U => Phi Gammaih LG u x y) (Ptheta D theta) := by
    intro x y
    exact (hMeasNode D x y (Ptheta D theta) hP_scale hcompl).1
  have hdens_meas_all : ∀ D' : Fin m → X × H,
      AEMeasurable (fun u : U => temperedDens beta m Gammaih LG D' u) (Ptheta D theta) :=
    fun D' => (hMeasNode D' (D ⟨0, hm⟩).1 (D ⟨0, hm⟩).2 (Ptheta D theta) hP_scale hcompl).2.2
  have hsigma2_tendsto_tsum : Tendsto (fun n : ℕ => ∑' k : ℕ,
      (priorEigen lam Nc theta.2 k)⁻¹ *
        (inner ℝ (e k) (fm (Dn n) theta.1 - fm D theta.1)) ^ 2) atTop (𝓝 0) := by
    simpa only [hsigma2_def] using hsigma2_tendsto
  have hmoment_rho : ∀ (n : ℕ) (q : ℝ), 0 < q →
      (∫⁻ u : U, ENNReal.rpow (rho n u) q ∂(Ptheta D theta))
        = ENNReal.ofReal (Real.exp (q * (q - 1) / 2 *
            (∑' k : ℕ, (priorEigen lam Nc theta.2 k)⁻¹ *
              (inner ℝ (e k) (fm (Dn n) theta.1 - fm D theta.1)) ^ 2))) := by
    intro n q hq
    rw [hrho_moment n q hq, hsigma2_def]
  have hNorm := statopia_math_node_934913505_908353c8 U H X e lam hlam_pos hlam_anti Gamma
    hGamma_pos hGamma_inj Gammah hGammah_symm hGammah_pos hGammah_sq Gammaih hGammaih_left iotaH
    bH mu hmu_pos hmu_anti C1 hC1_pos hC1_inj hC1_eigen LG s0 s1 s st alpha hs0_nonneg hs0_lt
    hs1_nonneg hs1_lt hs_gt hs_le hst_gt hst_le halpha C1c C2c hC1c hC2c M1 hM1_mono hM1_nonneg M2
    hM2_nonneg hM2_mono_fst hM2_mono_snd hA1 hA2 hA3 hA4 hLG_all_range beta hbeta m hm Nc hNc
    Theta1 Ptheta hPtheta_isProb theta D mubar hmubar kappa hkappa h6 h7 h8 delta0 hdelta0 hmoment
    hdelta_meas hP_scale delta1 hdelta1 hdelta1_bound r hr fm Dn hD_scale hD_rad hDn_scale
    (fun n j => by simpa [HScaleDist] using hDn_rad n j) hDn_tendsto hfm_cont hsigma2_tendsto_tsum
    (fun n => hsigma2_summable (Dn n)) Bbar hBbar rho hrho_meas hrho_dens hrhon_scale hmoment_rho hrho_bound
    hdens_meas_all
  have hZ_tendsto : Tendsto (fun n : ℕ => Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n)) atTop
      (𝓝 (Zm beta m Gammaih LG (Ptheta D theta) D)) := hNorm.1
  have hZ_pos : 0 < Zm beta m Gammaih LG (Ptheta D theta) D := hNorm.2.1
  have hZn_pos : ∀ n : ℕ, 0 < Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n) := hNorm.2.2.1
  have hsqrt_Pn : Tendsto (fun n : ℕ => ∫ u : U,
      (Real.sqrt (temperedDens beta m Gammaih LG (Dn n) u) -
        Real.sqrt (temperedDens beta m Gammaih LG D u)) ^ 2 ∂(Ptheta (Dn n) theta))
      atTop (𝓝 0) := hNorm.2.2.2.1
  have hT3a : Tendsto (fun n : ℕ => ∫ u : U, temperedDens beta m Gammaih LG D u *
      (Real.sqrt ((rho n u).toReal) - 1) ^ 2 ∂(Ptheta D theta)) atTop (𝓝 0) := hNorm.2.2.2.2.1
  have hT3b : Tendsto (fun n : ℕ => ∫ u : U, temperedDens beta m Gammaih LG (Dn n) u *
      (Real.sqrt ((rho n u).toReal) - 1) ^ 2 ∂(Ptheta D theta)) atTop (𝓝 0) := hNorm.2.2.2.2.2
  have hPotNode : ∀ (Dd : Fin m → X × H),
      (∀ j : Fin m, (HScaleNorm bH mu (alpha - s) (Dd j).2) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal r) →
      AEMeasurable (fun u : U => temperedDens beta m Gammaih LG Dd u) (Ptheta D theta) →
      (∀ u : U, UScale e lam (1 - st) u →
        potSum Gammaih LG Dd u ≥
          - ((m : ℝ) * kappa * r * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ∧
        temperedDens beta m Gammaih LG Dd u ≤
          Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1) +
            delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2)) ∧
      (∫⁻ u : U, ENNReal.ofReal (temperedDens beta m Gammaih LG Dd u) ∂(Ptheta D theta)) ≠ ⊤ ∧
      (∫⁻ u : U, ENNReal.ofReal
        (Real.exp (-(2 * beta / (m : ℝ)) * potSum Gammaih LG Dd u)) ∂(Ptheta D theta)) < ⊤ ∧
      (∫⁻ u : U, ENNReal.ofReal
        (Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1) +
          delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2))
        ∂(Ptheta D theta)) < ⊤ ∧
      (∫⁻ u : U, ENNReal.ofReal
        (Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1) +
          delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2))
        ∂(Ptheta D theta)) ≠ ⊤ := by
    intro Dd hrad hdens
    haveI : IsProbabilityMeasure (Ptheta D theta) := hPtheta_isProb D theta
    exact statopia_math_node_4147388267_4d56357b U H X e lam iotaH bH mu Gammaih LG s st alpha
      M1 hM1_mono hM1_nonneg kappa hkappa hPhi_lower beta hbeta m hm (Ptheta D theta) hP_scale
      delta0 hdelta0 (fun delta h0 hlt => (hmoment delta h0 hlt).indicator hUSS_meas_set)
      delta1 hdelta1 hdelta1_bound r hr Dd hrad hdens
  have hPot_D := hPotNode D (fun j => by simpa [HScaleDist] using hD_rad j) hmeas_f
  have hPot_Dn : ∀ n : ℕ,
      (∀ u : U, UScale e lam (1 - st) u →
        potSum Gammaih LG (Dn n) u ≥
          - ((m : ℝ) * kappa * r * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ∧
        temperedDens beta m Gammaih LG (Dn n) u ≤
          Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1) +
            delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2)) :=
    fun n => (hPotNode (Dn n) (fun j => by simpa [HScaleDist] using hDn_rad n j) (hmeas_fn n)).1
  have hLin_ne_top :
      (∫⁻ u : U, ENNReal.ofReal (temperedDens beta m Gammaih LG D u) ∂(Ptheta D theta)) ≠ ⊤ :=
    hPot_D.2.1
  have hLin_ne_top_n : ∀ n : ℕ,
      (∫⁻ u : U, ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) u)
        ∂(Ptheta D theta)) ≠ ⊤ :=
    fun n => (hPotNode (Dn n) (fun j => by simpa [HScaleDist] using hDn_rad n j) (hmeas_fn n)).2.1
  have hExp_lt_top :
      (∫⁻ u : U, ENNReal.ofReal
        (Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1) +
          delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2))
        ∂(Ptheta D theta)) < ⊤ :=
    hPot_D.2.2.2.1
  have hDens_le : ∀ u : U, UScale e lam (1 - st) u →
      temperedDens beta m Gammaih LG D u ≤
        Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1) +
          delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2) :=
    fun u hu => (hPot_D.1 u hu).2
  have hm_cast_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hf_nn : 0 ≤ᶠ[ae (Ptheta D theta)] (fun u : U => temperedDens beta m Gammaih LG D u) :=
    Filter.Eventually.of_forall (fun u => (Real.exp_pos _).le)
  have hf_pos : ∀ u : U, 0 < temperedDens beta m Gammaih LG D u := fun u => Real.exp_pos _
  have hf_int : Integrable (fun u : U => temperedDens beta m Gammaih LG D u) (Ptheta D theta) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmeas_f.aestronglyMeasurable hf_nn).mp
      hLin_ne_top
  have hZM : ENNReal.ofReal (Zm beta m Gammaih LG (Ptheta D theta) D) =
      ∫⁻ u : U, ENNReal.ofReal (temperedDens beta m Gammaih LG D u) ∂(Ptheta D theta) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf_int hf_nn
  have hM_ne_zero :
      (∫⁻ u : U, ENNReal.ofReal (temperedDens beta m Gammaih LG D u) ∂(Ptheta D theta)) ≠ 0 := by
    intro h0
    have hle :
        (∫⁻ u : U, ENNReal.ofReal (temperedDens beta m Gammaih LG D u) ∂(Ptheta D theta))
          ≤ ENNReal.ofReal (0 : ℝ) := by
      rw [h0]
      simp
    rw [← hZM] at hle
    have hz := (ENNReal.ofReal_le_ofReal_iff (le_refl (0 : ℝ))).mp hle
    linarith
  have hM_toReal :
      (∫⁻ u : U, ENNReal.ofReal (temperedDens beta m Gammaih LG D u) ∂(Ptheta D theta)).toReal
        = Zm beta m Gammaih LG (Ptheta D theta) D := by
    rw [← hZM]
    exact ENNReal.toReal_ofReal hZ_pos.le
  have hae_scale : ∀ᵐ u ∂(Ptheta D theta), u ∈ UScale e lam (1 - st) :=
    MeasureTheory.mem_ae_iff.mpr hcompl
  have hae_dens_n : ∀ n : ℕ, ∀ᵐ u ∂(Ptheta D theta),
      temperedDens beta m Gammaih LG (Dn n) u ≤
        Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1) +
          delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2) := by
    intro n
    filter_upwards [hae_scale] with u hu
    exact (hPot_Dn n u hu).2
  have hfn_int : ∀ n : ℕ,
      Integrable (fun u : U => temperedDens beta m Gammaih LG (Dn n) u) (Ptheta D theta) := by
    intro n
    exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      (hmeas_fn n).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun u => (Real.exp_pos _).le))).mp (hLin_ne_top_n n)
  have hfn_lint : ∀ n : ℕ,
      ENNReal.ofReal (∫ u : U, temperedDens beta m Gammaih LG (Dn n) u ∂(Ptheta D theta))
        = ∫⁻ u : U, ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) u)
            ∂(Ptheta D theta) := by
    intro n
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hfn_int n)
      (Filter.Eventually.of_forall (fun u => (Real.exp_pos _).le))
  have hlint_le_n : ∀ n : ℕ,
      (∫⁻ u : U, ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) u)
          ∂(Ptheta D theta))
        ≤ ∫⁻ u : U, ENNReal.ofReal
            (Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1) +
              delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2))
            ∂(Ptheta D theta) := by
    intro n
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [hae_dens_n n] with u hu
    exact ENNReal.ofReal_le_ofReal hu
  have hfn_bound : ∀ n : ℕ,
      (∫ u : U, temperedDens beta m Gammaih LG (Dn n) u ∂(Ptheta D theta))
        ≤ (∫⁻ u : U, ENNReal.ofReal
            (Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1) +
              delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2))
            ∂(Ptheta D theta)).toReal := by
    intro n
    have h2 : (∫ u : U, temperedDens beta m Gammaih LG (Dn n) u ∂(Ptheta D theta))
        = (∫⁻ u : U, ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) u)
            ∂(Ptheta D theta)).toReal := by
      rw [← hfn_lint n]
      exact (ENNReal.toReal_ofReal
        (MeasureTheory.integral_nonneg (fun u => (Real.exp_pos _).le))).symm
    rw [h2]
    exact (ENNReal.toReal_le_toReal (hLin_ne_top_n n) hPot_D.2.2.2.2).mpr (hlint_le_n n)
  have hmeas_dn_pn : ∀ n : ℕ,
      AEMeasurable (fun u : U => temperedDens beta m Gammaih LG (Dn n) u)
        (Ptheta (Dn n) theta) := by
    intro n
    exact (hMeasNode (Dn n) (D ⟨0, hm⟩).1 (D ⟨0, hm⟩).2 (Ptheta (Dn n) theta)
      (hrhon_scale n) (hcompl_n n)).2.2
  have hmeas_d_pn : ∀ n : ℕ,
      AEMeasurable (fun u : U => temperedDens beta m Gammaih LG D u)
        (Ptheta (Dn n) theta) := by
    intro n
    exact (hMeasNode D (D ⟨0, hm⟩).1 (D ⟨0, hm⟩).2 (Ptheta (Dn n) theta)
      (hrhon_scale n) (hcompl_n n)).2.2
  have hZ_inv_mul :
      ENNReal.ofReal (Zm beta m Gammaih LG (Ptheta D theta) D)⁻¹ *
        ENNReal.ofReal (Zm beta m Gammaih LG (Ptheta D theta) D) = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hZ_pos.le),
      inv_mul_cancel₀ hZ_pos.ne', ENNReal.ofReal_one]
  have hmeas_mk_f : Measurable
      (AEMeasurable.mk (fun u : U => temperedDens beta m Gammaih LG D u) hmeas_f) :=
    hmeas_f.measurable_mk
  have hmeas_ofreal_mk : Measurable
      (fun u : U => ENNReal.ofReal
        (AEMeasurable.mk (fun v : U => temperedDens beta m Gammaih LG D v) hmeas_f u)) :=
    ENNReal.measurable_ofReal.comp hmeas_mk_f
  have hMk_eq :
      (∫⁻ u : U, ENNReal.ofReal
          (AEMeasurable.mk (fun v : U => temperedDens beta m Gammaih LG D v) hmeas_f u)
          ∂(Ptheta D theta))
        = ∫⁻ u : U, ENNReal.ofReal (temperedDens beta m Gammaih LG D u)
            ∂(Ptheta D theta) := by
    refine le_antisymm ?_ ?_
    · refine MeasureTheory.lintegral_mono_ae ?_
      filter_upwards [hmeas_f.ae_eq_mk] with u hu
      rw [hu]
    · refine MeasureTheory.lintegral_mono_ae ?_
      filter_upwards [hmeas_f.ae_eq_mk] with u hu
      rw [hu]
  have hmeas_g1 : Measurable (fun u : U =>
      ENNReal.ofReal (Zm beta m Gammaih LG (Ptheta D theta) D)⁻¹ *
        ENNReal.ofReal
          (AEMeasurable.mk (fun v : U => temperedDens beta m Gammaih LG D v) hmeas_f u)) :=
    measurable_const.mul hmeas_ofreal_mk
  have hmass_g1 :
      (∫⁻ u : U,
          ENNReal.ofReal (Zm beta m Gammaih LG (Ptheta D theta) D)⁻¹ *
            ENNReal.ofReal
              (AEMeasurable.mk (fun v : U => temperedDens beta m Gammaih LG D v) hmeas_f u)
          ∂(Ptheta D theta)) = 1 := by
    rw [MeasureTheory.lintegral_const_mul _ hmeas_ofreal_mk, hMk_eq, ← hZM, hZ_inv_mul]
  have hg1_toReal : ∀ᵐ u ∂(Ptheta D theta),
      (ENNReal.ofReal (Zm beta m Gammaih LG (Ptheta D theta) D)⁻¹ *
        ENNReal.ofReal
          (AEMeasurable.mk (fun v : U => temperedDens beta m Gammaih LG D v) hmeas_f u)).toReal
        = (Zm beta m Gammaih LG (Ptheta D theta) D)⁻¹ *
            temperedDens beta m Gammaih LG D u := by
    filter_upwards [hmeas_f.ae_eq_mk] with u hu
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr hZ_pos.le),
      ENNReal.toReal_ofReal (by rw [← hu]; exact (Real.exp_pos _).le), hu]
  have hZn_inv_mul : ∀ n : ℕ,
      ENNReal.ofReal (Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n))⁻¹ *
        ENNReal.ofReal (Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n)) = 1 := by
    intro n
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (hZn_pos n).le),
      inv_mul_cancel₀ (hZn_pos n).ne', ENNReal.ofReal_one]
  have hmeas_mk_n : ∀ n : ℕ, Measurable
      (AEMeasurable.mk (fun u : U => temperedDens beta m Gammaih LG (Dn n) u)
        (hmeas_dn_pn n)) := by
    intro n
    exact (hmeas_dn_pn n).measurable_mk
  have hmeas_ofreal_mk_n : ∀ n : ℕ, Measurable
      (fun u : U => ENNReal.ofReal
        (AEMeasurable.mk (fun v : U => temperedDens beta m Gammaih LG (Dn n) v)
          (hmeas_dn_pn n) u)) := by
    intro n
    exact ENNReal.measurable_ofReal.comp (hmeas_mk_n n)
  have hMk_eq_n : ∀ n : ℕ,
      (∫⁻ u : U, ENNReal.ofReal
          (AEMeasurable.mk (fun v : U => temperedDens beta m Gammaih LG (Dn n) v)
            (hmeas_dn_pn n) u)
          ∂(Ptheta (Dn n) theta))
        = ∫⁻ u : U, ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) u)
            ∂(Ptheta (Dn n) theta) := by
    intro n
    refine le_antisymm ?_ ?_
    · refine MeasureTheory.lintegral_mono_ae ?_
      filter_upwards [(hmeas_dn_pn n).ae_eq_mk] with u hu
      rw [hu]
    · refine MeasureTheory.lintegral_mono_ae ?_
      filter_upwards [(hmeas_dn_pn n).ae_eq_mk] with u hu
      rw [hu]
  have hmeas_mk_pn : ∀ n : ℕ, Measurable
      (AEMeasurable.mk (fun u : U => temperedDens beta m Gammaih LG (Dn n) u)
        (hmeas_fn n)) := by
    intro n
    exact (hmeas_fn n).measurable_mk
  have hmeas_ofreal_mk_pn : ∀ n : ℕ, Measurable
      (fun u : U => ENNReal.ofReal
        (AEMeasurable.mk (fun v : U => temperedDens beta m Gammaih LG (Dn n) v)
          (hmeas_fn n) u)) := by
    intro n
    exact ENNReal.measurable_ofReal.comp (hmeas_mk_pn n)
  have hmeas_g2 : ∀ n : ℕ, Measurable (fun u : U =>
      rho n u * (ENNReal.ofReal (Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n))⁻¹ *
        ENNReal.ofReal
          (AEMeasurable.mk (fun v : U => temperedDens beta m Gammaih LG (Dn n) v)
            (hmeas_fn n) u))) := by
    intro n
    exact (hrho_meas n).mul (measurable_const.mul (hmeas_ofreal_mk_pn n))
  have hg2_toReal : ∀ n : ℕ, ∀ᵐ u ∂(Ptheta D theta),
      (rho n u * (ENNReal.ofReal (Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n))⁻¹ *
        ENNReal.ofReal
          (AEMeasurable.mk (fun v : U => temperedDens beta m Gammaih LG (Dn n) v)
            (hmeas_fn n) u))).toReal
        = (rho n u).toReal * ((Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n))⁻¹ *
            temperedDens beta m Gammaih LG (Dn n) u) := by
    intro n
    filter_upwards [(hmeas_fn n).ae_eq_mk] with u hu
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (inv_nonneg.mpr (hZn_pos n).le),
      ENNReal.toReal_ofReal (by rw [← hu]; exact (Real.exp_pos _).le), hu]
  have hZn_lower : ∀ᶠ n : ℕ in atTop,
      Zm beta m Gammaih LG (Ptheta D theta) D / 2
        < Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n) := by
    have hpt : Zm beta m Gammaih LG (Ptheta D theta) D ∈
        Set.Ioi (Zm beta m Gammaih LG (Ptheta D theta) D / 2) := by
      show Zm beta m Gammaih LG (Ptheta D theta) D / 2 <
        Zm beta m Gammaih LG (Ptheta D theta) D
      linarith
    have hmem : Set.Ioi (Zm beta m Gammaih LG (Ptheta D theta) D / 2) ∈
        𝓝 (Zm beta m Gammaih LG (Ptheta D theta) D) :=
      isOpen_Ioi.mem_nhds hpt
    exact hZ_tendsto.eventually hmem
  have hZ_ne0 : ENNReal.ofReal (Zm beta m Gammaih LG (Ptheta D theta) D) ≠ 0 := by
    rw [hZM]
    exact hM_ne_zero
  have hZ_neTop : ENNReal.ofReal (Zm beta m Gammaih LG (Ptheta D theta) D) ≠ ⊤ := by
    rw [hZM]
    exact hLin_ne_top
  have hInvZ : (ENNReal.ofReal (Zm beta m Gammaih LG (Ptheta D theta) D))⁻¹
      = ENNReal.ofReal (Zm beta m Gammaih LG (Ptheta D theta) D)⁻¹ := by
    have h := ENNReal.mul_inv_cancel_right
      (a := ENNReal.ofReal ((Zm beta m Gammaih LG (Ptheta D theta) D)⁻¹))
      (b := ENNReal.ofReal (Zm beta m Gammaih LG (Ptheta D theta) D)) hZ_ne0 hZ_neTop
    rwa [hZ_inv_mul, one_mul] at h
  have hQpost_dens_ae :
      (fun u : U => ENNReal.ofReal (temperedDens beta m Gammaih LG D u) /
          (∫⁻ v : U, ENNReal.ofReal (temperedDens beta m Gammaih LG D v)
            ∂(Ptheta D theta)))
        =ᵐ[Ptheta D theta] (fun u : U =>
          ENNReal.ofReal ((Zm beta m Gammaih LG (Ptheta D theta) D)⁻¹ *
            AEMeasurable.mk (fun v : U => temperedDens beta m Gammaih LG D v) hmeas_f u)) := by
    filter_upwards [hmeas_f.ae_eq_mk] with u hu
    show ENNReal.ofReal (temperedDens beta m Gammaih LG D u) *
        (∫⁻ v : U, ENNReal.ofReal (temperedDens beta m Gammaih LG D v) ∂(Ptheta D theta))⁻¹
      = ENNReal.ofReal ((Zm beta m Gammaih LG (Ptheta D theta) D)⁻¹ *
          AEMeasurable.mk (fun v : U => temperedDens beta m Gammaih LG D v) hmeas_f u)
    rw [← hZM, hInvZ, ENNReal.ofReal_mul (inv_nonneg.mpr hZ_pos.le), mul_comm, hu]
  have hQpost_with :
      Qpost beta m Gammaih LG (Ptheta D theta) D
        = (Ptheta D theta).withDensity (fun u : U =>
            ENNReal.ofReal ((Zm beta m Gammaih LG (Ptheta D theta) D)⁻¹ *
              AEMeasurable.mk (fun v : U => temperedDens beta m Gammaih LG D v) hmeas_f u)) := by
    unfold Qpost
    refine le_antisymm ?_ ?_
    · refine MeasureTheory.withDensity_mono ?_
      exact hQpost_dens_ae.le
    · refine MeasureTheory.withDensity_mono ?_
      exact hQpost_dens_ae.symm.le
  have hmeas_ofreal_f :
      AEMeasurable (fun u : U => ENNReal.ofReal (temperedDens beta m Gammaih LG D u))
        (Ptheta D theta) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hmeas_f
  have hmeas_ofreal_fn : ∀ n : ℕ,
      AEMeasurable (fun u : U => ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) u))
        (Ptheta D theta) := by
    intro n
    exact ENNReal.measurable_ofReal.comp_aemeasurable (hmeas_fn n)
  have hrho_aemeas : ∀ n : ℕ, AEMeasurable (rho n) (Ptheta D theta) := by
    intro n
    exact (hrho_meas n).aemeasurable
  have hPn_lin : ∀ n : ℕ,
      (∫⁻ u : U, ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) u)
          ∂(Ptheta (Dn n) theta))
        = ∫⁻ u : U, rho n u * ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) u)
            ∂(Ptheta D theta) := by
    intro n
    rw [hrho_dens n]
    exact MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀ (hrho_aemeas n) (hmeas_ofreal_fn n)
  have hmeas_g1' : Measurable (fun u : U =>
      ENNReal.ofReal ((Zm beta m Gammaih LG (Ptheta D theta) D)⁻¹ *
        AEMeasurable.mk (fun v : U => temperedDens beta m Gammaih LG D v) hmeas_f u)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul hmeas_mk_f)
  have hmass_g1' :
      (∫⁻ u : U, ENNReal.ofReal ((Zm beta m Gammaih LG (Ptheta D theta) D)⁻¹ *
          AEMeasurable.mk (fun v : U => temperedDens beta m Gammaih LG D v) hmeas_f u)
          ∂(Ptheta D theta)) = 1 := by
    rw [← hmass_g1]
    refine le_antisymm ?_ ?_
    · refine MeasureTheory.lintegral_mono_ae ?_
      exact Filter.Eventually.of_forall
        (fun u => le_of_eq (ENNReal.ofReal_mul (inv_nonneg.mpr hZ_pos.le)))
    · refine MeasureTheory.lintegral_mono_ae ?_
      exact Filter.Eventually.of_forall
        (fun u => le_of_eq (ENNReal.ofReal_mul (inv_nonneg.mpr hZ_pos.le)).symm)
  have hZn_cast_ne0 : ∀ n : ℕ,
      ENNReal.ofReal (Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n)) ≠ 0 := by
    intro n h0
    have h1 : (ENNReal.ofReal (Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n))).toReal
        = 0 := by
      rw [h0]
      simp
    rw [ENNReal.toReal_ofReal'] at h1
    have h2 : 0 < max (Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n)) 0 :=
      lt_of_lt_of_le (hZn_pos n) (le_max_left _ _)
    linarith
  have hZn_cast_neTop : ∀ n : ℕ,
      ENNReal.ofReal (Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n)) ≠ ⊤ :=
    fun n => ENNReal.top_ne_ofReal.symm
  have hInvZn : ∀ n : ℕ,
      (ENNReal.ofReal (Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n)))⁻¹
        = ENNReal.ofReal (Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n))⁻¹ := by
    intro n
    have h := ENNReal.mul_inv_cancel_right
      (a := ENNReal.ofReal ((Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n))⁻¹))
      (b := ENNReal.ofReal (Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n)))
      (hZn_cast_ne0 n) (hZn_cast_neTop n)
    rwa [hZn_inv_mul n, one_mul] at h
  have hBbar_neTop : ENNReal.ofReal Bbar ≠ ⊤ := ENNReal.top_ne_ofReal.symm
  have hAMGM : ∀ a b : ℝ≥0∞, a * b ≤ a ^ 2 + b ^ 2 := by
    intro a b
    rcases le_total a b with h | h
    · calc a * b ≤ b * b := mul_le_mul h le_rfl (zero_le b) (zero_le b)
        _ = b ^ 2 := (pow_two b).symm
        _ ≤ a ^ 2 + b ^ 2 := by
            simpa using add_le_add (zero_le (a ^ 2)) (le_refl (b ^ 2))
    · calc a * b ≤ a * a := mul_le_mul le_rfl h (zero_le b) (zero_le a)
        _ = a ^ 2 := (pow_two a).symm
        _ ≤ a ^ 2 + b ^ 2 := by
            simpa using add_le_add (le_refl (a ^ 2)) (zero_le (b ^ 2))
  have hexpsq : ∀ u : U,
      Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1) +
          delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2) *
        Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1) +
          delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2) =
      Real.exp (2 * ((beta * kappa * r) ^ 2 / (4 * delta1))) *
        Real.exp (2 * delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2) := by
    intro u
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hExpProd_ne_top :
      (∫⁻ u : U, ENNReal.ofReal (Real.exp (2 * ((beta * kappa * r) ^ 2 / (4 * delta1))) *
          Real.exp (2 * delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2))
          ∂(Ptheta D theta)) ≠ ⊤ := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      ((hmoment (2 * delta1) (by linarith) (by linarith)).const_mul
        (Real.exp (2 * ((beta * kappa * r) ^ 2 / (4 * delta1)))))
      (Filter.Eventually.of_forall
        (fun u => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))]
    exact ENNReal.top_ne_ofReal.symm
  have hSqDens_ne_top : ∀ n : ℕ,
      (∫⁻ u : U, (ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) u)) ^ 2
          ∂(Ptheta D theta)) ≠ ⊤ := by
    intro n
    have hle : (∫⁻ u : U, (ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) u)) ^ 2
        ∂(Ptheta D theta))
        ≤ ∫⁻ u : U, ENNReal.ofReal (Real.exp (2 * ((beta * kappa * r) ^ 2 / (4 * delta1))) *
            Real.exp (2 * delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2))
            ∂(Ptheta D theta) := by
      refine MeasureTheory.lintegral_mono_ae ?_
      filter_upwards [hae_dens_n n] with u hu
      have hE : 0 ≤ Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1) +
          delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2) :=
        (Real.exp_pos _).le
      calc (ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) u)) ^ 2
          ≤ (ENNReal.ofReal (Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1) +
              delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2))) ^ 2 :=
            pow_le_pow_left₀ (zero_le _) (ENNReal.ofReal_le_ofReal hu) 2
        _ = ENNReal.ofReal (Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1) +
              delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2) *
            Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1) +
              delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2)) := by
            rw [pow_two, ← ENNReal.ofReal_mul hE]
        _ = ENNReal.ofReal (Real.exp (2 * ((beta * kappa * r) ^ 2 / (4 * delta1))) *
            Real.exp (2 * delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2)) := by
            rw [hexpsq u]
    exact lt_top_iff_ne_top.mp (lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hExpProd_ne_top))
  have hProd_ne_top : ∀ n : ℕ,
      (∫⁻ u : U, rho n u * ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) u)
          ∂(Ptheta D theta)) ≠ ⊤ := by
    intro n
    have hle :
        (∫⁻ u : U, rho n u * ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) u)
            ∂(Ptheta D theta))
          ≤ ∫⁻ u : U,
              (rho n u) ^ 2 + (ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) u)) ^ 2
              ∂(Ptheta D theta) := by
      refine MeasureTheory.lintegral_mono_ae ?_
      exact Filter.Eventually.of_forall (fun u => hAMGM _ _)
    have hsplit :
        (∫⁻ u : U,
            (rho n u) ^ 2 + (ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) u)) ^ 2
            ∂(Ptheta D theta))
          = (∫⁻ u : U, (rho n u) ^ 2 ∂(Ptheta D theta)) +
            (∫⁻ u : U, (ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) u)) ^ 2
              ∂(Ptheta D theta)) :=
      MeasureTheory.lintegral_add_left ((hrho_meas n).pow_const 2)
        (fun u : U => (ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) u)) ^ 2)
    rw [hsplit] at hle
    exact lt_top_iff_ne_top.mp (lt_of_le_of_lt hle (ENNReal.add_lt_top.mpr
      ⟨lt_of_le_of_lt (hrho_bound n) (lt_top_iff_ne_top.mpr hBbar_neTop),
        lt_top_iff_ne_top.mpr (hSqDens_ne_top n)⟩))
  have hLn_ne_top : ∀ n : ℕ,
      (∫⁻ u : U, ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) u)
          ∂(Ptheta (Dn n) theta)) ≠ ⊤ := by
    intro n
    rw [hPn_lin n]
    exact hProd_ne_top n
  have hfn_int_n : ∀ n : ℕ,
      Integrable (fun u : U => temperedDens beta m Gammaih LG (Dn n) u)
        (Ptheta (Dn n) theta) := by
    intro n
    exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      (hmeas_dn_pn n).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun u => (Real.exp_pos _).le))).mp (hLn_ne_top n)
  have hLn_eq : ∀ n : ℕ,
      ENNReal.ofReal (Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n))
        = ∫⁻ u : U, ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) u)
            ∂(Ptheta (Dn n) theta) := by
    intro n
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hfn_int_n n)
      (Filter.Eventually.of_forall (fun u => (Real.exp_pos _).le))
  have hQpost_with_n : ∀ n : ℕ,
      Qpost beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n)
        = (Ptheta D theta).withDensity (fun u : U =>
            rho n u *
              (ENNReal.ofReal (Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n))⁻¹ *
                ENNReal.ofReal
                  (AEMeasurable.mk (fun v : U => temperedDens beta m Gammaih LG (Dn n) v)
                    (hmeas_fn n) u))) := by
    intro n
    have hdens : (fun u : U => rho n u *
          (ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) u) *
            (∫⁻ v : U, ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) v)
              ∂(Ptheta (Dn n) theta))⁻¹))
        =ᵐ[Ptheta D theta] (fun u : U => rho n u *
          (ENNReal.ofReal (Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n))⁻¹ *
            ENNReal.ofReal
              (AEMeasurable.mk (fun v : U => temperedDens beta m Gammaih LG (Dn n) v)
                (hmeas_fn n) u))) := by
      filter_upwards [(hmeas_fn n).ae_eq_mk] with u hu
      rw [← hLn_eq n, hInvZn n, hu,
        mul_comm (ENNReal.ofReal
          (AEMeasurable.mk (fun v : U => temperedDens beta m Gammaih LG (Dn n) v)
            (hmeas_fn n) u))]
    have hd_p : AEMeasurable
        (fun u : U => ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) u) *
          (∫⁻ v : U, ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) v)
            ∂(Ptheta (Dn n) theta))⁻¹) (Ptheta D theta) :=
      (hmeas_ofreal_fn n).mul measurable_const.aemeasurable
    have hmul := MeasureTheory.withDensity_mul₀ (μ := Ptheta D theta) (f := rho n)
      (g := fun u : U => ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) u) *
        (∫⁻ v : U, ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) v)
          ∂(Ptheta (Dn n) theta))⁻¹) (hrho_aemeas n) hd_p
    rw [← hrho_dens n] at hmul
    have hstep : Qpost beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n)
        = (Ptheta D theta).withDensity (fun u : U =>
            rho n u *
              (ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) u) *
                (∫⁻ v : U, ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) v)
                  ∂(Ptheta (Dn n) theta))⁻¹)) := by
      rw [show (Ptheta D theta).withDensity (fun u : U =>
            rho n u *
              (ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) u) *
                (∫⁻ v : U, ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) v)
                  ∂(Ptheta (Dn n) theta))⁻¹))
          = (Ptheta (Dn n) theta).withDensity (fun u : U =>
              ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) u) *
                (∫⁻ v : U, ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) v)
                  ∂(Ptheta (Dn n) theta))⁻¹) from hmul]
      rfl
    rw [hstep]
    refine le_antisymm ?_ ?_
    · exact MeasureTheory.withDensity_mono hdens.le
    · exact MeasureTheory.withDensity_mono hdens.symm.le
  have hmass_g2 : ∀ n : ℕ,
      (∫⁻ u : U, rho n u *
          (ENNReal.ofReal (Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n))⁻¹ *
            ENNReal.ofReal
              (AEMeasurable.mk (fun v : U => temperedDens beta m Gammaih LG (Dn n) v)
                (hmeas_fn n) u)) ∂(Ptheta D theta)) = 1 := by
    intro n
    have hpt : ∀ u : U, rho n u *
          (ENNReal.ofReal (Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n))⁻¹ *
            ENNReal.ofReal
              (AEMeasurable.mk (fun v : U => temperedDens beta m Gammaih LG (Dn n) v)
                (hmeas_fn n) u))
        = ENNReal.ofReal (Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n))⁻¹ *
            (rho n u *
              ENNReal.ofReal
                (AEMeasurable.mk (fun v : U => temperedDens beta m Gammaih LG (Dn n) v)
                  (hmeas_fn n) u)) := by
      intro u
      rw [← mul_assoc, mul_comm (rho n u), mul_assoc]
    have hcongr : (∫⁻ u : U, rho n u *
          (ENNReal.ofReal (Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n))⁻¹ *
            ENNReal.ofReal
              (AEMeasurable.mk (fun v : U => temperedDens beta m Gammaih LG (Dn n) v)
                (hmeas_fn n) u)) ∂(Ptheta D theta))
        = ∫⁻ u : U,
            ENNReal.ofReal (Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n))⁻¹ *
              (rho n u *
                ENNReal.ofReal
                  (AEMeasurable.mk (fun v : U => temperedDens beta m Gammaih LG (Dn n) v)
                    (hmeas_fn n) u)) ∂(Ptheta D theta) := by
      refine le_antisymm ?_ ?_
      · refine MeasureTheory.lintegral_mono_ae ?_
        exact Filter.Eventually.of_forall (fun u => le_of_eq (hpt u))
      · refine MeasureTheory.lintegral_mono_ae ?_
        exact Filter.Eventually.of_forall (fun u => le_of_eq (hpt u).symm)
    have hinner : (∫⁻ u : U, rho n u *
          ENNReal.ofReal
            (AEMeasurable.mk (fun v : U => temperedDens beta m Gammaih LG (Dn n) v)
              (hmeas_fn n) u) ∂(Ptheta D theta))
        = ∫⁻ u : U, rho n u *
            ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) u)
            ∂(Ptheta D theta) := by
      refine le_antisymm ?_ ?_
      · refine MeasureTheory.lintegral_mono_ae ?_
        filter_upwards [(hmeas_fn n).ae_eq_mk] with u hu
        rw [hu]
      · refine MeasureTheory.lintegral_mono_ae ?_
        filter_upwards [(hmeas_fn n).ae_eq_mk] with u hu
        rw [hu]
    rw [hcongr, MeasureTheory.lintegral_const_mul _
      ((hrho_meas n).mul (hmeas_ofreal_mk_pn n)), hinner, ← hPn_lin n, ← hLn_eq n,
      hZn_inv_mul n]
  have hhell_eq : ∀ n : ℕ,
      hellingerDist (Qpost beta m Gammaih LG (Ptheta D theta) D)
          (Qpost beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n))
        = Real.sqrt ((1 / 2 : ℝ) * (∫⁻ u : U, ENNReal.ofReal
            ((Real.sqrt ((ENNReal.ofReal ((Zm beta m Gammaih LG (Ptheta D theta) D)⁻¹ *
                  AEMeasurable.mk (fun v : U => temperedDens beta m Gammaih LG D v)
                    hmeas_f u)).toReal) -
              Real.sqrt ((rho n u * (ENNReal.ofReal
                    (Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n))⁻¹ *
                  ENNReal.ofReal
                    (AEMeasurable.mk (fun v : U => temperedDens beta m Gammaih LG (Dn n) v)
                      (hmeas_fn n) u))).toReal)) ^ 2)
            ∂(Ptheta D theta)).toReal) := by
    intro n
    haveI : IsProbabilityMeasure (Ptheta D theta) := hPtheta_isProb D theta
    rw [hQpost_with, hQpost_with_n n]
    exact statopia_math_node_4026486579_064ccf6a U (Ptheta D theta) _ _
      hmeas_g1' (hmeas_g2 n) hmass_g1' (hmass_g2 n)
  have hg1'_toReal : ∀ᵐ u ∂(Ptheta D theta),
      (ENNReal.ofReal ((Zm beta m Gammaih LG (Ptheta D theta) D)⁻¹ *
        AEMeasurable.mk (fun v : U => temperedDens beta m Gammaih LG D v) hmeas_f u)).toReal
        = (Zm beta m Gammaih LG (Ptheta D theta) D)⁻¹ *
            temperedDens beta m Gammaih LG D u := by
    filter_upwards [hmeas_f.ae_eq_mk] with u hu
    rw [ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.mpr hZ_pos.le)
      (by rw [← hu]; exact (Real.exp_pos _).le)), hu]
  have hinv_sqrt_tendsto :
      Tendsto (fun n : ℕ => (Real.sqrt (Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n)))⁻¹)
        atTop (𝓝 ((Real.sqrt (Zm beta m Gammaih LG (Ptheta D theta) D))⁻¹)) := by
    have hcont : ContinuousAt (fun t : ℝ => (Real.sqrt t)⁻¹)
        (Zm beta m Gammaih LG (Ptheta D theta) D) :=
      (Real.continuous_sqrt.continuousAt).inv₀ (ne_of_gt (Real.sqrt_pos.mpr hZ_pos))
    exact hcont.tendsto.comp hZ_tendsto
  simp only [hhell_eq]
  have hsqrt_g1 : ∀ᵐ u ∂(Ptheta D theta),
      Real.sqrt ((ENNReal.ofReal ((Zm beta m Gammaih LG (Ptheta D theta) D)⁻¹ *
          AEMeasurable.mk (fun v : U => temperedDens beta m Gammaih LG D v)
            hmeas_f u)).toReal)
        = (Real.sqrt (Zm beta m Gammaih LG (Ptheta D theta) D))⁻¹ *
            Real.sqrt (temperedDens beta m Gammaih LG D u) := by
    filter_upwards [hg1'_toReal] with u hu
    rw [hu, Real.sqrt_mul (inv_nonneg.mpr hZ_pos.le), Real.sqrt_inv]
  have hsqrt_g2 : ∀ n : ℕ, ∀ᵐ u ∂(Ptheta D theta),
      Real.sqrt ((rho n u * (ENNReal.ofReal
            (Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n))⁻¹ *
          ENNReal.ofReal
            (AEMeasurable.mk (fun v : U => temperedDens beta m Gammaih LG (Dn n) v)
              (hmeas_fn n) u))).toReal)
        = Real.sqrt ((rho n u).toReal) *
            ((Real.sqrt (Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n)))⁻¹ *
              Real.sqrt (temperedDens beta m Gammaih LG (Dn n) u)) := by
    intro n
    filter_upwards [hg2_toReal n] with u hu
    rw [hu, Real.sqrt_mul ENNReal.toReal_nonneg,
      Real.sqrt_mul (inv_nonneg.mpr (hZn_pos n).le), Real.sqrt_inv]
  have hkey_alg : ∀ (a an r c d : ℝ), 0 ≤ a → 0 ≤ an → 0 ≤ r → 0 ≤ c → 0 ≤ d →
      (c * a - r * (d * an)) ^ 2 ≤
        4 * d ^ 2 * (a ^ 2 * (1 - r) ^ 2) +
          4 * d ^ 2 * (r ^ 2 * (an - a) ^ 2) + 2 * a ^ 2 * (c - d) ^ 2 := by
    intro a an r c d ha han hr hc hd
    have hs1 : (a - r * an) ^ 2 ≤ 2 * (a ^ 2 * (1 - r) ^ 2) + 2 * (r ^ 2 * (an - a) ^ 2) := by
      have hsplit : a - r * an = a * (1 - r) + r * (a - an) := by ring
      have hb : (a * (1 - r) + r * (a - an)) ^ 2 ≤
          2 * (a * (1 - r)) ^ 2 + 2 * (r * (a - an)) ^ 2 := by
        have hsum : (a * (1 - r) + r * (a - an)) ^ 2 +
            (a * (1 - r) - r * (a - an)) ^ 2 =
            2 * (a * (1 - r)) ^ 2 + 2 * (r * (a - an)) ^ 2 := by ring
        rw [← hsum]
        exact le_add_of_nonneg_right (sq_nonneg _)
      calc (a - r * an) ^ 2 = (a * (1 - r) + r * (a - an)) ^ 2 := by rw [hsplit]
        _ ≤ 2 * (a * (1 - r)) ^ 2 + 2 * (r * (a - an)) ^ 2 := hb
        _ = 2 * (a ^ 2 * (1 - r) ^ 2) + 2 * (r ^ 2 * (an - a) ^ 2) := by ring
    have hs2 : (c * a - r * (d * an)) ^ 2 ≤
        2 * (d * (a - r * an)) ^ 2 + 2 * (a * (c - d)) ^ 2 := by
      have hsplit : c * a - r * (d * an) = d * (a - r * an) + a * (c - d) := by ring
      have hb : (d * (a - r * an) + a * (c - d)) ^ 2 ≤
          2 * (d * (a - r * an)) ^ 2 + 2 * (a * (c - d)) ^ 2 := by
        have hsum : (d * (a - r * an) + a * (c - d)) ^ 2 +
            (d * (a - r * an) - a * (c - d)) ^ 2 =
            2 * (d * (a - r * an)) ^ 2 + 2 * (a * (c - d)) ^ 2 := by ring
        rw [← hsum]
        exact le_add_of_nonneg_right (sq_nonneg _)
      calc (c * a - r * (d * an)) ^ 2 = (d * (a - r * an) + a * (c - d)) ^ 2 := by rw [hsplit]
        _ ≤ 2 * (d * (a - r * an)) ^ 2 + 2 * (a * (c - d)) ^ 2 := hb
    have hs3 : 2 * d ^ 2 * (a - r * an) ^ 2 ≤
        4 * d ^ 2 * (a ^ 2 * (1 - r) ^ 2) + 4 * d ^ 2 * (r ^ 2 * (an - a) ^ 2) := by
      have h := mul_le_mul_of_nonneg_left hs1
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg d))
      calc 2 * d ^ 2 * (a - r * an) ^ 2
          ≤ 2 * d ^ 2 * (2 * (a ^ 2 * (1 - r) ^ 2) + 2 * (r ^ 2 * (an - a) ^ 2)) := h
        _ = 4 * d ^ 2 * (a ^ 2 * (1 - r) ^ 2) + 4 * d ^ 2 * (r ^ 2 * (an - a) ^ 2) := by ring
    have hs2' : (c * a - r * (d * an)) ^ 2 ≤
        2 * d ^ 2 * (a - r * an) ^ 2 + 2 * a ^ 2 * (c - d) ^ 2 := by
      calc (c * a - r * (d * an)) ^ 2
          ≤ 2 * (d * (a - r * an)) ^ 2 + 2 * (a * (c - d)) ^ 2 := hs2
        _ = 2 * d ^ 2 * (a - r * an) ^ 2 + 2 * a ^ 2 * (c - d) ^ 2 := by ring
    calc (c * a - r * (d * an)) ^ 2
        ≤ 2 * d ^ 2 * (a - r * an) ^ 2 + 2 * a ^ 2 * (c - d) ^ 2 := hs2'
      _ ≤ (4 * d ^ 2 * (a ^ 2 * (1 - r) ^ 2) + 4 * d ^ 2 * (r ^ 2 * (an - a) ^ 2)) +
            2 * a ^ 2 * (c - d) ^ 2 := add_le_add hs3 le_rfl
      _ = 4 * d ^ 2 * (a ^ 2 * (1 - r) ^ 2) + 4 * d ^ 2 * (r ^ 2 * (an - a) ^ 2) +
            2 * a ^ 2 * (c - d) ^ 2 := by ring

  have hkey_pt : ∀ n : ℕ, ∀ᵐ u ∂(Ptheta D theta),
      (Real.sqrt ((ENNReal.ofReal ((Zm beta m Gammaih LG (Ptheta D theta) D)⁻¹ *
              AEMeasurable.mk (fun v : U => temperedDens beta m Gammaih LG D v)
                hmeas_f u)).toReal) -
          Real.sqrt ((rho n u * (ENNReal.ofReal
                (Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n))⁻¹ *
              ENNReal.ofReal
                (AEMeasurable.mk (fun v : U => temperedDens beta m Gammaih LG (Dn n) v)
                  (hmeas_fn n) u))).toReal)) ^ 2
        ≤ 4 * ((Real.sqrt (Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n)))⁻¹) ^ 2 *
            (temperedDens beta m Gammaih LG D u *
              (1 - Real.sqrt ((rho n u).toReal)) ^ 2) +
          4 * ((Real.sqrt (Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n)))⁻¹) ^ 2 *
            ((rho n u).toReal *
              (Real.sqrt (temperedDens beta m Gammaih LG (Dn n) u) -
                Real.sqrt (temperedDens beta m Gammaih LG D u)) ^ 2) +
          2 * temperedDens beta m Gammaih LG D u *
            ((Real.sqrt (Zm beta m Gammaih LG (Ptheta D theta) D))⁻¹ -
              (Real.sqrt (Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n)))⁻¹) ^ 2 := by
    intro n
    filter_upwards [hsqrt_g1, hsqrt_g2 n] with u h3 h4
    rw [h3, h4]
    have hA : (Real.sqrt (temperedDens beta m Gammaih LG D u)) ^ 2 =
        temperedDens beta m Gammaih LG D u := Real.sq_sqrt (Real.exp_pos _).le
    have hR : (Real.sqrt ((rho n u).toReal)) ^ 2 = (rho n u).toReal :=
      Real.sq_sqrt ENNReal.toReal_nonneg
    have hinst := hkey_alg (Real.sqrt (temperedDens beta m Gammaih LG D u))
      (Real.sqrt (temperedDens beta m Gammaih LG (Dn n) u))
      (Real.sqrt ((rho n u).toReal))
      ((Real.sqrt (Zm beta m Gammaih LG (Ptheta D theta) D))⁻¹)
      ((Real.sqrt (Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n)))⁻¹)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      (inv_nonneg.mpr (Real.sqrt_nonneg _)) (inv_nonneg.mpr (Real.sqrt_nonneg _))
    refine le_trans hinst ?_
    rw [hA, hR]
  have hZn_upper : ∀ᶠ n : ℕ in atTop,
      Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n)
        < 2 * (Zm beta m Gammaih LG (Ptheta D theta) D) := by
    have hpt : Zm beta m Gammaih LG (Ptheta D theta) D ∈
        Set.Iio (2 * (Zm beta m Gammaih LG (Ptheta D theta) D)) := by
      show Zm beta m Gammaih LG (Ptheta D theta) D <
        2 * (Zm beta m Gammaih LG (Ptheta D theta) D)
      linarith
    have hmem : Set.Iio (2 * (Zm beta m Gammaih LG (Ptheta D theta) D)) ∈
        𝓝 (Zm beta m Gammaih LG (Ptheta D theta) D) :=
      isOpen_Iio.mem_nhds hpt
    exact hZ_tendsto.eventually hmem
  have hI_le : ∀ n : ℕ,
      (∫⁻ u : U, ENNReal.ofReal
          ((Real.sqrt ((ENNReal.ofReal ((Zm beta m Gammaih LG (Ptheta D theta) D)⁻¹ *
                AEMeasurable.mk (fun v : U => temperedDens beta m Gammaih LG D v)
                  hmeas_f u)).toReal) -
            Real.sqrt ((rho n u * (ENNReal.ofReal
                  (Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n))⁻¹ *
                ENNReal.ofReal
                  (AEMeasurable.mk (fun v : U => temperedDens beta m Gammaih LG (Dn n) v)
                    (hmeas_fn n) u))).toReal)) ^ 2) ∂(Ptheta D theta))
        ≤ ∫⁻ u : U, ENNReal.ofReal
            (4 * ((Real.sqrt (Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n)))⁻¹) ^ 2 *
                (temperedDens beta m Gammaih LG D u *
                  (1 - Real.sqrt ((rho n u).toReal)) ^ 2) +
              4 * ((Real.sqrt (Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n)))⁻¹) ^ 2 *
                ((rho n u).toReal *
                  (Real.sqrt (temperedDens beta m Gammaih LG (Dn n) u) -
                    Real.sqrt (temperedDens beta m Gammaih LG D u)) ^ 2) +
              2 * temperedDens beta m Gammaih LG D u *
                ((Real.sqrt (Zm beta m Gammaih LG (Ptheta D theta) D))⁻¹ -
                  (Real.sqrt (Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n)))⁻¹) ^ 2)
            ∂(Ptheta D theta) := by
    intro n
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [hkey_pt n] with u hu
    exact ENNReal.ofReal_le_ofReal hu
  have hSqDens_base_ne_top :
      (∫⁻ u : U, (ENNReal.ofReal (temperedDens beta m Gammaih LG D u)) ^ 2
          ∂(Ptheta D theta)) ≠ ⊤ := by
    have hle : (∫⁻ u : U, (ENNReal.ofReal (temperedDens beta m Gammaih LG D u)) ^ 2
        ∂(Ptheta D theta))
        ≤ ∫⁻ u : U, ENNReal.ofReal (Real.exp (2 * ((beta * kappa * r) ^ 2 / (4 * delta1))) *
            Real.exp (2 * delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2))
            ∂(Ptheta D theta) := by
      refine MeasureTheory.lintegral_mono_ae ?_
      filter_upwards [hae_scale] with u hu
      have hE : 0 ≤ Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1) +
          delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2) :=
        (Real.exp_pos _).le
      calc (ENNReal.ofReal (temperedDens beta m Gammaih LG D u)) ^ 2
          ≤ (ENNReal.ofReal (Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1) +
              delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2))) ^ 2 :=
            pow_le_pow_left₀ (zero_le _) (ENNReal.ofReal_le_ofReal (hDens_le u hu)) 2
        _ = ENNReal.ofReal (Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1) +
              delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2) *
            Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1) +
              delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2)) := by
            rw [pow_two, ← ENNReal.ofReal_mul hE]
        _ = ENNReal.ofReal (Real.exp (2 * ((beta * kappa * r) ^ 2 / (4 * delta1))) *
            Real.exp (2 * delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2)) := by
            rw [hexpsq u]
    exact lt_top_iff_ne_top.mp (lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hExpProd_ne_top))
  have hProd_base_ne_top : ∀ n : ℕ,
      (∫⁻ u : U, rho n u * ENNReal.ofReal (temperedDens beta m Gammaih LG D u)
          ∂(Ptheta D theta)) ≠ ⊤ := by
    intro n
    have hle :
        (∫⁻ u : U, rho n u * ENNReal.ofReal (temperedDens beta m Gammaih LG D u)
            ∂(Ptheta D theta))
          ≤ ∫⁻ u : U,
              (rho n u) ^ 2 + (ENNReal.ofReal (temperedDens beta m Gammaih LG D u)) ^ 2
              ∂(Ptheta D theta) := by
      refine MeasureTheory.lintegral_mono_ae ?_
      exact Filter.Eventually.of_forall (fun u => hAMGM _ _)
    have hsplit :
        (∫⁻ u : U,
            (rho n u) ^ 2 + (ENNReal.ofReal (temperedDens beta m Gammaih LG D u)) ^ 2
            ∂(Ptheta D theta))
          = (∫⁻ u : U, (rho n u) ^ 2 ∂(Ptheta D theta)) +
            (∫⁻ u : U, (ENNReal.ofReal (temperedDens beta m Gammaih LG D u)) ^ 2
              ∂(Ptheta D theta)) :=
      MeasureTheory.lintegral_add_left ((hrho_meas n).pow_const 2)
        (fun u : U => (ENNReal.ofReal (temperedDens beta m Gammaih LG D u)) ^ 2)
    rw [hsplit] at hle
    exact lt_top_iff_ne_top.mp (lt_of_le_of_lt hle (ENNReal.add_lt_top.mpr
      ⟨lt_of_le_of_lt (hrho_bound n) (lt_top_iff_ne_top.mpr hBbar_neTop),
        lt_top_iff_ne_top.mpr hSqDens_base_ne_top⟩))
  have hLin_f_pn : ∀ n : ℕ,
      (∫⁻ u : U, ENNReal.ofReal (temperedDens beta m Gammaih LG D u)
          ∂(Ptheta (Dn n) theta)) ≠ ⊤ := by
    intro n
    have heq : (∫⁻ u : U, ENNReal.ofReal (temperedDens beta m Gammaih LG D u)
          ∂(Ptheta (Dn n) theta))
        = ∫⁻ u : U, rho n u * ENNReal.ofReal (temperedDens beta m Gammaih LG D u)
            ∂(Ptheta D theta) := by
      rw [hrho_dens n]
      exact MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀ (hrho_aemeas n) hmeas_ofreal_f
    rw [heq]
    exact hProd_base_ne_top n
  have hf_int_pn : ∀ n : ℕ,
      Integrable (fun u : U => temperedDens beta m Gammaih LG D u) (Ptheta (Dn n) theta) := by
    intro n
    exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable (hmeas_d_pn n).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun u => (Real.exp_pos _).le))).mp (hLin_f_pn n)
  have hW_alg : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (Real.sqrt a - Real.sqrt b) ^ 2 ≤ 2 * (a + b) := by
    intro a b ha hb
    have h1 : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha
    have h2 : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb
    nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  have hW_int : ∀ n : ℕ, Integrable (fun u : U =>
      (Real.sqrt (temperedDens beta m Gammaih LG (Dn n) u) -
        Real.sqrt (temperedDens beta m Gammaih LG D u)) ^ 2) (Ptheta (Dn n) theta) := by
    intro n
    have hAEM1 : AEMeasurable (fun u : U => ENNReal.ofReal
        (temperedDens beta m Gammaih LG (Dn n) u)) (Ptheta (Dn n) theta) :=
      ENNReal.measurable_ofReal.comp_aemeasurable (hmeas_dn_pn n)
    have hAEM2 : AEMeasurable (fun u : U => ENNReal.ofReal
        (temperedDens beta m Gammaih LG D u)) (Ptheta (Dn n) theta) :=
      ENNReal.measurable_ofReal.comp_aemeasurable (hmeas_d_pn n)
    have hw_aesm : AEStronglyMeasurable (fun u : U =>
        (Real.sqrt (temperedDens beta m Gammaih LG (Dn n) u) -
          Real.sqrt (temperedDens beta m Gammaih LG D u)) ^ 2) (Ptheta (Dn n) theta) :=
      ((((Real.continuous_sqrt.measurable.comp_aemeasurable' (hmeas_dn_pn n)).sub
        (Real.continuous_sqrt.measurable.comp_aemeasurable' (hmeas_d_pn n))).pow_const
        2)).aestronglyMeasurable
    have hfin : (∫⁻ u : U, ENNReal.ofReal
        ((Real.sqrt (temperedDens beta m Gammaih LG (Dn n) u) -
          Real.sqrt (temperedDens beta m Gammaih LG D u)) ^ 2)
        ∂(Ptheta (Dn n) theta)) ≠ ⊤ := by
      have hpt : ∀ u : U, ENNReal.ofReal
          ((Real.sqrt (temperedDens beta m Gammaih LG (Dn n) u) -
            Real.sqrt (temperedDens beta m Gammaih LG D u)) ^ 2)
            ≤ ENNReal.ofReal 2 * (ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) u) +
                ENNReal.ofReal (temperedDens beta m Gammaih LG D u)) := by
        intro u
        have h1 : (0 : ℝ) ≤ temperedDens beta m Gammaih LG (Dn n) u := (Real.exp_pos _).le
        have h2 : (0 : ℝ) ≤ temperedDens beta m Gammaih LG D u := (Real.exp_pos _).le
        have heq : ENNReal.ofReal
            (2 * (temperedDens beta m Gammaih LG (Dn n) u +
              temperedDens beta m Gammaih LG D u))
            = ENNReal.ofReal 2 *
                (ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) u) +
                  ENNReal.ofReal (temperedDens beta m Gammaih LG D u)) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_add h1 h2]
        rw [← heq]
        exact ENNReal.ofReal_le_ofReal (hW_alg _ _ h1 h2)
      have hstep : (∫⁻ u : U, ENNReal.ofReal
          ((Real.sqrt (temperedDens beta m Gammaih LG (Dn n) u) -
            Real.sqrt (temperedDens beta m Gammaih LG D u)) ^ 2) ∂(Ptheta (Dn n) theta))
          ≤ ∫⁻ u : U, ENNReal.ofReal 2 *
              (ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) u) +
                ENNReal.ofReal (temperedDens beta m Gammaih LG D u))
              ∂(Ptheta (Dn n) theta) :=
        MeasureTheory.lintegral_mono_ae (Filter.Eventually.of_forall hpt)
      have hsplit : (∫⁻ u : U, ENNReal.ofReal 2 *
            (ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) u) +
              ENNReal.ofReal (temperedDens beta m Gammaih LG D u))
            ∂(Ptheta (Dn n) theta))
          = ENNReal.ofReal 2 *
            ((∫⁻ u : U, ENNReal.ofReal (temperedDens beta m Gammaih LG (Dn n) u)
                ∂(Ptheta (Dn n) theta)) +
              ∫⁻ u : U, ENNReal.ofReal (temperedDens beta m Gammaih LG D u)
                ∂(Ptheta (Dn n) theta)) := by
        rw [MeasureTheory.lintegral_const_mul'' (ENNReal.ofReal 2) (hAEM1.add hAEM2),
          MeasureTheory.lintegral_add_left' hAEM1
            (fun u : U => ENNReal.ofReal (temperedDens beta m Gammaih LG D u))]
      rw [hsplit] at hstep
      exact ne_of_lt (lt_of_le_of_lt hstep (ENNReal.mul_lt_top
        (lt_top_iff_ne_top.mpr ENNReal.top_ne_ofReal.symm)
        (ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr (hLn_ne_top n),
          lt_top_iff_ne_top.mpr (hLin_f_pn n)⟩)))
    exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hw_aesm
      (Filter.Eventually.of_forall (fun u => sq_nonneg _))).mp hfin


  have hMid_eq : ∀ n : ℕ,
      (∫⁻ u : U, rho n u * ENNReal.ofReal
          ((Real.sqrt (AEMeasurable.mk
                (fun v : U => temperedDens beta m Gammaih LG (Dn n) v) (hmeas_fn n) u) -
              Real.sqrt (AEMeasurable.mk
                (fun v : U => temperedDens beta m Gammaih LG D v) hmeas_f u)) ^ 2)
          ∂(Ptheta D theta))
        = ∫⁻ u : U, ENNReal.ofReal
            ((Real.sqrt (temperedDens beta m Gammaih LG (Dn n) u) -
              Real.sqrt (temperedDens beta m Gammaih LG D u)) ^ 2)
            ∂(Ptheta (Dn n) theta) := by
    intro n
    have hXmeas : Measurable (fun u : U => ENNReal.ofReal
        ((Real.sqrt (AEMeasurable.mk
              (fun v : U => temperedDens beta m Gammaih LG (Dn n) v) (hmeas_fn n) u) -
            Real.sqrt (AEMeasurable.mk
              (fun v : U => temperedDens beta m Gammaih LG D v) hmeas_f u)) ^ 2)) :=
      ENNReal.measurable_ofReal.comp
        (((Real.continuous_sqrt.measurable.comp (hmeas_mk_pn n)).sub
          (Real.continuous_sqrt.measurable.comp hmeas_mk_f)).pow_const 2)
    have hcongr : (∫⁻ u : U, ENNReal.ofReal
        ((Real.sqrt (AEMeasurable.mk
              (fun v : U => temperedDens beta m Gammaih LG (Dn n) v) (hmeas_fn n) u) -
            Real.sqrt (AEMeasurable.mk
              (fun v : U => temperedDens beta m Gammaih LG D v) hmeas_f u)) ^ 2)
        ∂(Ptheta (Dn n) theta))
        = ∫⁻ u : U, ENNReal.ofReal
            ((Real.sqrt (temperedDens beta m Gammaih LG (Dn n) u) -
              Real.sqrt (temperedDens beta m Gammaih LG D u)) ^ 2)
            ∂(Ptheta (Dn n) theta) := by
      refine le_antisymm ?_ ?_
      · refine MeasureTheory.lintegral_mono_ae ?_
        filter_upwards [MeasureTheory.Measure.AbsolutelyContinuous.ae_eq (hrho_ac n)
            (hmeas_fn n).ae_eq_mk,
          MeasureTheory.Measure.AbsolutelyContinuous.ae_eq (hrho_ac n) hmeas_f.ae_eq_mk]
          with u h1 h2
        rw [← h1, ← h2]
      · refine MeasureTheory.lintegral_mono_ae ?_
        filter_upwards [MeasureTheory.Measure.AbsolutelyContinuous.ae_eq (hrho_ac n)
            (hmeas_fn n).ae_eq_mk,
          MeasureTheory.Measure.AbsolutelyContinuous.ae_eq (hrho_ac n) hmeas_f.ae_eq_mk]
          with u h1 h2
        rw [← h1, ← h2]
    have hstep := MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀
      (μ := Ptheta D theta) (f := rho n)
      (g := fun u : U => ENNReal.ofReal
        ((Real.sqrt (AEMeasurable.mk
              (fun v : U => temperedDens beta m Gammaih LG (Dn n) v) (hmeas_fn n) u) -
            Real.sqrt (AEMeasurable.mk
              (fun v : U => temperedDens beta m Gammaih LG D v) hmeas_f u)) ^ 2))
      (hrho_aemeas n) hXmeas.aemeasurable
    rw [← hrho_dens n] at hstep
    exact hstep.symm.trans hcongr
  have hMid_actual : ∀ n : ℕ,
      (∫⁻ u : U, rho n u * ENNReal.ofReal
          ((Real.sqrt (temperedDens beta m Gammaih LG (Dn n) u) -
            Real.sqrt (temperedDens beta m Gammaih LG D u)) ^ 2)
          ∂(Ptheta D theta))
        = ∫⁻ u : U, rho n u * ENNReal.ofReal
            ((Real.sqrt (AEMeasurable.mk
                  (fun v : U => temperedDens beta m Gammaih LG (Dn n) v) (hmeas_fn n) u) -
                Real.sqrt (AEMeasurable.mk
                  (fun v : U => temperedDens beta m Gammaih LG D v) hmeas_f u)) ^ 2)
            ∂(Ptheta D theta) := by
    intro n
    refine le_antisymm ?_ ?_
    · refine MeasureTheory.lintegral_mono_ae ?_
      filter_upwards [(hmeas_fn n).ae_eq_mk, hmeas_f.ae_eq_mk] with u h1 h2
      rw [← h1, ← h2]
    · refine MeasureTheory.lintegral_mono_ae ?_
      filter_upwards [(hmeas_fn n).ae_eq_mk, hmeas_f.ae_eq_mk] with u h1 h2
      rw [← h1, ← h2]
  have hT3 : Tendsto (fun n : ℕ =>
      (∫⁻ u : U, rho n u * ENNReal.ofReal
        ((Real.sqrt (temperedDens beta m Gammaih LG (Dn n) u) -
          Real.sqrt (temperedDens beta m Gammaih LG D u)) ^ 2)
        ∂(Ptheta D theta)).toReal) atTop (𝓝 0) := by
    have hcongr : (fun n : ℕ =>
        (∫⁻ u : U, rho n u * ENNReal.ofReal
          ((Real.sqrt (temperedDens beta m Gammaih LG (Dn n) u) -
            Real.sqrt (temperedDens beta m Gammaih LG D u)) ^ 2)
          ∂(Ptheta D theta)).toReal)
        = (fun n : ℕ => ∫ u : U,
            (Real.sqrt (temperedDens beta m Gammaih LG (Dn n) u) -
              Real.sqrt (temperedDens beta m Gammaih LG D u)) ^ 2
            ∂(Ptheta (Dn n) theta)) := by
      funext n
      rw [hMid_actual n, hMid_eq n]
      have h := MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hW_int n)
        (Filter.Eventually.of_forall (fun u => sq_nonneg _))
      rw [← h, ENNReal.toReal_ofReal (MeasureTheory.integral_nonneg
        (fun u => sq_nonneg _))]
    rw [hcongr]
    exact hsqrt_Pn
  have hofReal_tendsto : ∀ (I : ℕ → ℝ), (∀ n : ℕ, 0 ≤ I n) → Tendsto I atTop (𝓝 0) →
      Tendsto (fun n : ℕ => ENNReal.ofReal (I n)) atTop (𝓝 0) := by
    intro I hnn hI
    refine tendsto_order.2 ⟨fun b hb => absurd hb (not_lt.mpr (zero_le b)), ?_⟩
    intro b hb
    rcases eq_or_ne b ⊤ with hbT | hbT
    · rw [hbT]
      exact Filter.Eventually.of_forall
        (fun n => lt_top_iff_ne_top.mpr ENNReal.top_ne_ofReal.symm)
    · have hbpos : 0 < b.toReal := ENNReal.toReal_pos (ne_of_gt hb) hbT
      have hmem : Set.Iio b.toReal ∈ 𝓝 (0 : ℝ) := isOpen_Iio.mem_nhds hbpos
      filter_upwards [hI.eventually hmem] with n hn
      have hgoal : ENNReal.ofReal (I n) < ENNReal.ofReal b.toReal := by
        refine lt_of_le_of_ne (ENNReal.ofReal_le_ofReal hn.le) ?_
        intro hEq
        have h2 : (ENNReal.ofReal (I n)).toReal = (ENNReal.ofReal b.toReal).toReal := by
          rw [hEq]
        rw [ENNReal.toReal_ofReal (hnn n), ENNReal.toReal_ofReal hbpos.le] at h2
        exact absurd h2 (ne_of_lt hn)
      rw [← ENNReal.ofReal_toReal hbT]
      exact hgoal
  have h3enn : Tendsto (fun n : ℕ =>
      ∫⁻ u : U, rho n u * ENNReal.ofReal
        ((Real.sqrt (temperedDens beta m Gammaih LG (Dn n) u) -
          Real.sqrt (temperedDens beta m Gammaih LG D u)) ^ 2)
        ∂(Ptheta D theta)) atTop (𝓝 0) := by
    have hcongr : (fun n : ℕ =>
        ∫⁻ u : U, rho n u * ENNReal.ofReal
          ((Real.sqrt (temperedDens beta m Gammaih LG (Dn n) u) -
            Real.sqrt (temperedDens beta m Gammaih LG D u)) ^ 2)
          ∂(Ptheta D theta))
        = (fun n : ℕ => ENNReal.ofReal (∫ u : U,
            (Real.sqrt (temperedDens beta m Gammaih LG (Dn n) u) -
              Real.sqrt (temperedDens beta m Gammaih LG D u)) ^ 2
            ∂(Ptheta (Dn n) theta))) := by
      funext n
      rw [hMid_actual n, hMid_eq n]
      exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hW_int n)
        (Filter.Eventually.of_forall (fun u => sq_nonneg _))).symm
    rw [hcongr]
    exact hofReal_tendsto (fun n : ℕ => ∫ u : U,
      (Real.sqrt (temperedDens beta m Gammaih LG (Dn n) u) -
        Real.sqrt (temperedDens beta m Gammaih LG D u)) ^ 2 ∂(Ptheta (Dn n) theta))
      (fun n => MeasureTheory.integral_nonneg (fun u => sq_nonneg _)) hsqrt_Pn
  have hg_int : ∀ n : ℕ, Integrable (fun u : U =>
      temperedDens beta m Gammaih LG D u * (Real.sqrt ((rho n u).toReal) - 1) ^ 2)
      (Ptheta D theta) := by
    intro n
    have hsqrt_meas : Measurable (fun u : U => Real.sqrt ((rho n u).toReal)) :=
      Real.continuous_sqrt.measurable.comp (hrho_meas n).ennreal_toReal
    have hmeas_g : AEMeasurable (fun u : U =>
        temperedDens beta m Gammaih LG D u * (Real.sqrt ((rho n u).toReal) - 1) ^ 2)
        (Ptheta D theta) :=
      hmeas_f.mul ((hsqrt_meas.sub (measurable_const : Measurable fun _ : U => (1 : ℝ))).pow_const 2).aemeasurable
    have hfin : (∫⁻ u : U, ENNReal.ofReal (temperedDens beta m Gammaih LG D u *
        (Real.sqrt ((rho n u).toReal) - 1) ^ 2) ∂(Ptheta D theta)) ≠ ⊤ := by
      have hpt : ∀ u : U, ENNReal.ofReal (temperedDens beta m Gammaih LG D u *
          (Real.sqrt ((rho n u).toReal) - 1) ^ 2)
          ≤ ENNReal.ofReal 2 *
              (rho n u * ENNReal.ofReal (temperedDens beta m Gammaih LG D u) +
                ENNReal.ofReal (temperedDens beta m Gammaih LG D u)) := by
        intro u
        have hf : (0 : ℝ) ≤ temperedDens beta m Gammaih LG D u := (Real.exp_pos _).le
        have hr : (0 : ℝ) ≤ (rho n u).toReal := ENNReal.toReal_nonneg
        have hb : (Real.sqrt ((rho n u).toReal) - 1) ^ 2 ≤ 2 * ((rho n u).toReal + 1) := by
          simpa using hW_alg ((rho n u).toReal) 1 hr (zero_le_one)
        have hmul1 := mul_le_mul_of_nonneg_left hb hf
        have hmul2 : temperedDens beta m Gammaih LG D u * (2 * ((rho n u).toReal + 1))
            = 2 * (temperedDens beta m Gammaih LG D u * (rho n u).toReal +
                temperedDens beta m Gammaih LG D u) := by ring
        have hmul : temperedDens beta m Gammaih LG D u *
            (Real.sqrt ((rho n u).toReal) - 1) ^ 2 ≤
            2 * (temperedDens beta m Gammaih LG D u * (rho n u).toReal +
              temperedDens beta m Gammaih LG D u) := hmul2 ▸ hmul1
        have hE2 : ENNReal.ofReal
            (2 * (temperedDens beta m Gammaih LG D u * (rho n u).toReal +
              temperedDens beta m Gammaih LG D u))
            = ENNReal.ofReal 2 *
                (ENNReal.ofReal (temperedDens beta m Gammaih LG D u * (rho n u).toReal) +
                  ENNReal.ofReal (temperedDens beta m Gammaih LG D u)) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ENNReal.ofReal_add (mul_nonneg hf hr) hf]
        have hprod : ENNReal.ofReal (temperedDens beta m Gammaih LG D u * (rho n u).toReal)
            ≤ rho n u * ENNReal.ofReal (temperedDens beta m Gammaih LG D u) := by
          rw [ENNReal.ofReal_mul hf]
          calc ENNReal.ofReal (temperedDens beta m Gammaih LG D u) *
                ENNReal.ofReal ((rho n u).toReal)
              ≤ ENNReal.ofReal (temperedDens beta m Gammaih LG D u) * rho n u :=
                mul_le_mul le_rfl ENNReal.ofReal_toReal_le (zero_le _) (zero_le _)
            _ = rho n u * ENNReal.ofReal (temperedDens beta m Gammaih LG D u) := mul_comm _ _
        calc ENNReal.ofReal (temperedDens beta m Gammaih LG D u *
              (Real.sqrt ((rho n u).toReal) - 1) ^ 2)
            ≤ ENNReal.ofReal (2 * (temperedDens beta m Gammaih LG D u * (rho n u).toReal +
                temperedDens beta m Gammaih LG D u)) := ENNReal.ofReal_le_ofReal hmul
          _ = ENNReal.ofReal 2 *
                (ENNReal.ofReal (temperedDens beta m Gammaih LG D u * (rho n u).toReal) +
                  ENNReal.ofReal (temperedDens beta m Gammaih LG D u)) := hE2
          _ ≤ ENNReal.ofReal 2 *
                (rho n u * ENNReal.ofReal (temperedDens beta m Gammaih LG D u) +
                  ENNReal.ofReal (temperedDens beta m Gammaih LG D u)) :=
              mul_le_mul le_rfl (add_le_add hprod le_rfl) (zero_le _) (zero_le _)
      have hstep : (∫⁻ u : U, ENNReal.ofReal (temperedDens beta m Gammaih LG D u *
          (Real.sqrt ((rho n u).toReal) - 1) ^ 2) ∂(Ptheta D theta))
          ≤ ∫⁻ u : U, ENNReal.ofReal 2 *
              (rho n u * ENNReal.ofReal (temperedDens beta m Gammaih LG D u) +
                ENNReal.ofReal (temperedDens beta m Gammaih LG D u))
              ∂(Ptheta D theta) :=
        MeasureTheory.lintegral_mono_ae (Filter.Eventually.of_forall hpt)
      have hsplit : (∫⁻ u : U, ENNReal.ofReal 2 *
            (rho n u * ENNReal.ofReal (temperedDens beta m Gammaih LG D u) +
              ENNReal.ofReal (temperedDens beta m Gammaih LG D u))
            ∂(Ptheta D theta))
          = ENNReal.ofReal 2 *
            ((∫⁻ u : U, rho n u * ENNReal.ofReal (temperedDens beta m Gammaih LG D u)
                ∂(Ptheta D theta)) +
              ∫⁻ u : U, ENNReal.ofReal (temperedDens beta m Gammaih LG D u)
                ∂(Ptheta D theta)) := by
        rw [MeasureTheory.lintegral_const_mul''
            (ENNReal.ofReal 2)
            (((hrho_aemeas n).mul hmeas_ofreal_f).add hmeas_ofreal_f),
          MeasureTheory.lintegral_add_left' ((hrho_aemeas n).mul hmeas_ofreal_f)
            (fun u : U => ENNReal.ofReal (temperedDens beta m Gammaih LG D u))]
      rw [hsplit] at hstep
      exact ne_of_lt (lt_of_le_of_lt hstep (ENNReal.mul_lt_top
        (lt_top_iff_ne_top.mpr ENNReal.top_ne_ofReal.symm)
        (ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr (hProd_base_ne_top n),
          lt_top_iff_ne_top.mpr hLin_ne_top⟩)))
    exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmeas_g.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun u => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)))).mp hfin
  have h2enn : Tendsto (fun n : ℕ => ∫⁻ u : U, ENNReal.ofReal
      (temperedDens beta m Gammaih LG D u * (Real.sqrt ((rho n u).toReal) - 1) ^ 2)
      ∂(Ptheta D theta)) atTop (𝓝 0) := by
    have hcongr : (fun n : ℕ => ∫⁻ u : U, ENNReal.ofReal
        (temperedDens beta m Gammaih LG D u * (Real.sqrt ((rho n u).toReal) - 1) ^ 2)
        ∂(Ptheta D theta))
        = (fun n : ℕ => ENNReal.ofReal (∫ u : U,
            temperedDens beta m Gammaih LG D u * (Real.sqrt ((rho n u).toReal) - 1) ^ 2
            ∂(Ptheta D theta))) := by
      funext n
      exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hg_int n)
        (Filter.Eventually.of_forall
          (fun u => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)))).symm
    rw [hcongr]
    exact hofReal_tendsto (fun n : ℕ => ∫ u : U,
      temperedDens beta m Gammaih LG D u * (Real.sqrt ((rho n u).toReal) - 1) ^ 2
      ∂(Ptheta D theta))
      (fun n => MeasureTheory.integral_nonneg
        (fun u => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))) hT3a
  have hI_eq : ∀ n : ℕ,
      (∫⁻ u : U, ENNReal.ofReal
          ((Real.sqrt ((ENNReal.ofReal ((Zm beta m Gammaih LG (Ptheta D theta) D)⁻¹ *
                AEMeasurable.mk (fun v : U => temperedDens beta m Gammaih LG D v)
                  hmeas_f u)).toReal) -
            Real.sqrt ((rho n u * (ENNReal.ofReal
                  (Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n))⁻¹ *
                ENNReal.ofReal
                  (AEMeasurable.mk (fun v : U => temperedDens beta m Gammaih LG (Dn n) v)
                    (hmeas_fn n) u))).toReal)) ^ 2) ∂(Ptheta D theta))
        = ∫⁻ u : U, ENNReal.ofReal
            ((((Real.sqrt (Zm beta m Gammaih LG (Ptheta D theta) D))⁻¹) *
                Real.sqrt (temperedDens beta m Gammaih LG D u) -
              Real.sqrt ((rho n u).toReal) *
                (((Real.sqrt (Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n)))⁻¹) *
                  Real.sqrt (temperedDens beta m Gammaih LG (Dn n) u))) ^ 2)
            ∂(Ptheta D theta) := by
    intro n
    refine le_antisymm ?_ ?_
    · refine MeasureTheory.lintegral_mono_ae ?_
      filter_upwards [hsqrt_g1, hsqrt_g2 n] with u h1 h2
      rw [h1, h2]
    · refine MeasureTheory.lintegral_mono_ae ?_
      filter_upwards [hsqrt_g1, hsqrt_g2 n] with u h1 h2
      rw [← h1, ← h2]
  simp only [hI_eq]
  haveI : IsProbabilityMeasure (Ptheta D theta) := hPtheta_isProb D theta
  exact statopia_math_node_1524419607_fd93d37d U (Ptheta D theta)
    (Zm beta m Gammaih LG (Ptheta D theta) D) hZ_pos
    (fun n : ℕ => Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n)) hZn_pos
    hinv_sqrt_tendsto hZn_lower rho hrho_meas
    (fun u : U => temperedDens beta m Gammaih LG D u)
    (fun (n : ℕ) (u : U) => temperedDens beta m Gammaih LG (Dn n) u)
    (fun u => (Real.exp_pos _).le) (fun n u => (Real.exp_pos _).le)
    hmeas_f hmeas_fn hZM.symm h2enn h3enn
  /- @proof-region region.target-node.session.45d7ff6a81eb7586 end -/

end Statlib.Imported
end

