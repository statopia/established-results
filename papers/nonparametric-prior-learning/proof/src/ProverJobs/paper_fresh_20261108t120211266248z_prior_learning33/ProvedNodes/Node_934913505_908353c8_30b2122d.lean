import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_1220214867_7bace56e_4839d7d8
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_2045408823_ad3ced10_a3540a44
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_2103907506_2297e1dc_fe47e4b0
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_2196947115_1f200b37_5f16393c
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_287562685_40351574_94646401
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3685606887_454ff366_3117069c
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3748965445_c602f3c6_80a972ef
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_4147388267_4d56357b_aae526a8
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_4260936017_8c420380_a93f429d
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_627162574_1890e6dd_1165f275
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_971375954_c360ad8c_83c54105

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
theorem statopia_math_node_934913505_908353c8 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
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
    (fm : (Fin m → X × H) → Theta1 → U)
    (Dn : ℕ → Fin m → X × H)
    (hS_scale : ∀ j : Fin m, HScale bH mu (alpha - s) ((S j).2))
    (hS_rad : ∀ j : Fin m, HScaleDist bH mu (alpha - s) ((S j).2) 0 ≤ ENNReal.ofReal r)
    (hDn_scale : ∀ (n : ℕ) (j : Fin m), HScale bH mu (alpha - s) ((Dn n j).2))
    (hDn_rad : ∀ (n : ℕ) (j : Fin m),
      HScaleDist bH mu (alpha - s) ((Dn n j).2) 0 ≤ ENNReal.ofReal r)
    (hDn_tendsto : Tendsto Dn atTop
      (dataNhds (fun z : H => (HScaleNorm bH mu (alpha - s) z) ^ (1 / 2 : ℝ))
        (HScale bH mu (alpha - s)) S))
    (hfm_cont : Tendsto (fun S' : Fin m → X × H =>
        UScaleDist e lam (1 + st) (fm S' theta.1) (fm S theta.1))
      (dataNhds (fun z : H => (HScaleNorm bH mu (alpha - s) z) ^ (1 / 2 : ℝ))
        (HScale bH mu (alpha - s)) S) (𝓝 0))
    (hsigma2_tendsto : Tendsto
      (fun n : ℕ => ∑' k : ℕ, (priorEigen lam Nc theta.2 k)⁻¹ *
        (inner ℝ (e k) (fm (Dn n) theta.1 - fm S theta.1)) ^ 2)
      atTop (𝓝 0))
    (hsigma2_summable : ∀ n : ℕ, Summable
      (fun k : ℕ => (priorEigen lam Nc theta.2 k)⁻¹ *
        (inner ℝ (e k) (fm (Dn n) theta.1 - fm S theta.1)) ^ 2))
    (Bbar : ℝ) (hBbar : 0 ≤ Bbar)
    (rho : ℕ → U → ℝ≥0∞) (hrho_meas : ∀ n : ℕ, Measurable (rho n))
    (hrho_dens : ∀ n : ℕ, Ptheta (Dn n) theta = (Ptheta S theta).withDensity (rho n))
    (hrhon_scale : ∀ n : ℕ, (Ptheta (Dn n) theta) (UScale e lam (1 - st)) = 1)
    (hmoment_rho : ∀ (n : ℕ) (q : ℝ), 0 < q →
      (∫⁻ u : U, ENNReal.rpow (rho n u) q ∂(Ptheta S theta))
        = ENNReal.ofReal (Real.exp (q * (q - 1) / 2 *
            (∑' k : ℕ, (priorEigen lam Nc theta.2 k)⁻¹ *
              (inner ℝ (e k) (fm (Dn n) theta.1 - fm S theta.1)) ^ 2))))
    (hrho_bound : ∀ n : ℕ, ∫⁻ u : U, (rho n u) ^ 2 ∂(Ptheta S theta) ≤ ENNReal.ofReal Bbar)
    (hdens_meas_all : ∀ D : Fin m → X × H,
      AEMeasurable (fun u : U => temperedDens beta m Gammaih LG D u) (Ptheta S theta)),
    Tendsto (fun n : ℕ => Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n))
        atTop (𝓝 (Zm beta m Gammaih LG (Ptheta S theta) S)) ∧
      0 < Zm beta m Gammaih LG (Ptheta S theta) S ∧
      (∀ n : ℕ, 0 < Zm beta m Gammaih LG (Ptheta (Dn n) theta) (Dn n)) ∧
      Tendsto (fun n : ℕ => ∫ u : U,
          (Real.sqrt (temperedDens beta m Gammaih LG (Dn n) u) -
            Real.sqrt (temperedDens beta m Gammaih LG S u)) ^ 2
          ∂(Ptheta (Dn n) theta)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => ∫ u : U,
          temperedDens beta m Gammaih LG S u *
            (Real.sqrt ((rho n u).toReal) - 1) ^ 2 ∂(Ptheta S theta)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => ∫ u : U,
          temperedDens beta m Gammaih LG (Dn n) u *
            (Real.sqrt ((rho n u).toReal) - 1) ^ 2 ∂(Ptheta S theta)) atTop (𝓝 0) := by
  /- @proof-region region.target-node.session.c038c5d2cfd484e7 begin -/
  intro U iU1 iU2 iU3 iU4 iU5 iU6 H iH1 iH2 iH3 iH4 iH5 iH6 X iX1 iX2 iX3 iX4 iX5
  intro e lam hlam_pos hlam_anti Gamma hGamma_pos hGamma_inj Gammah hGammah_symm hGammah_pos
    hGammah_sq Gammaih hGammaih_left
  intro iotaH iP1 bH mu hmu_pos hmu_anti C1 hC1_pos hC1_inj hC1_eigen LG s0 s1 s st alpha
  intro hs0_nonneg hs0_lt hs1_nonneg hs1_lt hs_gt hs_le hst_gt hst_le halpha C1c C2c hC1c hC2c
  intro M1 hM1_mono hM1_nonneg M2 hM2_nonneg hM2_mono_fst hM2_mono_snd hA1 hA2 hA3 hA4
    hLG_all_range
  intro beta hbeta m hm Nc hNc Theta1 iT1 iT2 iT3 iT4 iT5 Ptheta hPtheta_isProb theta S mubar
    hmubar kappa hkappa h6 h7 h8
  intro delta0 hdelta0 hmoment hdelta_meas hP_scale delta1 hdelta1 hdelta1_bound r hr
  intro fm Dn hS_scale hS_rad hDn_scale hDn_rad hDn_tendsto hfm_cont hsigma2_tendsto
    hsigma2_summable Bbar hBbar rho hrho_meas hrho_dens hrhon_scale hmoment_rho hrho_bound
    hdens_meas_all
  have hrho_ac : ∀ n : ℕ,
      Measure.AbsolutelyContinuous (Ptheta (Dn n) theta) (Ptheta S theta) := by
    intro n
    rw [hrho_dens n]
    exact MeasureTheory.withDensity_absolutelyContinuous (Ptheta S theta) (rho n)
  have hexp_sigma2 : Tendsto (fun n : ℕ =>
      Real.exp (∑' k : ℕ, (priorEigen lam Nc theta.2 k)⁻¹ *
        (inner ℝ (e k) (fm (Dn n) theta.1 - fm S theta.1)) ^ 2) - 1) atTop (𝓝 0) := by
    have h2 : Tendsto (fun n : ℕ =>
        Real.exp (∑' k : ℕ, (priorEigen lam Nc theta.2 k)⁻¹ *
          (inner ℝ (e k) (fm (Dn n) theta.1 - fm S theta.1)) ^ 2) - 1) atTop
        (𝓝 (Real.exp 0 - 1)) :=
      ((Real.continuous_exp.sub continuous_const).tendsto 0).comp hsigma2_tendsto
    simpa using h2
  have hrho_sq_tendsto : Tendsto (fun n : ℕ =>
      ∫⁻ u : U, ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) ∂(Ptheta S theta))
      atTop (𝓝 0) := by
    haveI : IsProbabilityMeasure (Ptheta S theta) := hPtheta_isProb S theta
    exact statopia_math_node_3685606887_454ff366 (U := U) (P := Ptheta S theta)
      (rho := rho)
      (s2 := fun n : ℕ => ∑' k : ℕ, (priorEigen lam Nc theta.2 k)⁻¹ *
        (inner ℝ (e k) (fm (Dn n) theta.1 - fm S theta.1)) ^ 2)
      hrho_meas
      (fun n => by
        have h := hmoment_rho n 2 two_pos
        have harg : (2 : ℝ) * (2 - 1) / 2 *
            (∑' k : ℕ, (priorEigen lam Nc theta.2 k)⁻¹ *
              (inner ℝ (e k) (fm (Dn n) theta.1 - fm S theta.1)) ^ 2) =
            (∑' k : ℕ, (priorEigen lam Nc theta.2 k)⁻¹ *
              (inner ℝ (e k) (fm (Dn n) theta.1 - fm S theta.1)) ^ 2) := by
          ring
        rw [harg] at h
        exact h)
      (fun n => by
        have h := hmoment_rho n 1 one_pos
        have harg : (1 : ℝ) * (1 - 1) / 2 *
            (∑' k : ℕ, (priorEigen lam Nc theta.2 k)⁻¹ *
              (inner ℝ (e k) (fm (Dn n) theta.1 - fm S theta.1)) ^ 2) = 0 := by
          ring
        rw [harg, Real.exp_zero, ENNReal.ofReal_one] at h
        exact h)
      hexp_sigma2
  have hdens_pos : ∀ (D : Fin m → X × H) (u : U), 0 < temperedDens beta m Gammaih LG D u :=
    fun D u => Real.exp_pos _
  have hdens_nonneg : ∀ (D : Fin m → X × H) (u : U), 0 ≤ temperedDens beta m Gammaih LG D u :=
    fun D u => (hdens_pos D u).le
  haveI hprobS : IsProbabilityMeasure (Ptheta S theta) := hPtheta_isProb S theta
  have hZm_eq : ∀ (D : Fin m → X × H) (Q : Measure U),
      Zm beta m Gammaih LG Q D = ∫ u : U, temperedDens beta m Gammaih LG D u ∂Q :=
    fun D Q => rfl
  have hΓih_zero : Gammaih 0 = 0 := by
    simpa using hGammaih_left 0
  have hPhi_zero_nonneg : ∀ (x : X) (u : U), 0 ≤ Phi Gammaih LG u x 0 := by
    intro x u
    simp only [Phi, hΓih_zero, inner_zero_left, sub_zero]
    positivity
  have hHScale_zero : ∀ t : ℝ, HScale bH mu t (0 : H) := by
    intro t
    show HScaleNorm bH mu t (0 : H) < ⊤
    have hzero : HScaleNorm bH mu t (0 : H) = 0 := by
      simp [HScaleNorm]
    rw [hzero]
    exact ENNReal.zero_lt_top
  have hdelta_int_S : ∀ delta : ℝ, 0 ≤ delta → delta < delta0 →
      Integrable ((UScale e lam (1 - st)).indicator
        (fun u : U =>
          Real.exp (delta * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2)))
        (Ptheta S theta) := by
    intro delta hd hdlt
    have hbase := hmoment delta hd hdlt
    have hf_nonneg : ∀ u : U,
        0 ≤ Real.exp (delta * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2) :=
      fun u => (Real.exp_pos _).le
    have hnonneg : ∀ u : U, 0 ≤ ((UScale e lam (1 - st)).indicator
        (fun v : U =>
          Real.exp (delta * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2))) u := by
      intro u
      classical
      by_cases hu : u ∈ UScale e lam (1 - st)
      · simpa [Set.indicator_apply, if_pos hu] using hf_nonneg u
      · simpa [Set.indicator_apply, if_neg hu]
    have hle : (∫⁻ u : U, ENNReal.ofReal (((UScale e lam (1 - st)).indicator
        (fun v : U =>
          Real.exp (delta * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2))) u)
        ∂(Ptheta S theta)) ≤
        ENNReal.ofReal (∫ u : U,
          Real.exp (delta * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2)
          ∂(Ptheta S theta)) := by
      rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hbase
        (Filter.Eventually.of_forall hf_nonneg)]
      refine lintegral_mono (fun u => ?_)
      have hpt : ((UScale e lam (1 - st)).indicator
          (fun v : U =>
            Real.exp (delta * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2))) u ≤
          Real.exp (delta * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2) := by
        classical
        by_cases hu : u ∈ UScale e lam (1 - st)
        · simpa [Set.indicator_apply, if_pos hu] using le_rfl
        · simpa [Set.indicator_apply, if_neg hu] using hf_nonneg u
      exact ENNReal.ofReal_le_ofReal hpt
    refine (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      (hdelta_meas delta).aestronglyMeasurable (Filter.Eventually.of_forall hnonneg)).1 ?_
    exact ne_of_lt (lt_of_le_of_lt hle (lt_of_le_of_ne le_top ENNReal.ofReal_ne_top))
  have hind_nonneg : ∀ (delta : ℝ), 0 ≤ delta → ∀ u : U,
      0 ≤ ((UScale e lam (1 - st)).indicator
        (fun v : U =>
          Real.exp (delta * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2))) u := by
    intro delta hd u
    classical
    by_cases hu : u ∈ UScale e lam (1 - st)
    · exact le_of_lt (by
        simpa [Set.indicator_apply, if_pos hu] using
          Real.exp_pos (delta * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2))
    · simpa [Set.indicator_apply, if_neg hu]
  have hdelta_int_Dn : ∀ (n : ℕ) (delta : ℝ), 0 ≤ delta → delta < delta0 / 2 →
      Integrable ((UScale e lam (1 - st)).indicator
        (fun u : U =>
          Real.exp (delta * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2)))
        (Ptheta (Dn n) theta) := by
    intro n delta hd hdlt
    have h2d0 : (0 : ℝ) ≤ 2 * delta := by linarith
    have h2d : 2 * delta < delta0 := by linarith
    have hW_sq_eq : ∀ u : U,
        (ENNReal.ofReal (((UScale e lam (1 - st)).indicator
          (fun v : U =>
            Real.exp (delta * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2))) u)) ^ 2
        = ENNReal.ofReal (((UScale e lam (1 - st)).indicator
          (fun v : U =>
            Real.exp ((2 * delta) * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)))
            u) := by
      intro u
      classical
      by_cases hu : u ∈ UScale e lam (1 - st)
      · have hxpos : 0 ≤ Real.exp
            (delta * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2) :=
          (Real.exp_pos _).le
        simp only [Set.indicator_apply, if_pos hu]
        rw [pow_two, ← ENNReal.ofReal_mul hxpos]
        congr 1
        rw [← Real.exp_add]
        congr 1
        ring
      · simp only [Set.indicator_apply, if_neg hu]
        simp
    have hW_sq_top : (∫⁻ u : U, (ENNReal.ofReal (((UScale e lam (1 - st)).indicator
        (fun v : U =>
          Real.exp (delta * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2))) u)) ^ 2
        ∂(Ptheta S theta)) < ⊤ := by
      simp only [hW_sq_eq]
      exact lt_top_iff_ne_top.2 ((MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
        (hdelta_meas (2 * delta)).aestronglyMeasurable
        (Filter.Eventually.of_forall (hind_nonneg (2 * delta) h2d0))).2
          (hdelta_int_S (2 * delta) h2d0 h2d))
    have hlt : (∫⁻ u : U, ENNReal.ofReal (((UScale e lam (1 - st)).indicator
        (fun v : U =>
          Real.exp (delta * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2))) u)
        ∂(Ptheta (Dn n) theta)) < ⊤ := by
      rw [hrho_dens n]
      have hW_aem : AEMeasurable (fun u : U => ENNReal.ofReal (((UScale e lam (1 - st)).indicator
          (fun v : U =>
            Real.exp (delta * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2))) u))
          (Ptheta S theta) := by
        simpa [Function.comp_def] using
          ENNReal.measurable_ofReal.comp_aemeasurable (hdelta_meas delta)
      exact statopia_math_node_971375954_c360ad8c (U := U) (P := Ptheta S theta)
        (rho := rho n)
        (W := fun u : U => ENNReal.ofReal (((UScale e lam (1 - st)).indicator
          (fun v : U =>
            Real.exp (delta * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2))) u))
        (hrho_meas n) hW_aem
        (lt_of_le_of_lt (hrho_bound n) (lt_of_le_of_ne le_top ENNReal.ofReal_ne_top))
        hW_sq_top
    refine (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      ((hdelta_meas delta).mono_ac (hrho_ac n)).aestronglyMeasurable
      (Filter.Eventually.of_forall (hind_nonneg delta hd))).1 ?_
    exact lt_top_iff_ne_top.1 hlt
  have hdens_meas_all_local : ∀ D : Fin m → X × H,
      AEMeasurable (fun u : U => temperedDens beta m Gammaih LG D u) (Ptheta S theta) :=
    hdens_meas_all
  have hUScale_meas : MeasurableSet (UScale e lam (1 - st)) := by
    have hterm : ∀ k : ℕ, Measurable (fun u : U =>
        ENNReal.ofReal (Real.rpow (lam k) (-(1 - st)) * (inner ℝ (e k) u) ^ 2)) := by
      intro k
      have hin : Measurable (fun u : U => inner ℝ (e k) u) :=
        (continuous_const.inner continuous_id).measurable
      exact ENNReal.measurable_ofReal.comp (measurable_const.mul (hin.pow_const 2))
    have hnorm_meas : Measurable (fun u : U => UScaleNorm e lam (1 - st) u) :=
      Measurable.ennreal_tsum hterm
    exact measurableSet_lt hnorm_meas measurable_const
  have hae_scale_S : ∀ᵐ u ∂(Ptheta S theta), u ∈ UScale e lam (1 - st) := by
    rw [MeasureTheory.ae_iff]
    have hcompl : (Ptheta S theta) (UScale e lam (1 - st))ᶜ = 0 := by
      rw [measure_compl hUScale_meas (by rw [hP_scale]; exact ENNReal.one_ne_top),
        measure_univ, hP_scale]
      simp
    exact hcompl
  have hae_scale_of : ∀ (Q : Measure U) [IsProbabilityMeasure Q],
      Q (UScale e lam (1 - st)) = 1 → ∀ᵐ u ∂Q, u ∈ UScale e lam (1 - st) := by
    intro Q hQprob hQ_scale
    rw [MeasureTheory.ae_iff]
    have hcompl : Q (UScale e lam (1 - st))ᶜ = 0 := by
      rw [measure_compl hUScale_meas (by rw [hQ_scale]; exact ENNReal.one_ne_top),
        measure_univ, hQ_scale]
      simp
    exact hcompl
  have hae_scale_Dn : ∀ n : ℕ, ∀ᵐ u ∂(Ptheta (Dn n) theta), u ∈ UScale e lam (1 - st) := by
    intro n
    haveI : IsProbabilityMeasure (Ptheta (Dn n) theta) := hPtheta_isProb (Dn n) theta
    exact hae_scale_of (Ptheta (Dn n) theta) (hrhon_scale n)
  have hEmaj_aem : AEMeasurable (fun u : U =>
      ((UScale e lam (1 - st)).indicator
        (fun v : U => Real.exp (1 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
          delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)))) u)
      (Ptheta S theta) := by
    have heq : (fun u : U =>
        ((UScale e lam (1 - st)).indicator
          (fun v : U => Real.exp (1 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
            delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)))) u)
        = fun u : U => Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1)) *
            ((UScale e lam (1 - st)).indicator
              (fun v : U =>
                Real.exp (delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)))
              u := by
      funext u
      classical
      by_cases hu : u ∈ UScale e lam (1 - st)
      · simp only [Set.indicator_apply, if_pos hu, one_mul]
        rw [Real.exp_add]
      · simp only [Set.indicator_apply, if_neg hu, mul_zero]
    rw [heq]
    exact (hdelta_meas delta1).const_mul _

  have hEmaj_lt_top : ∀ (Q : Measure U) [IsProbabilityMeasure Q],
      (∀ delta : ℝ, 0 ≤ delta → delta < delta0 / 2 →
        Integrable ((UScale e lam (1 - st)).indicator
          (fun u : U =>
            Real.exp (delta * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2))) Q) →
      (∫⁻ u : U,
        ENNReal.ofReal (Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1))) *
        ENNReal.ofReal (((UScale e lam (1 - st)).indicator
          (fun v : U =>
            Real.exp (delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2))) u)
        ∂Q) < ⊤ := by
    intro Q hQprob hQ_int
    rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine ENNReal.mul_lt_top (lt_of_le_of_ne le_top ENNReal.ofReal_ne_top) ?_
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (hQ_int delta1 hdelta1.le (by linarith))
      (Filter.Eventually.of_forall (hind_nonneg delta1 hdelta1.le))]
    exact lt_of_le_of_ne le_top ENNReal.ofReal_ne_top
  have hEmaj_nonneg : ∀ u : U, 0 ≤ ((UScale e lam (1 - st)).indicator
      (fun v : U => Real.exp (1 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
        delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)))) u := by
    intro u
    classical
    by_cases hu : u ∈ UScale e lam (1 - st)
    · simp only [Set.indicator_apply, if_pos hu]
      exact (Real.exp_pos _).le
    · simp only [Set.indicator_apply, if_neg hu]
      exact le_rfl
  have hEmaj_lintegral_lt_top : (∫⁻ u : U, ENNReal.ofReal (((UScale e lam (1 - st)).indicator
      (fun v : U => Real.exp (1 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
        delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)))) u)
      ∂(Ptheta S theta)) < ⊤ := by
    have hpt : ∀ u : U, ENNReal.ofReal (((UScale e lam (1 - st)).indicator
        (fun v : U => Real.exp (1 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
          delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)))) u)
        = ENNReal.ofReal (Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1))) *
            ENNReal.ofReal (((UScale e lam (1 - st)).indicator
              (fun v : U =>
                Real.exp (delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)))
              u) := by
      intro u
      classical
      by_cases hu : u ∈ UScale e lam (1 - st)
      · simp only [Set.indicator_apply, if_pos hu, one_mul]
        rw [← ENNReal.ofReal_mul (Real.exp_pos ((beta * kappa * r) ^ 2 / (4 * delta1))).le]
        congr 1
        rw [Real.exp_add]
      · simp only [Set.indicator_apply, if_neg hu]
        simp
    simp only [hpt]
    exact hEmaj_lt_top (Ptheta S theta) (fun delta hd hlt => hdelta_int_S delta hd (by linarith))
  have hEmaj_sq_lt_top : (∫⁻ u : U, ENNReal.ofReal ((((UScale e lam (1 - st)).indicator
      (fun v : U => Real.exp (1 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
        delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)))) u) ^ 2)
      ∂(Ptheta S theta)) < ⊤ := by
    have h2nn : (0 : ℝ) ≤ 2 * delta1 := by linarith
    have h2lt : 2 * delta1 < delta0 := by linarith
    have hpt : ∀ u : U, ENNReal.ofReal ((((UScale e lam (1 - st)).indicator
        (fun v : U => Real.exp (1 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
          delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)))) u) ^ 2)
        ≤ ENNReal.ofReal (Real.exp (2 * ((beta * kappa * r) ^ 2 / (4 * delta1)))) *
            ENNReal.ofReal (((UScale e lam (1 - st)).indicator
              (fun v : U => Real.exp ((2 * delta1) *
                (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2))) u) := by
      intro u
      classical
      by_cases hu : u ∈ UScale e lam (1 - st)
      · have hreal : (Real.exp (1 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
              delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2))) ^ 2
            ≤ Real.exp (2 * ((beta * kappa * r) ^ 2 / (4 * delta1))) *
              Real.exp ((2 * delta1) *
                (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2) := by
          have e1 : Real.exp (1 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
                delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2))
              = Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1)) *
                Real.exp (delta1 *
                  (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2) := by
            rw [one_mul, Real.exp_add]
          have e2 : Real.exp (2 * ((beta * kappa * r) ^ 2 / (4 * delta1)))
              = Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1)) *
                Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1)) := by
            rw [show 2 * ((beta * kappa * r) ^ 2 / (4 * delta1))
                = (beta * kappa * r) ^ 2 / (4 * delta1) +
                  (beta * kappa * r) ^ 2 / (4 * delta1) by ring, Real.exp_add]
          have e3 : Real.exp ((2 * delta1) *
                (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2)
              = Real.exp (delta1 *
                  (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2) *
                Real.exp (delta1 *
                  (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2) := by
            rw [show (2 * delta1) *
                  (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2
                = delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2 +
                  delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2 by ring,
              Real.exp_add]
          rw [e1, e2, e3]
          exact le_of_eq (by ring)
        simp only [Set.indicator_apply, if_pos hu]
        refine le_trans (ENNReal.ofReal_le_ofReal hreal) (le_of_eq ?_)
        rw [← ENNReal.ofReal_mul
          (Real.exp_pos (2 * ((beta * kappa * r) ^ 2 / (4 * delta1)))).le]
      · have hz : ((UScale e lam (1 - st)).indicator
            (fun v : U => Real.exp (1 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
              delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)))) u = 0 := by
          simp only [Set.indicator_apply, if_neg hu]
        have hz2 : ((UScale e lam (1 - st)).indicator
            (fun v : U => Real.exp ((2 * delta1) *
              (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2))) u = 0 := by
          simp only [Set.indicator_apply, if_neg hu]
        rw [hz, hz2]
        simp
    refine lt_of_le_of_lt (lintegral_mono hpt) ?_
    rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine ENNReal.mul_lt_top (lt_of_le_of_ne le_top ENNReal.ofReal_ne_top) ?_
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (hdelta_int_S (2 * delta1) h2nn h2lt)
      (Filter.Eventually.of_forall (hind_nonneg (2 * delta1) h2nn))]
    exact lt_of_le_of_ne le_top ENNReal.ofReal_ne_top

  have hpotSum_lower_gen : ∀ (D : Fin m → X × H),
      (∀ j : Fin m, HScale bH mu (alpha - s) (D j).2) →
      (∀ j : Fin m, HScaleDist bH mu (alpha - s) (D j).2 0 ≤ ENNReal.ofReal r) →
      ∀ u : U, UScale e lam (1 - st) u →
        potSum Gammaih LG D u ≥
          - ((m : ℝ) * kappa * r * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) := by
    intro D hDsc hDrd u hu
    have hstep : ∀ j : Fin m, Phi Gammaih LG u (D j).1 (D j).2 ≥
        - (kappa * r * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) := by
      intro j
      have h6j := h6 (D j).1 (D j).1 (D j).2 0 (hDsc j)
        (hHScale_zero (alpha - s)) u hu
      have hzeroj : 0 ≤ Phi Gammaih LG u (D j).1 0 := hPhi_zero_nonneg (D j).1 u
      have hBnn : (0 : ℝ) ≤ M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) :=
        hM1_nonneg _
      have hdist : ENNReal.toReal (HScaleDist bH mu (alpha - s) (D j).2 0) ≤ r :=
        le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hDrd j))
          (by rw [ENNReal.toReal_ofReal hr])
      have hle1 : kappa * ENNReal.toReal (HScaleDist bH mu (alpha - s) (D j).2 0) *
            M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) ≤
          kappa * r * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdist hkappa) hBnn
      have hneg := neg_abs_le
        (Phi Gammaih LG u (D j).1 (D j).2 - Phi Gammaih LG u (D j).1 0)
      linarith
    have hsum : (∑ _j : Fin m,
          - (kappa * r * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)))) ≤
        potSum Gammaih LG D u := by
      rw [potSum]
      exact Finset.sum_le_sum (fun j _ => hstep j)
    have hconst : - ((m : ℝ) * kappa * r *
          M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) =
        ∑ _j : Fin m,
          - (kappa * r * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    linarith
  have hpot_upper_gen : ∀ (D : Fin m → X × H),
      (∀ j : Fin m, HScale bH mu (alpha - s) (D j).2) →
      (∀ j : Fin m, HScaleDist bH mu (alpha - s) (D j).2 0 ≤ ENNReal.ofReal r) →
      ∀ u : U, UScale e lam (1 - st) u →
        temperedDens beta m Gammaih LG D u ≤
          Real.exp (1 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
            delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2)) := by
    intro D hDsc hDrd u hu
    have hpot_low := hpotSum_lower_gen D hDsc hDrd u hu
    have hkey : (beta * kappa * r) *
          M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) ≤
        (beta * kappa * r) ^ 2 / (4 * delta1) +
          delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2 := by
      have hA : (beta * kappa * r) ^ 2 / (4 * delta1) * (4 * delta1) = (beta * kappa * r) ^ 2 :=
        div_mul_cancel₀ _ (ne_of_gt (by positivity : (0 : ℝ) < 4 * delta1))
      nlinarith [sq_nonneg ((beta * kappa * r) -
        2 * delta1 * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))), hA, hdelta1]
    have hexp1 : -(beta / (m : ℝ)) * potSum Gammaih LG D u ≤
        (beta * kappa * r) * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := by
      have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
      have hcoef : -(beta / (m : ℝ)) ≤ 0 := by
        have hpos : (0 : ℝ) < beta / (m : ℝ) := div_pos hbeta hmpos
        linarith
      have h1 : -(beta / (m : ℝ)) * potSum Gammaih LG D u ≤
          -(beta / (m : ℝ)) * (-((m : ℝ) * kappa * r *
            M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)))) :=
        mul_le_mul_of_nonpos_left hpot_low hcoef
      refine le_trans h1 (le_of_eq ?_)
      calc -(beta / (m : ℝ)) * (-((m : ℝ) * kappa * r *
              M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))))
          = (beta / (m : ℝ) * (m : ℝ)) *
              (kappa * r * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) := by ring
        _ = beta * (kappa * r * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) := by
            rw [div_mul_cancel₀ _ hmne]
        _ = (beta * kappa * r) * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := by ring
    simp only [temperedDens, one_mul]
    rw [Real.exp_le_exp]
    linarith
  have hpotSum_lower_S : ∀ u : U, UScale e lam (1 - st) u →
      potSum Gammaih LG S u ≥
        - ((m : ℝ) * kappa * r * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) :=
    fun u hu => hpotSum_lower_gen S hS_scale hS_rad u hu
  have hfs_sq_lt_top :
      (∫⁻ u : U, ENNReal.ofReal (temperedDens beta m Gammaih LG S u ^ 2)
        ∂(Ptheta S theta)) < ⊤ := by
    have hmaj_top : (∫⁻ u : U,
        ENNReal.ofReal (Real.exp ((beta * kappa * r) ^ 2 / delta1)) *
        ENNReal.ofReal (((UScale e lam (1 - st)).indicator
          (fun v : U =>
            Real.exp (delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2))) u)
        ∂(Ptheta S theta)) < ⊤ := by
      rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine ENNReal.mul_lt_top (lt_of_le_of_ne le_top ENNReal.ofReal_ne_top) ?_
      exact lt_top_iff_ne_top.2 ((MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
        (hdelta_meas delta1).aestronglyMeasurable
        (Filter.Eventually.of_forall (hind_nonneg delta1 hdelta1.le))).2
          (hdelta_int_S delta1 hdelta1.le (by linarith)))
    refine lt_of_le_of_lt ?_ hmaj_top
    refine lintegral_mono_ae ?_
    filter_upwards [hae_scale_S] with u hu
    have hind : ((UScale e lam (1 - st)).indicator
        (fun v : U =>
          Real.exp (delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2))) u =
        Real.exp (delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2) := by
      rw [Set.indicator_of_mem hu]
    rw [hind, ← ENNReal.ofReal_mul (Real.exp_pos ((beta * kappa * r) ^ 2 / delta1)).le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hkey : 2 * ((beta * kappa * r) *
          M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ≤
        (beta * kappa * r) ^ 2 / delta1 +
          delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2 := by
      have hA2 : (beta * kappa * r) ^ 2 / delta1 * delta1 = (beta * kappa * r) ^ 2 :=
        div_mul_cancel₀ _ hdelta1.ne'
      nlinarith [sq_nonneg ((beta * kappa * r) -
        delta1 * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))), hA2, hdelta1]
    have hexp1 : -(beta / (m : ℝ)) * potSum Gammaih LG S u ≤
        (beta * kappa * r) * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := by
      have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
      have hlow := hpotSum_lower_S u hu
      have hcoef : -(beta / (m : ℝ)) ≤ 0 := by
        have hpos : (0 : ℝ) < beta / (m : ℝ) := div_pos hbeta hmpos
        linarith
      have h1 : -(beta / (m : ℝ)) * potSum Gammaih LG S u ≤
          -(beta / (m : ℝ)) * (-((m : ℝ) * kappa * r *
            M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)))) :=
        mul_le_mul_of_nonpos_left hlow hcoef
      refine le_trans h1 (le_of_eq ?_)
      calc -(beta / (m : ℝ)) * (-((m : ℝ) * kappa * r *
              M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))))
          = (beta / (m : ℝ) * (m : ℝ)) *
              (kappa * r * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) := by ring
        _ = beta * (kappa * r *
              M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) := by
            rw [div_mul_cancel₀ _ hmne]
        _ = (beta * kappa * r) *
              M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := by ring
    have hf2 : temperedDens beta m Gammaih LG S u ^ 2 =
        Real.exp (-(beta / (m : ℝ)) * potSum Gammaih LG S u +
          (-(beta / (m : ℝ)) * potSum Gammaih LG S u)) := by
      simp only [temperedDens, pow_two, ← Real.exp_add]
    rw [hf2, ← Real.exp_add, Real.exp_le_exp]
    linarith
  have hZm_pos_gen : ∀ (D : Fin m → X × H) (Q : Measure U) [IsProbabilityMeasure Q],
      Q (UScale e lam (1 - st)) = 1 →
      (∀ delta : ℝ, 0 ≤ delta → delta < delta0 / 2 →
        Integrable ((UScale e lam (1 - st)).indicator
          (fun u : U =>
            Real.exp (delta * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2))) Q) →
      (∀ j : Fin m, HScale bH mu (alpha - s) (D j).2) →
      (∀ j : Fin m, HScaleDist bH mu (alpha - s) (D j).2 0 ≤ ENNReal.ofReal r) →
      AEMeasurable (fun u : U => temperedDens beta m Gammaih LG D u) Q →
      0 < Zm beta m Gammaih LG Q D := by
    intro D Q hQprob hQ_scale hQ_int hD_scale hD_rad hdens_meas
    have hae_scale_Q : ∀ᵐ u ∂Q, u ∈ UScale e lam (1 - st) := hae_scale_of Q hQ_scale
    have hpot_low : ∀ u : U, UScale e lam (1 - st) u →
        potSum Gammaih LG D u ≥
          - ((m : ℝ) * kappa * r * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) := by
      intro u hu
      have hstep : ∀ j : Fin m, Phi Gammaih LG u (D j).1 (D j).2 ≥
          - (kappa * r * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) := by
        intro j
        have h6j := h6 (D j).1 (D j).1 (D j).2 0 (hD_scale j)
          (hHScale_zero (alpha - s)) u hu
        have hzeroj : 0 ≤ Phi Gammaih LG u (D j).1 0 := hPhi_zero_nonneg (D j).1 u
        have hBnn : (0 : ℝ) ≤ M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) :=
          hM1_nonneg _
        have hdist : ENNReal.toReal (HScaleDist bH mu (alpha - s) (D j).2 0) ≤ r :=
          le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hD_rad j))
            (by rw [ENNReal.toReal_ofReal hr])
        have hle1 : kappa * ENNReal.toReal (HScaleDist bH mu (alpha - s) (D j).2 0) *
              M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) ≤
            kappa * r * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdist hkappa) hBnn
        have hneg := neg_abs_le
          (Phi Gammaih LG u (D j).1 (D j).2 - Phi Gammaih LG u (D j).1 0)
        linarith
      have hsum : (∑ _j : Fin m,
            - (kappa * r * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)))) ≤
          potSum Gammaih LG D u := by
        rw [potSum]
        exact Finset.sum_le_sum (fun j _ => hstep j)
      have hconst : - ((m : ℝ) * kappa * r *
            M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) =
          ∑ _j : Fin m,
            - (kappa * r * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      linarith
    have hdens_le : ∀ u : U, UScale e lam (1 - st) u →
        temperedDens beta m Gammaih LG D u ≤
          Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1)) *
            Real.exp (delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2) := by
      intro u hu
      have hkey : (beta * kappa * r) *
            M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) ≤
          (beta * kappa * r) ^ 2 / (4 * delta1) +
            delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2 := by
        have hA : (beta * kappa * r) ^ 2 / (4 * delta1) * (4 * delta1) = (beta * kappa * r) ^ 2 :=
          div_mul_cancel₀ _ (ne_of_gt (by positivity : (0 : ℝ) < 4 * delta1))
        nlinarith [sq_nonneg ((beta * kappa * r) -
          2 * delta1 * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))), hA, hdelta1]
      have hexp1 : -(beta / (m : ℝ)) * potSum Gammaih LG D u ≤
          (beta * kappa * r) * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := by
        have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
        have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
        have hlow := hpot_low u hu
        have hcoef : -(beta / (m : ℝ)) ≤ 0 := by
          have hpos : (0 : ℝ) < beta / (m : ℝ) := div_pos hbeta hmpos
          linarith
        have h1 : -(beta / (m : ℝ)) * potSum Gammaih LG D u ≤
            -(beta / (m : ℝ)) * (-((m : ℝ) * kappa * r *
              M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)))) :=
          mul_le_mul_of_nonpos_left hlow hcoef
        refine le_trans h1 (le_of_eq ?_)
        calc -(beta / (m : ℝ)) * (-((m : ℝ) * kappa * r *
                M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))))
            = (beta / (m : ℝ) * (m : ℝ)) *
                (kappa * r * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) := by ring
          _ = beta * (kappa * r *
                M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) := by
              rw [div_mul_cancel₀ _ hmne]
          _ = (beta * kappa * r) *
                M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := by ring
      simp only [temperedDens]
      rw [← Real.exp_add, Real.exp_le_exp]
      linarith
    have hlint_lt : (∫⁻ u : U, ENNReal.ofReal (temperedDens beta m Gammaih LG D u) ∂Q) < ⊤ := by
      have hmaj_top : (∫⁻ u : U,
          ENNReal.ofReal (Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1))) *
          ENNReal.ofReal (((UScale e lam (1 - st)).indicator
            (fun v : U =>
              Real.exp (delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2))) u)
          ∂Q) < ⊤ :=
        hEmaj_lt_top Q hQ_int
      refine lt_of_le_of_lt ?_ hmaj_top
      refine lintegral_mono_ae ?_
      filter_upwards [hae_scale_Q] with u hu
      have hind : ((UScale e lam (1 - st)).indicator
          (fun v : U =>
            Real.exp (delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2))) u =
          Real.exp (delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2) := by
        rw [Set.indicator_of_mem hu]
      rw [hind, ← ENNReal.ofReal_mul
        (Real.exp_pos ((beta * kappa * r) ^ 2 / (4 * delta1))).le]
      exact ENNReal.ofReal_le_ofReal (hdens_le u hu)
    have hInt : Integrable (fun u : U => temperedDens beta m Gammaih LG D u) Q :=
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hdens_meas.aestronglyMeasurable
        (Filter.Eventually.of_forall (hdens_nonneg D))).1 (ne_of_lt hlint_lt)
    have hsupp : Function.support (fun u : U => temperedDens beta m Gammaih LG D u) = Set.univ := by
      ext u
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact ne_of_gt (hdens_pos D u)
    rw [hZm_eq D Q]
    refine (MeasureTheory.integral_pos_iff_support_of_nonneg (hdens_nonneg D) hInt).2 ?_
    rw [hsupp, measure_univ]
    exact zero_lt_one
  have hEmaj_int : Integrable (fun u : U => ((UScale e lam (1 - st)).indicator
      (fun v : U => Real.exp (1 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
        delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)))) u)
      (Ptheta S theta) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hEmaj_aem.aestronglyMeasurable
      (Filter.Eventually.of_forall hEmaj_nonneg)).1 (ne_of_lt hEmaj_lintegral_lt_top)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · let E : U → ℝ := fun u : U => ((UScale e lam (1 - st)).indicator
        (fun v : U => Real.exp (1 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
          delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)))) u
    have hE_nonneg : ∀ u : U, 0 ≤ E u := hEmaj_nonneg
    have hE_meas : AEMeasurable E (Ptheta S theta) := hEmaj_aem
    have hE_int : Integrable E (Ptheta S theta) := hEmaj_int
    have hE_sq : (∫⁻ u : U, (ENNReal.ofReal (E u)) ^ 2 ∂(Ptheta S theta)) < ⊤ := by
      have hp : (fun u : U => (ENNReal.ofReal (E u)) ^ 2)
          = fun u : U => ENNReal.ofReal (E u ^ 2) := by
        funext u
        rw [pow_two, pow_two, ENNReal.ofReal_mul (hEmaj_nonneg u)]
      rw [hp]
      exact hEmaj_sq_lt_top
    have hE_meas_Pn : ∀ n : ℕ, AEMeasurable E ((Ptheta S theta).withDensity (rho n)) := by
      intro n
      rw [← hrho_dens n]
      exact hEmaj_aem.mono_ac (hrho_ac n)
    have hE_int_Pn : ∀ n : ℕ, Integrable E ((Ptheta S theta).withDensity (rho n)) := by
      intro n
      refine (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
        (hE_meas_Pn n).aestronglyMeasurable
        (Filter.Eventually.of_forall hEmaj_nonneg)).1 (ne_of_lt ?_)
      exact statopia_math_node_971375954_c360ad8c (U := U) (P := Ptheta S theta)
        (rho := rho n)
        (W := fun u : U => ENNReal.ofReal (((UScale e lam (1 - st)).indicator
          (fun v : U => Real.exp (1 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
            delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)))) u))
        (hrho_meas n)
        (by simpa [Function.comp_def] using
          ENNReal.measurable_ofReal.comp_aemeasurable hEmaj_aem)
        (lt_of_le_of_lt (hrho_bound n) (lt_of_le_of_ne le_top ENNReal.ofReal_ne_top)) hE_sq
    have hE_eq : ∀ u : U, u ∈ UScale e lam (1 - st) → E u =
        Real.exp (1 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
          delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2)) := by
      intro u hu
      show ((UScale e lam (1 - st)).indicator
        (fun v : U => Real.exp (1 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
          delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)))) u =
        Real.exp (1 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
          delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2))
      rw [Set.indicator_of_mem hu]
    have hconv : Tendsto (fun n : ℕ => ∫ u : U,
        |(beta / (m : ℝ)) * potSum Gammaih LG (Dn n) u -
          (beta / (m : ℝ)) * potSum Gammaih LG S u| * E u
        ∂((Ptheta S theta).withDensity (rho n))) atTop (𝓝 0) := by
      have hd := (statopia_math_node_2045408823_ad3ced10 (U := U) (H := H) (X := X)
        (e := e) (lam := lam) (hlam_pos := hlam_pos) (hlam_anti := hlam_anti)
        (Gamma := Gamma) (hGamma_pos := hGamma_pos) (hGamma_inj := hGamma_inj)
        (Gammah := Gammah) (hGammah_symm := hGammah_symm) (hGammah_pos := hGammah_pos)
        (hGammah_sq := hGammah_sq) (Gammaih := Gammaih) (hGammaih_left := hGammaih_left)
        (iotaH := iotaH) (bH := bH) (mu := mu) (hmu_pos := hmu_pos) (hmu_anti := hmu_anti)
        (C1 := C1) (hC1_pos := hC1_pos) (hC1_inj := hC1_inj) (hC1_eigen := hC1_eigen)
        (LG := LG) (s0 := s0) (s1 := s1) (s := s) (st := st) (alpha := alpha)
        (hs0_nonneg := hs0_nonneg) (hs0_lt := hs0_lt) (hs1_nonneg := hs1_nonneg)
        (hs1_lt := hs1_lt) (hs_gt := hs_gt) (hs_le := hs_le) (hst_gt := hst_gt)
        (hst_le := hst_le) (halpha := halpha)
        (C1c := C1c) (C2c := C2c) (hC1c := hC1c) (hC2c := hC2c)
        (M1 := M1) (hM1_mono := hM1_mono) (hM1_nonneg := hM1_nonneg)
        (M2 := M2) (hM2_nonneg := hM2_nonneg) (hM2_mono_fst := hM2_mono_fst)
        (hM2_mono_snd := hM2_mono_snd)
        (hA1 := hA1) (hA2 := hA2) (hA3 := hA3) (hA4 := hA4)
        (hLG_all_range := hLG_all_range)
        (beta := beta) (hbeta := hbeta) (m := m) (hm := hm) (Nc := Nc) (hNc := hNc)
        (Theta1 := Theta1) (Ptheta := Ptheta) (hPtheta_isProb := hPtheta_isProb)
        (theta := theta) (S := S) (mubar := mubar) (hmubar := hmubar)
        (kappa := kappa) (hkappa := hkappa) (h6 := h6) (h7 := h7) (h8 := h8)
        (delta0 := delta0) (hdelta0 := hdelta0) (hmoment := hmoment)
        (hdelta_meas := hdelta_meas) (hP_scale := hP_scale)
        (delta1 := delta1) (hdelta1 := hdelta1) (hdelta1_bound := hdelta1_bound)
        (r := r) (hr := hr) (D := S) (Dn := Dn)
        (hD_scale := hS_scale) (hDn_scale := hDn_scale) (hD_rad := hS_rad)
        (hDn_rad := hDn_rad) (hDn_tendsto := hDn_tendsto) (Bbar := Bbar) (hBbar := hBbar)
        (rho := rho) (hrho_meas := hrho_meas) (hrho_dens := hrho_dens)
        (hrhon_scale := hrhon_scale) (hrho_bound := hrho_bound)
        (eta := 1) (heta_pos := one_pos) (heta_le := by norm_num)).2.2.2
      simpa only [← hrho_dens] using hd
    have hconv_int : ∀ n : ℕ, Integrable (fun u : U =>
        |(beta / (m : ℝ)) * potSum Gammaih LG (Dn n) u -
          (beta / (m : ℝ)) * potSum Gammaih LG S u| * E u)
        ((Ptheta S theta).withDensity (rho n)) := by
      intro n
      haveI : IsProbabilityMeasure ((Ptheta S theta).withDensity (rho n)) := by
        rw [← hrho_dens n]
        exact hPtheta_isProb (Dn n) theta
      exact (statopia_math_node_2196947115_1f200b37 (U := U) (H := H) (X := X)
        (e := e) (lam := lam) (iotaH := iotaH) (bH := bH) (mu := mu)
        (Gammaih := Gammaih) (LG := LG) (s := s) (st := st) (alpha := alpha)
        (M1 := M1) (hM1_mono := hM1_mono) (hM1_nonneg := hM1_nonneg)
        (kappa := kappa) (hkappa := hkappa) (mubar := mubar) (hmubar := hmubar)
        (h6 := h6) (h7 := h7) (h8 := h8)
        (beta := beta) (hbeta := hbeta) (m := m) (hm := hm) (r := r) (hr := hr)
        (delta1 := delta1) (hdelta1 := hdelta1)
        (Q := (Ptheta S theta).withDensity (rho n))
        (hQ_scale := by rw [← hrho_dens n]; exact hrhon_scale n)
        (D := Dn n) (Dp := S) (hD := hDn_scale n) (hDp := hS_scale)
        (hD_rad := hDn_rad n) (hDp_rad := hS_rad)
        (hEt_int := by
          rw [← hrho_dens n]
          exact hdelta_int_Dn n (4 * delta1) (by linarith) (by linarith))
        (hDm := by
          rw [← hrho_dens n]
          simpa only [temperedDens, neg_mul] using
            (hdens_meas_all (Dn n)).mono_ac (hrho_ac n))
        (hDmp := by
          rw [← hrho_dens n]
          simpa only [temperedDens, neg_mul] using
            (hdens_meas_all S).mono_ac (hrho_ac n))).1
    have hmain := statopia_math_node_4260936017_8c420380 (U := U) (P := Ptheta S theta)
      (rho := rho)
      (s := fun u : U => (beta / (m : ℝ)) * potSum Gammaih LG S u)
      (sn := fun n : ℕ => fun u : U => (beta / (m : ℝ)) * potSum Gammaih LG (Dn n) u)
      (E := E) hrho_meas
      (by simpa only [temperedDens, neg_mul] using hdens_meas_all S)
      (fun n => by
        have h := (hdens_meas_all (Dn n)).mono_ac (hrho_ac n)
        rw [hrho_dens n] at h
        simpa only [temperedDens, neg_mul] using h)
      hE_nonneg hE_meas hE_int hE_meas_Pn hE_int_Pn
      (by
        filter_upwards [hae_scale_S] with u hu
        rw [hE_eq u hu]
        simpa only [temperedDens, neg_mul] using hpot_upper_gen S hS_scale hS_rad u hu)
      (fun n => by
        rw [← hrho_dens n]
        filter_upwards [hae_scale_Dn n] with u hu
        rw [hE_eq u hu]
        exact ⟨by
            simpa only [temperedDens, neg_mul] using
              hpot_upper_gen (Dn n) (hDn_scale n) (hDn_rad n) u hu,
          by simpa only [temperedDens, neg_mul] using
            hpot_upper_gen S hS_scale hS_rad u hu⟩)
      (by simpa only [temperedDens, neg_mul] using hfs_sq_lt_top)
      hrho_sq_tendsto hconv_int hconv
    simpa only [hZm_eq, temperedDens, neg_mul, ← hrho_dens] using hmain
  · exact hZm_pos_gen S (Ptheta S theta) hP_scale
      (fun delta hd hlt => hdelta_int_S delta hd (by linarith))
      hS_scale hS_rad (hdens_meas_all S)
  · intro n
    haveI : IsProbabilityMeasure (Ptheta (Dn n) theta) := hPtheta_isProb (Dn n) theta
    exact hZm_pos_gen (Dn n) (Ptheta (Dn n) theta) (hrhon_scale n) (hdelta_int_Dn n)
      (hDn_scale n) (hDn_rad n) ((hdens_meas_all (Dn n)).mono_ac (hrho_ac n))
  · let E : U → ℝ := fun u : U => ((UScale e lam (1 - st)).indicator
        (fun v : U => Real.exp (1 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
          delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)))) u
    have hE_meas_Pn : ∀ n : ℕ, AEMeasurable E ((Ptheta S theta).withDensity (rho n)) := by
      intro n
      rw [← hrho_dens n]
      exact hEmaj_aem.mono_ac (hrho_ac n)
    have hE_sq_top : (∫⁻ u : U, (ENNReal.ofReal (E u)) ^ 2 ∂(Ptheta S theta)) < ⊤ := by
      have hp : (fun u : U => (ENNReal.ofReal (E u)) ^ 2)
          = fun u : U => ENNReal.ofReal (E u ^ 2) := by
        funext u
        rw [pow_two, pow_two, ENNReal.ofReal_mul (hEmaj_nonneg u)]
      rw [hp]
      exact hEmaj_sq_lt_top
    have hE_int_Pn : ∀ n : ℕ, Integrable E ((Ptheta S theta).withDensity (rho n)) := by
      intro n
      refine (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
        (hE_meas_Pn n).aestronglyMeasurable
        (Filter.Eventually.of_forall hEmaj_nonneg)).1 (ne_of_lt ?_)
      exact statopia_math_node_971375954_c360ad8c (U := U) (P := Ptheta S theta)
        (rho := rho n)
        (W := fun u : U => ENNReal.ofReal (((UScale e lam (1 - st)).indicator
          (fun v : U => Real.exp (1 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
            delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)))) u))
        (hrho_meas n)
        (by simpa [Function.comp_def] using
          ENNReal.measurable_ofReal.comp_aemeasurable hEmaj_aem)
        (lt_of_le_of_lt (hrho_bound n) (lt_of_le_of_ne le_top ENNReal.ofReal_ne_top)) hE_sq_top
    have hE_eq : ∀ u : U, u ∈ UScale e lam (1 - st) → E u =
        Real.exp (1 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
          delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2)) := by
      intro u hu
      show ((UScale e lam (1 - st)).indicator
        (fun v : U => Real.exp (1 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
          delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)))) u =
        Real.exp (1 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
          delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2))
      rw [Set.indicator_of_mem hu]
    have hmaj_n : ∀ n : ℕ, ∀ᵐ u ∂((Ptheta S theta).withDensity (rho n)),
        Real.exp (-((beta / (m : ℝ)) * potSum Gammaih LG (Dn n) u)) ≤ E u ∧
        Real.exp (-((beta / (m : ℝ)) * potSum Gammaih LG S u)) ≤ E u := by
      intro n
      rw [← hrho_dens n]
      filter_upwards [hae_scale_Dn n] with u hu
      rw [hE_eq u hu]
      exact ⟨by
          simpa only [temperedDens, neg_mul] using
            hpot_upper_gen (Dn n) (hDn_scale n) (hDn_rad n) u hu,
        by simpa only [temperedDens, neg_mul] using
          hpot_upper_gen S hS_scale hS_rad u hu⟩
    have hlim : Tendsto (fun n : ℕ => ∫ u : U,
        ((beta / (m : ℝ)) * potSum Gammaih LG (Dn n) u -
          (beta / (m : ℝ)) * potSum Gammaih LG S u) ^ 2 * E u
        ∂((Ptheta S theta).withDensity (rho n))) atTop (𝓝 0) := by
      have hd := (statopia_math_node_2045408823_ad3ced10 (U := U) (H := H) (X := X)
        (e := e) (lam := lam) (hlam_pos := hlam_pos) (hlam_anti := hlam_anti)
        (Gamma := Gamma) (hGamma_pos := hGamma_pos) (hGamma_inj := hGamma_inj)
        (Gammah := Gammah) (hGammah_symm := hGammah_symm) (hGammah_pos := hGammah_pos)
        (hGammah_sq := hGammah_sq) (Gammaih := Gammaih) (hGammaih_left := hGammaih_left)
        (iotaH := iotaH) (bH := bH) (mu := mu) (hmu_pos := hmu_pos) (hmu_anti := hmu_anti)
        (C1 := C1) (hC1_pos := hC1_pos) (hC1_inj := hC1_inj) (hC1_eigen := hC1_eigen)
        (LG := LG) (s0 := s0) (s1 := s1) (s := s) (st := st) (alpha := alpha)
        (hs0_nonneg := hs0_nonneg) (hs0_lt := hs0_lt) (hs1_nonneg := hs1_nonneg)
        (hs1_lt := hs1_lt) (hs_gt := hs_gt) (hs_le := hs_le) (hst_gt := hst_gt)
        (hst_le := hst_le) (halpha := halpha)
        (C1c := C1c) (C2c := C2c) (hC1c := hC1c) (hC2c := hC2c)
        (M1 := M1) (hM1_mono := hM1_mono) (hM1_nonneg := hM1_nonneg)
        (M2 := M2) (hM2_nonneg := hM2_nonneg) (hM2_mono_fst := hM2_mono_fst)
        (hM2_mono_snd := hM2_mono_snd)
        (hA1 := hA1) (hA2 := hA2) (hA3 := hA3) (hA4 := hA4)
        (hLG_all_range := hLG_all_range)
        (beta := beta) (hbeta := hbeta) (m := m) (hm := hm) (Nc := Nc) (hNc := hNc)
        (Theta1 := Theta1) (Ptheta := Ptheta) (hPtheta_isProb := hPtheta_isProb)
        (theta := theta) (S := S) (mubar := mubar) (hmubar := hmubar)
        (kappa := kappa) (hkappa := hkappa) (h6 := h6) (h7 := h7) (h8 := h8)
        (delta0 := delta0) (hdelta0 := hdelta0) (hmoment := hmoment)
        (hdelta_meas := hdelta_meas) (hP_scale := hP_scale)
        (delta1 := delta1) (hdelta1 := hdelta1) (hdelta1_bound := hdelta1_bound)
        (r := r) (hr := hr) (D := S) (Dn := Dn)
        (hD_scale := hS_scale) (hDn_scale := hDn_scale) (hD_rad := hS_rad)
        (hDn_rad := hDn_rad) (hDn_tendsto := hDn_tendsto) (Bbar := Bbar) (hBbar := hBbar)
        (rho := rho) (hrho_meas := hrho_meas) (hrho_dens := hrho_dens)
        (hrhon_scale := hrhon_scale) (hrho_bound := hrho_bound)
        (eta := 1) (heta_pos := one_pos) (heta_le := by norm_num)).2.1
      simpa only [sq_abs, ← hrho_dens] using hd
    have hmaj_int : ∀ n : ℕ, Integrable (fun u : U =>
        ((beta / (m : ℝ)) * potSum Gammaih LG (Dn n) u -
          (beta / (m : ℝ)) * potSum Gammaih LG S u) ^ 2 * E u)
        ((Ptheta S theta).withDensity (rho n)) := by
      intro n
      haveI : IsProbabilityMeasure ((Ptheta S theta).withDensity (rho n)) := by
        rw [← hrho_dens n]
        exact hPtheta_isProb (Dn n) theta
      exact (statopia_math_node_2196947115_1f200b37 (U := U) (H := H) (X := X)
        (e := e) (lam := lam) (iotaH := iotaH) (bH := bH) (mu := mu)
        (Gammaih := Gammaih) (LG := LG) (s := s) (st := st) (alpha := alpha)
        (M1 := M1) (hM1_mono := hM1_mono) (hM1_nonneg := hM1_nonneg)
        (kappa := kappa) (hkappa := hkappa) (mubar := mubar) (hmubar := hmubar)
        (h6 := h6) (h7 := h7) (h8 := h8)
        (beta := beta) (hbeta := hbeta) (m := m) (hm := hm) (r := r) (hr := hr)
        (delta1 := delta1) (hdelta1 := hdelta1)
        (Q := (Ptheta S theta).withDensity (rho n))
        (hQ_scale := by rw [← hrho_dens n]; exact hrhon_scale n)
        (D := Dn n) (Dp := S) (hD := hDn_scale n) (hDp := hS_scale)
        (hD_rad := hDn_rad n) (hDp_rad := hS_rad)
        (hEt_int := by
          rw [← hrho_dens n]
          exact hdelta_int_Dn n (4 * delta1) (by linarith) (by linarith))
        (hDm := by
          rw [← hrho_dens n]
          simpa only [temperedDens, neg_mul] using
            (hdens_meas_all (Dn n)).mono_ac (hrho_ac n))
        (hDmp := by
          rw [← hrho_dens n]
          simpa only [temperedDens, neg_mul] using
            (hdens_meas_all S).mono_ac (hrho_ac n))).2
    have hmain := statopia_math_node_3748965445_c602f3c6 (U := U) (P := Ptheta S theta)
      (rho := rho)
      (s := fun u : U => (beta / (m : ℝ)) * potSum Gammaih LG S u)
      (sn := fun n : ℕ => fun u : U => (beta / (m : ℝ)) * potSum Gammaih LG (Dn n) u)
      (E := E) hrho_meas
      (fun n => by
        have h := (hdens_meas_all (Dn n)).mono_ac (hrho_ac n)
        rw [hrho_dens n] at h
        simpa only [temperedDens, neg_mul] using h)
      (fun n => by
        have h := (hdens_meas_all S).mono_ac (hrho_ac n)
        rw [hrho_dens n] at h
        simpa only [temperedDens, neg_mul] using h)
      hEmaj_nonneg hE_meas_Pn hE_int_Pn hmaj_n hmaj_int hlim
    simpa only [temperedDens, neg_mul, ← hrho_dens] using hmain
  · exact statopia_math_node_627162574_1890e6dd (U := U) (P := Ptheta S theta)
      (f := fun u : U => temperedDens beta m Gammaih LG S u) (rho := rho)
      (hdens_meas_all S) (hdens_nonneg S) hfs_sq_lt_top hrho_meas hrho_sq_tendsto
  · let E : U → ℝ := fun u : U => ((UScale e lam (1 - st)).indicator
        (fun v : U => Real.exp (1 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
          delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)))) u
    have hE_exp : ∀ᵐ u ∂(Ptheta S theta), E u =
        Real.exp (1 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
          delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2)) := by
      filter_upwards [hae_scale_S] with u hu
      show ((UScale e lam (1 - st)).indicator
          (fun v : U => Real.exp (1 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
            delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)))) u =
          Real.exp (1 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
            delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2))
      rw [Set.indicator_of_mem hu]
    have hWmeas : ∀ n : ℕ, Measurable (fun u : U =>
        (Real.sqrt ((rho n u).toReal) - 1) ^ 2) := by
      intro n
      have h1 : Measurable (fun u : U => (rho n u).toReal) := (hrho_meas n).ennreal_toReal
      exact ((Real.continuous_sqrt.measurable.comp h1).sub measurable_const).pow_const 2
    have hsq : ∀ u : U, ENNReal.ofReal (E u ^ 2)
        = ENNReal.ofReal (E u) * ENNReal.ofReal (E u) := by
      intro u
      rw [pow_two, ENNReal.ofReal_mul (hEmaj_nonneg u)]
    have ha1 : AEMeasurable (fun u : U => ENNReal.ofReal (E u)) (Ptheta S theta) :=
      ENNReal.measurable_ofReal.comp_aemeasurable hEmaj_aem
    have ha2 : AEMeasurable (fun u : U =>
        ENNReal.ofReal (E u) * ENNReal.ofReal (E u)) (Ptheta S theta) := ha1.mul ha1
    have hE_lin : (∫⁻ u : U, ENNReal.ofReal (E u) ∂(Ptheta S theta)) < ⊤ :=
      hEmaj_lintegral_lt_top
    have hE_sq : (∫⁻ u : U, ENNReal.ofReal (E u) * ENNReal.ofReal (E u)
        ∂(Ptheta S theta)) < ⊤ := by
      have hp : (fun u : U => ENNReal.ofReal (E u) * ENNReal.ofReal (E u))
          = fun u : U => ENNReal.ofReal (E u ^ 2) := by
        funext u
        exact (hsq u).symm
      rw [hp]
      exact hEmaj_sq_lt_top
    have hmaj_lt : ∀ n : ℕ, (∫⁻ u : U, ENNReal.ofReal (E u *
        (Real.sqrt ((rho n u).toReal) - 1) ^ 2) ∂(Ptheta S theta)) < ⊤ := by
      intro n
      have hX_sq : (∫⁻ u : U, ENNReal.ofReal ((rho n u).toReal ^ 2)
          ∂(Ptheta S theta)) < ⊤ := by
        have hle : ∀ u : U, ENNReal.ofReal ((rho n u).toReal ^ 2) ≤ (rho n u) ^ 2 := by
          intro u
          have h1 : ENNReal.ofReal ((rho n u).toReal ^ 2)
              = (ENNReal.ofReal ((rho n u).toReal)) ^ 2 := by
            rw [pow_two, pow_two, ENNReal.ofReal_mul ENNReal.toReal_nonneg]
          rw [h1, pow_two, pow_two]
          exact mul_le_mul ENNReal.ofReal_toReal_le ENNReal.ofReal_toReal_le
            (zero_le _) (zero_le _)
        exact lt_of_le_of_lt (lintegral_mono hle)
          (lt_of_le_of_lt (hrho_bound n) (lt_of_le_of_ne le_top ENNReal.ofReal_ne_top))
      have hpt : ∀ u : U, ENNReal.ofReal (E u * (Real.sqrt ((rho n u).toReal) - 1) ^ 2) ≤
          ENNReal.ofReal (E u) +
            (ENNReal.ofReal (E u) * ENNReal.ofReal (E u) +
              ENNReal.ofReal ((rho n u).toReal ^ 2)) := by
        intro u
        generalize hEu : E u = a
        have hE0 : (0 : ℝ) ≤ a := by rw [← hEu]; exact hEmaj_nonneg u
        have hX0 : (0 : ℝ) ≤ (rho n u).toReal := ENNReal.toReal_nonneg
        have hwle : (Real.sqrt ((rho n u).toReal) - 1) ^ 2 ≤ 1 + (rho n u).toReal := by
          have hs : (Real.sqrt ((rho n u).toReal) - 1) ^ 2
              = (rho n u).toReal - 2 * Real.sqrt ((rho n u).toReal) + 1 := by
            rw [sub_sq, Real.sq_sqrt hX0]
            ring
          rw [hs]
          linarith [Real.sqrt_nonneg ((rho n u).toReal)]
        have h3 : a * (rho n u).toReal ≤ a ^ 2 + (rho n u).toReal ^ 2 := by
          have hs : (0 : ℝ) ≤ (a - (rho n u).toReal) ^ 2 := sq_nonneg _
          have hexp : (a - (rho n u).toReal) ^ 2
              = a ^ 2 - 2 * (a * (rho n u).toReal) + (rho n u).toReal ^ 2 := by
            rw [sub_sq]
            ring
          have ha2 : (0 : ℝ) ≤ a ^ 2 := sq_nonneg a
          have hx2 : (0 : ℝ) ≤ (rho n u).toReal ^ 2 := sq_nonneg _
          linarith [hs, hexp, ha2, hx2]
        have hmain : a * (Real.sqrt ((rho n u).toReal) - 1) ^ 2 ≤
            a + (a ^ 2 + (rho n u).toReal ^ 2) := by
          have h1 : a * (Real.sqrt ((rho n u).toReal) - 1) ^ 2 ≤
              a * (1 + (rho n u).toReal) := mul_le_mul_of_nonneg_left hwle hE0
          have h2 : a * (1 + (rho n u).toReal) = a + a * (rho n u).toReal := by ring
          linarith [h1, h2, h3]
        have hsqA : ENNReal.ofReal (a ^ 2) = ENNReal.ofReal a * ENNReal.ofReal a := by
          rw [pow_two, ENNReal.ofReal_mul hE0]
        have hgoal : ENNReal.ofReal (a * (Real.sqrt ((rho n u).toReal) - 1) ^ 2) ≤
            ENNReal.ofReal a + (ENNReal.ofReal a * ENNReal.ofReal a +
              ENNReal.ofReal ((rho n u).toReal ^ 2)) := by
          refine le_trans (ENNReal.ofReal_le_ofReal hmain) (le_of_eq ?_)
          rw [ENNReal.ofReal_add hE0
              (add_nonneg (sq_nonneg a) (sq_nonneg ((rho n u).toReal))),
            ENNReal.ofReal_add (sq_nonneg a) (sq_nonneg ((rho n u).toReal)), hsqA]
        exact hgoal
      refine lt_of_le_of_lt (lintegral_mono hpt) ?_
      rw [MeasureTheory.lintegral_add_left' ha1]
      rw [MeasureTheory.lintegral_add_left' ha2]
      exact ENNReal.add_lt_top.2 ⟨hE_lin, ENNReal.add_lt_top.2 ⟨hE_sq, hX_sq⟩⟩
    have hmaj_int : ∀ n : ℕ, Integrable (fun u : U => E u *
        (Real.sqrt ((rho n u).toReal) - 1) ^ 2) (Ptheta S theta) := by
      intro n
      exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
        (hEmaj_aem.mul (hWmeas n).aemeasurable).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun u =>
          mul_nonneg (hEmaj_nonneg u) (sq_nonneg _)))).1 (ne_of_lt (hmaj_lt n))
    have hLHS_int : ∀ n : ℕ, Integrable (fun u : U =>
        temperedDens beta m Gammaih LG (Dn n) u *
          (Real.sqrt ((rho n u).toReal) - 1) ^ 2) (Ptheta S theta) := by
      intro n
      refine (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
        ((hdens_meas_all (Dn n)).mul (hWmeas n).aemeasurable).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun u =>
          mul_nonneg (hdens_nonneg (Dn n) u) (sq_nonneg _)))).1 ?_
      refine ne_of_lt (lt_of_le_of_lt ?_ (hmaj_lt n))
      refine lintegral_mono_ae ?_
      filter_upwards [hae_scale_S, hE_exp] with u hu hEu
      rw [hEu]
      exact ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (hpot_upper_gen (Dn n) (hDn_scale n) (hDn_rad n) u hu)
          (sq_nonneg _))
    refine squeeze_zero (fun n => ?_) (fun n => ?_)
      (statopia_math_node_627162574_1890e6dd (U := U) (P := Ptheta S theta)
        (f := fun u : U => ((UScale e lam (1 - st)).indicator
          (fun v : U => Real.exp (1 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
            delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)))) u)
        (rho := rho) hEmaj_aem hEmaj_nonneg hEmaj_sq_lt_top hrho_meas hrho_sq_tendsto)
    · refine MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall (fun u => ?_))
      exact mul_nonneg (hdens_nonneg (Dn n) u) (sq_nonneg _)
    · refine integral_mono_ae (hLHS_int n) (hmaj_int n) ?_
      filter_upwards [hae_scale_S] with u hu
      have hind : ((UScale e lam (1 - st)).indicator
          (fun v : U => Real.exp (1 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
            delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)))) u =
          Real.exp (1 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
            delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2)) := by
        rw [Set.indicator_of_mem hu]
      rw [hind]
      exact mul_le_mul_of_nonneg_right
        (hpot_upper_gen (Dn n) (hDn_scale n) (hDn_rad n) u hu) (sq_nonneg _)
  /- @proof-region region.target-node.session.c038c5d2cfd484e7 end -/

end Statlib.Imported
end

