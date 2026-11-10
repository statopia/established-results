import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_1912460074_9ad458a1_fd8c2d8a
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_2035098161_9f60db94_bdde90c8
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3191669108_71ceb7f7_23142090
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
theorem statopia_math_node_732817276_8749eb7a : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
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
        atTop (𝓝 0) ∧
    Tendsto
        (fun n : ℕ => ∫ u : U,
          |(beta / (m : ℝ)) * potSum Gammaih LG (Dn n) u -
              (beta / (m : ℝ)) * potSum Gammaih LG D u| *
            (UScale e lam (1 - st)).indicator
              (fun v : U =>
                Real.exp ((1 : ℝ) * ((beta * kappa * r) ^ 2 / (4 * delta1) +
                  delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2))) u
          ∂(Ptheta (Dn n) theta))
        atTop (𝓝 0) := by
  /- @proof-region region.target-node.session.b6adf30a73a8838c begin -/
  intro U _ _ _ _ _ H _ _ _ X _ e lam hlam_pos hlam_anti Gamma hGamma_pos hGamma_inj
    Gammah hGammah_symm hGammah_pos hGammah_sq Gammaih hGammaih_left iotaH _ bH mu hmu_pos
    hmu_anti C1 hC1_pos hC1_inj hC1_eigen LG s0 s1 s st alpha hs0_nonneg hs0_lt hs1_nonneg hs1_lt
    hs_gt hs_le hst_gt hst_le halpha C1c C2c hC1c hC2c M1 hM1_mono hM1_nonneg M2 hM2_nonneg
    hM2_mono_fst hM2_mono_snd hA1 hA2 hA3 hA4 hLG_all_range beta hbeta m hm Nc hNc Theta1 _ _ _
    _ _ Ptheta hPtheta_isProb theta S mubar hmubar kappa hkappa h6 h7 h8 delta0 hdelta0 hmoment
    hdelta_meas hP_scale delta1 hdelta1 hdelta1_bound r hr D Dn hD_scale hDn_scale hD_rad hDn_rad
    hDn_tendsto Bbar hBbar rho hrho_meas hrho_dens hrhon_scale hrho_bound eta heta_pos heta_le
  refine ⟨?_, ?_⟩
  · exact statopia_math_node_3191669108_71ceb7f7 U H X e lam hlam_pos hlam_anti Gamma hGamma_pos
      hGamma_inj Gammah hGammah_symm hGammah_pos hGammah_sq Gammaih hGammaih_left iotaH bH mu hmu_pos
      hmu_anti C1 hC1_pos hC1_inj hC1_eigen LG s0 s1 s st alpha hs0_nonneg hs0_lt hs1_nonneg hs1_lt
      hs_gt hs_le hst_gt hst_le halpha C1c C2c hC1c hC2c M1 hM1_mono hM1_nonneg M2 hM2_nonneg
      hM2_mono_fst hM2_mono_snd hA1 hA2 hA3 hA4 hLG_all_range beta hbeta m hm Nc hNc Theta1 Ptheta
      hPtheta_isProb theta S mubar hmubar kappa hkappa h6 h7 h8 delta0 hdelta0 hmoment hdelta_meas
      hP_scale delta1 hdelta1 hdelta1_bound r hr D Dn hD_scale hDn_scale hD_rad hDn_rad hDn_tendsto
      Bbar hBbar rho hrho_meas hrho_dens hrhon_scale hrho_bound eta heta_pos heta_le
  · exact statopia_math_node_1912460074_9ad458a1 U H X e lam hlam_pos hlam_anti Gamma hGamma_pos
      hGamma_inj Gammah hGammah_symm hGammah_pos hGammah_sq Gammaih hGammaih_left iotaH bH mu hmu_pos
      hmu_anti C1 hC1_pos hC1_inj hC1_eigen LG s0 s1 s st alpha hs0_nonneg hs0_lt hs1_nonneg hs1_lt
      hs_gt hs_le hst_gt hst_le halpha C1c C2c hC1c hC2c M1 hM1_mono hM1_nonneg M2 hM2_nonneg
      hM2_mono_fst hM2_mono_snd hA1 hA2 hA3 hA4 hLG_all_range beta hbeta m hm Nc hNc Theta1 Ptheta
      hPtheta_isProb theta S mubar hmubar kappa hkappa h6 h7 h8 delta0 hdelta0 hmoment hdelta_meas
      hP_scale delta1 hdelta1 hdelta1_bound r hr D Dn hD_scale hDn_scale hD_rad hDn_rad hDn_tendsto
      Bbar hBbar rho hrho_meas hrho_dens hrhon_scale hrho_bound
  /- @proof-region region.target-node.session.b6adf30a73a8838c end -/

end Statlib.Imported
end

