import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3916768571_a9930ecf_948a7b8d
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3975929643_b00873c3_38223545

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
theorem statopia_math_node_1729749604_be8e8033 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
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
      HScaleDist bH mu (alpha - s) ((Dn n j).2) 0 ≤ ENNReal.ofReal r),
    (∀ (n : ℕ), Integrable (fun u : U =>
        ((beta / (m : ℝ)) * potSum Gammaih LG (Dn n) u - (beta / (m : ℝ)) * potSum Gammaih LG D u) ^ 2 *
          (UScale e lam (1 - st)).indicator
            (fun v : U => Real.exp (2 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
              delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2))) u)
      (Ptheta S theta)) ∧
    (∀ (n : ℕ), Integrable (fun u : U => Real.sqrt
        (((beta / (m : ℝ)) * potSum Gammaih LG (Dn n) u - (beta / (m : ℝ)) * potSum Gammaih LG D u) ^ 2 *
          (UScale e lam (1 - st)).indicator
            (fun v : U => Real.exp (2 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
              delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2))) u))
      (Ptheta S theta)) ∧
    (∀ (n : ℕ) (u : U), 0 ≤
        ((beta / (m : ℝ)) * potSum Gammaih LG (Dn n) u - (beta / (m : ℝ)) * potSum Gammaih LG D u) ^ 2 *
          (UScale e lam (1 - st)).indicator
            (fun v : U => Real.exp (2 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
              delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2))) u) := by
  /- @proof-region region.target-node.session.5662c8937e506d6e begin -/
  intro U _ _ _ _ _ H _ _ _ X _ e lam hlam_pos hlam_anti Gamma hGamma_pos hGamma_inj Gammah
    hGammah_symm hGammah_pos hGammah_sq Gammaih hGammaih_left iotaH _ bH mu hmu_pos hmu_anti
    C1 hC1_pos hC1_inj hC1_eigen LG s0 s1 s st alpha hs0_nonneg hs0_lt hs1_nonneg hs1_lt hs_gt
    hs_le hst_gt hst_le halpha C1c C2c hC1c hC2c M1 hM1_mono hM1_nonneg M2 hM2_nonneg
    hM2_mono_fst hM2_mono_snd hA1 hA2 hA3 hA4 hLG_all_range beta hbeta m hm Nc hNc Theta1
    _ _ _ _ _ Ptheta hPtheta_isProb theta S mubar hmubar kappa hkappa h6 h7 h8 delta0 hdelta0
    hmoment hdelta_meas hP_scale delta1 hdelta1 hdelta1_bound r hr D Dn hD_scale hDn_scale
    hD_rad hDn_rad
  let y : U → ℝ := fun u => (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2
  let A0 : ℝ := (beta * kappa * r) ^ 2 / (4 * delta1)
  let Kc : ℝ := beta * (4 * kappa * r + 2 * Real.rpow mubar st)
  let Cst : ℝ := Kc ^ 2 * (2 * (1 + 1 / (18 * delta1 ^ 2))) * Real.exp (2 * A0)
  let G : U → ℝ := fun u => Real.exp (8 * delta1 * y u)
  let Del : ℕ → U → ℝ := fun n u =>
    (beta / (m : ℝ)) * potSum Gammaih LG (Dn n) u - (beta / (m : ℝ)) * potSum Gammaih LG D u
  let F : ℕ → U → ℝ := fun n u =>
    (Del n u) ^ 2 *
      (UScale e lam (1 - st)).indicator (fun v : U => Real.exp (2 * (A0 + delta1 * y v))) u
  have hexp1 : ∀ x : ℝ, 0 ≤ x → (1 : ℝ) ≤ Real.exp x := fun x hx => by
    simpa using Real.pow_div_factorial_le_exp x hx 0
  have hy_nonneg : ∀ u : U, 0 ≤ y u := fun u => sq_nonneg _
  have hδ2 : (0 : ℝ) < 18 * delta1 ^ 2 := by nlinarith [hdelta1]
  have hdom := statopia_math_node_3975929643_b00873c3 U H X Gammaih LG e lam iotaH bH mu
    hmu_pos M1 hM1_mono hM1_nonneg s st alpha m hm beta hbeta mubar kappa hmubar hkappa h6 h7 h8
  have hΔ : ∀ (n : ℕ) (u : U), UScale e lam (1 - st) u → |Del n u| ≤ Kc * (1 + y u) := by
    intro n u hu
    have h := hdom.2.1 r hr (Dn n) D (hDn_scale n) hD_scale (hDn_rad n) hD_rad u hu
    show |((beta / (m : ℝ)) * potSum Gammaih LG (Dn n) u -
        (beta / (m : ℝ)) * potSum Gammaih LG D u)| ≤
      (beta * (4 * kappa * r + 2 * Real.rpow mubar st)) *
        (1 + (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2)
    exact h
  have hCst_nonneg : 0 ≤ Cst := by
    show 0 ≤ Kc ^ 2 * (2 * (1 + 1 / (18 * delta1 ^ 2))) * Real.exp (2 * A0)
    have h6 : 0 ≤ Kc ^ 2 * (2 * (1 + 1 / (18 * delta1 ^ 2))) := by
      have h3 : 0 ≤ 1 / (18 * delta1 ^ 2) := div_nonneg zero_le_one hδ2.le
      nlinarith [h3, sq_nonneg Kc]
    exact mul_nonneg h6 (Real.exp_pos _).le
  have hpoly : ∀ yv : ℝ, 0 ≤ yv →
      (1 + yv) ^ 2 * Real.exp (2 * (A0 + delta1 * yv)) ≤
        (2 * (1 + 1 / (18 * delta1 ^ 2))) * Real.exp (2 * A0) * Real.exp (8 * delta1 * yv) := by
    intro yv hyv
    have hx : 0 ≤ 6 * delta1 * yv := by nlinarith [hdelta1, hyv]
    have hE1 : (1 : ℝ) ≤ Real.exp (6 * delta1 * yv) := hexp1 _ hx
    have hfact := Real.pow_div_factorial_le_exp (6 * delta1 * yv) hx 2
    have hfac : (6 * delta1 * yv) ^ 2 / 2 ≤ Real.exp (6 * delta1 * yv) := by simpa using hfact
    have hE2 : yv ^ 2 ≤ Real.exp (6 * delta1 * yv) / (18 * delta1 ^ 2) := by
      rw [le_div_iff₀ hδ2]
      have h2' : (6 * delta1 * yv) ^ 2 = 36 * delta1 ^ 2 * yv ^ 2 := by ring
      nlinarith [hfac, h2']
    have hsum : 1 + yv ^ 2 ≤ (1 + 1 / (18 * delta1 ^ 2)) * Real.exp (6 * delta1 * yv) := by
      have h1 : 1 + yv ^ 2 ≤
          Real.exp (6 * delta1 * yv) + Real.exp (6 * delta1 * yv) / (18 * delta1 ^ 2) := by
        linarith [hE1, hE2]
      have h2 : Real.exp (6 * delta1 * yv) + Real.exp (6 * delta1 * yv) / (18 * delta1 ^ 2)
          = (1 + 1 / (18 * delta1 ^ 2)) * Real.exp (6 * delta1 * yv) := by ring
      rw [← h2]
      exact h1
    have h4 : (1 + yv) ^ 2 ≤ 2 * (1 + yv ^ 2) := by nlinarith [sq_nonneg (yv - 1)]
    have hexp : Real.exp (6 * delta1 * yv) * Real.exp (2 * (A0 + delta1 * yv)) =
        Real.exp (2 * A0) * Real.exp (8 * delta1 * yv) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc (1 + yv) ^ 2 * Real.exp (2 * (A0 + delta1 * yv))
        ≤ (2 * (1 + yv ^ 2)) * Real.exp (2 * (A0 + delta1 * yv)) :=
          mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
      _ ≤ (2 * ((1 + 1 / (18 * delta1 ^ 2)) * Real.exp (6 * delta1 * yv))) *
            Real.exp (2 * (A0 + delta1 * yv)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          linarith [hsum]
      _ = (2 * (1 + 1 / (18 * delta1 ^ 2))) *
            (Real.exp (6 * delta1 * yv) * Real.exp (2 * (A0 + delta1 * yv))) := by ring
      _ = (2 * (1 + 1 / (18 * delta1 ^ 2))) *
            (Real.exp (2 * A0) * Real.exp (8 * delta1 * yv)) := by rw [hexp]
      _ = (2 * (1 + 1 / (18 * delta1 ^ 2))) * Real.exp (2 * A0) *
            Real.exp (8 * delta1 * yv) := by ring
  have hF_nonneg : ∀ (n : ℕ) (u : U), 0 ≤ F n u := by
    intro n u
    show 0 ≤ (Del n u) ^ 2 *
      (UScale e lam (1 - st)).indicator (fun v : U => Real.exp (2 * (A0 + delta1 * y v))) u
    by_cases hu : u ∈ UScale e lam (1 - st)
    · rw [Set.indicator_of_mem hu]
      exact mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
    · simp [Set.indicator, hu]
  have hF_le : ∀ (n : ℕ) (u : U), F n u ≤ Cst * G u := by
    intro n u
    by_cases hu : u ∈ UScale e lam (1 - st)
    · have hFu : F n u = (Del n u) ^ 2 * Real.exp (2 * (A0 + delta1 * y u)) := by
        show (Del n u) ^ 2 *
            (UScale e lam (1 - st)).indicator (fun v : U => Real.exp (2 * (A0 + delta1 * y v))) u =
          (Del n u) ^ 2 * Real.exp (2 * (A0 + delta1 * y u))
        rw [Set.indicator_of_mem hu]
      rw [hFu]
      have hΔu := hΔ n u hu
      have hsq : (Del n u) ^ 2 ≤ Kc ^ 2 * (1 + y u) ^ 2 := by
        have h1 : |Del n u| * |Del n u| ≤ (Kc * (1 + y u)) * (Kc * (1 + y u)) :=
          mul_self_le_mul_self (abs_nonneg _) hΔu
        have h2 : |Del n u| * |Del n u| = (Del n u) ^ 2 := by
          rw [← sq_abs (Del n u)]
          ring
        have h3 : (Kc * (1 + y u)) * (Kc * (1 + y u)) = Kc ^ 2 * (1 + y u) ^ 2 := by ring
        linarith [h1, h2, h3]
      have hp := hpoly (y u) (hy_nonneg u)
      calc (Del n u) ^ 2 * Real.exp (2 * (A0 + delta1 * y u))
          ≤ (Kc ^ 2 * (1 + y u) ^ 2) * Real.exp (2 * (A0 + delta1 * y u)) :=
            mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
        _ = Kc ^ 2 * ((1 + y u) ^ 2 * Real.exp (2 * (A0 + delta1 * y u))) := by ring
        _ ≤ Kc ^ 2 * ((2 * (1 + 1 / (18 * delta1 ^ 2))) * Real.exp (2 * A0) *
              Real.exp (8 * delta1 * y u)) := mul_le_mul_of_nonneg_left hp (sq_nonneg _)
        _ = Cst * G u := by
            have hC : Cst = Kc ^ 2 * (2 * (1 + 1 / (18 * delta1 ^ 2))) * Real.exp (2 * A0) := rfl
            have hG : G u = Real.exp (8 * delta1 * y u) := rfl
            rw [hC, hG]
            ring
    · have hFu : F n u = 0 := by
        show (Del n u) ^ 2 *
            (UScale e lam (1 - st)).indicator (fun v : U => Real.exp (2 * (A0 + delta1 * y v))) u = 0
        simp [Set.indicator, hu]
      rw [hFu]
      exact mul_nonneg hCst_nonneg (Real.exp_pos _).le
  have hsqrt_le : ∀ (n : ℕ) (u : U), Real.sqrt (F n u) ≤ G u + Cst * G u := by
    intro n u
    have h1 : Real.sqrt (F n u) ≤ 1 + F n u := by
      have hb : (0 : ℝ) ≤ 1 + F n u := by linarith [hF_nonneg n u]
      have hsq : (Real.sqrt (F n u)) ^ 2 ≤ (1 + F n u) ^ 2 := by
        rw [Real.sq_sqrt (hF_nonneg n u)]
        nlinarith [hF_nonneg n u]
      exact (abs_le_of_sq_le_sq' hsq hb).2
    have h2 : F n u ≤ Cst * G u := hF_le n u
    have h3 : (1 : ℝ) ≤ G u := by
      show (1 : ℝ) ≤ Real.exp (8 * delta1 * y u)
      exact hexp1 _ (by nlinarith [hdelta1, hy_nonneg u])
    calc Real.sqrt (F n u) ≤ 1 + F n u := h1
      _ ≤ G u + Cst * G u := add_le_add h3 h2
  have hG_int : Integrable G (Ptheta S theta) := by
    have h0 : 0 ≤ 8 * delta1 := by linarith
    exact hmoment (8 * delta1) h0 hdelta1_bound
  have hUneas : Measurable (fun u : U => UScaleNorm e lam (1 - st) u) := by
    show Measurable (fun u : U => ∑' k : ℕ,
      ENNReal.ofReal (Real.rpow (lam k) (-(1 - st)) * (inner ℝ (e k) u) ^ 2))
    apply Measurable.ennreal_tsum
    intro k
    have hi : Measurable (fun u : U => inner ℝ (e k) u) := by
      have hc : Continuous fun u : U => ((innerSL ℝ) (e k)) u := (innerSL ℝ (e k)).continuous
      simpa only [innerSL_apply_apply] using hc.measurable
    have hpow : Measurable (fun u : U => (inner ℝ (e k) u) ^ 2) := by
      have h := hi.mul hi
      simpa [pow_two] using h
    exact ENNReal.measurable_ofReal.comp (measurable_const.mul hpow)
  have hsc_meas : MeasurableSet (UScale e lam (1 - st)) := by
    have h := MeasureTheory.StronglyMeasurable.measurableSet_lt hUneas.stronglyMeasurable
      (stronglyMeasurable_const (b := (⊤ : ℝ≥0∞)))
    exact h
  have hPcompl : (Ptheta S theta) ((UScale e lam (1 - st))ᶜ) = 0 := by
    haveI := hPtheta_isProb S theta
    have hc := MeasureTheory.measure_compl (μ := Ptheta S theta) hsc_meas
      (by rw [hP_scale]; exact ENNReal.one_ne_top)
    rw [hc, MeasureTheory.measure_univ, hP_scale]
    simp
  have hF_meas : ∀ n : ℕ, AEMeasurable (F n) (Ptheta S theta) := by
    have hdep := statopia_math_node_3916768571_a9930ecf U H X e lam hlam_pos hlam_anti Gamma
      hGamma_pos hGamma_inj Gammah hGammah_symm hGammah_pos hGammah_sq Gammaih hGammaih_left iotaH
      bH mu hmu_pos hmu_anti C1 hC1_pos hC1_inj hC1_eigen LG s0 s1 s st alpha hs0_nonneg hs0_lt
      hs1_nonneg hs1_lt hs_gt hs_le hst_gt hst_le halpha C1c C2c hC1c hC2c M1 hM1_mono hM1_nonneg
      M2 hM2_nonneg hM2_mono_fst hM2_mono_snd hA1 hA2 hA3 hA4 hLG_all_range beta hbeta m hm
    have hpot : ∀ D' : Fin m → X × H,
        AEMeasurable (fun u : U => potSum Gammaih LG D' u) (Ptheta S theta) := fun D' =>
      (hdep.2.2 D' (S ⟨0, hm⟩).1 (S ⟨0, hm⟩).2 (Ptheta S theta) hP_scale hPcompl).2.1
    have hDel_meas : ∀ n : ℕ, AEMeasurable (Del n) (Ptheta S theta) := by
      intro n
      have h1 : AEMeasurable (fun u : U => (beta / (m : ℝ)) * potSum Gammaih LG (Dn n) u)
          (Ptheta S theta) := (hpot (Dn n)).const_mul _
      have h2 : AEMeasurable (fun u : U => (beta / (m : ℝ)) * potSum Gammaih LG D u)
          (Ptheta S theta) := (hpot D).const_mul _
      exact h1.sub h2
    have hind : AEMeasurable ((UScale e lam (1 - st)).indicator
        (fun v : U => Real.exp (2 * (A0 + delta1 * y v)))) (Ptheta S theta) := by
      have hbase := hdelta_meas (2 * delta1)
      have hfun : ((UScale e lam (1 - st)).indicator
            (fun v : U => Real.exp (2 * (A0 + delta1 * y v))))
          = fun u => Real.exp (2 * A0) * ((UScale e lam (1 - st)).indicator
              (fun v : U => Real.exp (2 * delta1 * y v))) u := by
        funext u
        by_cases hu : u ∈ UScale e lam (1 - st)
        · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, ← Real.exp_add]
          congr 1
          ring
        · simp [Set.indicator, hu]
      rw [hfun]
      exact hbase.const_mul (Real.exp (2 * A0))
    intro n
    have hsq_meas : AEMeasurable (fun u : U => (Del n u) ^ 2) (Ptheta S theta) := by
      have h := (hDel_meas n).mul (hDel_meas n)
      simpa [pow_two] using h
    exact hsq_meas.mul hind
  refine ⟨?_, ?_, ?_⟩
  · intro n
    have hM0 : ∀ u : U, (0 : ℝ) ≤ Cst * G u := fun u =>
      mul_nonneg hCst_nonneg (Real.exp_pos _).le
    refine MeasureTheory.Integrable.mono' (hG_int.const_mul Cst) (hF_meas n).aestronglyMeasurable ?_
    filter_upwards with u
    have h4 : (F n u) ^ 2 ≤ (Cst * G u) ^ 2 := by
      have h := mul_le_mul (hF_le n u) (hF_le n u) (hF_nonneg n u) (hM0 u)
      simpa [pow_two] using h
    simpa only [Real.norm_eq_abs] using abs_le_of_sq_le_sq h4 (hM0 u)
  · intro n
    have hb : ∀ u : U, (0 : ℝ) ≤ G u + Cst * G u := fun u =>
      add_nonneg (le_of_lt (Real.exp_pos _)) (mul_nonneg hCst_nonneg (Real.exp_pos _).le)
    refine MeasureTheory.Integrable.mono' (hG_int.add (hG_int.const_mul Cst))
      (Real.continuous_sqrt.measurable.comp_aemeasurable (hF_meas n)).aestronglyMeasurable ?_
    filter_upwards with u
    have hneg : -((G u + Cst * G u)) ≤ Real.sqrt (F n u) :=
      le_trans (neg_nonpos.mpr (hb u)) (Real.sqrt_nonneg (F n u))
    have h4 : (Real.sqrt (F n u)) ^ 2 ≤ (G u + Cst * G u) ^ 2 :=
      sq_le_sq' hneg (hsqrt_le n u)
    simpa only [Real.norm_eq_abs] using abs_le_of_sq_le_sq h4 (hb u)
  · intro n u
    exact hF_nonneg n u
  /- @proof-region region.target-node.session.5662c8937e506d6e end -/

end Statlib.Imported
end

