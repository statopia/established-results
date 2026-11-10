import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_1729749604_be8e8033_a1908b89
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
theorem statopia_math_node_1912460074_9ad458a1 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
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
    (hrho_bound : ∀ n : ℕ, ∫⁻ u : U, (rho n u) ^ 2 ∂(Ptheta S theta) ≤ ENNReal.ofReal Bbar),
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
  /- @proof-region region.target-node.session.566026028fa72e05 begin -/
  intro U _ _ _ _ _ H _ _ _ X _ e lam hlam_pos hlam_anti Gamma hGamma_pos hGamma_inj Gammah hGammah_symm hGammah_pos hGammah_sq Gammaih hGammaih_left iotaH _ bH mu hmu_pos hmu_anti C1 hC1_pos hC1_inj hC1_eigen LG s0 s1 s st alpha hs0_nonneg hs0_lt hs1_nonneg hs1_lt hs_gt hs_le hst_gt hst_le halpha C1c C2c hC1c hC2c M1 hM1_mono hM1_nonneg M2 hM2_nonneg hM2_mono_fst hM2_mono_snd hA1 hA2 hA3 hA4 hLG_all_range beta hbeta m hm Nc hNc Theta1 _ _ _ _ _ Ptheta hPtheta_isProb theta S mubar hmubar kappa hkappa h6 h7 h8 delta0 hdelta0 hmoment hdelta_meas hP_scale delta1 hdelta1 hdelta1_bound r hr D Dn hD_scale hDn_scale hD_rad hDn_rad hDn_tendsto Bbar hBbar rho hrho_meas hrho_dens hrhon_scale hrho_bound
  haveI hprob : IsProbabilityMeasure (Ptheta S theta) := hPtheta_isProb S theta
  set A0 : ℝ := (beta * kappa * r) ^ 2 / (4 * delta1) with hA0
  set Mfun : U → ℝ := fun u => M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) with hMfun
  set Z : U → ℝ := fun v => A0 + delta1 * (Mfun v) ^ 2 with hZ
  set Δ : ℕ → U → ℝ :=
    fun n u => (beta / (m : ℝ)) * potSum Gammaih LG (Dn n) u - (beta / (m : ℝ)) * potSum Gammaih LG D u with hΔ
  set F : ℕ → U → ℝ :=
    fun n u => (Δ n u) ^ 2 * (UScale e lam (1 - st)).indicator (fun v => Real.exp (2 * Z v)) u with hF
  set G : ℕ → U → ℝ :=
    fun n u => |Δ n u| * (UScale e lam (1 - st)).indicator (fun v => Real.exp (1 * Z v)) u with hG
  have h397 := statopia_math_node_3975929643_b00873c3 U H X Gammaih LG e lam iotaH bH mu hmu_pos
    M1 hM1_mono hM1_nonneg s st alpha m hm beta hbeta mubar kappa hmubar hkappa h6 h7 h8
  have hbound : ∀ (n : ℕ) (u : U), UScale e lam (1 - st) u →
      |Δ n u| ≤ beta * (4 * kappa * r + 2 * Real.rpow mubar st) * (1 + (Mfun u) ^ 2) := by
    intro n u hu
    have h := h397.2.1 r hr (Dn n) D (hDn_scale n) hD_scale (hDn_rad n) hD_rad u hu
    simpa only [hΔ, hMfun] using h
  have hUSN_meas : Measurable (UScaleNorm e lam (1 - st)) := by
    apply Measurable.ennreal_tsum
    intro k
    apply Measurable.ennreal_ofReal
    have hinner : Continuous (fun u : U => inner ℝ (e k) u) :=
      continuous_inner.comp (continuous_const.prodMk continuous_id)
    exact (continuous_const.mul (hinner.pow 2)).measurable
  have hUScale_meas : MeasurableSet (UScale e lam (1 - st)) :=
    measurableSet_lt hUSN_meas measurable_const
  have hPne_top : (Ptheta S theta) (UScale e lam (1 - st)) ≠ ⊤ := by
    rw [hP_scale]; exact ENNReal.one_ne_top
  have hPcompl : (Ptheta S theta) ((UScale e lam (1 - st))ᶜ) = 0 := by
    rw [measure_compl hUScale_meas hPne_top, hP_scale, measure_univ, tsub_self]
  have h391 := statopia_math_node_3916768571_a9930ecf U H X e lam hlam_pos hlam_anti Gamma
    hGamma_pos hGamma_inj Gammah hGammah_symm hGammah_pos hGammah_sq Gammaih hGammaih_left iotaH bH
    mu hmu_pos hmu_anti C1 hC1_pos hC1_inj hC1_eigen LG s0 s1 s st alpha hs0_nonneg hs0_lt hs1_nonneg
    hs1_lt hs_gt hs_le hst_gt hst_le halpha C1c C2c hC1c hC2c M1 hM1_mono hM1_nonneg M2 hM2_nonneg
    hM2_mono_fst hM2_mono_snd hA1 hA2 hA3 hA4 hLG_all_range beta hbeta m hm
  have hPot_meas : ∀ D' : Fin m → X × H,
      AEMeasurable (fun u : U => potSum Gammaih LG D' u) (Ptheta S theta) := by
    intro D'
    exact (h391.2.2 D' (D ⟨0, hm⟩).1 (D ⟨0, hm⟩).2 (Ptheta S theta) hP_scale hPcompl).2.1
  have hΔ_meas : ∀ n : ℕ, AEMeasurable (fun u : U => Δ n u) (Ptheta S theta) := by
    intro n
    have h1 : AEMeasurable (fun u : U => (beta / (m : ℝ)) * potSum Gammaih LG (Dn n) u)
        (Ptheta S theta) := (hPot_meas (Dn n)).const_mul (beta / (m : ℝ))
    have h2 : AEMeasurable (fun u : U => (beta / (m : ℝ)) * potSum Gammaih LG D u)
        (Ptheta S theta) := (hPot_meas D).const_mul (beta / (m : ℝ))
    simpa only [hΔ] using h1.sub h2
  have hΔabs_meas : ∀ n : ℕ, AEMeasurable (fun u : U => |Δ n u|) (Ptheta S theta) := by
    intro n
    simpa only [Real.norm_eq_abs] using (hΔ_meas n).norm
  have hind_meas : AEMeasurable
      (fun u : U => (UScale e lam (1 - st)).indicator (fun v => Real.exp (1 * Z v)) u)
      (Ptheta S theta) := by
    have hb : AEMeasurable
        (fun u : U => Real.exp A0 * (UScale e lam (1 - st)).indicator
          (fun v => Real.exp (delta1 *
            (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)) u)
        (Ptheta S theta) :=
      (hdelta_meas delta1).const_mul (Real.exp A0)
    have heq : (fun u : U => Real.exp A0 * (UScale e lam (1 - st)).indicator
          (fun v => Real.exp (delta1 *
            (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)) u)
        = (fun u : U => (UScale e lam (1 - st)).indicator (fun v => Real.exp (1 * Z v)) u) := by
      funext u
      by_cases hu : u ∈ UScale e lam (1 - st)
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, ← Real.exp_add]
        congr 1
        simp only [hZ, hMfun, one_mul]
      · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, mul_zero]
    rw [heq] at hb
    exact hb
  have hpoly : ∀ y : ℝ, 0 ≤ y → (1 + y) ^ 2 ≤ (2 + 4 / delta1 ^ 2) * Real.exp (delta1 * y) := by
    intro y hy
    have hdy : 0 ≤ delta1 * y := mul_nonneg hdelta1.le hy
    have hfac : (delta1 * y) ^ 2 / 2 ≤ Real.exp (delta1 * y) := by
      have h := Real.pow_div_factorial_le_exp (delta1 * y) hdy 2
      simpa using h
    have hy2 : 2 * y ^ 2 ≤ (4 / delta1 ^ 2) * Real.exp (delta1 * y) := by
      have hle : (0 : ℝ) ≤ 4 / delta1 ^ 2 := div_nonneg (by norm_num) (sq_nonneg delta1)
      have hmul := mul_le_mul_of_nonneg_left hfac hle
      have heq : (4 / delta1 ^ 2) * ((delta1 * y) ^ 2 / 2) = 2 * y ^ 2 := by
        field_simp
        ring
      simpa only [heq] using hmul
    have hE : 1 ≤ Real.exp (delta1 * y) := Real.one_le_exp hdy
    have hEnn : 0 ≤ Real.exp (delta1 * y) := (Real.exp_pos _).le
    have hs1 : (1 + y) ^ 2 ≤ 2 + 2 * y ^ 2 := by nlinarith [sq_nonneg (1 - y)]
    nlinarith [hy2, hE, hEnn, hs1]
  have hF_nonneg : ∀ (n : ℕ) (u : U), 0 ≤ F n u := by
    intro n u
    by_cases hu : u ∈ UScale e lam (1 - st)
    · simp only [hF, Set.indicator_of_mem hu]
      positivity
    · simp only [hF, Set.indicator_of_notMem hu, mul_zero]
      exact le_rfl
  have hG_nonneg : ∀ (n : ℕ) (u : U), 0 ≤ G n u := by
    intro n u
    by_cases hu : u ∈ UScale e lam (1 - st)
    · simp only [hG, Set.indicator_of_mem hu]
      positivity
    · simp only [hG, Set.indicator_of_notMem hu, mul_zero]
      exact le_rfl
  have hFG : ∀ (n : ℕ) (u : U), F n u = (G n u) ^ 2 := by
    intro n u
    by_cases hu : u ∈ UScale e lam (1 - st)
    · have hexp : Real.exp (2 * Z u) = Real.exp (Z u) ^ 2 := by
        rw [show (2 : ℝ) * Z u = Z u + Z u by ring, Real.exp_add, sq]
      simp only [hF, hG, Set.indicator_of_mem hu, hexp, mul_pow, sq_abs, one_mul]
    · simp [hF, hG, Set.indicator_of_notMem hu]
  have hpt : ∀ (n : ℕ) (u : U), Real.sqrt (F n u) = G n u := by
    intro n u
    rw [hFG n u, Real.sqrt_sq (hG_nonneg n u)]
  have hG_meas : ∀ n : ℕ, AEMeasurable (G n) (Ptheta S theta) := by
    intro n
    have h2 : AEMeasurable (fun u : U => |Δ n u| *
        (UScale e lam (1 - st)).indicator (fun v => Real.exp (1 * Z v)) u) (Ptheta S theta) :=
      (hΔabs_meas n).mul hind_meas
    simpa only [hG] using h2
  have hG_aesm : ∀ n : ℕ, AEStronglyMeasurable (G n) (Ptheta S theta) := fun n =>
    (hG_meas n).aestronglyMeasurable
  have hF_aesm : ∀ n : ℕ, AEStronglyMeasurable (F n) (Ptheta S theta) := by
    intro n
    have h : F n = (fun u : U => G n u * G n u) := by
      funext u
      rw [hFG n u, sq]
    rw [h]
    exact (hG_aesm n).mul (hG_aesm n)
  have hpk := statopia_math_node_1729749604_be8e8033 U H X e lam hlam_pos hlam_anti Gamma
    hGamma_pos hGamma_inj Gammah hGammah_symm hGammah_pos hGammah_sq Gammaih hGammaih_left iotaH bH
    mu hmu_pos hmu_anti C1 hC1_pos hC1_inj hC1_eigen LG s0 s1 s st alpha hs0_nonneg hs0_lt hs1_nonneg
    hs1_lt hs_gt hs_le hst_gt hst_le halpha C1c C2c hC1c hC2c M1 hM1_mono hM1_nonneg M2 hM2_nonneg
    hM2_mono_fst hM2_mono_snd hA1 hA2 hA3 hA4 hLG_all_range beta hbeta m hm Nc hNc Theta1 Ptheta
    hPtheta_isProb theta S mubar hmubar kappa hkappa h6 h7 h8 delta0 hdelta0 hmoment hdelta_meas
    hP_scale delta1 hdelta1 hdelta1_bound r hr D Dn hD_scale hDn_scale hD_rad hDn_rad
  have hF_int : ∀ n : ℕ, Integrable (F n) (Ptheta S theta) := hpk.1
  have hF_sqrt_int : ∀ n : ℕ, Integrable (fun u : U => Real.sqrt (F n u)) (Ptheta S theta) :=
    hpk.2.1
  have hF_nonneg : ∀ (n : ℕ) (u : U), 0 ≤ F n u := hpk.2.2
  set_option maxHeartbeats 1600000 in
  have hgt := (statopia_math_node_480728362_b0f6f73a U H X e lam hlam_pos hlam_anti Gamma
    hGamma_pos hGamma_inj Gammah hGammah_symm hGammah_pos hGammah_sq Gammaih hGammaih_left iotaH bH
    mu hmu_pos hmu_anti C1 hC1_pos hC1_inj hC1_eigen LG s0 s1 s st alpha hs0_nonneg hs0_lt hs1_nonneg
    hs1_lt hs_gt hs_le hst_gt hst_le halpha C1c C2c hC1c hC2c M1 hM1_mono hM1_nonneg M2 hM2_nonneg
    hM2_mono_fst hM2_mono_snd hA1 hA2 hA3 hA4 hLG_all_range beta hbeta m hm Nc hNc Theta1 Ptheta
    hPtheta_isProb theta S mubar hmubar kappa hkappa h6 h7 h8 delta0 hdelta0 hmoment hdelta_meas
    hP_scale delta1 hdelta1 hdelta1_bound r hr D Dn hD_scale hDn_scale hD_rad hDn_rad hDn_tendsto
    Bbar hBbar rho hrho_meas hrho_dens hrhon_scale hrho_bound 2 (by norm_num) (by norm_num)).2
  have hF_tendsto : Tendsto (fun n : ℕ => ∫ u : U, F n u ∂(Ptheta S theta)) atTop (𝓝 0) := by
    have h2 := hgt
    simp only [sq_abs] at h2
    exact h2
  set_option maxHeartbeats 1600000 in
  have h203 := statopia_math_node_2035098161_9f60db94 U (Ptheta S theta)
    (fun n : ℕ => Ptheta (Dn n) theta) rho hrho_meas hrho_dens Bbar hBbar hrho_bound F hF_int
    hF_sqrt_int hF_nonneg hF_tendsto
  have hfun : (fun n : ℕ => ∫ u : U, Real.sqrt (F n u) ∂(Ptheta (Dn n) theta))
      = (fun n : ℕ => ∫ u : U, G n u ∂(Ptheta (Dn n) theta)) := by
    funext n
    exact integral_congr_ae (Filter.Eventually.of_forall (hpt n))
  rw [hfun] at h203
  simpa only [hG, hΔ, hZ, hMfun, hA0] using h203
  /- @proof-region region.target-node.session.566026028fa72e05 end -/

end Statlib.Imported
end

