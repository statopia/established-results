import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_2851629989_595f419e_3052f1ce
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
theorem statopia_math_node_480728362_b0f6f73a : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
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
              (beta / (m : ℝ)) * potSum Gammaih LG D u| ^ 4 *
            (UScale e lam (1 - st)).indicator
              (fun v : U =>
                Real.exp ((2 * eta) * ((beta * kappa * r) ^ 2 / (4 * delta1) +
                  delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2))) u
          ∂(Ptheta S theta))
        atTop (𝓝 0) ∧
    Tendsto
        (fun n : ℕ => ∫ u : U,
          |(beta / (m : ℝ)) * potSum Gammaih LG (Dn n) u -
              (beta / (m : ℝ)) * potSum Gammaih LG D u| ^ 2 *
            (UScale e lam (1 - st)).indicator
              (fun v : U =>
                Real.exp (eta * ((beta * kappa * r) ^ 2 / (4 * delta1) +
                  delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2))) u
          ∂(Ptheta S theta))
        atTop (𝓝 0) := by
  /- @proof-region region.target-node.session.ebeef85ae37e3133 begin -/
  intro U _ _ _ _ _ H _ _ _ X _ e lam hlam_pos hlam_anti Gamma hGamma_pos hGamma_inj Gammah
    hGammah_symm hGammah_pos hGammah_sq Gammaih hGammaih_left iotaH _ bH mu hmu_pos hmu_anti
    C1 hC1_pos hC1_inj hC1_eigen LG s0 s1 s st alpha hs0_nonneg hs0_lt hs1_nonneg hs1_lt hs_gt
    hs_le hst_gt hst_le halpha C1c C2c hC1c hC2c M1 hM1_mono hM1_nonneg M2 hM2_nonneg hM2_mono_fst
    hM2_mono_snd hA1 hA2 hA3 hA4 hLG_all_range beta hbeta m hm Nc hNc Theta1 _ _ _ _ _
    Ptheta hPtheta_isProb theta S mubar hmubar kappa hkappa h6 h7 h8 delta0 hdelta0 hmoment
    hdelta_meas hP_scale delta1 hdelta1 hdelta1_bound r hr D Dn hD_scale hDn_scale hD_rad hDn_rad
    hDn_tendsto Bbar hBbar rho hrho_meas hrho_dens hrhon_scale hrho_bound eta heta_pos heta_le
  let P : Measure U := Ptheta S theta
  let sc : Set U := UScale e lam (1 - st)
  let x : U → ℝ := fun u => (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2
  let A : ℝ := (beta * kappa * r) ^ 2 / (4 * delta1)
  let K : ℝ := beta * (4 * kappa * r + 2 * Real.rpow mubar st)
  haveI hPprob : IsProbabilityMeasure P := hPtheta_isProb S theta
  have hPsc : P sc = 1 := hP_scale
  have hK_nonneg : 0 ≤ K := by
    have hmub : (0 : ℝ) < mubar := by linarith
    have h2 : 0 < Real.rpow mubar st := Real.rpow_pos_of_pos hmub st
    have h1 : 0 ≤ 4 * kappa * r := by nlinarith [hkappa, hr]
    have h3 : 0 ≤ 4 * kappa * r + 2 * Real.rpow mubar st := by nlinarith
    exact mul_nonneg hbeta.le h3
  have hx_nonneg : ∀ u : U, 0 ≤ x u := fun u => sq_nonneg _
  have hUSN_meas : Measurable (fun u : U => UScaleNorm e lam (1 - st) u) := by
    have hterm : ∀ k : ℕ, Measurable (fun u : U =>
        ENNReal.ofReal (Real.rpow (lam k) (-(1 - st)) * (inner ℝ (e k) u) ^ 2)) := by
      intro k
      have hinner : Measurable (fun u : U => inner ℝ (e k) u) :=
        (continuous_inner.comp (continuous_const.prodMk continuous_id)).measurable
      have h2 : Measurable (fun u : U => (inner ℝ (e k) u) ^ 2) := by
        simpa [pow_two] using hinner.mul hinner
      exact (measurable_const.mul h2).ennreal_ofReal
    exact Measurable.ennreal_tsum hterm
  have hsc_meas : MeasurableSet sc := by
    have hIio : MeasurableSet (Set.Iio (⊤ : ℝ≥0∞)) := by
      have h : Set.Iio (⊤ : ℝ≥0∞) = {⊤}ᶜ := by
        ext a
        simp [lt_top_iff_ne_top]
      rw [h]
      exact MeasurableSet.compl (measurableSet_singleton ⊤)
    exact hUSN_meas hIio
  have hP_compl : P scᶜ = 0 := by
    have hfin : P sc ≠ ⊤ := by rw [hPsc]; exact ENNReal.one_ne_top
    rw [measure_compl hsc_meas hfin, hPsc, measure_univ]
    simp
  have hae_sc : ∀ᵐ u ∂P, u ∈ sc := by
    rw [MeasureTheory.ae_iff]
    have hset : {u : U | ¬ u ∈ sc} = scᶜ := rfl
    rw [hset, hP_compl]
  have hmeas := statopia_math_node_3916768571_a9930ecf U H X e lam hlam_pos hlam_anti Gamma
    hGamma_pos hGamma_inj Gammah hGammah_symm hGammah_pos hGammah_sq Gammaih hGammaih_left iotaH
    bH mu hmu_pos hmu_anti C1 hC1_pos hC1_inj hC1_eigen LG s0 s1 s st alpha hs0_nonneg hs0_lt
    hs1_nonneg hs1_lt hs_gt hs_le hst_gt hst_le halpha C1c C2c hC1c hC2c M1 hM1_mono hM1_nonneg
    M2 hM2_nonneg hM2_mono_fst hM2_mono_snd hA1 hA2 hA3 hA4 hLG_all_range beta hbeta m hm
  have hPS_meas : ∀ D' : Fin m → X × H, AEMeasurable (fun u : U => potSum Gammaih LG D' u) P := by
    intro D'
    exact (hmeas.2.2 D' (D ⟨0, hm⟩).1 (D ⟨0, hm⟩).2 P hPsc hP_compl).2.1
  have hE_meas : ∀ c : ℝ,
      AEMeasurable (sc.indicator (fun v : U => Real.exp (c * (A + delta1 * x v)))) P := by
    intro c
    have hbase : AEMeasurable (sc.indicator (fun v : U => Real.exp ((c * delta1) * x v))) P := by
      have h0 := hdelta_meas (c * delta1)
      simpa [x, sc, P] using h0
    have hpt : sc.indicator (fun v : U => Real.exp (c * (A + delta1 * x v)))
        = fun u : U =>
          Real.exp (c * A) * sc.indicator (fun v : U => Real.exp ((c * delta1) * x v)) u := by
      funext u
      by_cases hu : u ∈ sc
      · simp only [Set.indicator_of_mem hu, ← Real.exp_add]
        congr 1
        ring
      · simp [hu]
    rw [hpt]
    exact hbase.const_mul _
  have hexp1 : ∀ y : ℝ, 0 ≤ y → 1 + y ≤ (1 + delta1⁻¹) * Real.exp (delta1 * y) := by
    intro y hy
    have h1 : 1 + delta1 * y ≤ Real.exp (delta1 * y) := by
      have h := Real.add_one_le_exp (delta1 * y)
      linarith
    have h2 : (0 : ℝ) < 1 + delta1⁻¹ := by positivity
    have h3 : (1 + delta1⁻¹) * (1 + delta1 * y) ≤ (1 + delta1⁻¹) * Real.exp (delta1 * y) :=
      mul_le_mul_of_nonneg_left h1 h2.le
    have h4 : 1 + y ≤ (1 + delta1⁻¹) * (1 + delta1 * y) := by
      have hd1 : delta1⁻¹ * delta1 = 1 := by
        rw [← div_eq_inv_mul]
        exact div_self hdelta1.ne'
      have hdy : delta1⁻¹ * (delta1 * y) = y := by
        rw [← mul_assoc, hd1, one_mul]
      have e : (1 + delta1⁻¹) * (1 + delta1 * y) = 1 + y + (delta1 * y + delta1⁻¹) := by
        calc (1 + delta1⁻¹) * (1 + delta1 * y)
            = 1 + delta1 * y + delta1⁻¹ + delta1⁻¹ * (delta1 * y) := by ring
          _ = 1 + delta1 * y + delta1⁻¹ + y := by rw [hdy]
          _ = 1 + y + (delta1 * y + delta1⁻¹) := by ring
      have hnn : 0 ≤ delta1 * y + delta1⁻¹ := by
        have hy2 : 0 ≤ delta1 * y := mul_nonneg hdelta1.le hy
        have hinv : 0 < delta1⁻¹ := inv_pos.mpr hdelta1
        linarith
      linarith [e, hnn]
    linarith
  have hexp_pow : ∀ (p : ℕ) (y : ℝ), 0 ≤ y →
      (1 + y) ^ p ≤ (1 + delta1⁻¹) ^ p * Real.exp ((p : ℝ) * delta1 * y) := by
    intro p y hy
    have h1 := hexp1 y hy
    have hy1 : (0 : ℝ) ≤ 1 + y := by linarith
    have h2 : (1 + y) ^ p ≤ ((1 + delta1⁻¹) * Real.exp (delta1 * y)) ^ p :=
      pow_le_pow_left₀ hy1 h1 p
    have harg : (p : ℝ) * (delta1 * y) = (p : ℝ) * delta1 * y := by ring
    have h3 : ((1 + delta1⁻¹) * Real.exp (delta1 * y)) ^ p =
        (1 + delta1⁻¹) ^ p * Real.exp ((p : ℝ) * delta1 * y) := by
      rw [mul_pow, ← Real.exp_nat_mul, harg]
    linarith [h2, h3]
  let Δ : ℕ → U → ℝ := fun n u =>
    (beta / (m : ℝ)) * potSum Gammaih LG (Dn n) u - (beta / (m : ℝ)) * potSum Gammaih LG D u
  have hpot := statopia_math_node_3975929643_b00873c3 U H X Gammaih LG e lam iotaH bH mu hmu_pos
    M1 hM1_mono hM1_nonneg s st alpha m hm beta hbeta mubar kappa hmubar hkappa h6 h7 h8
  have main : ∀ (p : ℕ) (c : ℝ), 1 ≤ p → (p : ℝ) ≤ 4 → 0 ≤ c → c ≤ (p : ℝ) →
      Tendsto (fun n : ℕ => ∫ u : U,
          |Δ n u| ^ p * sc.indicator (fun v : U => Real.exp (c * (A + delta1 * x v))) u ∂P)
        atTop (𝓝 0) := by
    intro p c hp1 hp4 hc0 hcp
    let G : U → ℝ := fun u =>
      (K ^ p * (1 + delta1⁻¹) ^ p * Real.exp (c * A)) * Real.exp (2 * (p : ℝ) * delta1 * x u)
    have hdinv : (0 : ℝ) < 1 + delta1⁻¹ := by
      have := inv_pos.mpr hdelta1
      linarith
    have hCnn : 0 ≤ K ^ p * (1 + delta1⁻¹) ^ p :=
      mul_nonneg (pow_nonneg hK_nonneg p) (pow_nonneg hdinv.le p)
    have hBnn : 0 ≤ K ^ p * (1 + delta1⁻¹) ^ p * Real.exp (c * A) :=
      mul_nonneg hCnn (Real.exp_pos _).le
    have hunit : ∀ u : U, Real.exp ((p : ℝ) * delta1 * x u) * Real.exp ((p : ℝ) * delta1 * x u)
        = Real.exp (2 * (p : ℝ) * delta1 * x u) := by
      intro u
      rw [← Real.exp_add]
      congr 1
      ring
    have hbound : ∀ (n : ℕ) (u : U),
        |Δ n u| ^ p * sc.indicator (fun v : U => Real.exp (c * (A + delta1 * x v))) u ≤ G u := by
      intro n u
      by_cases hu : u ∈ sc
      · have hΔ : |Δ n u| ≤ K * (1 + x u) :=
          hpot.2.1 r hr (Dn n) D (fun j => hDn_scale n j) hD_scale (hDn_rad n) hD_rad u hu
        have h1 : |Δ n u| ^ p ≤
            K ^ p * (1 + delta1⁻¹) ^ p * Real.exp ((p : ℝ) * delta1 * x u) := by
          have hpp : |Δ n u| ^ p ≤ (K * (1 + x u)) ^ p :=
            pow_le_pow_left₀ (by positivity) hΔ p
          have hp2 : (K * (1 + x u)) ^ p = K ^ p * (1 + x u) ^ p := mul_pow _ _ _
          have hp3 : (1 + x u) ^ p ≤ (1 + delta1⁻¹) ^ p * Real.exp ((p : ℝ) * delta1 * x u) :=
            hexp_pow p (x u) (hx_nonneg u)
          have hp4' : K ^ p * (1 + x u) ^ p ≤
              K ^ p * ((1 + delta1⁻¹) ^ p * Real.exp ((p : ℝ) * delta1 * x u)) :=
            mul_le_mul_of_nonneg_left hp3 (pow_nonneg hK_nonneg p)
          calc |Δ n u| ^ p ≤ (K * (1 + x u)) ^ p := hpp
            _ = K ^ p * (1 + x u) ^ p := hp2
            _ ≤ K ^ p * ((1 + delta1⁻¹) ^ p * Real.exp ((p : ℝ) * delta1 * x u)) := hp4'
            _ = K ^ p * (1 + delta1⁻¹) ^ p * Real.exp ((p : ℝ) * delta1 * x u) := by ring
        have h2 : Real.exp (c * (A + delta1 * x u)) ≤
            Real.exp (c * A) * Real.exp ((p : ℝ) * delta1 * x u) := by
          have hdx : 0 ≤ delta1 * x u := mul_nonneg hdelta1.le (hx_nonneg u)
          have hstep : c * (delta1 * x u) ≤ (p : ℝ) * (delta1 * x u) :=
            mul_le_mul_of_nonneg_right hcp hdx
          have harg : c * (A + delta1 * x u) ≤ c * A + (p : ℝ) * delta1 * x u := by
            nlinarith [hstep]
          calc Real.exp (c * (A + delta1 * x u))
              ≤ Real.exp (c * A + (p : ℝ) * delta1 * x u) := Real.exp_le_exp.mpr harg
            _ = Real.exp (c * A) * Real.exp ((p : ℝ) * delta1 * x u) := Real.exp_add _ _
        have hbnn : 0 ≤ K ^ p * (1 + delta1⁻¹) ^ p * Real.exp ((p : ℝ) * delta1 * x u) :=
          mul_nonneg hCnn (Real.exp_pos _).le
        have hmul := mul_le_mul h1 h2 (Real.exp_pos _).le hbnn
        have hE : (K ^ p * (1 + delta1⁻¹) ^ p * Real.exp ((p : ℝ) * delta1 * x u)) *
            (Real.exp (c * A) * Real.exp ((p : ℝ) * delta1 * x u)) = G u := by
          show _ = (K ^ p * (1 + delta1⁻¹) ^ p * Real.exp (c * A)) *
            Real.exp (2 * (p : ℝ) * delta1 * x u)
          rw [← hunit u]
          ring
        rw [Set.indicator_of_mem hu]
        rw [hE] at hmul
        exact hmul
      · have hGnn : 0 ≤ G u := mul_nonneg hBnn (Real.exp_pos _).le
        have hzero : sc.indicator (fun v : U => Real.exp (c * (A + delta1 * x v))) u = 0 := by
          simp [hu]
        rw [hzero, mul_zero]
        exact hGnn
    have hGint : Integrable G P := by
      have hlt : 2 * (p : ℝ) * delta1 < delta0 := by
        nlinarith [hdelta1, hdelta1_bound, hp4]
      have hnn : 0 ≤ 2 * (p : ℝ) * delta1 := by
        have := Nat.cast_nonneg (α := ℝ) p
        nlinarith [hdelta1]
      exact (hmoment (2 * (p : ℝ) * delta1) hnn hlt).const_mul _
    have hF_meas : ∀ n : ℕ, AEStronglyMeasurable
        (fun u : U => |Δ n u| ^ p * sc.indicator (fun v : U => Real.exp (c * (A + delta1 * x v))) u)
        P := by
      intro n
      have hΔ_meas : AEMeasurable (fun u : U => Δ n u) P :=
        ((hPS_meas (Dn n)).const_mul (beta / (m : ℝ))).sub
          ((hPS_meas D).const_mul (beta / (m : ℝ)))
      exact ((hΔ_meas.abs.pow_const p).mul (hE_meas c)).aestronglyMeasurable
    have hdom : ∀ n : ℕ, ∀ᵐ u ∂P,
        ‖|Δ n u| ^ p * sc.indicator (fun v : U => Real.exp (c * (A + delta1 * x v))) u‖ ≤ G u := by
      intro n
      refine Filter.Eventually.of_forall (fun u => ?_)
      have hFnn : 0 ≤ |Δ n u| ^ p *
          sc.indicator (fun v : U => Real.exp (c * (A + delta1 * x v))) u := by
        have h1 : 0 ≤ |Δ n u| ^ p := by positivity
        have h2 : 0 ≤ sc.indicator (fun v : U => Real.exp (c * (A + delta1 * x v))) u := by
          by_cases hu : u ∈ sc
          · rw [Set.indicator_of_mem hu]
            exact (Real.exp_pos _).le
          · have hzero : sc.indicator (fun v : U => Real.exp (c * (A + delta1 * x v))) u = 0 := by
              simp [hu]
            rw [hzero]
        exact mul_nonneg h1 h2
      calc ‖|Δ n u| ^ p * sc.indicator (fun v : U => Real.exp (c * (A + delta1 * x v))) u‖
          = |Δ n u| ^ p * sc.indicator (fun v : U => Real.exp (c * (A + delta1 * x v))) u := by
            rw [Real.norm_eq_abs, abs_of_nonneg hFnn]
        _ ≤ G u := hbound n u
    have hconv : ∀ᵐ u ∂P, Tendsto
        (fun n : ℕ => |Δ n u| ^ p * sc.indicator (fun v : U => Real.exp (c * (A + delta1 * x v))) u)
        atTop (𝓝 0) := by
      filter_upwards [hae_sc] with u hu
      have hpt := hpot.2.2 hA4 Dn D hDn_scale hD_scale hDn_tendsto u hu
      have hΔ0 : Tendsto (fun n : ℕ => Δ n u) atTop (𝓝 0) := by
        have hc : Continuous (fun z : ℝ => z - (beta / (m : ℝ)) * potSum Gammaih LG D u) :=
          continuous_id.sub continuous_const
        have h1 : Tendsto (fun n : ℕ => (beta / (m : ℝ)) * potSum Gammaih LG (Dn n) u -
            (beta / (m : ℝ)) * potSum Gammaih LG D u) atTop (𝓝 0) := by
          have h2 := (hc.tendsto ((beta / (m : ℝ)) * potSum Gammaih LG D u)).comp hpt
          simpa using h2
        exact h1
      have hcont : Continuous (fun z : ℝ =>
          |z| ^ p * sc.indicator (fun v : U => Real.exp (c * (A + delta1 * x v))) u) :=
        (continuous_abs.pow p).mul continuous_const
      have h3 := (hcont.tendsto (0 : ℝ)).comp hΔ0
      have h0 : |(0 : ℝ)| ^ p *
          sc.indicator (fun v : U => Real.exp (c * (A + delta1 * x v))) u = 0 := by
        have hp0 : (0 : ℝ) ^ p = 0 := zero_pow (by omega)
        simp [hp0]
      rwa [h0] at h3
    have hmain := MeasureTheory.tendsto_integral_of_dominated_convergence (μ := P)
      (F := fun n : ℕ => fun u : U =>
        |Δ n u| ^ p * sc.indicator (fun v : U => Real.exp (c * (A + delta1 * x v))) u)
      (f := fun _ : U => (0 : ℝ)) G hF_meas hGint hdom hconv
    simpa using hmain
  refine ⟨?_, ?_⟩
  · exact main 4 (2 * eta) (by norm_num) (by norm_num) (by linarith) (by push_cast; linarith)
  · exact main 2 eta (by norm_num) (by norm_num) (by linarith) (by push_cast; linarith)
  /- @proof-region region.target-node.session.ebeef85ae37e3133 end -/

end Statlib.Imported
end

