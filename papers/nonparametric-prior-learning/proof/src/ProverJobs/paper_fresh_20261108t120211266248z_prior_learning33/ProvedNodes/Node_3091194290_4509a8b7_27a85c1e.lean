import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_2115369929_fddcacc3_34c4d4cd

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
theorem statopia_math_node_3091194290_4509a8b7 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [MeasurableSpace U] [BorelSpace U]
    (hU_infinite : ¬ FiniteDimensional ℝ U)
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H]
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X] [MeasurableSpace X]
    (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [TopologicalSpace.SeparableSpace Y] [MeasurableSpace Y]
    (iotaY : H →L[ℝ] Y) (hiotaY : ∀ v : H, ‖iotaY v‖ = ‖v‖)
    (m : ℕ) (hm : 0 < m)
    (Lx : X → H →L[ℝ] H) (Gop : U → H) (LG : X → U → H)
    (hLG : ∀ (x : X) (u : U), LG x u = Lx x (Gop u))
    (Gamma : H →L[ℝ] H) (hGamma_pos : Gamma.IsPositive)
    (hGamma_inj : ∀ v : H, Gamma v = 0 → v = 0)
    (Gammah : H →ₗ[ℝ] H)
    (hGammah_symm : ∀ v w : H, inner ℝ (Gammah v) w = inner ℝ v (Gammah w))
    (hGammah_pos : ∀ v : H, 0 ≤ inner ℝ v (Gammah v))
    (hGammah_sq : ∀ v : H, Gammah (Gammah v) = Gamma v)
    (Gammaih : H → H) (hGammaih_left : ∀ v : H, Gammaih (Gammah v) = v)
    (e : HilbertBasis ℕ ℝ U) (lam : ℕ → ℝ)
    (hlam_pos : ∀ k : ℕ, 0 < lam k) (hlam_anti : Antitone lam)
    (C0 : U →L[ℝ] U) (hC0_pos : C0.IsPositive)
    (hC0_inj : ∀ u : U, C0 u = 0 → u = 0)
    (hC0_basis : ∀ k : ℕ, C0 (e k) = lam k • e k)
    (hC0_expand : ∀ u : U, HasSum (fun k : ℕ => (lam k * inner ℝ (e k) u) • e k) (C0 u))
    (hC0_trace : Summable lam)
    (s0 : ℝ) (hs0_nonneg : 0 ≤ s0) (hs0_lt : s0 < 1)
    (hs0_trace : ∀ t : ℝ, s0 < t → Summable (fun k : ℕ => Real.rpow (lam k) t))
    (C1 : H →L[ℝ] H) (hC1_pos : C1.IsPositive)
    (hC1_inj : ∀ v : H, C1 v = 0 → v = 0)
    (hC1_comm : C1.comp Gamma = Gamma.comp C1)
    (iotaH : Type*) [Preorder iotaH] (bH : HilbertBasis iotaH ℝ H) (mu : iotaH → ℝ)
    (hmu_pos : ∀ i : iotaH, 0 < mu i) (hmu_anti : Antitone mu)
    (hC1_eigen : ∀ i : iotaH, C1 (bH i) = mu i • bH i)
    (C1s : ℝ → H → H) (hC1s_one : C1s 1 = fun v => C1 v)
    (hC1s_eigen : ∀ (t : ℝ) (i : iotaH), C1s t (bH i) = Real.rpow (mu i) t • bH i)
    (s1 : ℝ) (hs1_nonneg : 0 ≤ s1) (hs1_lt : s1 < 1)
    (hs1_trace : ∀ t : ℝ, s1 < t → Summable (fun i : iotaH => inner ℝ (bH i) ((C1s t) (bH i))))
    (Nc : ℕ) (hNc : 0 < Nc)
    (Theta1 : Type*) [NormedAddCommGroup Theta1] [InnerProductSpace ℝ Theta1] [CompleteSpace Theta1]
    [TopologicalSpace.SeparableSpace Theta1] [MeasurableSpace Theta1]
    [MeasurableSpace (Fin Nc → ℝ)]
    (P1 : Measure Theta1) [IsProbabilityMeasure P1]
    (P2 : Measure (Fin Nc → ℝ)) [IsProbabilityMeasure P2]
    (thetaMin thetaMax : ℝ) (hthetaMin_lt : thetaMin < thetaMax)
    (hP2_support : ∀ᵐ t ∂P2, ∀ k : Fin Nc, thetaMin ≤ t k ∧ t k ≤ thetaMax)
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
    (Omega : Type*) [MeasurableSpace Omega] (muOmega : Measure Omega) [IsProbabilityMeasure muOmega]
    (uDagger : U)
    (D : Measure (X × Y)) [IsProbabilityMeasure D]
    (eta : Fin m → Omega → H → ℝ)
    (heta_lin : ∀ (j : Fin m) (omega : Omega) (a b : ℝ) (v w : H),
      eta j omega (a • v + b • w) = a * eta j omega v + b * eta j omega w)
    (heta_gauss : ∀ (j : Fin m) (v : H),
      Measure.map (fun omega : Omega => eta j omega v) muOmega =
        gaussianReal 0 (Real.toNNReal (inner ℝ v (Gamma v))))
    (heta_indep : iIndepFun (fun j : Fin m => eta j) muOmega)
    (Zobs : Fin m → Omega → X × Y) (hZobs : ∀ j : Fin m, Measurable (Zobs j))
    (hsample_law : Measure.map (fun omega => fun j : Fin m => Zobs j omega) muOmega
      = Measure.pi (fun _ : Fin m => D))
    (s st alpha : ℝ) (hs_gt : s1 < s) (hs_le : s ≤ 1) (hst_gt : s0 < st) (hst_le : st ≤ 1)
    (halpha : 0 ≤ alpha)
    (C1c C2c : ℝ) (hC1c : 0 < C1c) (hC2c : 0 < C2c)
    (M1 : ℝ → ℝ) (hM1_mono : Monotone M1) (hM1_nonneg : ∀ r : ℝ, 0 ≤ M1 r)
    (M2 : ℝ → ℝ → ℝ) (hM2_nonneg : ∀ r1 r2 : ℝ, 0 ≤ M2 r1 r2)
    (hM2_mono_fst : ∀ r2 : ℝ, Monotone (fun r : ℝ => M2 r r2))
    (hM2_mono_snd : ∀ r1 : ℝ, Monotone (fun r : ℝ => M2 r1 r))
    (hA1 : (¬ FiniteDimensional ℝ H) → ∀ (w : H) (rho : ℝ), HScale bH mu (alpha - s) w →
      ((Int.floor (alpha - s1 - 1) : ℤ) : ℝ) ≤ rho → rho < alpha - s1 →
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
    (beta : ℝ) (hbeta : 0 < beta)
    (theta : Theta1 × (Fin Nc → ℝ))
    (S : Fin m → X × H)
    (hS_scale : ∀ j : Fin m, HScale bH mu (alpha - s) (S j).2)
    (omega0 : Omega) (hS_real_x : ∀ j : Fin m, (S j).1 = (Zobs j omega0).1)
    (hS_real_y : ∀ j : Fin m, iotaY (S j).2 = (Zobs j omega0).2)
    (hmodel : ∀ (j : Fin m) (v : H),
      inner ℝ v (S j).2 = inner ℝ v (LG (S j).1 uDagger) + eta j omega0 v)
    (hS_range : ∀ j : Fin m, ∃ w : H, Gammah w = (S j).2)
    (hLG_range : ∀ (S' : Fin m → X × H) (theta' : Theta1 × (Fin Nc → ℝ)),
      ∀ᵐ u ∂(Ptheta S' theta'), ∀ j : Fin m, ∃ w : H, Gammah w = LG (S' j).1 u)
    (hLG_all_range : ∀ (x : X) (u : U), UScale e lam (1 - st) u → ∃ w : H, Gammah w = LG x u)
    (hHsub : ∀ w : H, HScale bH mu (alpha - s) w → ∃ a : H, Gammah a = w)
    (hdelta_meas : ∀ delta : ℝ,
      AEMeasurable (fun u : U => momentExpENN M1 delta (UScaleDist e lam (1 - st) u 0))
        (Ptheta S theta))
    (hdelta : ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ delta : ℝ, 0 ≤ delta → delta < delta0 →
      (∫⁻ u : U, momentExpENN M1 delta (UScaleDist e lam (1 - st) u 0) ∂(Ptheta S theta)) ≠ ⊤)
    (hMgrowth : ∃ M : ℝ → ℝ, Monotone M ∧ (∀ r : ℝ, 0 ≤ M r) ∧ ∀ r : ℝ,
      (∀ j : Fin m, (HScaleNorm bH mu (alpha - s) (S j).2) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal r) →
        UScale e lam (1 + st) (fm S theta.1) ∧
        (UScaleNorm e lam (1 + st) (fm S theta.1)) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (M r))
    (hfm_cont : Tendsto (fun S' : Fin m → X × H =>
        UScaleDist e lam (1 + st) (fm S' theta.1) (fm S theta.1))
      (dataNhds (fun z : H => (HScaleNorm bH mu (alpha - s) z) ^ (1 / 2 : ℝ))
        (HScale bH mu (alpha - s)) S) (𝓝 0))
    (hPhi_meas : ∀ j : Fin m,
      AEMeasurable (fun u : U => Phi Gammaih LG u (S j).1 (S j).2) (Ptheta S theta))
    (hdens_meas : AEMeasurable (fun u : U => temperedDens beta m Gammaih LG S u) (Ptheta S theta)),
    (∀ (sigma : ℝ) (Dd : Fin m → X × H), s0 < sigma → sigma ≤ 1 →
        UScale e lam 1 (fm Dd theta.1) →
        (Ptheta Dd theta) (UScale e lam (1 - sigma)) = 1) ∧
      (∀ (Dd : Fin m → X × H), (Ptheta Dd theta) (UScale e lam (1 - st)) = 1) ∧
      (∀ (delta0 : ℝ), 0 < delta0 →
        (∀ (delta : ℝ), 0 ≤ delta → delta < delta0 →
          (∫⁻ u : U, momentExpENN M1 delta (UScaleDist e lam (1 - st) u 0)
            ∂(Ptheta S theta)) ≠ ⊤) →
        ∀ (delta : ℝ), 0 ≤ delta → delta < delta0 →
          Integrable (fun u : U =>
            Real.exp (delta * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2))
            (Ptheta S theta)) := by
  /- @proof-region region.target-node.session.22fa643528c6abf1 begin -/
  rintro U _ _ _ _ _ _ hU_infinite H _ _ _ _ _ _ X _ _ _ _ _ Y _ _ _ _ _ iotaY hiotaY m hm
    Lx Gop LG hLG
  rintro Gamma hGamma_pos hGamma_inj Gammah hGammah_symm hGammah_pos hGammah_sq Gammaih
    hGammaih_left e lam hlam_pos hlam_anti C0 hC0_pos hC0_inj hC0_basis hC0_expand hC0_trace
  rintro s0 hs0_nonneg hs0_lt hs0_trace C1 hC1_pos hC1_inj hC1_comm iotaH _ bH mu hmu_pos hmu_anti
    hC1_eigen C1s hC1s_one hC1s_eigen s1 hs1_nonneg hs1_lt hs1_trace
  rintro Nc hNc Theta1 _ _ _ _ _ _ P1 _ P2 _ thetaMin thetaMax hthetaMin_lt hP2_support C0th
    hC0th_basis hC0th_expand
  rintro R_u hR_u fm Ptheta hPtheta_isProb hPtheta_gauss hPtheta_mean hPtheta_cov hPtheta_int1
    hPtheta_int2 hfm_ball
  rintro Omega _ muOmega _ uDagger D _ eta heta_lin heta_gauss heta_indep Zobs hZobs hsample_law
  rintro s st alpha hs_gt hs_le hst_gt hst_le halpha C1c C2c hC1c hC2c M1 hM1_mono hM1_nonneg M2
    hM2_nonneg hM2_mono_fst hM2_mono_snd
  rintro hA1 hA2 hA3 hA4 beta hbeta theta S hS_scale omega0 hS_real_x hS_real_y hmodel hS_range
    hLG_range hLG_all_range hHsub hdelta_meas hdelta hMgrowth hfm_cont hPhi_meas hdens_meas
  refine ⟨?_, ?_, ?_⟩
  · intro sigma Dd hσ0 hσ1 hm
    haveI : IsProbabilityMeasure (Ptheta Dd theta) := hPtheta_isProb Dd theta
    have h := statopia_math_node_2115369929_fddcacc3 U e lam hlam_pos hlam_anti hC0_trace s0
      hs0_nonneg hs0_lt hs0_trace Nc hNc theta.2 C0th (fun k => hC0th_basis theta.2 k)
    exact h.2 (fm Dd theta.1) (Ptheta Dd theta) (hPtheta_mean Dd theta) (hPtheta_cov Dd theta)
      (hPtheta_int1 Dd theta) (hPtheta_int2 Dd theta) sigma hσ0 hσ1 hm
  · intro Dd
    haveI : IsProbabilityMeasure (Ptheta Dd theta) := hPtheta_isProb Dd theta
    have h := statopia_math_node_2115369929_fddcacc3 U e lam hlam_pos hlam_anti hC0_trace s0
      hs0_nonneg hs0_lt hs0_trace Nc hNc theta.2 C0th (fun k => hC0th_basis theta.2 k)
    have h1 : UScale e lam 1 (fm Dd theta.1) := h.1 (fm Dd theta.1) (hfm_ball Dd theta).1
    exact h.2 (fm Dd theta.1) (Ptheta Dd theta) (hPtheta_mean Dd theta) (hPtheta_cov Dd theta)
      (hPtheta_int1 Dd theta) (hPtheta_int2 Dd theta) st hst_gt hst_le h1
  · intro delta0 hdelta0 hne delta hdelta_nonneg hdelta_lt
    let mu0 : Measure U := Ptheta S theta
    let r0 : U → ℝ≥0∞ := fun u => UScaleDist e lam (1 - st) u 0
    change Integrable (fun u : U => Real.exp (delta * (M1 ((r0 u).toReal)) ^ 2)) mu0
    have hne' : (∫⁻ u : U, momentExpENN M1 delta (r0 u) ∂mu0) ≠ ⊤ :=
      hne delta hdelta_nonneg hdelta_lt
    obtain ⟨g, hgmeas, hgeq⟩ : ∃ g : U → ℝ≥0∞, Measurable g ∧
        (fun u : U => momentExpENN M1 delta (r0 u)) =ᵐ[mu0] g :=
      ⟨(hdelta_meas delta).mk, (hdelta_meas delta).measurable_mk, (hdelta_meas delta).ae_eq_mk⟩
    have hgint : (∫⁻ u : U, g u ∂mu0) ≠ ⊤ := by
      rw [← lintegral_congr_ae hgeq]
      exact hne'
    have hgfin : ∀ᵐ u ∂mu0, g u < ⊤ := ae_lt_top hgmeas hgint
    have hmem : ∀ᵐ u ∂mu0, r0 u < ⊤ := by
      filter_upwards [hgfin, hgeq] with u hu heq
      by_contra hcon
      have htop : momentExpENN M1 delta (r0 u) = ⊤ := by
        unfold momentExpENN
        rw [dif_neg hcon]
      rw [← heq, htop] at hu
      exact absurd hu (lt_irrefl ⊤)
    have hInt : Integrable (fun u : U => (momentExpENN M1 delta (r0 u)).toReal) mu0 :=
      MeasureTheory.integrable_toReal_of_lintegral_ne_top (hdelta_meas delta) hne'
    refine hInt.congr ?_
    filter_upwards [hmem] with u hu
    show (momentExpENN M1 delta (r0 u)).toReal
      = Real.exp (delta * (M1 ((r0 u).toReal)) ^ 2)
    unfold momentExpENN
    rw [dif_pos hu, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  /- @proof-region region.target-node.session.22fa643528c6abf1 end -/

end Statlib.Imported
end

