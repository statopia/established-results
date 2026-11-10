import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base

namespace PaperProofTasks.paper_fresh_20261108t120211266248z_prior_learning33

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

theorem Theorem_3_3_Bayesian_Well_Posedness_of_Inverse_Problems_posterior_density_positive_finite_normalizer_and_Hellinger_conti
    
    (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [MeasurableSpace U] [BorelSpace U]
    (hU_infinite : ¬ FiniteDimensional ℝ U)
    
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H]
    
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X] [MeasurableSpace X]
    (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [TopologicalSpace.SeparableSpace Y] [MeasurableSpace Y]
    (ιY : H →L[ℝ] Y) (hιY : ∀ v : H, ‖ιY v‖ = ‖v‖)
    
    (m : ℕ) (hm : 0 < m)
    
    (Lx : X → H →L[ℝ] H) (Gop : U → H) (LG : X → U → H)
    (hLG : ∀ (x : X) (u : U), LG x u = Lx x (Gop u))
    
    
    
    
    
    
    
    
    
    (Γ : H →L[ℝ] H) (hΓ_pos : Γ.IsPositive) (hΓ_inj : ∀ v : H, Γ v = 0 → v = 0)
    (Γh : H →ₗ[ℝ] H)
    (hΓh_symm : ∀ v w : H, inner ℝ (Γh v) w = inner ℝ v (Γh w))
    (hΓh_pos : ∀ v : H, 0 ≤ inner ℝ v (Γh v))
    (hΓh_sq : ∀ v : H, Γh (Γh v) = Γ v)
    (Γih : H → H) (hΓih_left : ∀ v : H, Γih (Γh v) = v)
    
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
    (hC1_comm : C1.comp Γ = Γ.comp C1)
    (ιH : Type*) [Preorder ιH] (bH : HilbertBasis ιH ℝ H) (mu : ιH → ℝ)
    (hmu_pos : ∀ i : ιH, 0 < mu i) (hmu_anti : Antitone mu)
    (hC1_eigen : ∀ i : ιH, C1 (bH i) = mu i • bH i)
    
    
    (C1s : ℝ → H → H) (hC1s_one : C1s 1 = fun v => C1 v)
    (hC1s_eigen : ∀ (t : ℝ) (i : ιH), C1s t (bH i) = Real.rpow (mu i) t • bH i)
    (s1 : ℝ) (hs1_nonneg : 0 ≤ s1) (hs1_lt : s1 < 1)
    (hs1_trace : ∀ t : ℝ, s1 < t → Summable (fun i : ιH => inner ℝ (bH i) ((C1s t) (bH i))))
    
    (Nc : ℕ) (hNc : 0 < Nc)
    (Θ1 : Type*) [NormedAddCommGroup Θ1] [InnerProductSpace ℝ Θ1] [CompleteSpace Θ1]
    [TopologicalSpace.SeparableSpace Θ1] [MeasurableSpace Θ1]
    [MeasurableSpace (Fin Nc → ℝ)]
    (P1 : Measure Θ1) [IsProbabilityMeasure P1]
    (P2 : Measure (Fin Nc → ℝ)) [IsProbabilityMeasure P2]
    (θmin θmax : ℝ) (hθmin_lt : θmin < θmax)
    (hP2_support : ∀ᵐ t ∂P2, ∀ k : Fin Nc, θmin ≤ t k ∧ t k ≤ θmax)
    
    (C0th : (Fin Nc → ℝ) → U →L[ℝ] U)
    (hC0th_basis : ∀ (θ2 : Fin Nc → ℝ) (k : ℕ), C0th θ2 (e k) = priorEigen lam Nc θ2 k • e k)
    (hC0th_expand : ∀ (θ2 : Fin Nc → ℝ) (u : U),
      HasSum (fun k : ℕ => (priorEigen lam Nc θ2 k * inner ℝ (e k) u) • e k) (C0th θ2 u))
    
    
    (R_u : ℝ) (hR_u : 0 < R_u)
    (fm : (Fin m → X × H) → Θ1 → U)
    (Ptheta : (Fin m → X × H) → (Θ1 × (Fin Nc → ℝ)) → Measure U)
    (hPtheta_isProb : ∀ (S : Fin m → X × H) (θ : Θ1 × (Fin Nc → ℝ)),
      IsProbabilityMeasure (Ptheta S θ))
    (hPtheta_gauss : ∀ (S : Fin m → X × H) (θ : Θ1 × (Fin Nc → ℝ)),
      ProbabilityTheory.IsGaussian (Ptheta S θ))
    (hPtheta_mean : ∀ (S : Fin m → X × H) (θ : Θ1 × (Fin Nc → ℝ)) (v : U),
      ∫ u, inner ℝ v u ∂(Ptheta S θ) = inner ℝ v (fm S θ.1))
    (hPtheta_cov : ∀ (S : Fin m → X × H) (θ : Θ1 × (Fin Nc → ℝ)) (v w : U),
      ∫ u, (inner ℝ v u - inner ℝ v (fm S θ.1)) * (inner ℝ w u - inner ℝ w (fm S θ.1))
        ∂(Ptheta S θ) = inner ℝ v (C0th θ.2 w))
    
    
    (hPtheta_int1 : ∀ (S : Fin m → X × H) (θ : Θ1 × (Fin Nc → ℝ)) (v : U),
      Integrable (fun u : U => inner ℝ v u) (Ptheta S θ))
    (hPtheta_int2 : ∀ (S : Fin m → X × H) (θ : Θ1 × (Fin Nc → ℝ)) (v w : U),
      Integrable (fun u : U =>
        (inner ℝ v u - inner ℝ v (fm S θ.1)) * (inner ℝ w u - inner ℝ w (fm S θ.1)))
        (Ptheta S θ))
    (hfm_ball : ∀ (S : Fin m → X × H) (θ : Θ1 × (Fin Nc → ℝ)),
      UScale e lam 2 (fm S θ.1) ∧
      (UScaleNorm e lam 2 (fm S θ.1)) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal R_u)
    
    (Ω : Type*) [MeasurableSpace Ω] (μΩ : Measure Ω) [IsProbabilityMeasure μΩ]
    (uDagger : U)
    (D : Measure (X × Y)) [IsProbabilityMeasure D]
    
    
    
    
    
    (η : Fin m → Ω → H → ℝ)
    (hη_lin : ∀ (j : Fin m) (ω : Ω) (a b : ℝ) (v w : H),
      η j ω (a • v + b • w) = a * η j ω v + b * η j ω w)
    (hη_gauss : ∀ (j : Fin m) (v : H),
      Measure.map (fun ω : Ω => η j ω v) μΩ = gaussianReal 0 (Real.toNNReal (inner ℝ v (Γ v))))
    
    
    
    (hη_indep : iIndepFun (fun j : Fin m => η j) μΩ)

    
    
    (Zobs : Fin m → Ω → X × Y) (hZobs : ∀ j : Fin m, Measurable (Zobs j))
    (hsample_law : Measure.map (fun ω => fun j : Fin m => Zobs j ω) μΩ
      = Measure.pi (fun _ : Fin m => D))

    
    (s st α : ℝ) (hs_gt : s1 < s) (hs_le : s ≤ 1) (hst_gt : s0 < st) (hst_le : st ≤ 1)
    (hα : 0 ≤ α)
    (C1c C2c : ℝ) (hC1c : 0 < C1c) (hC2c : 0 < C2c)
    (M1 : ℝ → ℝ) (hM1_mono : Monotone M1) (hM1_nonneg : ∀ r : ℝ, 0 ≤ M1 r)
    (M2 : ℝ → ℝ → ℝ) (hM2_nonneg : ∀ r1 r2 : ℝ, 0 ≤ M2 r1 r2)
    (hM2_mono_fst : ∀ r2 : ℝ, Monotone (fun r : ℝ => M2 r r2))
    (hM2_mono_snd : ∀ r1 : ℝ, Monotone (fun r : ℝ => M2 r1 r))
    
    
    
    (hA1 : (¬ FiniteDimensional ℝ H) → ∀ (w : H) (ρ : ℝ), HScale bH mu (α - s) w →
      ((Int.floor (α - s1 - 1) : ℤ) : ℝ) ≤ ρ → ρ < α - s1 →
      HScale bH mu (-st) (Γih w) ∧ HScale bH mu st (Γh w) ∧ HScale bH mu (ρ - α) w ∧
      (HScaleNorm bH mu (-st) (Γih w)) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal C1c * (HScaleNorm bH mu (α - s) w) ^ (1 / 2 : ℝ) ∧
      (HScaleNorm bH mu st (Γh w)) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal C2c * (HScaleNorm bH mu (ρ - α) w) ^ (1 / 2 : ℝ))
    (hA2 : ∀ (x : X) (u : U), UScale e lam (1 - st) u →
      (HScaleNorm bH mu st (Γih (LG x u))) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))))
    (hA3 : ∀ (x : X) (u1 u2 : U), UScale e lam (1 - st) u1 → UScale e lam (1 - st) u2 →
      UScale e lam (1 - st) (u1 - u2) →
      (HScaleNorm bH mu st (Γih (LG x u1 - LG x u2))) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (M2 (ENNReal.toReal (UScaleDist e lam (1 - st) u1 0))
            (ENNReal.toReal (UScaleDist e lam (1 - st) u2 0))) *
          UScaleDist e lam (1 - st) (u1 - u2) 0)
    (hA4 : ∀ (x' : X) (u : U), UScale e lam (1 - st) u →
      Tendsto (fun x : X => (HScaleNorm bH mu st (Γih (LG x u - LG x' u))) ^ (1 / 2 : ℝ))
        (𝓝 x') (𝓝 0))
    
    (β : ℝ) (hβ : 0 < β)
    
    (θ : Θ1 × (Fin Nc → ℝ))
    (S : Fin m → X × H)
    (hS_scale : ∀ j : Fin m, HScale bH mu (α - s) (S j).2)

    
    (ω₀ : Ω) (hS_real_x : ∀ j : Fin m, (S j).1 = (Zobs j ω₀).1)
    (hS_real_y : ∀ j : Fin m, ιY (S j).2 = (Zobs j ω₀).2)
    
    
    
    
    (hmodel : ∀ (j : Fin m) (v : H),
      inner ℝ v (S j).2 = inner ℝ v (LG (S j).1 uDagger) + η j ω₀ v)
    
    
    
    
    
    
    
    
    
    
    (hS_range : ∀ j : Fin m, ∃ w : H, Γh w = (S j).2)
    (hLG_range : ∀ (S' : Fin m → X × H) (θ' : Θ1 × (Fin Nc → ℝ)),
      ∀ᵐ u ∂(Ptheta S' θ'), ∀ j : Fin m, ∃ w : H, Γh w = LG (S' j).1 u)
    
    
    (hLG_all_range : ∀ (x : X) (u : U), UScale e lam (1 - st) u → ∃ w : H, Γh w = LG x u)
    
    
    
    
    
    
    (hHsub : ∀ w : H, HScale bH mu (α - s) w → ∃ a : H, Γh a = w)


    
    
    (hδ_meas : ∀ δ : ℝ,
      AEMeasurable (fun u : U => momentExpENN M1 δ (UScaleDist e lam (1 - st) u 0))
        (Ptheta S θ))

    
    
    
    
    
    
    
    
    (hδ : ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ δ : ℝ, 0 ≤ δ → δ < δ0 →
      (∫⁻ u : U, momentExpENN M1 δ (UScaleDist e lam (1 - st) u 0) ∂(Ptheta S θ)) ≠ ⊤)

    
    
    
    (hMgrowth : ∃ M : ℝ → ℝ, Monotone M ∧ (∀ r : ℝ, 0 ≤ M r) ∧ ∀ r : ℝ,
      (∀ j : Fin m, (HScaleNorm bH mu (α - s) (S j).2) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal r) →
        UScale e lam (1 + st) (fm S θ.1) ∧
        (UScaleNorm e lam (1 + st) (fm S θ.1)) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (M r))
    
    (hfm_cont : Tendsto (fun S' : Fin m → X × H =>
        UScaleDist e lam (1 + st) (fm S' θ.1) (fm S θ.1))
      (dataNhds (fun z : H => (HScaleNorm bH mu (α - s) z) ^ (1 / 2 : ℝ))
        (HScale bH mu (α - s)) S) (𝓝 0))
    
    (hPhi_meas : ∀ j : Fin m,
      AEMeasurable (fun u : U => Phi Γih LG u (S j).1 (S j).2) (Ptheta S θ))

    
    (hdens_meas : AEMeasurable (fun u : U => temperedDens β m Γih LG S u) (Ptheta S θ))
    
    : MeasureTheory.Measure.AbsolutelyContinuous
        (Qpost β m Γih LG (Ptheta S θ) S) (Ptheta S θ) ∧
      (∀ᵐ u ∂(Ptheta S θ),
        (Qpost β m Γih LG (Ptheta S θ) S).rnDeriv (Ptheta S θ) u
          = ENNReal.ofReal ((Zm β m Γih LG (Ptheta S θ) S)⁻¹ * temperedDens β m Γih LG S u)) ∧
      0 < Zm β m Γih LG (Ptheta S θ) S ∧
      Integrable (fun u : U => temperedDens β m Γih LG S u) (Ptheta S θ) ∧
      Tendsto (fun S' : Fin m → X × H =>
            hellingerDist (Qpost β m Γih LG (Ptheta S θ) S) (Qpost β m Γih LG (Ptheta S' θ) S'))
          (dataNhds (fun z : H => (HScaleNorm bH mu (α - s) z) ^ (1 / 2 : ℝ))
            (HScale bH mu (α - s)) S)
          (𝓝 0)
:= by
  /- @proof-region region.root.bf58e61c8834 begin -/
  obtain ⟨mubar, hmubar, kappa, hkappa, hPhi_lower, hPhi_upper⟩ :=
    statopia_math_node_3294149986_d09fdee2 U H X e lam hlam_pos ιH bH mu hmu_pos C1 hC1_eigen
      Γ hΓ_pos hΓ_inj Γh hΓh_symm hΓh_pos hΓh_sq Γih hΓih_left LG s0 s1 s st α
      hs0_nonneg hs0_lt hs1_nonneg hs1_lt hs_gt hs_le hst_gt hst_le hα C1c hC1c M1
      hM1_mono hM1_nonneg
      (fun hinf w ρ hw h1 h2 =>
        ⟨(hA1 hinf w ρ hw h1 h2).1, (hA1 hinf w ρ hw h1 h2).2.2.2.1⟩)
      hA2
  haveI : IsProbabilityMeasure (Ptheta S θ) := hPtheta_isProb S θ
  obtain ⟨delta0, hdelta0_pos, hscale, hmoment_int⟩ :=
    statopia_math_node_2395645464_8193eae1 U e lam hlam_pos s0 st hs0_nonneg hs0_lt hst_gt
      hst_le M1 hM1_mono hM1_nonneg (Ptheta S θ) hδ
  have hdelta1_pos : 0 < delta0 / 32 := by linarith
  have hdelta1_lt : 8 * (delta0 / 32) < delta0 := by linarith
  set r : ℝ :=
    1 + Finset.univ.sum
      (fun j : Fin m => ((HScaleNorm bH mu (α - s) (S j).2) ^ (1 / 2 : ℝ)).toReal) with hrdef
  have hr : 0 ≤ r := by
    rw [hrdef]
    exact add_nonneg zero_le_one (Finset.sum_nonneg (fun i _ => ENNReal.toReal_nonneg))
  have hD : ∀ j : Fin m, (HScaleNorm bH mu (α - s) (S j).2) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal r := by
    intro j
    have hlt : (HScaleNorm bH mu (α - s) (S j).2) ^ (1 / 2 : ℝ) < ⊤ :=
      (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).2 (hS_scale j)
    have hle : ((HScaleNorm bH mu (α - s) (S j).2) ^ (1 / 2 : ℝ)).toReal ≤ r := by
      have hs := Finset.single_le_sum
        (f := fun i : Fin m => ((HScaleNorm bH mu (α - s) (S i).2) ^ (1 / 2 : ℝ)).toReal)
        (fun i _ => ENNReal.toReal_nonneg) (Finset.mem_univ j)
      rw [hrdef]
      linarith
    exact (ENNReal.ofReal_toReal hlt.ne).symm.trans_le (ENNReal.ofReal_le_ofReal hle)
  haveI : IsProbabilityMeasure (Ptheta S θ) := hPtheta_isProb S θ
  obtain ⟨_, hInteg, hZpos, _, _, hAC, hdens⟩ :=
    statopia_math_node_1220214867_7bace56e U H X e lam ιH bH mu Γih LG s st α M1 hM1_mono
      hM1_nonneg mubar kappa hmubar hkappa hPhi_lower hPhi_upper β hβ m hm (Ptheta S θ)
      hscale delta0 hdelta0_pos hmoment_int (delta0 / 32) hdelta1_pos hdelta1_lt r hr S hD
      hdens_meas
  obtain ⟨mubar₂, kappa₂, hmubar₂, hkappa₂, h678⟩ :=
    statopia_math_node_1558896730_aca48620 U H X e lam hlam_pos ιH bH mu hmu_pos C1 hC1_eigen
      Γ hΓ_pos hΓ_inj Γh hΓh_symm hΓh_pos hΓh_sq Γih hΓih_left LG s0 s1 s st α
      hs0_nonneg hs0_lt hs1_nonneg hs1_lt hs_gt hs_le hst_gt hst_le hα C1c hC1c M1
      hM1_mono hM1_nonneg
      (fun hinf w ρ hw h1 h2 =>
        ⟨(hA1 hinf w ρ hw h1 h2).1, (hA1 hinf w ρ hw h1 h2).2.2.2.1⟩)
      hA2 hHsub hLG_all_range
  have hcont : Tendsto (fun S' : Fin m → X × H =>
      hellingerDist (Qpost β m Γih LG (Ptheta S θ) S) (Qpost β m Γih LG (Ptheta S' θ) S'))
      (dataNhds (fun z : H => (HScaleNorm bH mu (α - s) z) ^ (1 / 2 : ℝ))
        (HScale bH mu (α - s)) S)
      (𝓝 0) := by
    refine (statopia_math_node_3122936556_c663d910 X H
      (fun z : H => (HScaleNorm bH mu (α - s) z) ^ (1 / 2 : ℝ))
      (HScale bH mu (α - s)) m hm S 0 ℝ 0
      (fun S' : Fin m → X × H =>
        hellingerDist (Qpost β m Γih LG (Ptheta S θ) S)
          (Qpost β m Γih LG (Ptheta S' θ) S'))).2.2 ?_
    intro Dn₀ hDn₀
    have hmink₂ := statopia_math_node_2221445841_9c042308 H ιH bH mu hmu_pos (α - s) U e lam
      hlam_pos 2
    have hcoord : ∀ j : Fin m,
        Tendsto (fun n : ℕ => (Dn₀ n j).2) atTop
          (scaleNhds (fun z : H => (HScaleNorm bH mu (α - s) z) ^ (1 / 2 : ℝ))
            (HScale bH mu (α - s)) ((S j).2)) := by
      intro j
      have hle : dataNhds (fun z : H => (HScaleNorm bH mu (α - s) z) ^ (1 / 2 : ℝ))
          (HScale bH mu (α - s)) S ≤
          Filter.comap (fun S' : Fin m → X × H => (S' j).2)
            (scaleNhds (fun z : H => (HScaleNorm bH mu (α - s) z) ^ (1 / 2 : ℝ))
              (HScale bH mu (α - s)) ((S j).2)) :=
        le_trans (iInf_le _ j) inf_le_right
      exact (Filter.tendsto_comap_iff (f := Dn₀)
        (g := fun S' : Fin m → X × H => (S' j).2) (a := atTop)
        (c := scaleNhds (fun z : H => (HScaleNorm bH mu (α - s) z) ^ (1 / 2 : ℝ))
          (HScale bH mu (α - s)) ((S j).2))).mp (hDn₀.mono_right hle)
    have hstep₀ : ∀ j : Fin m, ∃ Nj : ℕ, ∀ n : ℕ, Nj ≤ n →
        HScale bH mu (α - s) ((Dn₀ n j).2) ∧
        HScaleDist bH mu (α - s) ((Dn₀ n j).2) 0 ≤ ENNReal.ofReal (r + 1) := by
      intro j
      have hsmall : ∀ᶠ n : ℕ in atTop,
          HScale bH mu (α - s) ((Dn₀ n j).2) ∧
          (HScaleNorm bH mu (α - s) ((Dn₀ n j).2 - (S j).2)) ^ (1 / 2 : ℝ) <
            ENNReal.ofReal 1 := by
        have hle : scaleNhds (fun z : H => (HScaleNorm bH mu (α - s) z) ^ (1 / 2 : ℝ))
            (HScale bH mu (α - s)) ((S j).2) ≤
            Filter.principal {y' : H | HScale bH mu (α - s) y' ∧
              (HScaleNorm bH mu (α - s) (y' - (S j).2)) ^ (1 / 2 : ℝ) <
                ENNReal.ofReal 1} :=
          iInf_le _ (⟨1, by norm_num⟩ : { ε : ℝ // 0 < ε })
        exact Filter.tendsto_principal.mp ((hcoord j).mono_right hle)
      obtain ⟨Nj, hNj⟩ := Filter.eventually_atTop.1 hsmall
      refine ⟨Nj, fun n hn => ?_⟩
      obtain ⟨hok, hlt⟩ := hNj n hn
      refine ⟨hok, ?_⟩
      have hdist : HScaleDist bH mu (α - s) ((Dn₀ n j).2) 0 =
          (HScaleNorm bH mu (α - s) ((Dn₀ n j).2)) ^ (1 / 2 : ℝ) := by
        simp [HScaleDist]
      rw [hdist]
      have hmink' := hmink₂.1 ((Dn₀ n j).2 - (S j).2) ((S j).2)
      rw [sub_add_cancel] at hmink'
      have h2 : (HScaleNorm bH mu (α - s) ((S j).2)) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal r := by
        simpa [HScaleDist] using hD j
      refine le_trans hmink' ?_
      refine le_trans (add_le_add (le_of_lt hlt) h2) ?_
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) hr]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    choose Nj hNj using hstep₀
    set K : ℕ := (Finset.univ : Finset (Fin m)).sum Nj with hKdef
    have hNjK : ∀ j : Fin m, Nj j ≤ K := by
      intro j
      rw [hKdef]
      exact Finset.single_le_sum (f := Nj) (fun i _ => Nat.zero_le (Nj i)) (Finset.mem_univ j)
    set Dn : ℕ → Fin m → X × H := fun n => Dn₀ (n + K) with hDndef
    have hDn : Tendsto Dn atTop
        (dataNhds (fun z : H => (HScaleNorm bH mu (α - s) z) ^ (1 / 2 : ℝ))
          (HScale bH mu (α - s)) S) := by
      have hshift : Tendsto (fun n : ℕ => n + K) atTop atTop :=
        tendsto_atTop_mono (fun n : ℕ => Nat.le_add_right n K) tendsto_id
      exact hDn₀.comp hshift
    have hmeasNorm : Measurable (fun u : U => UScaleNorm e lam (1 - st) u) := by
      refine Measurable.ennreal_tsum (fun k => ?_)
      have hk : Measurable (fun u : U => inner ℝ (e k) u) := by
        have h' := (innerSL ℝ (e k)).continuous.measurable
        simpa [coe_innerSL_apply] using h'
      exact ENNReal.measurable_ofReal.comp (measurable_const.mul (hk.pow_const 2))
    have hmeasScale : MeasurableSet (UScale e lam (1 - st)) :=
      hmeasNorm measurableSet_Iio
    have hmoment_plain : ∀ delta : ℝ, 0 ≤ delta → delta < delta0 →
        Integrable (fun u : U =>
          Real.exp (delta * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2))
          (Ptheta S θ) := by
      intro delta h0 hlt
      have hcompl : (Ptheta S θ) (UScale e lam (1 - st))ᶜ = 0 := by
        rw [MeasureTheory.measure_compl hmeasScale (measure_ne_top _ _), hscale]
        simp
      have hae : ((UScale e lam (1 - st)).indicator
            (fun u : U =>
              Real.exp (delta * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2)))
          =ᵐ[Ptheta S θ]
          (fun u : U =>
            Real.exp (delta * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2)) := by
        filter_upwards [MeasureTheory.ae_iff.2 hcompl] with u hu
        rw [Set.indicator_of_mem (s := UScale e lam (1 - st)) hu]
      exact (hmoment_int delta h0 hlt).congr hae
    have hdelta_meas' : ∀ delta : ℝ,
        AEMeasurable ((UScale e lam (1 - st)).indicator
          (fun v : U =>
            Real.exp (delta * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)))
          (Ptheta S θ) := by
      intro delta
      have hinner : AEMeasurable
          (fun v : U => (momentExpENN M1 delta (UScaleDist e lam (1 - st) v 0)).toReal)
          (Ptheta S θ) :=
        ENNReal.measurable_toReal.comp_aemeasurable (hδ_meas delta)
      have heq : (fun v : U => (momentExpENN M1 delta (UScaleDist e lam (1 - st) v 0)).toReal)
          =ᵐ[Ptheta S θ]
          ((UScale e lam (1 - st)).indicator
            (fun v : U =>
              Real.exp (delta * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2))) := by
        filter_upwards with v
        by_cases hv : UScale e lam (1 - st) v
        · have hN : UScaleNorm e lam (1 - st) (v - 0) < ⊤ := by
            simpa using (show UScaleNorm e lam (1 - st) v < ⊤ from hv)
          have hlt : UScaleDist e lam (1 - st) v 0 < ⊤ :=
            (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).2 hN
          rw [Set.indicator_of_mem (s := UScale e lam (1 - st)) hv, momentExpENN, dif_pos hlt,
            ENNReal.toReal_ofReal (Real.exp_pos _).le]
        · have hlt : ¬ UScaleDist e lam (1 - st) v 0 < ⊤ := by
            intro h
            refine hv ?_
            have h' : UScaleNorm e lam (1 - st) (v - 0) < ⊤ :=
              (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).1 h
            simpa using h'
          rw [Set.indicator_of_notMem (s := UScale e lam (1 - st)) hv, momentExpENN, dif_neg hlt,
            ENNReal.toReal_top]
      exact hinner.congr heq
    set sigma2 : (Fin m → X × H) → ℝ := fun Dd =>
      ∑' k : ℕ,
        (priorEigen lam Nc θ.2 k)⁻¹ * (inner ℝ (e k) (fm Dd θ.1 - fm S θ.1)) ^ 2 with hsigma2def
    have hsigma2_def : ∀ Dd : Fin m → X × H, sigma2 Dd = ∑' k : ℕ,
        (priorEigen lam Nc θ.2 k)⁻¹ * (inner ℝ (e k) (fm Dd θ.1 - fm S θ.1)) ^ 2 := by
      intro Dd
      rw [hsigma2def]
    obtain ⟨Lam, hLam1, hLam_lb, hLam_summ, hLam_tendsto⟩ :=
      statopia_math_node_803467792_48128371 U e lam hlam_pos hlam_anti Nc hNc θ.2
    have hmink := statopia_math_node_2221445841_9c042308 H ιH bH mu hmu_pos (α - s) U e lam
      hlam_pos 2
    have hsigma2_summable : ∀ Dd : Fin m → X × H, Summable (fun k : ℕ =>
        (priorEigen lam Nc θ.2 k)⁻¹ * (inner ℝ (e k) (fm Dd θ.1 - fm S θ.1)) ^ 2) := by
      intro Dd
      have hmem : UScale e lam 2 (fm Dd θ.1 - fm S θ.1) := by
        have h1 : (UScaleNorm e lam 2 (fm Dd θ.1)) ^ (1 / 2 : ℝ) < ⊤ :=
          (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).2 (hfm_ball Dd θ).1
        have h2 : (UScaleNorm e lam 2 (fm S θ.1)) ^ (1 / 2 : ℝ) < ⊤ :=
          (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).2 (hfm_ball S θ).1
        have h3 : (UScaleNorm e lam 2 (fm Dd θ.1 - fm S θ.1)) ^ (1 / 2 : ℝ) < ⊤ :=
          lt_of_le_of_lt (hmink.2.2.2 (fm Dd θ.1) (fm S θ.1))
            (ENNReal.add_lt_top.2 ⟨h1, h2⟩)
        exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).1 h3
      exact (hLam_summ 1 (by norm_num) (fm Dd θ.1 - fm S θ.1) (by
        have h : (1 : ℝ) + 1 = 2 := by norm_num
        rw [h]
        exact hmem)).1
    have h6 : ∀ (x x' : X) (y y' : H), HScale bH mu (α - s) y → HScale bH mu (α - s) y' →
        ∀ u : U, UScale e lam (1 - st) u →
        |Phi Γih LG u x y - Phi Γih LG u x y'| ≤
          kappa₂ * ENNReal.toReal (HScaleDist bH mu (α - s) y y') *
            M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) :=
      fun x x' y y' hy hy' u hu => (h678 x x' y y' u hy hy' hu).1
    have h7 : ∀ (x x' : X) (y y' : H), HScale bH mu (α - s) y → HScale bH mu (α - s) y' →
        ∀ u : U, UScale e lam (1 - st) u →
        |Phi Γih LG u x y - Phi Γih LG u x' y| ≤
          (Real.rpow mubar₂ st * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) +
            kappa₂ * ENNReal.toReal (HScaleDist bH mu (α - s) y 0)) *
            ENNReal.toReal (HScaleDist bH mu st (Γih (LG x u - LG x' u)) 0) :=
      fun x x' y y' hy hy' u hu => (h678 x x' y y' u hy hy' hu).2.1
    have h8 : ∀ (x x' : X) (y y' : H), HScale bH mu (α - s) y → HScale bH mu (α - s) y' →
        ∀ u : U, UScale e lam (1 - st) u →
        ENNReal.toReal (HScaleDist bH mu st (Γih (LG x u - LG x' u)) 0) ≤
          2 * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) :=
      fun x x' y y' hy hy' u hu => (h678 x x' y y' u hy hy' hu).2.2
    have hD_rad : ∀ j : Fin m,
        (HScaleNorm bH mu (α - s) (S j).2) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (r + 1) :=
      fun j => le_trans (hD j) (ENNReal.ofReal_le_ofReal (by linarith))
    have hDn_scale : ∀ (n : ℕ) (j : Fin m), HScale bH mu (α - s) ((Dn n j).2) := by
      intro n j
      have h := (hNj j (n + K) (le_trans (hNjK j) (Nat.le_add_left K n))).1
      simpa only [hDndef] using h
    have hDn_rad : ∀ (n : ℕ) (j : Fin m),
        (HScaleNorm bH mu (α - s) ((Dn n j).2)) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (r + 1) := by
      intro n j
      have h := (hNj j (n + K) (le_trans (hNjK j) (Nat.le_add_left K n))).2
      simpa only [hDndef, HScaleDist, sub_zero] using h
  
    have hst_nonneg : 0 ≤ st := by linarith
    have hMb : mubar ≤ max mubar mubar₂ := le_max_left _ _
    have hKb : kappa ≤ max kappa kappa₂ := le_max_left _ _
    have hMb₂ : mubar₂ ≤ max mubar mubar₂ := le_max_right _ _
    have hKb₂ : kappa₂ ≤ max kappa kappa₂ := le_max_right _ _
    have hmb' : 1 ≤ max mubar mubar₂ := le_trans hmubar hMb
    have hkp' : 0 ≤ max kappa kappa₂ := le_trans hkappa hKb
    have hPhi_lower' : ∀ (x : X) (y : H) (u : U), HScale bH mu (α - s) y →
        UScale e lam (1 - st) u →
        Phi Γih LG u x y ≥ -(max kappa kappa₂ *
          ENNReal.toReal (HScaleDist bH mu (α - s) y 0) *
          M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) := by
      intro x y u hy hu
      have h0 := hPhi_lower x y u hy hu
      have hc : kappa * ENNReal.toReal (HScaleDist bH mu (α - s) y 0) ≤
          max kappa kappa₂ * ENNReal.toReal (HScaleDist bH mu (α - s) y 0) :=
        mul_le_mul_of_nonneg_right hKb ENNReal.toReal_nonneg
      have hd : kappa * ENNReal.toReal (HScaleDist bH mu (α - s) y 0) *
            M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) ≤
          max kappa kappa₂ * ENNReal.toReal (HScaleDist bH mu (α - s) y 0) *
            M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) :=
        mul_le_mul_of_nonneg_right hc (hM1_nonneg _)
      exact le_trans (neg_le_neg hd) h0
    have h6' : ∀ (x x' : X) (y y' : H), HScale bH mu (α - s) y → HScale bH mu (α - s) y' →
        ∀ u : U, UScale e lam (1 - st) u →
        |Phi Γih LG u x y - Phi Γih LG u x y'| ≤
          max kappa kappa₂ * ENNReal.toReal (HScaleDist bH mu (α - s) y y') *
            M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := by
      intro x x' y y' hy hy' u hu
      have h0 := h6 x x' y y' hy hy' u hu
      have hc : kappa₂ * ENNReal.toReal (HScaleDist bH mu (α - s) y y') ≤
          max kappa kappa₂ * ENNReal.toReal (HScaleDist bH mu (α - s) y y') :=
        mul_le_mul_of_nonneg_right hKb₂ ENNReal.toReal_nonneg
      have hd : kappa₂ * ENNReal.toReal (HScaleDist bH mu (α - s) y y') *
            M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) ≤
          max kappa kappa₂ * ENNReal.toReal (HScaleDist bH mu (α - s) y y') *
            M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) :=
        mul_le_mul_of_nonneg_right hc (hM1_nonneg _)
      exact le_trans h0 hd
    have h7' : ∀ (x x' : X) (y y' : H), HScale bH mu (α - s) y → HScale bH mu (α - s) y' →
        ∀ u : U, UScale e lam (1 - st) u →
        |Phi Γih LG u x y - Phi Γih LG u x' y| ≤
          (Real.rpow (max mubar mubar₂) st *
              M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) +
            max kappa kappa₂ * ENNReal.toReal (HScaleDist bH mu (α - s) y 0)) *
            ENNReal.toReal (HScaleDist bH mu st (Γih (LG x u - LG x' u)) 0) := by
      intro x x' y y' hy hy' u hu
      have h0 := h7 x x' y y' hy hy' u hu
      have hpow : mubar₂ ^ st ≤ max mubar mubar₂ ^ st :=
        Real.rpow_le_rpow (le_trans zero_le_one hmubar₂) hMb₂ hst_nonneg
      have hp1 : mubar₂ ^ st * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) ≤
          max mubar mubar₂ ^ st * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) :=
        mul_le_mul_of_nonneg_right hpow (hM1_nonneg _)
      have hp2 : kappa₂ * ENNReal.toReal (HScaleDist bH mu (α - s) y 0) ≤
          max kappa kappa₂ * ENNReal.toReal (HScaleDist bH mu (α - s) y 0) :=
        mul_le_mul_of_nonneg_right hKb₂ ENNReal.toReal_nonneg
      have hX : 0 ≤ ENNReal.toReal (HScaleDist bH mu st (Γih (LG x u - LG x' u)) 0) :=
        ENNReal.toReal_nonneg
      exact le_trans h0 (mul_le_mul_of_nonneg_right (add_le_add hp1 hp2) hX)
    have hseq : Tendsto (fun n : ℕ =>
        hellingerDist (Qpost β m Γih LG (Ptheta S θ) S)
          (Qpost β m Γih LG (Ptheta (Dn n) θ) (Dn n))) atTop (𝓝 0) :=
      statopia_math_node_3741426978_6fbf5eac U H X e lam hlam_pos hlam_anti
        Γ hΓ_pos hΓ_inj Γh hΓh_symm hΓh_pos hΓh_sq Γih hΓih_left ιH bH mu hmu_pos hmu_anti
        C1 hC1_pos hC1_inj hC1_eigen LG s0 s1 s st α hs0_nonneg hs0_lt hs1_nonneg hs1_lt
        hs_gt hs_le hst_gt hst_le hα C1c C2c hC1c hC2c M1 hM1_mono hM1_nonneg M2 hM2_nonneg
        hM2_mono_fst hM2_mono_snd hA1 hA2 hA3 hA4 hLG_all_range β hβ m hm Nc hNc Θ1 C0th
        hC0th_basis hC0th_expand R_u hR_u fm Ptheta
        hPtheta_isProb hPtheta_gauss hPtheta_mean hPtheta_cov hPtheta_int1 hPtheta_int2
        hfm_ball θ S (max mubar mubar₂) hmb' (max kappa kappa₂) hkp' hPhi_lower' h6' h7' h8
        delta0 hdelta0_pos hmoment_plain hdelta_meas' hscale (delta0 / 32) hdelta1_pos
        hdelta1_lt (r + 1) (by linarith : (0 : ℝ) ≤ r + 1) hS_scale hD_rad Dn hDn_scale
        hDn_rad hDn hfm_cont
    have hconvs : Tendsto (fun n : ℕ =>
        hellingerDist (Qpost β m Γih LG (Ptheta S θ) S)
          (Qpost β m Γih LG (Ptheta (Dn₀ (n + K)) θ) (Dn₀ (n + K)))) atTop (𝓝 0) := by
      simpa only [hDndef] using hseq
    refine Metric.tendsto_atTop.2 fun ε hε => ?_
    obtain ⟨N', hN'⟩ := Metric.tendsto_atTop.1 hconvs ε hε
    refine ⟨N' + K, fun m' hm' => ?_⟩
    have h1 : N' ≤ m' - K := by omega
    have h2 := hN' (m' - K) h1
    have h3 : m' - K + K = m' := by omega
    rwa [h3] at h2
  exact ⟨hAC, hdens, hZpos, hInteg, hcont⟩
  /- @proof-region region.root.bf58e61c8834 end -/

end Statlib.Imported

-- Paper root revision 20a58cff-c6d4-4c77-91af-52be2f770f1d

