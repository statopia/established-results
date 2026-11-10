import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_2633566936_711aab76_fba1da53
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3561399116_4ab5c1fc_158d698f
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_376187579_6cbc376f_e2a384b6
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_744484935_68a4c774_8f753d90

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
theorem statopia_math_node_2103907506_2297e1dc : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [MeasurableSpace U] [BorelSpace U]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H]
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X] [MeasurableSpace X]
    (m : ℕ) (hm : 0 < m)
    (e : HilbertBasis ℕ ℝ U) (lam : ℕ → ℝ)
    (hlam_pos : ∀ k : ℕ, 0 < lam k) (hlam_anti : Antitone lam)
    (ιH : Type*) [Preorder ιH] (bH : HilbertBasis ιH ℝ H) (mu : ιH → ℝ)
    (s α st : ℝ) (hst_nonneg : 0 ≤ st)
    (Nc : ℕ) (hNc : 0 < Nc)
    (Θ1 : Type*) [NormedAddCommGroup Θ1] [InnerProductSpace ℝ Θ1] [CompleteSpace Θ1]
    [TopologicalSpace.SeparableSpace Θ1] [MeasurableSpace Θ1]
    (C0th : (Fin Nc → ℝ) → U →L[ℝ] U)
    (hC0th_basis : ∀ (θ2 : Fin Nc → ℝ) (k : ℕ),
      C0th θ2 (e k) = priorEigen lam Nc θ2 k • e k)
    (hC0th_expand : ∀ (θ2 : Fin Nc → ℝ) (u : U),
      HasSum (fun k : ℕ => (priorEigen lam Nc θ2 k * inner ℝ (e k) u) • e k) (C0th θ2 u))
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
    (R_u : ℝ) (hR_u : 0 < R_u)
    (hfm_ball : ∀ (S : Fin m → X × H) (θ : Θ1 × (Fin Nc → ℝ)),
      UScale e lam 2 (fm S θ.1) ∧
      (UScaleNorm e lam 2 (fm S θ.1)) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal R_u)
    (θ : Θ1 × (Fin Nc → ℝ))
    (S : Fin m → X × H)
    (hfm_cont : Tendsto (fun S' : Fin m → X × H =>
        UScaleDist e lam (1 + st) (fm S' θ.1) (fm S θ.1))
      (dataNhds (fun z : H => (HScaleNorm bH mu (α - s) z) ^ (1 / 2 : ℝ))
        (HScale bH mu (α - s)) S) (𝓝 0)),
    let c : ℕ → ℝ := fun k => priorEigen lam Nc θ.2 k
    let m0 : U := fm S θ.1
    let sigma2 : (Fin m → X × H) → ℝ := fun D =>
      ∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (fm D θ.1 - m0)) ^ 2
    let rho : (Fin m → X × H) → U → ℝ≥0∞ := fun D u =>
      ENNReal.ofReal (Real.exp
        ((Filter.limsup (fun n : ℕ => ∑ k ∈ Finset.range n,
            (c k)⁻¹ * inner ℝ (e k) (fm D θ.1 - m0) * inner ℝ (e k) (u - m0)) Filter.atTop)
          - sigma2 D / 2))
    let Lambda : ℝ := max 1 (sSup {r : ℝ | ∃ k : Fin Nc, r = lam (k : ℕ) / c (k : ℕ)})
    let Bbar : ℝ := Real.exp (Lambda * lam 0 * (2 * R_u) ^ 2)
    (∀ k : ℕ, 0 < c k) ∧
      (∀ (k : ℕ) (hk : k < Nc), c k = Real.exp (θ.2 ⟨k, hk⟩)) ∧
      (∀ (k : ℕ), Nc ≤ k → c k = lam k) ∧
      (∀ k : ℕ, C0th θ.2 (e k) = c k • e k) ∧
      1 ≤ Lambda ∧
      (∀ D : Fin m → X × H,
        Summable (fun k : ℕ => (c k)⁻¹ * (inner ℝ (e k) (fm D θ.1 - m0)) ^ 2) ∧
        Ptheta D θ = (Ptheta S θ).withDensity (rho D) ∧
        (∀ q : ℝ, 0 < q →
          (∫⁻ u : U, ENNReal.rpow (rho D u) q ∂(Ptheta S θ))
            = ENNReal.ofReal (Real.exp (q * (q - 1) / 2 * sigma2 D))) ∧
        (∫⁻ u : U, rho D u ∂(Ptheta S θ)) = 1 ∧
        (∫⁻ u : U, ENNReal.rpow (rho D u) (2 : ℝ) ∂(Ptheta S θ))
          = ENNReal.ofReal (Real.exp (sigma2 D)) ∧
        (∀ g : U → ℝ, Measurable g → (∀ u : U, 0 ≤ g u) →
          (∫ u, g u ∂(Ptheta D θ)) = ∫ u, g u * (rho D u).toReal ∂(Ptheta S θ)) ∧
        Measure.AbsolutelyContinuous (Ptheta D θ) (Ptheta S θ) ∧
        (Ptheta D θ).rnDeriv (Ptheta S θ) =ᵐ[Ptheta S θ] rho D) ∧
      (∀ D : Fin m → X × H,
        sigma2 D ≤
          Lambda * (∑' k : ℕ, (lam k)⁻¹ * (inner ℝ (e k) (fm D θ.1 - m0)) ^ 2) ∧
        Lambda * (∑' k : ℕ, (lam k)⁻¹ * (inner ℝ (e k) (fm D θ.1 - m0)) ^ 2)
          ≤ Lambda * lam 0 *
            (∑' k : ℕ, ((lam k)⁻¹) ^ 2 * (inner ℝ (e k) (fm D θ.1 - m0)) ^ 2) ∧
        Lambda * lam 0 *
            (∑' k : ℕ, ((lam k)⁻¹) ^ 2 * (inner ℝ (e k) (fm D θ.1 - m0)) ^ 2)
          ≤ Lambda * lam 0 * (2 * R_u) ^ 2 ∧
        (∫⁻ u : U, ENNReal.rpow (rho D u) (2 : ℝ) ∂(Ptheta S θ)) ≤ ENNReal.ofReal Bbar) ∧
      (∀ Dseq : ℕ → Fin m → X × H,
        Tendsto Dseq atTop
          (dataNhds (fun z : H => (HScaleNorm bH mu (α - s) z) ^ (1 / 2 : ℝ))
            (HScale bH mu (α - s)) S) →
        Tendsto (fun n : ℕ => sigma2 (Dseq n)) atTop (𝓝 0) ∧
        Tendsto (fun n : ℕ =>
            ∫⁻ u : U, ENNReal.ofReal (((rho (Dseq n) u).toReal - 1) ^ 2) ∂(Ptheta S θ))
          atTop (𝓝 0) ∧
        Tendsto (fun n : ℕ => Real.exp (sigma2 (Dseq n)) - 1) atTop (𝓝 0)) := by
  /- @proof-region region.target-node.session.e9d9b1b19c25ea15 begin -/
  classical
  intro U _ _ _ _ _ _ H _ _ _ _ _ _ X _ _ _ _ _ m hm e lam hlam_pos hlam_anti iotaH _ bH mu s alpha st hst_nonneg Nc hNc Θ1 _ _ _ _ _ C0th hC0th_basis hC0th_expand fm Ptheta hPtheta_isProb hPtheta_gauss hPtheta_mean hPtheta_cov hPtheta_int1 hPtheta_int2 R_u hR_u hfm_ball theta S hfm_cont c m0 sigma2 rho Lambda Bbar
  have hK : ∀ D : Fin m → X × H,
      Summable (fun k : ℕ => (c k)⁻¹ * (inner ℝ (e k) (fm D theta.1 - m0)) ^ 2) ∧
      sigma2 D ≤ Lambda * (∑' k : ℕ, (lam k)⁻¹ * (inner ℝ (e k) (fm D theta.1 - m0)) ^ 2) ∧
      Lambda * (∑' k : ℕ, (lam k)⁻¹ * (inner ℝ (e k) (fm D theta.1 - m0)) ^ 2)
        ≤ Lambda * lam 0 *
            (∑' k : ℕ, ((lam k)⁻¹) ^ 2 * (inner ℝ (e k) (fm D theta.1 - m0)) ^ 2) ∧
      Lambda * lam 0 *
          (∑' k : ℕ, ((lam k)⁻¹) ^ 2 * (inner ℝ (e k) (fm D theta.1 - m0)) ^ 2)
        ≤ Lambda * lam 0 * (2 * R_u) ^ 2 := by
    intro D
    exact statopia_math_node_2633566936_711aab76 U e lam hlam_pos hlam_anti Nc hNc theta.2 R_u hR_u
      (fm D theta.1) (fm S theta.1) (hfm_ball D theta).1 (hfm_ball S theta).1
      (hfm_ball D theta).2 (hfm_ball S theta).2
  have hA : ∀ D : Fin m → X × H,
      Ptheta D theta = (Ptheta S theta).withDensity (rho D) ∧
      (∀ q : ℝ, 0 < q →
        (∫⁻ u : U, ENNReal.rpow (rho D u) q ∂(Ptheta S theta))
          = ENNReal.ofReal (Real.exp (q * (q - 1) / 2 * sigma2 D))) ∧
      (∫⁻ u : U, rho D u ∂(Ptheta S theta)) = 1 ∧
      (∫⁻ u : U, ENNReal.rpow (rho D u) (2 : ℝ) ∂(Ptheta S theta))
        = ENNReal.ofReal (Real.exp (sigma2 D)) ∧
      (∀ g : U → ℝ, Measurable g → (∀ u : U, 0 ≤ g u) →
        (∫ u, g u ∂(Ptheta D theta)) = ∫ u, g u * (rho D u).toReal ∂(Ptheta S theta)) ∧
      MeasureTheory.Measure.AbsolutelyContinuous (Ptheta D theta) (Ptheta S theta) ∧
      (Ptheta D theta).rnDeriv (Ptheta S theta) =ᵐ[Ptheta S theta] rho D := by
    intro D
    haveI hPi : IsProbabilityMeasure (Ptheta S theta) := hPtheta_isProb S theta
    haveI hQi : IsProbabilityMeasure (Ptheta D theta) := hPtheta_isProb D theta
    exact statopia_math_node_376187579_6cbc376f U e lam hlam_pos Nc theta.2 (C0th theta.2)
      (hC0th_expand theta.2) (Ptheta S theta) (Ptheta D theta)
      (hPtheta_gauss S theta) (hPtheta_gauss D theta) (fm S theta.1) (fm D theta.1)
      (hPtheta_mean S theta) (hPtheta_mean D theta)
      (hPtheta_cov S theta) (hPtheta_cov D theta)
      (hPtheta_int1 S theta) (hPtheta_int1 D theta)
      (hPtheta_int2 S theta) (hPtheta_int2 D theta) (hK D).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    have h : c k = priorEigen lam Nc theta.2 k := rfl
    rw [h]
    unfold priorEigen
    split_ifs with hk
    · exact Real.exp_pos _
    · exact hlam_pos k
  · intro k hk
    have h : c k = priorEigen lam Nc theta.2 k := rfl
    rw [h]
    unfold priorEigen
    rw [dif_pos hk]
  · intro k hk
    have h : c k = priorEigen lam Nc theta.2 k := rfl
    rw [h]
    unfold priorEigen
    rw [dif_neg (not_lt.mpr hk)]
  · intro k
    exact hC0th_basis theta.2 k
  · exact le_max_left 1 _
  · intro D
    exact ⟨(hK D).1, hA D⟩
  · intro D
    have h4 : sigma2 D ≤ Lambda * lam 0 * (2 * R_u) ^ 2 :=
      le_trans (hK D).2.1 (le_trans (hK D).2.2.1 (hK D).2.2.2)
    refine ⟨(hK D).2.1, (hK D).2.2.1, (hK D).2.2.2, ?_⟩
    rw [(hA D).2.2.2.1]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr h4)
  · intro Dseq hDseq
    have hD : Tendsto (fun n : ℕ =>
        (UScaleNorm e lam (1 + st) (fm (Dseq n) theta.1 - fm S theta.1)) ^ (1 / 2 : ℝ))
        atTop (𝓝 0) := hfm_cont.comp hDseq
    have hmeas : ∀ n : ℕ, AEMeasurable (rho (Dseq n)) (Ptheta S theta) := by
      intro n
      haveI hPi : IsProbabilityMeasure (Ptheta S theta) := hPtheta_isProb S theta
      haveI hQi : IsProbabilityMeasure (Ptheta (Dseq n) theta) := hPtheta_isProb (Dseq n) theta
      have hrn : Measurable ((Ptheta (Dseq n) theta).rnDeriv (Ptheta S theta)) :=
        Measure.measurable_rnDeriv (Ptheta (Dseq n) theta) (Ptheta S theta)
      exact hrn.aemeasurable.congr (hA (Dseq n)).2.2.2.2.2.2
    haveI hPi : IsProbabilityMeasure (Ptheta S theta) := hPtheta_isProb S theta
    exact statopia_math_node_3561399116_4ab5c1fc U e lam hlam_pos hlam_anti Nc hNc theta.2 st
      hst_nonneg R_u hR_u (fm S theta.1) (fun n : ℕ => fm (Dseq n) theta.1) (Ptheta S theta)
      hD hmeas (fun n : ℕ => ⟨(hA (Dseq n)).2.2.1, (hA (Dseq n)).2.2.2.1⟩)
  /- @proof-region region.target-node.session.e9d9b1b19c25ea15 end -/

end Statlib.Imported
end

