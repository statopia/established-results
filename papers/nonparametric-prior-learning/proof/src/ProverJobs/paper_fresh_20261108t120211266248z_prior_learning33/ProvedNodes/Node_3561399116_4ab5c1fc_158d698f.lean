import Statlib.StatFoundation.BasicAnalysis.ENNRealBridge
import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_2795698314_c0cc56f5_c6e067b9
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_4158364297_64e7b82f_818b20bf

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
theorem statopia_math_node_3561399116_4ab5c1fc : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [MeasurableSpace U] [BorelSpace U]
    (e : HilbertBasis ℕ ℝ U) (lam : ℕ → ℝ) (hlam_pos : ∀ k : ℕ, 0 < lam k)
    (hlam_anti : Antitone lam) (Nc : ℕ) (hNc : 0 < Nc) (theta2 : Fin Nc → ℝ)
    (st : ℝ) (hst_nonneg : 0 ≤ st) (R_u : ℝ) (hR_u : 0 < R_u)
    (m0 : U) (D : ℕ → U) (P : Measure U) [IsProbabilityMeasure P]
    (hD : Tendsto (fun n : ℕ => (UScaleNorm e lam (1 + st) (D n - m0)) ^ (1 / 2 : ℝ))
      atTop (𝓝 0)),
    let c : ℕ → ℝ := fun k => priorEigen lam Nc theta2 k
    let sigma2 : ℕ → ℝ := fun n => ∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (D n - m0)) ^ 2
    let rho : ℕ → U → ℝ≥0∞ := fun n u => ENNReal.ofReal (Real.exp (
      (Filter.limsup (fun j : ℕ => ∑ k ∈ Finset.range j,
          (c k)⁻¹ * inner ℝ (e k) (D n - m0) * inner ℝ (e k) (u - m0)) Filter.atTop)
        - sigma2 n / 2))
    (∀ n : ℕ, AEMeasurable (rho n) P) →
    (∀ n : ℕ,
        (∫⁻ u : U, rho n u ∂P) = 1 ∧
        (∫⁻ u : U, ENNReal.rpow (rho n u) 2 ∂P) = ENNReal.ofReal (Real.exp (sigma2 n))) →
    Tendsto (fun n : ℕ => sigma2 n) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => ∫⁻ u : U, ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) ∂P)
        atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => Real.exp (sigma2 n) - 1) atTop (𝓝 0) := by
  /- @proof-region region.target-node.session.d6cee6c47742a67d begin -/
  intro U i1 i2 i3 i4 i5 e lam hlam_pos hlam_anti Nc hNc theta2 st hst_nonneg R_u hR_u m0 D P hP hD
  intro c sigma2 rho hmeas hmom
  have hsig : Tendsto sigma2 atTop (𝓝 0) := by
    have h :=
      statopia_math_node_4158364297_64e7b82f U e lam hlam_pos hlam_anti Nc hNc theta2 st
        hst_nonneg m0 D hD
    simpa only [sigma2, c] using h
  have hexp : Tendsto (fun n : ℕ => Real.exp (sigma2 n) - 1) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => Real.exp (sigma2 n)) atTop (𝓝 1) := by
      have hcomp := (Real.continuous_exp.tendsto 0).comp hsig
      simpa using hcomp
    have h2 : Tendsto (fun n : ℕ => Real.exp (sigma2 n) - 1) atTop (𝓝 (1 - 1)) :=
      h1.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
    simpa using h2
  have hchi :
      Tendsto (fun n : ℕ => ∫⁻ u : U, ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) ∂P)
        atTop (𝓝 0) := by
    have hid : ∀ n : ℕ, ∫⁻ u : U, ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) ∂P
        = ENNReal.ofReal (Real.exp (sigma2 n) - 1) := by
      intro n
      have hne : ∀ u : U, rho n u ≠ ⊤ := by
        intro u
        simp only [rho]
        exact ENNReal.ofReal_ne_top
      have hof : ∀ u : U, ENNReal.ofReal ((rho n u).toReal) = rho n u := by
        intro u
        exact ENNReal.ofReal_toReal (hne u)
      have hmeas_t : AEMeasurable (fun u : U => (rho n u).toReal) P :=
        (hmeas n).ennreal_toReal
      have hstrong_t : AEStronglyMeasurable (fun u : U => (rho n u).toReal) P :=
        hmeas_t.aestronglyMeasurable
      have hint1_lin : ∫⁻ u : U, ENNReal.ofReal ((rho n u).toReal) ∂P = 1 := by
        have h_eq : (fun u : U => ENNReal.ofReal ((rho n u).toReal)) = rho n := funext hof
        rw [h_eq]
        exact (hmom n).1
      have hint1_int : Integrable (fun u : U => (rho n u).toReal) P :=
        (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hstrong_t
            (Filter.Eventually.of_forall (fun u => ENNReal.toReal_nonneg))).mp
          (by rw [hint1_lin]; simp)
      have hint1_val : ∫ u : U, (rho n u).toReal ∂P = 1 := by
        rw [Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.integral_eq_lintegral_toReal_of_nonneg
          (Filter.Eventually.of_forall (fun u => ENNReal.toReal_nonneg)) hint1_int, hint1_lin]
        exact ENNReal.toReal_one
      have hA2_strong : AEStronglyMeasurable (fun u : U => (rho n u).toReal ^ 2) P :=
        hstrong_t.pow 2
      have hpw : ∀ u : U, ENNReal.ofReal ((rho n u).toReal ^ 2) = ENNReal.rpow (rho n u) 2 := by
        intro u
        rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, hof u, ← ENNReal.rpow_natCast (rho n u) 2]
        norm_num
      have hint2_lin : ∫⁻ u : U, ENNReal.ofReal ((rho n u).toReal ^ 2) ∂P
          = ENNReal.ofReal (Real.exp (sigma2 n)) := by
        simp only [hpw]
        exact (hmom n).2
      have hint2_int : Integrable (fun u : U => (rho n u).toReal ^ 2) P :=
        (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hA2_strong
            (Filter.Eventually.of_forall (fun u => sq_nonneg ((rho n u).toReal)))).mp
          (by rw [hint2_lin]; exact ENNReal.ofReal_ne_top)
      have hint2_val : ∫ u : U, (rho n u).toReal ^ 2 ∂P = Real.exp (sigma2 n) := by
        rw [Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.integral_eq_lintegral_toReal_of_nonneg
          (Filter.Eventually.of_forall (fun u => sq_nonneg ((rho n u).toReal))) hint2_int,
          hint2_lin]
        exact ENNReal.toReal_ofReal (Real.exp_pos (sigma2 n)).le
      have hconst : ∫ u : U, (1 : ℝ) ∂P = 1 := by
        rw [MeasureTheory.integral_const]
        simp
      have hf_strong : AEStronglyMeasurable (fun u : U => ((rho n u).toReal - 1) ^ 2) P :=
        (hstrong_t.sub aestronglyMeasurable_const).pow 2
      have hcomb_int :
          Integrable (fun u : U => (rho n u).toReal ^ 2 - 2 * (rho n u).toReal + 1) P :=
        (hint2_int.sub (hint1_int.const_mul 2)).add (MeasureTheory.integrable_const (1 : ℝ))
      have hf_int : Integrable (fun u : U => ((rho n u).toReal - 1) ^ 2) P :=
        hcomb_int.congr (Filter.Eventually.of_forall (fun u => by ring))
      have hmain : ∫ u : U, ((rho n u).toReal - 1) ^ 2 ∂P = Real.exp (sigma2 n) - 1 := by
        have e1 : Integrable (fun u : U => (rho n u).toReal ^ 2 - 2 * (rho n u).toReal) P :=
          hint2_int.sub (hint1_int.const_mul 2)
        have e2 : Integrable (fun u : U => 2 * (rho n u).toReal) P :=
          hint1_int.const_mul 2
        calc ∫ u : U, ((rho n u).toReal - 1) ^ 2 ∂P
            = ∫ u : U, (rho n u).toReal ^ 2 - 2 * (rho n u).toReal + 1 ∂P := by
              rw [show (fun u : U => ((rho n u).toReal - 1) ^ 2)
                  = (fun u : U => (rho n u).toReal ^ 2 - 2 * (rho n u).toReal + 1) from
                  funext (fun u => by ring)]
          _ = (∫ u : U, (rho n u).toReal ^ 2 - 2 * (rho n u).toReal ∂P)
                + ∫ u : U, (1 : ℝ) ∂P :=
              MeasureTheory.integral_add e1 (MeasureTheory.integrable_const (1 : ℝ))
          _ = ((∫ u : U, (rho n u).toReal ^ 2 ∂P)
                - ∫ u : U, 2 * (rho n u).toReal ∂P) + ∫ u : U, (1 : ℝ) ∂P := by
              rw [MeasureTheory.integral_sub hint2_int e2]
          _ = ((∫ u : U, (rho n u).toReal ^ 2 ∂P)
                - 2 * ∫ u : U, (rho n u).toReal ∂P) + ∫ u : U, (1 : ℝ) ∂P := by
              rw [MeasureTheory.integral_const_mul]
          _ = (Real.exp (sigma2 n) - 2 * 1) + 1 := by
              rw [hint2_val, hint1_val, hconst]
          _ = Real.exp (sigma2 n) - 1 := by ring
      have hne_top : ∫⁻ u : U, ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) ∂P ≠ ⊤ :=
        (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hf_strong
            (Filter.Eventually.of_forall (fun u => sq_nonneg ((rho n u).toReal - 1)))).mpr
          hf_int
      have hfin : ENNReal.ofReal (∫ u : U, ((rho n u).toReal - 1) ^ 2 ∂P)
          = ∫⁻ u : U, ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) ∂P := by
        rw [Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.integral_eq_lintegral_toReal_of_nonneg
          (Filter.Eventually.of_forall (fun u => sq_nonneg ((rho n u).toReal - 1))) hf_int]
        exact ENNReal.ofReal_toReal hne_top
      rw [← hfin, hmain]
    simp only [hid]
    simpa using ENNReal.tendsto_ofReal hexp
  exact ⟨hsig, hchi, hexp⟩
  /- @proof-region region.target-node.session.d6cee6c47742a67d end -/

end Statlib.Imported
end

