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
theorem statopia_math_node_1461527046_1f5c51aa : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [MeasurableSpace U] [BorelSpace U]
    (e : HilbertBasis ℕ ℝ U) (lam : ℕ → ℝ) (hlam_pos : ∀ k : ℕ, 0 < lam k)
    (hlam_anti : Antitone lam) (Nc : ℕ) (hNc : 0 < Nc) (θ2 : Fin Nc → ℝ)
    (st : ℝ) (hst_nonneg : 0 ≤ st) (R_u : ℝ) (hR_u : 0 < R_u)
    (m0 : U) (D : ℕ → U) (P : Measure U) [IsProbabilityMeasure P]
    (hD : Tendsto (fun n : ℕ => (UScaleNorm e lam (1 + st) (D n - m0)) ^ (1 / 2 : ℝ))
      atTop (𝓝 0)),
    let c : ℕ → ℝ := fun k => priorEigen lam Nc θ2 k
    let sigma2 : ℕ → ℝ := fun n => ∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (D n - m0)) ^ 2
    let rho : ℕ → U → ℝ≥0∞ := fun n u => ENNReal.ofReal (Real.exp (
      (∑' k : ℕ, (c k)⁻¹ * inner ℝ (e k) (D n - m0) * inner ℝ (e k) (u - m0))
        - sigma2 n / 2))
    (∀ n : ℕ, AEMeasurable (rho n) P) →
    (∀ n : ℕ,
        (∫⁻ u : U, rho n u ∂P) = 1 ∧
        (∫⁻ u : U, ENNReal.rpow (rho n u) 2 ∂P) = ENNReal.ofReal (Real.exp (sigma2 n))) →
    Tendsto (fun n : ℕ => sigma2 n) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => Real.exp (sigma2 n) - 1) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => ∫⁻ u : U, ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) ∂P)
        atTop (𝓝 0) := by
  /- @proof-region region.target-node.session.2a5d5a3792dccd58 begin -/
  intro U _ _ _ _ _ e lam hlam_pos hlam_anti Nc hNc θ2 st hst_nonneg R_u hR_u m0 D P _ hD
  intro c sigma2 rho hmeas hmom
  have hsigma2def : sigma2 = fun n : ℕ => ∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (D n - m0)) ^ 2 := rfl
  have hsig : Tendsto sigma2 atTop (𝓝 0) := by
    have h := statopia_math_node_4158364297_64e7b82f U e lam hlam_pos hlam_anti Nc hNc θ2 st
      hst_nonneg m0 D hD
    rw [hsigma2def]
    exact h
  have hexp : Tendsto (fun n : ℕ => Real.exp (sigma2 n)) atTop (𝓝 (Real.exp 0)) :=
    (Real.continuous_exp.tendsto 0).comp hsig
  have hexp1 : Tendsto (fun n : ℕ => Real.exp (sigma2 n) - 1) atTop (𝓝 0) := by
    have hs : Tendsto (fun n : ℕ => Real.exp (sigma2 n) - 1) atTop (𝓝 (Real.exp 0 - 1)) :=
      hexp.sub (tendsto_const_nhds (x := (1 : ℝ)))
    simpa using hs
  refine ⟨hsig, hexp1, ?_⟩
  have hid : ∀ n : ℕ, ∫⁻ u : U, ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) ∂P
      = ENNReal.ofReal (Real.exp (sigma2 n) - 1) :=
    statopia_math_node_2795698314_c0cc56f5 U e lam Nc θ2 m0 D P hmeas hmom
  rw [show (fun n : ℕ => ∫⁻ u : U, ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) ∂P)
      = (fun n : ℕ => ENNReal.ofReal (Real.exp (sigma2 n) - 1)) from funext hid]
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ⊤ with hεtop | hεne
  · filter_upwards with n
    rw [hεtop]
    exact le_top
  · have hεpos : 0 < ε.toReal := by
      have h2 : 0 < ENNReal.ofReal ε.toReal := by
        rw [ENNReal.ofReal_toReal hεne]; exact hε
      exact ENNReal.ofReal_pos.mp h2
    have hev : ∀ᶠ n : ℕ in atTop, Real.exp (sigma2 n) - 1 < ε.toReal :=
      (tendsto_order.1 hexp1).2 ε.toReal hεpos
    filter_upwards [hev] with n hn
    rw [ENNReal.ofReal_le_iff_le_toReal hεne]
    linarith
  /- @proof-region region.target-node.session.2a5d5a3792dccd58 end -/

end Statlib.Imported
end

