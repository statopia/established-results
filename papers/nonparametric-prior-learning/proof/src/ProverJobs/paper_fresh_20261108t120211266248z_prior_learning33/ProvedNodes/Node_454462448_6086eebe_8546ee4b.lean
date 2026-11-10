import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_1159502109_f07fd652_e169c51a
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3199133157_4a242571_3372dd7b

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
theorem statopia_math_node_454462448_6086eebe : ∀ (ι : Type*) [Fintype ι] (σ m n : ι → ℝ) (hσ : ∀ k, 0 < σ k),
    (let δ : ι → ℝ := fun k => n k - m k
     let a : ι → ℝ := fun k => (σ k)⁻¹ * δ k
     let d : ι → ℝ → ℝ := fun k y => Real.exp (a k * (y - m k) - (2 : ℝ)⁻¹ * a k * δ k)
     let Pmu : Measure (ι → ℝ) :=
       Measure.pi (fun k => gaussianReal (m k) (Real.toNNReal (σ k)))
     let Pnu : Measure (ι → ℝ) :=
       Measure.pi (fun k => gaussianReal (n k) (Real.toNNReal (σ k)))
     Pnu = Pmu.withDensity (fun y => ENNReal.ofReal (∏ k, d k (y k))) ∧
       (∀ B : Set (ι → ℝ), MeasurableSet B →
         Pnu B = ∫⁻ y in B, ENNReal.ofReal (∏ k, d k (y k)) ∂Pmu) ∧
       (∫⁻ y, ENNReal.ofReal (∏ k, d k (y k)) ∂Pmu = 1) ∧
       (∫⁻ y, (ENNReal.ofReal (∏ k, d k (y k))) ^ 2 ∂Pmu =
         ENNReal.ofReal (Real.exp (∑ k, (σ k)⁻¹ * (δ k) ^ 2)))) := by
  /- @proof-region region.target-node.session.395a360068b8faaf begin -/
  intro ι _ σ m n hσ
  classical
  let d : ι → ℝ → ℝ :=
    fun k y => Real.exp ((σ k)⁻¹ * (n k - m k) * (y - m k) - 2⁻¹ * ((σ k)⁻¹ * (n k - m k)) * (n k - m k))
  let F : ι → ℝ → ENNReal := fun k x => ENNReal.ofReal (d k x)
  let μ : ι → Measure ℝ := fun k => gaussianReal (m k) (Real.toNNReal (σ k))
  let ν : ι → Measure ℝ := fun k => gaussianReal (n k) (Real.toNNReal (σ k))
  let G : (ι → ℝ) → ENNReal := fun y => ENNReal.ofReal (∏ k, d k (y k))
  let Gp : (ι → ℝ) → ENNReal := fun y => ∏ k, F k (y k)
  show Measure.pi ν = (Measure.pi μ).withDensity G ∧
      (∀ B : Set (ι → ℝ), MeasurableSet B → Measure.pi ν B = ∫⁻ y in B, G y ∂Measure.pi μ) ∧
      (∫⁻ y, G y ∂Measure.pi μ = 1) ∧
      (∫⁻ y, (G y) ^ 2 ∂Measure.pi μ
        = ENNReal.ofReal (Real.exp (∑ k, (σ k)⁻¹ * (n k - m k) ^ 2)))
  have hd : ∀ k, Measurable (F k) := fun k =>
    (statopia_math_node_3199133157_4a242571 (σ k) (hσ k) (m k) (n k)).1
  have hfin1 : ∀ k, ∀ᵐ x ∂(μ k), F k x < ⊤ := fun k =>
    Filter.Eventually.of_forall fun x => by
      first
        | exact ENNReal.ofReal_lt_top
        | simp
  have hfin2 : ∀ k, ∀ᵐ x ∂(μ k), (F k x) ^ 2 < ⊤ := fun k =>
    Filter.Eventually.of_forall fun x => by
      first
        | exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
        | exact ENNReal.pow_lt_top_iff.mpr ENNReal.ofReal_lt_top
        | simp
  have hG_eq : G = Gp := by
    funext y
    exact ENNReal.ofReal_prod_of_nonneg (fun k _ => (Real.exp_pos _).le)
  have hν : ν = fun k => (μ k).withDensity (F k) := by
    funext k
    exact (statopia_math_node_3199133157_4a242571 (σ k) (hσ k) (m k) (n k)).2.1
  have h1p : Measure.pi ν = (Measure.pi μ).withDensity Gp := by
    rw [hν]
    exact (statopia_math_node_1159502109_f07fd652 ι μ F hd hfin1).2.1
  have h1 : Measure.pi ν = (Measure.pi μ).withDensity G := by
    rw [hG_eq]
    exact h1p
  have h2 : ∀ B : Set (ι → ℝ), MeasurableSet B →
      Measure.pi ν B = ∫⁻ y in B, G y ∂Measure.pi μ := by
    intro B hB
    rw [h1]
    exact MeasureTheory.withDensity_apply G hB
  have h3p : ∫⁻ y, Gp y ∂Measure.pi μ = 1 := by
    show ∫⁻ y, ∏ k, F k (y k) ∂Measure.pi μ = 1
    rw [(statopia_math_node_1159502109_f07fd652 ι μ F hd hfin1).2.2]
    have hone : ∀ k, ∫⁻ x, F k x ∂μ k = 1 := fun k =>
      (statopia_math_node_3199133157_4a242571 (σ k) (hσ k) (m k) (n k)).2.2.1
    simp [hone]
  have h3 : ∫⁻ y, G y ∂Measure.pi μ = 1 := by
    rw [hG_eq]
    exact h3p
  have hsq : ∀ k, Measurable fun x : ℝ => (F k x) ^ 2 := by
    intro k
    first
      | measurability
      | simpa [pow_two] using (hd k).mul (hd k)
      | exact (hd k).pow 2
  have h4p : ∫⁻ y, (Gp y) ^ 2 ∂Measure.pi μ
      = ENNReal.ofReal (Real.exp (∑ k, (σ k)⁻¹ * (n k - m k) ^ 2)) := by
    show ∫⁻ y, (∏ k, F k (y k)) ^ 2 ∂Measure.pi μ
      = ENNReal.ofReal (Real.exp (∑ k, (σ k)⁻¹ * (n k - m k) ^ 2))
    have hfac : ∫⁻ y, ∏ k, (F k (y k)) ^ 2 ∂Measure.pi μ
        = ∏ k, ∫⁻ x, (F k x) ^ 2 ∂μ k :=
      (statopia_math_node_1159502109_f07fd652 ι μ (fun k x => (F k x) ^ 2) hsq hfin2).2.2
    have hone2 : ∀ k, ∫⁻ x, (F k x) ^ 2 ∂μ k
        = ENNReal.ofReal (Real.exp ((σ k)⁻¹ * (n k - m k) ^ 2)) := fun k =>
      (statopia_math_node_3199133157_4a242571 (σ k) (hσ k) (m k) (n k)).2.2.2
    have hprod : ∏ k, ENNReal.ofReal (Real.exp ((σ k)⁻¹ * (n k - m k) ^ 2))
        = ENNReal.ofReal (Real.exp (∑ k, (σ k)⁻¹ * (n k - m k) ^ 2)) := by
      rw [Real.exp_sum]
      exact (ENNReal.ofReal_prod_of_nonneg (fun k _ => (Real.exp_pos _).le)).symm
    calc ∫⁻ y, (∏ k, F k (y k)) ^ 2 ∂Measure.pi μ
        = ∫⁻ y, ∏ k, (F k (y k)) ^ 2 ∂Measure.pi μ := by
          simp only [Finset.prod_pow]
      _ = ∏ k, ∫⁻ x, (F k x) ^ 2 ∂μ k := hfac
      _ = ∏ k, ENNReal.ofReal (Real.exp ((σ k)⁻¹ * (n k - m k) ^ 2)) := by
          simp only [hone2]
      _ = ENNReal.ofReal (Real.exp (∑ k, (σ k)⁻¹ * (n k - m k) ^ 2)) := hprod
  have h4 : ∫⁻ y, (G y) ^ 2 ∂Measure.pi μ
      = ENNReal.ofReal (Real.exp (∑ k, (σ k)⁻¹ * (n k - m k) ^ 2)) := by
    rw [hG_eq]
    exact h4p
  exact ⟨h1, h2, h3, h4⟩
  /- @proof-region region.target-node.session.395a360068b8faaf end -/

end Statlib.Imported
end

