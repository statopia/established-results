import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base

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
theorem statopia_math_node_2795698314_c0cc56f5 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [MeasurableSpace U] [BorelSpace U]
    (e : HilbertBasis ℕ ℝ U) (lam : ℕ → ℝ) (Nc : ℕ) (theta2 : Fin Nc → ℝ)
    (m0 : U) (D : ℕ → U) (P : Measure U) [IsProbabilityMeasure P],
    let c : ℕ → ℝ := fun k => priorEigen lam Nc theta2 k
    let sigma2 : ℕ → ℝ := fun n => ∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (D n - m0)) ^ 2
    let rho : ℕ → U → ℝ≥0∞ := fun n u => ENNReal.ofReal (Real.exp (
      (∑' k : ℕ, (c k)⁻¹ * inner ℝ (e k) (D n - m0) * inner ℝ (e k) (u - m0))
        - sigma2 n / 2))
    (∀ n : ℕ, AEMeasurable (rho n) P) →
    (∀ n : ℕ,
        (∫⁻ u : U, rho n u ∂P) = 1 ∧
        (∫⁻ u : U, ENNReal.rpow (rho n u) 2 ∂P) = ENNReal.ofReal (Real.exp (sigma2 n))) →
    ∀ n : ℕ, ∫⁻ u : U, ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) ∂P
      = ENNReal.ofReal (Real.exp (sigma2 n) - 1) := by
  /- @proof-region region.target-node.session.b56ae601fec81e19 begin -/
  intro U _ _ _ _ _ e lam Nc theta2 m0 D P hP c sigma2 rho hmeas hmom n
  set W : U → ℝ := fun u => Real.exp
    ((∑' k : ℕ, (c k)⁻¹ * inner ℝ (e k) (D n - m0) * inner ℝ (e k) (u - m0)) - sigma2 n / 2)
    with hW
  have hWpos : ∀ u, 0 < W u := fun u => Real.exp_pos _
  have hWnn : ∀ u, 0 ≤ W u := fun u => (hWpos u).le
  have hrho : ∀ u, rho n u = ENNReal.ofReal (W u) := fun u => rfl
  have htoReal : ∀ u, (rho n u).toReal = W u :=
    fun u => by rw [hrho u]; exact ENNReal.toReal_ofReal (hWnn u)
  have hW_aem : AEMeasurable W P := by
    have h := AEMeasurable.ennreal_toReal (hmeas n)
    rwa [show (fun u => (rho n u).toReal) = W from funext htoReal] at h
  have hW_aesm : AEStronglyMeasurable W P := hW_aem.aestronglyMeasurable
  have hW2_aesm : AEStronglyMeasurable (fun u => (W u) ^ 2) P := hW_aesm.pow 2
  have h1 : ∫⁻ u, ENNReal.ofReal (W u) ∂P = 1 := by
    rw [← (hmom n).1]
  have hsq : ∀ u, ENNReal.ofReal ((W u) ^ 2) = ENNReal.rpow (rho n u) 2 := by
    intro u
    rw [hrho u]
    rw [show (ENNReal.ofReal (W u)).rpow 2 = (ENNReal.ofReal (W u)) ^ (2:ℝ) from rfl,
      ENNReal.ofReal_rpow_of_nonneg (hWnn u) (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    exact (Real.rpow_natCast (W u) 2).symm
  have h2 : ∫⁻ u, ENNReal.ofReal ((W u) ^ 2) ∂P = ENNReal.ofReal (Real.exp (sigma2 n)) := by
    rw [← (hmom n).2]
    exact lintegral_congr hsq
  have hW_int : Integrable W P := by
    refine (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable (f := W) hW_aesm
      (ae_of_all _ hWnn)).mp ?_
    rw [h1]; exact ENNReal.one_ne_top
  have hW2_int : Integrable (fun u => (W u) ^ 2) P := by
    refine (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      (f := fun u => (W u) ^ 2) hW2_aesm (ae_of_all _ (fun u => sq_nonneg (W u)))).mp ?_
    rw [h2]; exact ENNReal.ofReal_ne_top
  have e1 : ∫ u, W u ∂P = 1 := by
    have h := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hW_int (ae_of_all _ hWnn)
    rw [h1] at h
    exact (ENNReal.ofReal_eq_one).mp h
  have e2 : ∫ u, (W u) ^ 2 ∂P = Real.exp (sigma2 n) := by
    have h := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hW2_int
      (ae_of_all _ (fun u => sq_nonneg (W u)))
    rw [h2] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (p := ∫ u, (W u) ^ 2 ∂P) (q := Real.exp (sigma2 n))
      (integral_nonneg (fun u => sq_nonneg (W u))) (Real.exp_pos _).le).mp h
  have hone : (∫ _u : U, (1:ℝ) ∂P) = 1 := by
    rw [MeasureTheory.integral_const]; simp
  have hsub_int : Integrable (fun u => (W u) ^ 2 - 2 * W u) P :=
    hW2_int.sub (hW_int.const_mul 2)
  have hlin : ∫ u, (W u - 1) ^ 2 ∂P = Real.exp (sigma2 n) - 1 := by
    rw [show (fun u => (W u - 1) ^ 2) = (fun u => (W u) ^ 2 - 2 * W u + 1) from
      funext (fun u => by ring)]
    rw [integral_add hsub_int (integrable_const (1:ℝ)),
      integral_sub hW2_int (hW_int.const_mul 2), integral_const_mul, e1, e2, hone]
    ring

  have hfl_int : Integrable (fun u => (W u - 1) ^ 2) P := by
    have hbase : Integrable (fun u => (W u) ^ 2 - 2 * W u + 1) P :=
      (hW2_int.sub (hW_int.const_mul 2)).add (integrable_const (1:ℝ))
    refine hbase.congr ?_
    filter_upwards with u
    ring
  have hbridge := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfl_int
    (ae_of_all _ (fun u => sq_nonneg (W u - 1)))
  rw [hlin] at hbridge
  rw [hbridge]
  exact lintegral_congr (fun u => by rw [htoReal u])
  /- @proof-region region.target-node.session.b56ae601fec81e19 end -/

end Statlib.Imported
end

