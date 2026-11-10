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
theorem statopia_math_node_2268300080_7eda57a7 : ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Gamma : H →L[ℝ] H) (hGamma_inj : ∀ v : H, Gamma v = 0 → v = 0)
    (Gammah : H →ₗ[ℝ] H) (hGammah_sq : ∀ v : H, Gammah (Gammah v) = Gamma v)
    (Gammaih : H → H) (hGammaih_left : ∀ v : H, Gammaih (Gammah v) = v)
    (iotaH : Type*) (bH : HilbertBasis iotaH ℝ H) (mu : iotaH → ℝ)
    (hmu_pos : ∀ i : iotaH, 0 < mu i)
    (hfin : FiniteDimensional ℝ H),
    ∃ C : ℝ, 0 < C ∧ (∀ v : H, ‖Gammaih v‖ ≤ C * ‖v‖) ∧
      (∀ i : iotaH, C⁻¹ ≤ mu i) ∧ (∀ i : iotaH, mu i ≤ C) := by
  /- @proof-region region.target-node.session.5fe89e5e0538fb7a begin -/
  intro H _ _ _ Gamma hGamma_inj Gammah hGammah_sq Gammaih hGammaih_left iotaH bH mu hmu_pos hfin
  haveI : FiniteDimensional ℝ H := hfin
  have hGammah_inj : Function.Injective Gammah := by
    intro u v huv
    have hkey : Gamma (u - v) = 0 := by
      rw [map_sub, ← hGammah_sq u, ← hGammah_sq v, huv, sub_self]
    exact sub_eq_zero.mp (hGamma_inj (u - v) hkey)
  have hGammah_surj : Function.Surjective Gammah := by
    have hker : Gammah.ker = ⊥ := (LinearMap.ker_eq_bot (f := Gammah)).mpr hGammah_inj
    have hrange : Gammah.range = ⊤ :=
      (LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank
        (rfl : Module.finrank ℝ H = Module.finrank ℝ H)).mp hker
    intro v
    have hv : v ∈ Gammah.range := by rw [hrange]; exact Submodule.mem_top
    exact LinearMap.mem_range.mp hv
  obtain ⟨K, hKpos, hK⟩ := (LinearMap.injective_iff_antilipschitz Gammah).mp hGammah_inj
  have hKbound : ∀ w : H, ‖w‖ ≤ (K : ℝ) * ‖Gammah w‖ := by
    intro w
    have h := (antilipschitzWith_iff_le_mul_dist (f := ⇑Gammah) (K := K)).mp hK w 0
    rw [map_zero] at h
    simp only [dist_eq_norm, sub_zero] at h
    exact h
  have hnorm : ∀ v : H, ‖Gammaih v‖ ≤ (K : ℝ) * ‖v‖ := by
    intro v
    obtain ⟨w, hw⟩ := hGammah_surj v
    have hv : Gammaih v = w := by rw [← hw]; exact hGammaih_left w
    have hb := hKbound w
    rw [hv, ← hw]
    exact hb
  have hfin_idx : Finite iotaH := by
    have hli : LinearIndependent ℝ (⇑bH : iotaH → H) := bH.orthonormal.linearIndependent
    have hcard : Cardinal.mk iotaH < Cardinal.aleph0 := hli.lt_aleph0_of_finiteDimensional
    exact Cardinal.lt_aleph0_iff_finite.mp hcard
  haveI : Fintype iotaH := Fintype.ofFinite iotaH
  have hS1n : 0 ≤ (Finset.univ : Finset iotaH).sum (fun i => mu i) :=
    Finset.sum_nonneg (fun i _ => (hmu_pos i).le)
  have hS2n : 0 ≤ (Finset.univ : Finset iotaH).sum (fun i => (mu i)⁻¹) :=
    Finset.sum_nonneg (fun i _ => (inv_pos.mpr (hmu_pos i)).le)
  have hKn : (0:ℝ) ≤ (K : ℝ) := by positivity
  refine ⟨(K : ℝ) + (Finset.univ : Finset iotaH).sum (fun i => mu i)
      + (Finset.univ : Finset iotaH).sum (fun i => (mu i)⁻¹) + 1, ?_, ?_, ?_, ?_⟩
  · linarith
  · intro v
    have hCge : (K : ℝ) ≤ (K : ℝ) + (Finset.univ : Finset iotaH).sum (fun i => mu i)
        + (Finset.univ : Finset iotaH).sum (fun i => (mu i)⁻¹) + 1 := by linarith
    exact le_trans (hnorm v) (mul_le_mul_of_nonneg_right hCge (norm_nonneg v))
  · intro i
    have hmem : i ∈ (Finset.univ : Finset iotaH) := Finset.mem_univ i
    have hinvle : (mu i)⁻¹ ≤ (Finset.univ : Finset iotaH).sum (fun j => (mu j)⁻¹) :=
      Finset.single_le_sum (fun j _ => (inv_pos.mpr (hmu_pos j)).le) hmem
    have hle : (mu i)⁻¹ ≤ (K : ℝ) + (Finset.univ : Finset iotaH).sum (fun j => mu j)
        + (Finset.univ : Finset iotaH).sum (fun j => (mu j)⁻¹) + 1 := by linarith
    have hCpos : (0:ℝ) < (K : ℝ) + (Finset.univ : Finset iotaH).sum (fun j => mu j)
        + (Finset.univ : Finset iotaH).sum (fun j => (mu j)⁻¹) + 1 := by linarith
    have hmul : (1:ℝ) ≤ mu i * ((K : ℝ) + (Finset.univ : Finset iotaH).sum (fun j => mu j)
        + (Finset.univ : Finset iotaH).sum (fun j => (mu j)⁻¹) + 1) := by
      have h1 := mul_le_mul_of_nonneg_left hle (hmu_pos i).le
      rwa [mul_inv_cancel₀ (ne_of_gt (hmu_pos i))] at h1
    have h2 := mul_le_mul_of_nonneg_right hmul (inv_nonneg.mpr hCpos.le)
    rw [one_mul, mul_assoc, mul_inv_cancel₀ (ne_of_gt hCpos), mul_one] at h2
    exact h2
  · intro i
    have hmem : i ∈ (Finset.univ : Finset iotaH) := Finset.mem_univ i
    have hmule : mu i ≤ (Finset.univ : Finset iotaH).sum (fun j => mu j) :=
      Finset.single_le_sum (fun j _ => (hmu_pos j).le) hmem
    linarith
  /- @proof-region region.target-node.session.5fe89e5e0538fb7a end -/

end Statlib.Imported
end

