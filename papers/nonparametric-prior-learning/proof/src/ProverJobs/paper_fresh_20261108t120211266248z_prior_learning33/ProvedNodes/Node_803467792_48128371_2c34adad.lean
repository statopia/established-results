import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_327730843_5f5f707b_e6718304

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
theorem statopia_math_node_803467792_48128371 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (e : HilbertBasis ℕ ℝ U) (lam : ℕ → ℝ)
    (hlam_pos : ∀ k : ℕ, 0 < lam k) (hlam_anti : Antitone lam)
    (Nc : ℕ) (hNc : 0 < Nc) (theta2 : Fin Nc → ℝ),
    ∃ Lam : ℝ,
      1 ≤ Lam ∧
      (∀ k : ℕ, lam k / Lam ≤ priorEigen lam Nc theta2 k) ∧
      (∀ (t : ℝ), 0 ≤ t → ∀ u : U, UScale e lam (1 + t) u →
        Summable (fun k : ℕ => (priorEigen lam Nc theta2 k)⁻¹ * (inner ℝ (e k) u) ^ 2) ∧
        (∑' k : ℕ, (priorEigen lam Nc theta2 k)⁻¹ * (inner ℝ (e k) u) ^ 2)
          ≤ Lam * Real.rpow (lam 0) t * ENNReal.toReal (UScaleNorm e lam (1 + t) u)) ∧
      (∀ (t : ℝ), 0 ≤ t → ∀ u : ℕ → U,
        (∀ n : ℕ, UScale e lam (1 + t) (u n)) →
        Tendsto (fun n : ℕ => (UScaleNorm e lam (1 + t) (u n)) ^ (1 / 2 : ℝ)) atTop (𝓝 0) →
        Tendsto (fun n : ℕ =>
            ∑' k : ℕ, (priorEigen lam Nc theta2 k)⁻¹ * (inner ℝ (e k) (u n)) ^ 2)
          atTop (𝓝 0)) := by
  /- @proof-region region.target-node.session.8f9022d9e362dc24 begin -/
  intro U _ _ e lam hlam_pos hlam_anti Nc hNc theta2
  classical
  haveI : Nonempty (Fin Nc) := ⟨⟨0, hNc⟩⟩
  let f : Fin Nc → ℝ := fun k => lam k / Real.exp (theta2 k)
  let S : ℝ := (Finset.univ : Finset (Fin Nc)).sup' Finset.univ_nonempty f
  have hS_bound : ∀ k : Fin Nc, f k ≤ S := fun k => Finset.le_sup' f (Finset.mem_univ k)
  have hLam_ge : (1:ℝ) ≤ max 1 S := le_max_left 1 S
  have hLam_pos : (0:ℝ) < max 1 S := lt_of_lt_of_le one_pos hLam_ge
  have hkey : ∀ k : ℕ, lam k / max 1 S ≤ priorEigen lam Nc theta2 k := by
    intro k
    have hpe : priorEigen lam Nc theta2 k
        = (if h : k < Nc then Real.exp (theta2 ⟨k, h⟩) else lam k) := rfl
    rw [hpe]
    split_ifs with hk
    · have h1 : lam k / Real.exp (theta2 ⟨k, hk⟩) ≤ S := hS_bound ⟨k, hk⟩
      have h2 : lam k ≤ S * Real.exp (theta2 ⟨k, hk⟩) :=
        (div_le_iff₀ (Real.exp_pos _)).mp h1
      have h3 : S * Real.exp (theta2 ⟨k, hk⟩) ≤ max 1 S * Real.exp (theta2 ⟨k, hk⟩) :=
        mul_le_mul_of_nonneg_right (le_max_right 1 S) (le_of_lt (Real.exp_pos _))
      rw [div_le_iff₀ hLam_pos]
      exact le_trans h2 (h3.trans (le_of_eq (mul_comm _ _)))
    · rw [div_le_iff₀ hLam_pos]
      calc lam k = lam k * 1 := by ring
        _ ≤ lam k * max 1 S := mul_le_mul_of_nonneg_left hLam_ge (le_of_lt (hlam_pos k))
  have hc_pos : ∀ k : ℕ, (0:ℝ) < priorEigen lam Nc theta2 k :=
    fun k => lt_of_lt_of_le (div_pos (hlam_pos k) hLam_pos) (hkey k)
  have hconj2 : ∀ (t : ℝ), 0 ≤ t → ∀ u : U, UScale e lam (1 + t) u →
      Summable (fun k : ℕ => (priorEigen lam Nc theta2 k)⁻¹ * (inner ℝ (e k) u) ^ 2) ∧
      (∑' k : ℕ, (priorEigen lam Nc theta2 k)⁻¹ * (inner ℝ (e k) u) ^ 2)
        ≤ max 1 S * (lam 0) ^ t * (UScaleNorm e lam (1 + t) u).toReal := by
    intro t ht u hu
    have hle : ∀ k : ℕ,
        (priorEigen lam Nc theta2 k)⁻¹ * (inner ℝ (e k) u) ^ 2
          ≤ (max 1 S * (lam 0) ^ t) * ((lam k) ^ (-(1 + t)) * (inner ℝ (e k) u) ^ 2) := by
      intro k
      have hcle : lam k ≤ priorEigen lam Nc theta2 k * max 1 S :=
        (div_le_iff₀ hLam_pos).mp (hkey k)
      have hstep : (priorEigen lam Nc theta2 k)⁻¹ * lam k ≤ max 1 S := by
        calc (priorEigen lam Nc theta2 k)⁻¹ * lam k
            ≤ (priorEigen lam Nc theta2 k)⁻¹ * (priorEigen lam Nc theta2 k * max 1 S) :=
              mul_le_mul_of_nonneg_left hcle (le_of_lt (inv_pos.mpr (hc_pos k)))
          _ = max 1 S := by
              rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (hc_pos k)), one_mul]
      have hii : (priorEigen lam Nc theta2 k)⁻¹ ≤ max 1 S * (lam k)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ (hlam_pos k)]
        exact hstep
      have hsplit : (lam k)⁻¹ = (lam k) ^ t * (lam k) ^ (-(1 + t)) := by
        have h1 : (lam k)⁻¹ = (lam k) ^ (-1:ℝ) := (Real.rpow_neg_one (lam k)).symm
        rw [h1]
        have h2 : (-1:ℝ) = t + -(1 + t) := by ring
        rw [h2, Real.rpow_add (hlam_pos k) t (-(1 + t))]
      have hiii : (lam k)⁻¹ ≤ (lam 0) ^ t * (lam k) ^ (-(1 + t)) := by
        rw [hsplit]
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (le_of_lt (hlam_pos k)) (hlam_anti (Nat.zero_le k)) ht)
          (Real.rpow_nonneg (le_of_lt (hlam_pos k)) (-(1 + t)))
      calc (priorEigen lam Nc theta2 k)⁻¹ * (inner ℝ (e k) u) ^ 2
          ≤ (max 1 S * (lam k)⁻¹) * (inner ℝ (e k) u) ^ 2 :=
            mul_le_mul_of_nonneg_right hii (sq_nonneg _)
        _ ≤ (max 1 S * ((lam 0) ^ t * (lam k) ^ (-(1 + t)))) * (inner ℝ (e k) u) ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hiii (le_of_lt hLam_pos)) (sq_nonneg _)
        _ = (max 1 S * (lam 0) ^ t) * ((lam k) ^ (-(1 + t)) * (inner ℝ (e k) u) ^ 2) := by ring
    have hK_nonneg : (0:ℝ) ≤ max 1 S * (lam 0) ^ t :=
      mul_nonneg (le_of_lt hLam_pos) (Real.rpow_nonneg (le_of_lt (hlam_pos 0)) t)
    have hC_nonneg : (0:ℝ) ≤ (UScaleNorm e lam (1 + t) u).toReal := ENNReal.toReal_nonneg
    have hU_ne_top : UScaleNorm e lam (1 + t) u ≠ ⊤ := ne_of_lt hu
    let F : ℕ → ENNReal :=
      fun k => ENNReal.ofReal ((priorEigen lam Nc theta2 k)⁻¹ * (inner ℝ (e k) u) ^ 2)
    let G : ℕ → ENNReal :=
      fun k => ENNReal.ofReal (Real.rpow (lam k) (-(1 + t)) * (inner ℝ (e k) u) ^ 2)
    have hF_step : ∀ k : ℕ, F k ≤ ENNReal.ofReal (max 1 S * (lam 0) ^ t) * G k := by
      intro k
      have h1 : F k ≤ ENNReal.ofReal ((max 1 S * (lam 0) ^ t) * ((lam k) ^ (-(1 + t)) * (inner ℝ (e k) u) ^ 2)) :=
        ENNReal.ofReal_le_ofReal (hle k)
      rw [ENNReal.ofReal_mul hK_nonneg] at h1
      exact h1
    have hF_le : ∑' k : ℕ, F k
        ≤ ENNReal.ofReal ((max 1 S * (lam 0) ^ t) * (UScaleNorm e lam (1 + t) u).toReal) := by
      have hG_eq : (∑' k : ℕ, G k) = UScaleNorm e lam (1 + t) u := by rfl
      calc ∑' k : ℕ, F k
          ≤ ∑' k : ℕ, ENNReal.ofReal (max 1 S * (lam 0) ^ t) * G k := ENNReal.tsum_le_tsum hF_step
        _ = ENNReal.ofReal (max 1 S * (lam 0) ^ t) * ∑' k : ℕ, G k := ENNReal.tsum_mul_left
        _ = ENNReal.ofReal (max 1 S * (lam 0) ^ t) * UScaleNorm e lam (1 + t) u := by rw [hG_eq]
        _ = ENNReal.ofReal (max 1 S * (lam 0) ^ t) * ENNReal.ofReal (UScaleNorm e lam (1 + t) u).toReal := by
              rw [ENNReal.ofReal_toReal hU_ne_top]
        _ = ENNReal.ofReal ((max 1 S * (lam 0) ^ t) * (UScaleNorm e lam (1 + t) u).toReal) := by
              rw [ENNReal.ofReal_mul hK_nonneg]
    have hF_ne_top : (∑' k : ℕ, F k) ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hF_le ENNReal.ofReal_lt_top)
    have hh_nonneg : ∀ k, 0 ≤ (priorEigen lam Nc theta2 k)⁻¹ * (inner ℝ (e k) u) ^ 2 :=
      fun k => mul_nonneg (le_of_lt (inv_pos.mpr (hc_pos k))) (sq_nonneg _)
    refine ⟨?_, ?_⟩
    · exact (summable_congr (fun k => ENNReal.toReal_ofReal (hh_nonneg k))).mp
        (ENNReal.summable_toReal hF_ne_top)
    · have hsum_eq : (∑' k : ℕ, (priorEigen lam Nc theta2 k)⁻¹ * (inner ℝ (e k) u) ^ 2)
          = (∑' k : ℕ, ENNReal.ofReal ((priorEigen lam Nc theta2 k)⁻¹ * (inner ℝ (e k) u) ^ 2)).toReal := by
        rw [ENNReal.tsum_toReal_eq (fun k => ENNReal.ofReal_ne_top)]
        exact tsum_congr (fun k => (ENNReal.toReal_ofReal (hh_nonneg k)).symm)
      rw [hsum_eq]
      exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hK_nonneg hC_nonneg) hF_le
  refine ⟨max 1 S, hLam_ge, hkey, ?_, ?_⟩
  · exact hconj2
  · intro t ht u hu hU
    have hK_nonneg : (0:ℝ) ≤ max 1 S * (lam 0) ^ t :=
      mul_nonneg (le_of_lt hLam_pos) (Real.rpow_nonneg (le_of_lt (hlam_pos 0)) t)
    have htoReal : Tendsto (fun n : ℕ => (UScaleNorm e lam (1 + t) (u n)).toReal) atTop (𝓝 0) :=
      statopia_math_node_327730843_5f5f707b (fun n => UScaleNorm e lam (1 + t) (u n))
        (fun n => ne_of_lt (hu n)) hU
    have hnonneg : ∀ n : ℕ, 0 ≤ ∑' k : ℕ, (priorEigen lam Nc theta2 k)⁻¹ * (inner ℝ (e k) (u n)) ^ 2 := by
      intro n
      exact tsum_nonneg (fun k => mul_nonneg (le_of_lt (inv_pos.mpr (hc_pos k))) (sq_nonneg _))
    have hle2 : ∀ n : ℕ, (∑' k : ℕ, (priorEigen lam Nc theta2 k)⁻¹ * (inner ℝ (e k) (u n)) ^ 2)
        ≤ (max 1 S * (lam 0) ^ t) * (UScaleNorm e lam (1 + t) (u n)).toReal := by
      intro n
      exact (hconj2 t ht (u n) (hu n)).2
    have hKt : Tendsto (fun n : ℕ => (max 1 S * (lam 0) ^ t) * (UScaleNorm e lam (1 + t) (u n)).toReal)
        atTop (𝓝 0) := by
      have := Tendsto.const_mul (max 1 S * (lam 0) ^ t) htoReal
      simpa using this
    exact squeeze_zero hnonneg hle2 hKt
  /- @proof-region region.target-node.session.8f9022d9e362dc24 end -/

end Statlib.Imported
end

