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
theorem statopia_math_node_628101960_eb0c6fc8 : ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (ι : Type*) [Preorder ι] (bH : HilbertBasis ι ℝ H) (mu : ι → ℝ)
    (hmu : ∀ i : ι, 0 < mu i)
    (T st : ℝ) (hst : 0 < st)
    (Gammah : H →ₗ[ℝ] H) (hGammah_inj : ∀ v : H, Gammah v = 0 → v = 0)
    (Gammaih : H → H) (hGammaih : ∀ v : H, Gammaih (Gammah v) = v),
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y b : H,
      ENNReal.ofReal |inner ℝ (Gammaih y) b| ≤
        ENNReal.ofReal K * (HScaleNorm bH mu T y) ^ (1 / 2 : ℝ) *
          (HScaleNorm bH mu st b) ^ (1 / 2 : ℝ) := by
  /- @proof-region region.target-node.session.d712a13a339cae7b begin -/
  intro H _ _ _ ι _ bH mu hmu T st hst Gammah hGammah_inj Gammaih hGammaih
  classical
  haveI hfin : Finite ι :=
    Cardinal.lt_aleph0_iff_finite.mp
      (LinearIndependent.lt_aleph0_of_finiteDimensional (HilbertBasis.orthonormal bH).linearIndependent)
  haveI hft : Fintype ι := Fintype.ofFinite ι
  have key : ∀ (t w : ℝ), 0 ≤ w → (∀ i : ι, w ≤ Real.rpow (mu i) (-t)) → ∀ v : H,
      ENNReal.ofReal (w * ‖v‖ ^ 2) ≤ HScaleNorm bH mu t v := by
    intro t w hw hwle v
    have hsq : ∀ i : ι, (inner ℝ (bH i) v) ^ 2 = inner ℝ v (bH i) * inner ℝ (bH i) v := by
      intro i
      have h : inner ℝ v (bH i) = inner ℝ (bH i) v := by rw [real_inner_comm]
      rw [sq, h]
    have hsumm : Summable (fun i : ι => (inner ℝ (bH i) v) ^ 2) :=
      (HilbertBasis.summable_inner_mul_inner bH v v).congr (fun i => (hsq i).symm)
    have hparse : ENNReal.ofReal (‖v‖ ^ 2) =
        ∑' i : ι, ENNReal.ofReal ((inner ℝ (bH i) v) ^ 2) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (f := fun i : ι => (inner ℝ (bH i) v) ^ 2)
            (fun i => sq_nonneg _) hsumm]
      congr 1
      rw [← real_inner_self_eq_norm_sq v, ← HilbertBasis.tsum_inner_mul_inner bH v v]
      exact tsum_congr (fun i => (hsq i).symm)
    have hterm : ∀ i : ι, ENNReal.ofReal (w * (inner ℝ (bH i) v) ^ 2) ≤
        ENNReal.ofReal (Real.rpow (mu i) (-t) * (inner ℝ (bH i) v) ^ 2) := by
      intro i
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hwle i) (sq_nonneg _))
    calc ENNReal.ofReal (w * ‖v‖ ^ 2)
        = ENNReal.ofReal w * ENNReal.ofReal (‖v‖ ^ 2) := ENNReal.ofReal_mul hw
      _ = ENNReal.ofReal w * ∑' i : ι, ENNReal.ofReal ((inner ℝ (bH i) v) ^ 2) := by rw [hparse]
      _ = ∑' i : ι, ENNReal.ofReal w * ENNReal.ofReal ((inner ℝ (bH i) v) ^ 2) := by
            rw [ENNReal.tsum_mul_left]
      _ = ∑' i : ι, ENNReal.ofReal (w * (inner ℝ (bH i) v) ^ 2) := by
            apply tsum_congr
            intro i
            rw [ENNReal.ofReal_mul hw]
      _ ≤ ∑' i : ι, ENNReal.ofReal (Real.rpow (mu i) (-t) * (inner ℝ (bH i) v) ^ 2) :=
            ENNReal.tsum_le_tsum hterm
      _ = HScaleNorm bH mu t v := rfl
  have hweight : ∀ t : ℝ, ∃ w : ℝ, 0 < w ∧ ∀ i : ι, w ≤ Real.rpow (mu i) (-t) := by
    intro t
    by_cases hne : (Finset.univ : Finset ι).Nonempty
    · obtain ⟨i₀, -, hi₀⟩ :=
        Finset.exists_min_image (Finset.univ : Finset ι) (fun i => Real.rpow (mu i) (-t)) hne
      exact ⟨Real.rpow (mu i₀) (-t), Real.rpow_pos_of_pos (hmu i₀) _, fun j => hi₀ j (Finset.mem_univ j)⟩
    · exact ⟨1, one_pos, fun i => absurd ⟨i, Finset.mem_univ i⟩ hne⟩
  obtain ⟨wT, hwTpos, hwTle⟩ := hweight T
  obtain ⟨ws, hwspos, hwsle⟩ := hweight st
  have hinj : Function.Injective Gammah := by
    intro a b hab
    have h1 : Gammah (a - b) = 0 := by rw [map_sub, hab, sub_self]
    simpa only [sub_eq_zero] using hGammah_inj (a - b) h1
  let e : H ≃ₗ[ℝ] H := LinearEquiv.ofInjectiveEndo Gammah hinj
  have hGe : ∀ z : H, Gammaih z = e.symm z := by
    intro z
    have hz : Gammah (e.symm z) = z := by
      have h := LinearEquiv.apply_symm_apply e z
      exact h
    calc Gammaih z = Gammaih (Gammah (e.symm z)) := by rw [hz]
      _ = e.symm z := hGammaih (e.symm z)
  obtain ⟨cG, hcG0, hcG⟩ : ∃ c : ℝ, 0 ≤ c ∧ ∀ z : H, ‖Gammaih z‖ ≤ c * ‖z‖ := by
    let L : H →L[ℝ] H := ⟨(e.symm : H →ₗ[ℝ] H), LinearMap.continuous_of_finiteDimensional _⟩
    refine ⟨‖L‖, norm_nonneg L, fun z => ?_⟩
    calc ‖Gammaih z‖ = ‖e.symm z‖ := by rw [hGe z]
      _ = ‖L z‖ := rfl
      _ ≤ ‖L‖ * ‖z‖ := L.le_opNorm z
  have hfac : ∀ (t w : ℝ), 0 < w → (∀ i : ι, w ≤ Real.rpow (mu i) (-t)) →
      ∀ v : H, ENNReal.ofReal ‖v‖ ≤
        ENNReal.ofReal (1 / Real.sqrt w) * (HScaleNorm bH mu t v) ^ (1 / 2 : ℝ) := by
    intro t w hw hwle v
    have hmono : (ENNReal.ofReal (w * ‖v‖ ^ 2)) ^ (1 / 2 : ℝ) ≤ (HScaleNorm bH mu t v) ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow (key t w hw.le hwle v) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hlift : (ENNReal.ofReal (w * ‖v‖ ^ 2)) ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt w * ‖v‖) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hw.le (sq_nonneg _)) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      congr 1
      rw [← Real.sqrt_eq_rpow, Real.sqrt_mul hw.le, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg v)]
    rw [hlift] at hmono
    have hs : Real.sqrt w ≠ 0 := by
      intro h
      have h2 : w = 0 := by
        rw [← Real.sq_sqrt hw.le, h]
        norm_num
      exact absurd h2 hw.ne'
    calc ENNReal.ofReal ‖v‖
        = ENNReal.ofReal (1 / Real.sqrt w) * ENNReal.ofReal (Real.sqrt w * ‖v‖) := by
            rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 1 / Real.sqrt w by positivity)]
            congr 1
            field_simp
      _ ≤ ENNReal.ofReal (1 / Real.sqrt w) * (HScaleNorm bH mu t v) ^ (1 / 2 : ℝ) :=
            mul_le_mul_left' hmono _
  refine ⟨cG * (1 / Real.sqrt wT) * (1 / Real.sqrt ws), by positivity, ?_⟩
  intro y b
  have hinner : |inner ℝ (Gammaih y) b| ≤ cG * ‖y‖ * ‖b‖ := by
    calc |inner ℝ (Gammaih y) b| ≤ ‖Gammaih y‖ * ‖b‖ := abs_real_inner_le_norm _ _
      _ ≤ cG * ‖y‖ * ‖b‖ := mul_le_mul_of_nonneg_right (hcG y) (norm_nonneg b)
  have hcs : ENNReal.ofReal |inner ℝ (Gammaih y) b| ≤
      ENNReal.ofReal cG * ENNReal.ofReal ‖y‖ * ENNReal.ofReal ‖b‖ := by
    have h1 : ENNReal.ofReal (cG * ‖y‖ * ‖b‖) =
        ENNReal.ofReal cG * ENNReal.ofReal ‖y‖ * ENNReal.ofReal ‖b‖ := by
      rw [ENNReal.ofReal_mul (mul_nonneg hcG0 (norm_nonneg y)), ENNReal.ofReal_mul hcG0]
    rw [← h1, ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg hcG0 (norm_nonneg y)) (norm_nonneg b))]
    exact hinner
  calc ENNReal.ofReal |inner ℝ (Gammaih y) b|
      ≤ ENNReal.ofReal cG * ENNReal.ofReal ‖y‖ * ENNReal.ofReal ‖b‖ := hcs
    _ ≤ ENNReal.ofReal cG *
          (ENNReal.ofReal (1 / Real.sqrt wT) * (HScaleNorm bH mu T y) ^ (1 / 2 : ℝ)) *
          (ENNReal.ofReal (1 / Real.sqrt ws) * (HScaleNorm bH mu st b) ^ (1 / 2 : ℝ)) := by
          gcongr
          · exact hfac T wT hwTpos hwTle y
          · exact hfac st ws hwspos hwsle b
    _ = ENNReal.ofReal (cG * (1 / Real.sqrt wT) * (1 / Real.sqrt ws)) *
          (HScaleNorm bH mu T y) ^ (1 / 2 : ℝ) * (HScaleNorm bH mu st b) ^ (1 / 2 : ℝ) := by
          have hcoef : ENNReal.ofReal (cG * (1 / Real.sqrt wT) * (1 / Real.sqrt ws)) =
              ENNReal.ofReal cG * ENNReal.ofReal (1 / Real.sqrt wT) * ENNReal.ofReal (1 / Real.sqrt ws) := by
            rw [ENNReal.ofReal_mul (mul_nonneg hcG0 (show (0 : ℝ) ≤ 1 / Real.sqrt wT by positivity)),
              ENNReal.ofReal_mul hcG0]
          rw [hcoef]
          ac_rfl
  /- @proof-region region.target-node.session.d712a13a339cae7b end -/

end Statlib.Imported
end

