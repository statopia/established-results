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
theorem statopia_math_node_4158364297_64e7b82f : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [MeasurableSpace U] [BorelSpace U]
    (e : HilbertBasis ℕ ℝ U) (lam : ℕ → ℝ) (hlam_pos : ∀ k : ℕ, 0 < lam k)
    (hlam_anti : Antitone lam) (Nc : ℕ) (hNc : 0 < Nc) (theta2 : Fin Nc → ℝ)
    (st : ℝ) (hst_nonneg : 0 ≤ st)
    (m0 : U) (D : ℕ → U)
    (hD : Tendsto (fun n : ℕ => (UScaleNorm e lam (1 + st) (D n - m0)) ^ (1 / 2 : ℝ))
      atTop (𝓝 0)),
    Tendsto (fun n : ℕ => ∑' k : ℕ,
        ((priorEigen lam Nc theta2) k)⁻¹ * (inner ℝ (e k) (D n - m0)) ^ 2) atTop (𝓝 0) := by
  /- @proof-region region.target-node.session.407414bd6f08958f begin -/
  intro U instNA instIPS instCS instMS instBS e lam hlam_pos hlam_anti Nc hNc theta2 st hst_nonneg m0 D hD
  classical
  set c : ℕ → ℝ := fun k => priorEigen lam Nc theta2 k with hc
  set W : ℕ → ℝ≥0∞ := fun n => UScaleNorm e lam (1 + st) (D n - m0) with hWdef
  have hcpos : ∀ k : ℕ, 0 < c k := by
    intro k
    show 0 < priorEigen lam Nc theta2 k
    unfold priorEigen
    split_ifs with h
    · exact Real.exp_pos _
    · exact hlam_pos k
  have hlam0 : 0 < lam 0 := hlam_pos 0
  set Lam : ℝ := max 1 (Finset.univ.sum (fun k : Fin Nc => lam k / c k)) with hLam
  have hLam1 : 1 ≤ Lam := by
    rw [hLam]
    exact le_max_left _ _
  have hLampos : 0 < Lam := lt_of_lt_of_le one_pos hLam1
  have hLamnn : 0 ≤ Lam := le_of_lt hLampos
  have hstep1 : ∀ k : ℕ, (c k)⁻¹ ≤ Lam * (lam k)⁻¹ := by
    intro k
    have hkpos : 0 < lam k := hlam_pos k
    rcases lt_or_ge k Nc with hk | hk
    · have hle : lam k / c k ≤ Lam := by
        rw [hLam]
        refine le_trans ?_ (le_max_right _ _)
        exact Finset.single_le_sum (f := fun k' : Fin Nc => lam k' / c k')
          (fun k' _ => div_nonneg (le_of_lt (hlam_pos k')) (le_of_lt (hcpos k')))
          (Finset.mem_univ (⟨k, hk⟩ : Fin Nc))
      have hunit : (c k)⁻¹ * lam k ≤ Lam := by
        rw [← div_eq_inv_mul]
        exact hle
      calc (c k)⁻¹ = (c k)⁻¹ * lam k * (lam k)⁻¹ := by
              rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hkpos), mul_one]
        _ ≤ Lam * (lam k)⁻¹ :=
              mul_le_mul_of_nonneg_right hunit (inv_nonneg.2 (le_of_lt hkpos))
    · have hck : c k = lam k := by
        show priorEigen lam Nc theta2 k = lam k
        unfold priorEigen
        rw [dif_neg (not_lt.mpr hk)]
      calc (c k)⁻¹ = (lam k)⁻¹ := by rw [hck]
        _ = 1 * (lam k)⁻¹ := (one_mul _).symm
        _ ≤ Lam * (lam k)⁻¹ :=
            mul_le_mul_of_nonneg_right hLam1 (inv_nonneg.2 (le_of_lt hkpos))
  have hstep2 : ∀ k : ℕ, (lam k)⁻¹ ≤ Real.rpow (lam 0) st * Real.rpow (lam k) (-(1 + st)) := by
    intro k
    have hk : 0 < lam k := hlam_pos k
    have hk0 : lam k ≤ lam 0 := hlam_anti (Nat.zero_le k)
    have hle : Real.rpow (lam k) st ≤ Real.rpow (lam 0) st :=
      Real.rpow_le_rpow (le_of_lt hk) hk0 hst_nonneg
    have hnn : 0 ≤ Real.rpow (lam k) (-(1 + st)) := Real.rpow_nonneg (le_of_lt hk) _
    calc (lam k)⁻¹ = Real.rpow (lam k) (-1) := (Real.rpow_neg_one (lam k)).symm
      _ = Real.rpow (lam k) (-(1 + st) + st) := by
            rw [show -(1 + st) + st = -(1:ℝ) by ring]
      _ = Real.rpow (lam k) (-(1 + st)) * Real.rpow (lam k) st := Real.rpow_add hk _ _
      _ ≤ Real.rpow (lam k) (-(1 + st)) * Real.rpow (lam 0) st :=
            mul_le_mul_of_nonneg_left hle hnn
      _ = Real.rpow (lam 0) st * Real.rpow (lam k) (-(1 + st)) := by ring
  set K : ℝ := Real.rpow (lam 0) st * Lam with hK
  have hKnn : 0 ≤ K := mul_nonneg (Real.rpow_nonneg (le_of_lt hlam0) _) hLamnn
  have hweight : ∀ k : ℕ, (c k)⁻¹ ≤ K * Real.rpow (lam k) (-(1 + st)) := by
    intro k
    calc (c k)⁻¹ ≤ Lam * (lam k)⁻¹ := hstep1 k
      _ ≤ Lam * (Real.rpow (lam 0) st * Real.rpow (lam k) (-(1 + st))) :=
            mul_le_mul_of_nonneg_left (hstep2 k) hLamnn
      _ = K * Real.rpow (lam k) (-(1 + st)) := by rw [hK]; ring
  have hpoint : ∀ (n k : ℕ),
      (c k)⁻¹ * (inner ℝ (e k) (D n - m0)) ^ 2 ≤
        K * (Real.rpow (lam k) (-(1 + st)) * (inner ℝ (e k) (D n - m0)) ^ 2) := by
    intro n k
    have hs : (0:ℝ) ≤ (inner ℝ (e k) (D n - m0)) ^ 2 := sq_nonneg _
    calc (c k)⁻¹ * (inner ℝ (e k) (D n - m0)) ^ 2
        ≤ (K * Real.rpow (lam k) (-(1 + st))) * (inner ℝ (e k) (D n - m0)) ^ 2 :=
          mul_le_mul_of_nonneg_right (hweight k) hs
      _ = K * (Real.rpow (lam k) (-(1 + st)) * (inner ℝ (e k) (D n - m0)) ^ 2) := by ring
  have hENN : ∀ n : ℕ,
      ENNReal.ofReal (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (D n - m0)) ^ 2) ≤ ENNReal.ofReal K * W n := by
    intro n
    have hnn : ∀ k : ℕ, 0 ≤ (c k)⁻¹ * (inner ℝ (e k) (D n - m0)) ^ 2 :=
      fun k => mul_nonneg (inv_nonneg.2 (le_of_lt (hcpos k))) (sq_nonneg _)
    by_cases hsum : Summable (fun k : ℕ => (c k)⁻¹ * (inner ℝ (e k) (D n - m0)) ^ 2)
    · rw [ENNReal.ofReal_tsum_of_nonneg hnn hsum]
      have hterm : ∀ k : ℕ, ENNReal.ofReal ((c k)⁻¹ * (inner ℝ (e k) (D n - m0)) ^ 2)
          ≤ ENNReal.ofReal K *
            ENNReal.ofReal (Real.rpow (lam k) (-(1 + st)) * (inner ℝ (e k) (D n - m0)) ^ 2) := by
        intro k
        rw [← ENNReal.ofReal_mul hKnn]
        exact ENNReal.ofReal_le_ofReal (hpoint n k)
      calc ∑' k : ℕ, ENNReal.ofReal ((c k)⁻¹ * (inner ℝ (e k) (D n - m0)) ^ 2)
          ≤ ∑' k : ℕ, ENNReal.ofReal K *
              ENNReal.ofReal (Real.rpow (lam k) (-(1 + st)) * (inner ℝ (e k) (D n - m0)) ^ 2) :=
            ENNReal.tsum_le_tsum hterm
        _ = ENNReal.ofReal K * ∑' k : ℕ,
              ENNReal.ofReal (Real.rpow (lam k) (-(1 + st)) * (inner ℝ (e k) (D n - m0)) ^ 2) :=
            ENNReal.tsum_mul_left
        _ = ENNReal.ofReal K * W n := rfl
    · have hzero : ∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (D n - m0)) ^ 2 = 0 :=
        tsum_eq_zero_of_not_summable hsum
      rw [hzero, ENNReal.ofReal_zero]
      exact zero_le _
  have hsq : ∀ x : ℝ≥0∞, x = (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
    intro x
    have h1 := (ENNReal.rpow_mul x (1 / 2 : ℝ) 2).symm
    rw [show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one] at h1
    exact h1.symm
  have hW : Tendsto W atTop (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro a ha
    by_cases haT : a = ⊤
    · rw [haT]
      exact Eventually.of_forall (fun n => le_top)
    · have har : 0 < a.toReal := ENNReal.toReal_pos (ne_of_gt ha) haT
      have hhalf : 0 < Real.rpow a.toReal (1/2:ℝ) := Real.rpow_pos_of_pos har _
      have hbridge : ENNReal.ofReal (Real.rpow a.toReal (1/2:ℝ)) = a ^ (1/2:ℝ) := by
        have h4 : ENNReal.ofReal a.toReal ^ (1/2:ℝ) = ENNReal.ofReal (Real.rpow a.toReal (1/2:ℝ)) :=
          ENNReal.ofReal_rpow_of_nonneg (le_of_lt har) (by norm_num : (0:ℝ) ≤ 1/2)
        rw [← h4]
        rw [ENNReal.ofReal_toReal haT]
      filter_upwards [(ENNReal.tendsto_nhds_zero.mp hD)
        (ENNReal.ofReal (Real.rpow a.toReal (1/2:ℝ)))
        (ENNReal.ofReal_pos.mpr hhalf)] with n hn
      rw [hbridge] at hn
      calc W n = (W n ^ (1/2:ℝ)) ^ (2:ℝ) := hsq (W n)
        _ ≤ (a ^ (1/2:ℝ)) ^ (2:ℝ) := ENNReal.rpow_le_rpow hn (by norm_num : (0:ℝ) ≤ 2)
        _ = ENNReal.ofReal (Real.rpow a.toReal (1/2:ℝ) ^ (2:ℝ)) := by
              rw [← hbridge]
              exact ENNReal.ofReal_rpow_of_nonneg (x := Real.rpow a.toReal (1/2:ℝ)) (p := 2)
                (le_of_lt hhalf) (by norm_num : (0:ℝ) ≤ 2)
        _ = ENNReal.ofReal a.toReal := by
              have h2 : (Real.rpow a.toReal (1/2:ℝ)) ^ (2:ℝ) = Real.rpow a.toReal ((1/2:ℝ) * 2) :=
                (Real.rpow_mul (le_of_lt har) (1/2:ℝ) 2).symm
              have h3 : Real.rpow a.toReal ((1/2:ℝ) * 2) = Real.rpow a.toReal (1:ℝ) := by
                rw [show (1/2:ℝ) * 2 = (1:ℝ) by norm_num]
              have h4 : Real.rpow a.toReal (1:ℝ) = a.toReal := Real.rpow_one a.toReal
              exact congrArg ENNReal.ofReal (h2.trans (h3.trans h4))
        _ = a := ENNReal.ofReal_toReal haT
  have hmul : Tendsto (fun n : ℕ => ENNReal.ofReal K * W n) atTop (𝓝 0) := by
    have h1 := ENNReal.Tendsto.mul_const (f := atTop) (m := W) (a := (0:ℝ≥0∞))
      (b := ENNReal.ofReal K) hW (Or.inr ENNReal.ofReal_ne_top)
    rw [zero_mul] at h1
    have h3 : (fun n : ℕ => W n * ENNReal.ofReal K) = (fun n : ℕ => ENNReal.ofReal K * W n) := by
      funext n
      exact mul_comm (W n) (ENNReal.ofReal K)
    rw [h3] at h1
    exact h1
  have hconv : Tendsto (fun n : ℕ =>
      ENNReal.ofReal (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (D n - m0)) ^ 2)) atTop (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro r hr
    have hr' := (tendsto_order.1 hmul).2 r hr
    exact hr'.mono (fun n hn => le_of_lt (lt_of_le_of_lt (hENN n) hn))
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro b hb
    exact Eventually.of_forall (fun n => lt_of_lt_of_le hb
      (tsum_nonneg fun k => mul_nonneg (inv_nonneg.2 (le_of_lt (hcpos k))) (sq_nonneg _)))
  · intro b hb
    have hb2 : (0:ℝ) < b / 2 := by linarith
    have hev : ∀ᶠ n in atTop, ENNReal.ofReal
        (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (D n - m0)) ^ 2) ≤ ENNReal.ofReal (b / 2) :=
      (ENNReal.tendsto_nhds_zero.mp hconv) (ENNReal.ofReal (b / 2))
        (ENNReal.ofReal_pos.mpr hb2)
    filter_upwards [hev] with n hn
    have hle := (ENNReal.ofReal_le_ofReal_iff (le_of_lt hb2)).mp hn
    linarith
  /- @proof-region region.target-node.session.407414bd6f08958f end -/

end Statlib.Imported
end

