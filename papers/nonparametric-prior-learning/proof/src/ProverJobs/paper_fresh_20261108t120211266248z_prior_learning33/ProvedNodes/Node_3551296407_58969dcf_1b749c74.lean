import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_1768585877_01a1f85c_c590d0f5
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_2268300080_7eda57a7_47887b54
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3002875505_b32dcfa2_d1affbee
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3264912868_3df235ee_bd6bb5d8
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3335101267_d29aed84_787e2e17
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3476376768_6d4cc185_d1c985c7
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3944456172_a26782c9_98a9bbc9
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_54049410_53411e5b_5828847e

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
theorem statopia_math_node_3551296407_58969dcf : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (X : Type*)
    (LG : X → U → H)
    (Γ : H →L[ℝ] H) (hΓ_pos : Γ.IsPositive) (hΓ_inj : ∀ v : H, Γ v = 0 → v = 0)
    (Γh : H →ₗ[ℝ] H)
    (hΓh_symm : ∀ v w : H, inner ℝ (Γh v) w = inner ℝ v (Γh w))
    (hΓh_pos : ∀ v : H, 0 ≤ inner ℝ v (Γh v))
    (hΓh_sq : ∀ v : H, Γh (Γh v) = Γ v)
    (Γih : H → H) (hΓih_left : ∀ v : H, Γih (Γh v) = v)
    (e : HilbertBasis ℕ ℝ U) (lam : ℕ → ℝ) (hlam_pos : ∀ k : ℕ, 0 < lam k)
    (s0 : ℝ) (hs0_nonneg : 0 ≤ s0) (hs0_lt : s0 < 1)
    (hs0_trace : ∀ t : ℝ, s0 < t → Summable (fun k : ℕ => Real.rpow (lam k) t))
    (ιH : Type*) [Preorder ιH] (bH : HilbertBasis ιH ℝ H) (mu : ιH → ℝ)
    (hmu_pos : ∀ i : ιH, 0 < mu i)
    (C1 : H →L[ℝ] H) (hC1_pos : C1.IsPositive)
    (hC1_eigen : ∀ i : ιH, C1 (bH i) = mu i • bH i)
    (s1 : ℝ) (hs1_nonneg : 0 ≤ s1) (hs1_lt : s1 < 1)
    (C1c C2c : ℝ) (hC1c : 0 < C1c) (hC2c : 0 < C2c)
    (M1 : ℝ → ℝ) (hM1_mono : Monotone M1) (hM1_nonneg : ∀ r : ℝ, 0 ≤ M1 r)
    (M2 : ℝ → ℝ → ℝ) (hM2_nonneg : ∀ r1 r2 : ℝ, 0 ≤ M2 r1 r2)
    (hM2_mono_fst : ∀ r2 : ℝ, Monotone (fun r : ℝ => M2 r r2))
    (hM2_mono_snd : ∀ r1 : ℝ, Monotone (fun r : ℝ => M2 r1 r))
    (s st α : ℝ) (hs_gt : s1 < s) (hs_le : s ≤ 1) (hst_gt : s0 < st) (hst_le : st ≤ 1)
    (hα : 0 ≤ α)
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
    (hLG_all_range : ∀ (x : X) (u : U), UScale e lam (1 - st) u → ∃ w : H, Γh w = LG x u)
    (hHsub : ∀ w : H, HScale bH mu (α - s) w → ∃ a : H, Γh a = w), ∃ (mubar : ℝ) (kappa : ℝ), 1 ≤ mubar ∧ 0 ≤ kappa ∧
      ∀ (x x' : X) (y y' : H), HScale bH mu (α - s) y → HScale bH mu (α - s) y' →
        ∀ (u u1 u2 : U), UScale e lam (1 - st) u → UScale e lam (1 - st) u1 →
          UScale e lam (1 - st) u2 →
          (|inner ℝ (Γih y) (Γih (LG x u))| ≤
              kappa * ENNReal.toReal (HScaleDist bH mu (α - s) y 0) *
                M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ∧
          ((1 / 2 : ℝ) * ‖Γih (LG x u)‖ ^ 2 ≤
              (1 / 2 : ℝ) * (mubar ^ st) *
                (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2) ∧
          (Phi Γih LG u x y ≥
              - (kappa * ENNReal.toReal (HScaleDist bH mu (α - s) y 0) *
                  M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)))) ∧
          (Phi Γih LG u x y ≤
              (1 / 2 : ℝ) * (mubar ^ st) *
                  (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2 +
                kappa * ENNReal.toReal (HScaleDist bH mu (α - s) y 0) *
                  M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ∧
          (|Phi Γih LG u1 x y - Phi Γih LG u2 x y| ≤
              ((mubar ^ st) *
                  (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u1 0)) +
                    M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u2 0))) +
                kappa * ENNReal.toReal (HScaleDist bH mu (α - s) y 0)) *
                M2 (ENNReal.toReal (UScaleDist e lam (1 - st) u1 0))
                  (ENNReal.toReal (UScaleDist e lam (1 - st) u2 0)) *
                ENNReal.toReal (UScaleDist e lam (1 - st) u1 u2)) ∧
          (|Phi Γih LG u x y - Phi Γih LG u x y'| ≤
              kappa * ENNReal.toReal (HScaleDist bH mu (α - s) y y') *
                M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ∧
          (|Phi Γih LG u x y - Phi Γih LG u x' y| ≤
              ((mubar ^ st) * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) +
                kappa * ENNReal.toReal (HScaleDist bH mu (α - s) y 0)) *
                ENNReal.toReal (HScaleDist bH mu st (Γih (LG x u - LG x' u)) 0)) ∧
          (ENNReal.toReal (HScaleDist bH mu st (Γih (LG x u - LG x' u)) 0) ≤
              2 * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) := by
  /- @proof-region region.target-node.session.5178d8803b63248c begin -/
  classical
  intro U instU1 instU2 instU3 H instH1 instH2 instH3 X LG Γ hΓ_pos hΓ_inj Γh hΓh_symm hΓh_pos
    hΓh_sq Γih hΓih_left e lam hlam_pos s0 hs0_nonneg hs0_lt hs0_trace ιH instιH bH mu hmu_pos
    C1 hC1_pos hC1_eigen s1 hs1_nonneg hs1_lt C1c C2c hC1c hC2c M1 hM1_mono hM1_nonneg M2
    hM2_nonneg hM2_mono_fst hM2_mono_snd s st α hs_gt hs_le hst_gt hst_le hα hA1 hA2 hA3
    hLG_all_range hHsub
  have hB1 : ∀ i : ιH, ‖bH i‖ = 1 := fun i => bH.orthonormal.norm_eq_one i
  have hmu_inner : ∀ i : ιH, mu i = inner ℝ (bH i) (C1 (bH i)) := by
    intro i
    rw [hC1_eigen i, real_inner_smul_right, real_inner_self_eq_norm_sq, hB1 i]
    ring
  have hmu_le : ∀ i : ιH, mu i ≤ max 1 ‖C1‖ := by
    intro i
    rw [hmu_inner i]
    calc inner ℝ (bH i) (C1 (bH i))
        ≤ |inner ℝ (bH i) (C1 (bH i))| := le_abs_self _
      _ ≤ ‖bH i‖ * ‖C1 (bH i)‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖bH i‖ * (‖C1‖ * ‖bH i‖) := by
            gcongr
            exact C1.le_opNorm (bH i)
      _ = ‖C1‖ := by rw [hB1 i]; ring
      _ ≤ max 1 ‖C1‖ := le_max_right 1 _
  have hΓih_sub : ∀ a b : H, (∃ α : H, Γh α = a) → (∃ β : H, Γh β = b) →
      Γih (a - b) = Γih a - Γih b := by
    intro a b ha hb
    obtain ⟨α, rfl⟩ := ha
    obtain ⟨β, rfl⟩ := hb
    rw [← map_sub]
    simp only [hΓih_left]
  have hkappa_nonneg : 0 ≤ (if h : FiniteDimensional ℝ H then max 1 (Real.rpow (Classical.choose (statopia_math_node_2268300080_7eda57a7 H Γ hΓ_inj Γh hΓh_sq Γih hΓih_left ιH bH mu hmu_pos h)) (2 + st + |α - s|)) else C1c) := by
    split_ifs with h
    · exact le_trans zero_le_one (le_max_left 1 _)
    · exact le_of_lt hC1c
  refine ⟨max 1 ‖C1‖, (if h : FiniteDimensional ℝ H then max 1 (Real.rpow (Classical.choose (statopia_math_node_2268300080_7eda57a7 H Γ hΓ_inj Γh hΓh_sq Γih hΓih_left ιH bH mu hmu_pos h)) (2 + st + |α - s|)) else C1c),
    le_max_left 1 ‖C1‖, hkappa_nonneg, ?_⟩
  intro x x' y y' hy hy' u u1 u2 hu hu1 hu2
  have hXfin : HScaleNorm bH mu st (Γih (LG x u) - Γih (LG x' u)) ≠ ⊤ := by
    have hstn : 0 ≤ st := le_trans hs0_nonneg (le_of_lt hst_gt)
    have hsub := statopia_math_node_3002875505_b32dcfa2 H ιH bH mu hmu_pos st hstn
      (Γih (LG x u)) (-(Γih (LG x' u)))
    have hneg : HScaleNorm bH mu st (-(Γih (LG x' u))) = HScaleNorm bH mu st (Γih (LG x' u)) := by
      unfold HScaleNorm
      apply tsum_congr
      intro i
      rw [inner_neg_right, neg_sq]
    rw [hneg, ← sub_eq_add_neg] at hsub
    have hle : (HScaleNorm bH mu st (Γih (LG x u))) ^ (1/2:ℝ) +
        (HScaleNorm bH mu st (Γih (LG x' u))) ^ (1/2:ℝ) ≤
        ENNReal.ofReal (2 * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) := by
      refine le_trans (add_le_add (hA2 x u hu) (hA2 x' u hu)) ?_
      rw [← ENNReal.ofReal_add (hM1_nonneg _) (hM1_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      linarith
    have hlt : (HScaleNorm bH mu st (Γih (LG x u) - Γih (LG x' u))) ^ (1/2:ℝ) < ⊤ :=
      lt_of_le_of_lt (le_trans hsub hle) ENNReal.ofReal_lt_top
    intro htop
    rw [htop, ENNReal.top_rpow_of_pos (show (0:ℝ) < 1/2 by norm_num)] at hlt
    exact absurd hlt (lt_irrefl ⊤)
  have hinner_gen : ∀ (w v : H), HScale bH mu (α - s) w →
      (HScaleNorm bH mu st v) ^ (1/2:ℝ) ≠ ⊤ →
      |inner ℝ (Γih w) v| ≤
        (if h : FiniteDimensional ℝ H then max 1 (Real.rpow (Classical.choose (statopia_math_node_2268300080_7eda57a7 H Γ hΓ_inj Γh hΓh_sq Γih hΓih_left ιH bH mu hmu_pos h)) (2 + st + |α - s|)) else C1c) * ENNReal.toReal (HScaleDist bH mu (α - s) w 0) *
          ((HScaleNorm bH mu st v) ^ (1/2:ℝ)).toReal := by
    intro w v hw hvn
    split_ifs with hfin
    · obtain ⟨hCpos, hCbound, hClo, hChi⟩ := Classical.choose_spec (statopia_math_node_2268300080_7eda57a7 H Γ hΓ_inj Γh hΓh_sq Γih hΓih_left ιH bH mu hmu_pos hfin)
      set C : ℝ := Classical.choose (statopia_math_node_2268300080_7eda57a7 H Γ hΓ_inj Γh hΓh_sq Γih hΓih_left ιH bH mu hmu_pos hfin) with hCdef
      have hst_nonneg : 0 ≤ st := le_trans hs0_nonneg (le_of_lt hst_gt)
      have hCnn : 0 ≤ C := le_of_lt hCpos
      have hA0 : 0 ≤ (HScaleNorm bH mu (α - s) w).toReal := ENNReal.toReal_nonneg
      have hHD0 : 0 ≤ ENNReal.toReal (HScaleDist bH mu (α - s) w 0) := ENNReal.toReal_nonneg
      have hWv0 : 0 ≤ ((HScaleNorm bH mu st v) ^ (1/2:ℝ)).toReal := ENNReal.toReal_nonneg
      have hB0 : 0 ≤ (HScaleNorm bH mu st v).toReal := ENNReal.toReal_nonneg
      have hy_ne : HScaleNorm bH mu (α - s) w ≠ ⊤ := ne_of_lt hw
      have hv_ne : HScaleNorm bH mu st v ≠ ⊤ := by
        intro htop
        rw [htop, ENNReal.top_rpow_of_pos (show (0:ℝ) < 1/2 by norm_num)] at hvn
        exact hvn rfl
      have hYb : ‖w‖ ^ 2 ≤ Real.rpow C |α - s| * (HScaleNorm bH mu (α - s) w).toReal :=
        statopia_math_node_3335101267_d29aed84 H ιH bH mu hmu_pos C hCpos hClo hChi (α - s) w hy_ne
      have hVb : ‖v‖ ^ 2 ≤ Real.rpow C |st| * (HScaleNorm bH mu st v).toReal :=
        statopia_math_node_3335101267_d29aed84 H ιH bH mu hmu_pos C hCpos hClo hChi st v hv_ne
      have hWv2 : (((HScaleNorm bH mu st v) ^ (1/2:ℝ)).toReal) ^ 2 = (HScaleNorm bH mu st v).toReal := by
        rw [← ENNReal.toReal_rpow]
        rw [show (HScaleNorm bH mu st v).toReal ^ (1/2:ℝ) = Real.sqrt ((HScaleNorm bH mu st v).toReal) from (Real.sqrt_eq_rpow _).symm]
        exact Real.sq_sqrt hB0
      rw [← hWv2] at hVb
      have hHD2 : (ENNReal.toReal (HScaleDist bH mu (α - s) w 0)) ^ 2 = (HScaleNorm bH mu (α - s) w).toReal := by
        unfold HScaleDist
        rw [sub_zero, ← ENNReal.toReal_rpow]
        rw [show (HScaleNorm bH mu (α - s) w).toReal ^ (1/2:ℝ) = Real.sqrt ((HScaleNorm bH mu (α - s) w).toReal) from (Real.sqrt_eq_rpow _).symm]
        exact Real.sq_sqrt hA0
      have hGysq : ‖Γih w‖ ^ 2 ≤ C ^ 2 * ‖w‖ ^ 2 := by
        have h := mul_self_le_mul_self (norm_nonneg (Γih w)) (hCbound w)
        nlinarith [h]
      have hkey : C ^ 2 * Real.rpow C |α - s| * Real.rpow C |st| ≤ (max 1 (Real.rpow C (2 + st + |α - s|))) ^ 2 := by
        have hst_abs : |st| = st := abs_of_nonneg hst_nonneg
        have hE : C ^ 2 * Real.rpow C |α - s| * Real.rpow C |st| = Real.rpow C (2 + st + |α - s|) := by
          rw [hst_abs, show C ^ 2 = Real.rpow C 2 from (Real.rpow_natCast C 2).symm]
          change C ^ (2:ℝ) * C ^ (|α - s|) * C ^ st = C ^ (2 + st + |α - s|)
          rw [← Real.rpow_add hCpos, ← Real.rpow_add hCpos]
          congr 1
          ring
        rw [hE]
        calc Real.rpow C (2 + st + |α - s|) ≤ max 1 (Real.rpow C (2 + st + |α - s|)) := le_max_right 1 _
          _ ≤ (max 1 (Real.rpow C (2 + st + |α - s|))) ^ 2 := by
                nlinarith [le_max_left (1:ℝ) (Real.rpow C (2 + st + |α - s|))]
      have hP2 : (‖Γih w‖ * ‖v‖) ^ 2 ≤
          ((max 1 (Real.rpow C (2 + st + |α - s|))) * ENNReal.toReal (HScaleDist bH mu (α - s) w 0) * ((HScaleNorm bH mu st v) ^ (1/2:ℝ)).toReal) ^ 2 := by
        have hC2 : (0:ℝ) ≤ C ^ 2 := sq_nonneg _
        have hCa : (0:ℝ) ≤ Real.rpow C |α - s| := Real.rpow_nonneg hCnn _
        have hCs : (0:ℝ) ≤ Real.rpow C |st| := Real.rpow_nonneg hCnn _
        calc (‖Γih w‖ * ‖v‖) ^ 2
            = ‖Γih w‖ ^ 2 * ‖v‖ ^ 2 := by ring
          _ ≤ (C ^ 2 * ‖w‖ ^ 2) * (Real.rpow C |st| * (((HScaleNorm bH mu st v) ^ (1/2:ℝ)).toReal) ^ 2) :=
                mul_le_mul hGysq hVb (sq_nonneg _) (mul_nonneg hC2 (sq_nonneg _))
          _ ≤ (C ^ 2 * (Real.rpow C |α - s| * (HScaleNorm bH mu (α - s) w).toReal)) * (Real.rpow C |st| * (((HScaleNorm bH mu st v) ^ (1/2:ℝ)).toReal) ^ 2) := by
                apply mul_le_mul
                · exact mul_le_mul_of_nonneg_left hYb hC2
                · exact le_refl _
                · exact mul_nonneg hCs (sq_nonneg _)
                · exact mul_nonneg hC2 (mul_nonneg hCa hA0)
          _ = (C ^ 2 * Real.rpow C |α - s| * Real.rpow C |st|) * ((HScaleNorm bH mu (α - s) w).toReal * (((HScaleNorm bH mu st v) ^ (1/2:ℝ)).toReal) ^ 2) := by ring
          _ ≤ ((max 1 (Real.rpow C (2 + st + |α - s|))) ^ 2) * ((HScaleNorm bH mu (α - s) w).toReal * (((HScaleNorm bH mu st v) ^ (1/2:ℝ)).toReal) ^ 2) :=
                mul_le_mul_of_nonneg_right hkey (mul_nonneg hA0 (sq_nonneg _))
          _ = ((max 1 (Real.rpow C (2 + st + |α - s|))) * ENNReal.toReal (HScaleDist bH mu (α - s) w 0) * ((HScaleNorm bH mu st v) ^ (1/2:ℝ)).toReal) ^ 2 := by
                rw [← hHD2]; ring
      have hnn1 : (0:ℝ) ≤ ‖Γih w‖ * ‖v‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
      have hnn2 : (0:ℝ) ≤ (max 1 (Real.rpow C (2 + st + |α - s|))) * ENNReal.toReal (HScaleDist bH mu (α - s) w 0) * ((HScaleNorm bH mu st v) ^ (1/2:ℝ)).toReal :=
        mul_nonneg (mul_nonneg (le_trans zero_le_one (le_max_left (1:ℝ) _)) hHD0) hWv0
      refine le_trans (abs_real_inner_le_norm (Γih w) v) ?_
      have hsq := Real.sqrt_le_sqrt hP2
      rw [Real.sqrt_sq hnn1, Real.sqrt_sq hnn2] at hsq
      exact hsq
    · have hA1y := hA1 hfin w (α - s1 - 1) hw (Int.floor_le (α - s1 - 1)) (by linarith)
      have hA1b := hA1y.2.2.2.1
      have hAsub : HScale bH mu (-st) (Γih w) := hA1y.1
      have hW := statopia_math_node_54049410_53411e5b H ιH bH mu hmu_pos st (Γih w) v
      have hX1_ne : (HScaleNorm bH mu (α - s) w) ^ (1/2:ℝ) ≠ ⊤ :=
        ne_of_lt (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ne_of_lt hw))
      have hA1_ne : (HScaleNorm bH mu (-st) (Γih w)) ^ (1/2:ℝ) ≠ ⊤ :=
        ne_of_lt (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ne_of_lt hAsub))
      have hX1eq : (HScaleNorm bH mu (α - s) w) ^ (1/2:ℝ) =
          ENNReal.ofReal ((HScaleNorm bH mu (α - s) w) ^ (1/2:ℝ)).toReal :=
        (ENNReal.ofReal_toReal hX1_ne).symm
      have hA1eq : (HScaleNorm bH mu (-st) (Γih w)) ^ (1/2:ℝ) =
          ENNReal.ofReal ((HScaleNorm bH mu (-st) (Γih w)) ^ (1/2:ℝ)).toReal :=
        (ENNReal.ofReal_toReal hA1_ne).symm
      have hVeq' : (HScaleNorm bH mu st v) ^ (1/2:ℝ) =
          ENNReal.ofReal ((HScaleNorm bH mu st v) ^ (1/2:ℝ)).toReal :=
        (ENNReal.ofReal_toReal hvn).symm
      have hA1real : ((HScaleNorm bH mu (-st) (Γih w)) ^ (1/2:ℝ)).toReal ≤
          C1c * ((HScaleNorm bH mu (α - s) w) ^ (1/2:ℝ)).toReal := by
        have h := hA1b
        rw [hX1eq, ← ENNReal.ofReal_mul (le_of_lt hC1c)] at h
        exact ENNReal.toReal_le_of_le_ofReal
          (mul_nonneg (le_of_lt hC1c) ENNReal.toReal_nonneg) h
      have hWreal : |inner ℝ (Γih w) v| ≤
          ((HScaleNorm bH mu (-st) (Γih w)) ^ (1/2:ℝ)).toReal *
            ((HScaleNorm bH mu st v) ^ (1/2:ℝ)).toReal := by
        have h := hW
        rw [hA1eq, hVeq',
          ← ENNReal.ofReal_mul
            (show (0:ℝ) ≤ ((HScaleNorm bH mu (-st) (Γih w)) ^ (1/2:ℝ)).toReal
              from ENNReal.toReal_nonneg)] at h
        have h2 := ENNReal.toReal_le_of_le_ofReal
          (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) h
        rwa [ENNReal.toReal_ofReal (abs_nonneg _)] at h2
      have hHX : HScaleDist bH mu (α - s) w 0 = (HScaleNorm bH mu (α - s) w) ^ (1/2:ℝ) := by
        unfold HScaleDist
        rw [sub_zero]
      rw [hHX]
      calc |inner ℝ (Γih w) v|
          ≤ ((HScaleNorm bH mu (-st) (Γih w)) ^ (1/2:ℝ)).toReal *
              ((HScaleNorm bH mu st v) ^ (1/2:ℝ)).toReal := hWreal
        _ ≤ (C1c * ((HScaleNorm bH mu (α - s) w) ^ (1/2:ℝ)).toReal) *
              ((HScaleNorm bH mu st v) ^ (1/2:ℝ)).toReal :=
              mul_le_mul hA1real le_rfl ENNReal.toReal_nonneg
                (mul_nonneg (le_of_lt hC1c) ENNReal.toReal_nonneg)
  have hinner_bound : ∀ (w : H), HScale bH mu (α - s) w → |inner ℝ (Γih w) (Γih (LG x u))| ≤
      (if h : FiniteDimensional ℝ H then max 1 (Real.rpow (Classical.choose (statopia_math_node_2268300080_7eda57a7 H Γ hΓ_inj Γh hΓh_sq Γih hΓih_left ιH bH mu hmu_pos h)) (2 + st + |α - s|)) else C1c) * ENNReal.toReal (HScaleDist bH mu (α - s) w 0) *
        M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := by
    intro w hw
    have hv_sq_ne : (HScaleNorm bH mu st (Γih (LG x u))) ^ (1/2:ℝ) ≠ ⊤ := by
      intro htop
      have hA2hu := hA2 x u hu
      rw [htop] at hA2hu
      exact absurd hA2hu (not_le.mpr ENNReal.ofReal_lt_top)
    have hbound := hinner_gen w (Γih (LG x u)) hw hv_sq_ne
    have hM1 : ((HScaleNorm bH mu st (Γih (LG x u))) ^ (1/2:ℝ)).toReal ≤
        M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) :=
      ENNReal.toReal_le_of_le_ofReal (hM1_nonneg _) (hA2 x u hu)
    exact le_trans hbound (mul_le_mul_of_nonneg_left hM1 (mul_nonneg hkappa_nonneg ENNReal.toReal_nonneg))
  have hVnorm_bound : ‖Γih (LG x u)‖ ^ 2 ≤ (max 1 ‖C1‖) ^ st *
      (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2 := by
    have hst_nonneg : 0 ≤ st := le_trans hs0_nonneg (le_of_lt hst_gt)
    have hM_ge_one : 1 ≤ max 1 ‖C1‖ := le_max_left 1 _
    have hMpos : (0:ℝ) < max 1 ‖C1‖ := lt_of_lt_of_le one_pos hM_ge_one
    have hspec := statopia_math_node_3476376768_6d4cc185 H ιH bH mu
      (max 1 ‖C1‖) hmu_pos hM_ge_one hmu_le st hst_nonneg (Γih (LG x u))
    have hA2hu := hA2 x u hu
    have hA_ne_top : HScaleNorm bH mu st (Γih (LG x u)) ≠ ⊤ := by
      intro htop
      rw [htop, ENNReal.top_rpow_of_pos (show (0:ℝ) < 1/2 by norm_num)] at hA2hu
      exact (not_le.mpr ENNReal.ofReal_lt_top) hA2hu
    have h1 : (HScaleNorm bH mu st (Γih (LG x u))).toReal ^ (1/2:ℝ) ≤
        M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hA2hu
      rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (hM1_nonneg _)] at h
      exact h
    have h2 : (HScaleNorm bH mu st (Γih (LG x u))).toReal ≤
        (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2 := by
      have hbase : 0 ≤ (HScaleNorm bH mu st (Γih (LG x u))).toReal := ENNReal.toReal_nonneg
      have hsq : Real.sqrt (HScaleNorm bH mu st (Γih (LG x u))).toReal ≤
          M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := by
        rw [Real.sqrt_eq_rpow]; exact h1
      calc (HScaleNorm bH mu st (Γih (LG x u))).toReal
          = (Real.sqrt (HScaleNorm bH mu st (Γih (LG x u))).toReal) ^ 2 := (Real.sq_sqrt hbase).symm
        _ ≤ (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2 := by
              simpa only [pow_two] using mul_self_le_mul_self (Real.sqrt_nonneg _) hsq
    have hA_le : HScaleNorm bH mu st (Γih (LG x u)) ≤
        ENNReal.ofReal ((M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2) := by
      rw [← ENNReal.ofReal_toReal hA_ne_top]
      exact ENNReal.ofReal_le_ofReal h2
    have hspec' : ENNReal.ofReal (‖Γih (LG x u)‖ ^ 2) ≤
        ENNReal.ofReal ((max 1 ‖C1‖) ^ st) * HScaleNorm bH mu st (Γih (LG x u)) := hspec
    have hmain : ENNReal.ofReal (‖Γih (LG x u)‖ ^ 2) ≤
        ENNReal.ofReal ((max 1 ‖C1‖) ^ st *
          (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2) := by
      calc ENNReal.ofReal (‖Γih (LG x u)‖ ^ 2)
          ≤ ENNReal.ofReal ((max 1 ‖C1‖) ^ st) *
              HScaleNorm bH mu st (Γih (LG x u)) := hspec'
        _ ≤ ENNReal.ofReal ((max 1 ‖C1‖) ^ st) *
              ENNReal.ofReal ((M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2) := by
              gcongr
        _ = ENNReal.ofReal ((max 1 ‖C1‖) ^ st *
              (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2) := by
              rw [ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt hMpos) st)]
    exact (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (Real.rpow_nonneg (le_of_lt hMpos) st) (sq_nonneg _))).mp hmain
  have sq_half : ∀ (a : ℝ), 0 ≤ a → (a ^ (1/2:ℝ))^2 = a := by
    intro a ha
    rw [show a ^ (1/2:ℝ) = Real.sqrt a from (Real.sqrt_eq_rpow a).symm, Real.sq_sqrt ha]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hinner_bound y hy
  · nlinarith [hVnorm_bound]
  · unfold Phi
    nlinarith [hinner_bound y hy, le_abs_self (inner ℝ (Γih y) (Γih (LG x u))),
      sq_nonneg ‖Γih (LG x u)‖]
  · unfold Phi
    nlinarith [hVnorm_bound, (abs_le.mp (hinner_bound y hy)).1, (abs_le.mp (hinner_bound y hy)).2]
  · have huc : UScale e lam (1 - st) (u1 - u2) :=
      statopia_math_node_3944456172_a26782c9 U e lam hlam_pos (1 - st) u1 u2 hu1 hu2
    have hUDeq : UScaleDist e lam (1 - st) u1 u2 = UScaleDist e lam (1 - st) (u1 - u2) 0 := by
      unfold UScaleDist
      rw [sub_zero]
    have hU_ne : UScaleDist e lam (1 - st) u1 u2 ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ne_of_lt huc)
    have hstn : 0 ≤ st := le_trans hs0_nonneg (le_of_lt hst_gt)
    have hMge1 : 1 ≤ max 1 ‖C1‖ := le_max_left 1 _
    have hMpos : (0:ℝ) < max 1 ‖C1‖ := lt_of_lt_of_le one_pos hMge1
    have hcnonneg : (0:ℝ) ≤ (max 1 ‖C1‖) ^ st := Real.rpow_nonneg (le_of_lt hMpos) st
    have hlin_u : Γih (LG x u1 - LG x u2) = Γih (LG x u1) - Γih (LG x u2) :=
      hΓih_sub (LG x u1) (LG x u2) (hLG_all_range x u1 hu1) (hLG_all_range x u2 hu2)
    set V : ℝ := M2 (ENNReal.toReal (UScaleDist e lam (1 - st) u1 0)) (ENNReal.toReal (UScaleDist e lam (1 - st) u2 0)) * ENNReal.toReal (UScaleDist e lam (1 - st) u1 u2) with hVdef
    have hVnn : 0 ≤ V := by
      rw [hVdef]
      exact mul_nonneg (hM2_nonneg _ _) ENNReal.toReal_nonneg
    have h1 : ‖Γih (LG x u1) - Γih (LG x u2)‖ ^ 2 ≤ (max 1 ‖C1‖) ^ st * V ^ 2 := by
      have hA3xu := hA3 x u1 u2 hu1 hu2 huc
      rw [← hUDeq] at hA3xu
      have hRHS : ENNReal.ofReal (M2 (ENNReal.toReal (UScaleDist e lam (1 - st) u1 0)) (ENNReal.toReal (UScaleDist e lam (1 - st) u2 0))) * UScaleDist e lam (1 - st) u1 u2 = ENNReal.ofReal V := by
        rw [hVdef]
        conv_lhs => rw [← ENNReal.ofReal_toReal hU_ne]
        rw [← ENNReal.ofReal_mul (hM2_nonneg _ _)]
      rw [hRHS] at hA3xu
      have hA_lt : (HScaleNorm bH mu st (Γih (LG x u1 - LG x u2))) ^ (1/2:ℝ) < ⊤ :=
        lt_of_le_of_lt hA3xu ENNReal.ofReal_lt_top
      have hHNne_in : HScaleNorm bH mu st (Γih (LG x u1 - LG x u2)) ≠ ⊤ := by
        intro htop
        rw [htop, ENNReal.top_rpow_of_pos (show (0:ℝ) < 1/2 by norm_num)] at hA_lt
        exact absurd hA_lt (lt_irrefl ⊤)
      have hHNreal : (HScaleNorm bH mu st (Γih (LG x u1 - LG x u2))).toReal ≤ V ^ 2 := by
        have hstep : (HScaleNorm bH mu st (Γih (LG x u1 - LG x u2))).toReal ^ (1/2:ℝ) ≤ V := by
          have h := ENNReal.toReal_le_of_le_ofReal hVnn hA3xu
          rwa [← ENNReal.toReal_rpow] at h
        calc (HScaleNorm bH mu st (Γih (LG x u1 - LG x u2))).toReal
            = ((HScaleNorm bH mu st (Γih (LG x u1 - LG x u2))).toReal ^ (1/2:ℝ)) ^ 2 := (sq_half _ ENNReal.toReal_nonneg).symm
          _ ≤ V ^ 2 := by
                simpa only [pow_two] using mul_self_le_mul_self (Real.rpow_nonneg ENNReal.toReal_nonneg (1/2:ℝ)) hstep
      have hHNle : HScaleNorm bH mu st (Γih (LG x u1) - Γih (LG x u2)) ≤ ENNReal.ofReal (V ^ 2) := by
        rw [← hlin_u]
        exact (ENNReal.le_ofReal_iff_toReal_le hHNne_in (sq_nonneg V)).mpr hHNreal
      have hspec := statopia_math_node_3476376768_6d4cc185 H ιH bH mu (max 1 ‖C1‖) hmu_pos hMge1 hmu_le st hstn (Γih (LG x u1) - Γih (LG x u2))
      have hspec' : ENNReal.ofReal (‖Γih (LG x u1) - Γih (LG x u2)‖ ^ 2) ≤
          ENNReal.ofReal ((max 1 ‖C1‖) ^ st) * HScaleNorm bH mu st (Γih (LG x u1) - Γih (LG x u2)) := hspec
      have hmain : ENNReal.ofReal (‖Γih (LG x u1) - Γih (LG x u2)‖ ^ 2) ≤
          ENNReal.ofReal ((max 1 ‖C1‖) ^ st * V ^ 2) := by
        calc ENNReal.ofReal (‖Γih (LG x u1) - Γih (LG x u2)‖ ^ 2)
            ≤ ENNReal.ofReal ((max 1 ‖C1‖) ^ st) * HScaleNorm bH mu st (Γih (LG x u1) - Γih (LG x u2)) := hspec'
          _ ≤ ENNReal.ofReal ((max 1 ‖C1‖) ^ st) * ENNReal.ofReal (V ^ 2) := by
                gcongr
          _ = ENNReal.ofReal ((max 1 ‖C1‖) ^ st * V ^ 2) := by rw [ENNReal.ofReal_mul hcnonneg]
      exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hcnonneg (sq_nonneg _))).mp hmain
    have h2 : ‖Γih (LG x u1) + Γih (LG x u2)‖ ^ 2 ≤ (max 1 ‖C1‖) ^ st * (2 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u1 0)) + M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u2 0)))) ^ 2 := by
      have hsum12 : (HScaleNorm bH mu st (Γih (LG x u1) + Γih (LG x u2))) ^ (1/2:ℝ) ≤
          ENNReal.ofReal (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u1 0)) + M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u2 0))) := by
        refine le_trans (statopia_math_node_3002875505_b32dcfa2 H ιH bH mu hmu_pos st hstn (Γih (LG x u1)) (Γih (LG x u2))) ?_
        refine le_trans (add_le_add (hA2 x u1 hu1) (hA2 x u2 hu2)) ?_
        exact le_of_eq (ENNReal.ofReal_add (hM1_nonneg _) (hM1_nonneg _)).symm
      have hsum_ne : HScaleNorm bH mu st (Γih (LG x u1) + Γih (LG x u2)) ≠ ⊤ := by
        intro htop
        rw [htop, ENNReal.top_rpow_of_pos (show (0:ℝ) < 1/2 by norm_num)] at hsum12
        exact (not_le.mpr ENNReal.ofReal_lt_top) hsum12
      have hsumToreal : (HScaleNorm bH mu st (Γih (LG x u1) + Γih (LG x u2))).toReal ≤
          (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u1 0)) + M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u2 0))) ^ 2 := by
        have h12 : (HScaleNorm bH mu st (Γih (LG x u1) + Γih (LG x u2))).toReal ^ (1/2:ℝ) ≤
            M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u1 0)) + M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u2 0)) := by
          have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsum12
          rwa [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (add_nonneg (hM1_nonneg _) (hM1_nonneg _))] at h
        calc (HScaleNorm bH mu st (Γih (LG x u1) + Γih (LG x u2))).toReal
            = ((HScaleNorm bH mu st (Γih (LG x u1) + Γih (LG x u2))).toReal ^ (1/2:ℝ)) ^ 2 := (sq_half _ ENNReal.toReal_nonneg).symm
          _ ≤ (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u1 0)) + M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u2 0))) ^ 2 := by
                simpa only [pow_two] using mul_self_le_mul_self (Real.rpow_nonneg ENNReal.toReal_nonneg (1/2:ℝ)) h12
      have hspec2 := statopia_math_node_3476376768_6d4cc185 H ιH bH mu (max 1 ‖C1‖) hmu_pos hMge1 hmu_le st hstn (Γih (LG x u1) + Γih (LG x u2))
      have hspec2' : ENNReal.ofReal (‖Γih (LG x u1) + Γih (LG x u2)‖ ^ 2) ≤
          ENNReal.ofReal ((max 1 ‖C1‖) ^ st) * HScaleNorm bH mu st (Γih (LG x u1) + Γih (LG x u2)) := hspec2
      have hmain : ENNReal.ofReal (‖Γih (LG x u1) + Γih (LG x u2)‖ ^ 2) ≤
          ENNReal.ofReal ((max 1 ‖C1‖) ^ st * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u1 0)) + M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u2 0))) ^ 2) := by
        calc ENNReal.ofReal (‖Γih (LG x u1) + Γih (LG x u2)‖ ^ 2)
            ≤ ENNReal.ofReal ((max 1 ‖C1‖) ^ st) * HScaleNorm bH mu st (Γih (LG x u1) + Γih (LG x u2)) := hspec2'
          _ ≤ ENNReal.ofReal ((max 1 ‖C1‖) ^ st) * ENNReal.ofReal ((M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u1 0)) + M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u2 0))) ^ 2) := by
                gcongr
                rw [← ENNReal.ofReal_toReal hsum_ne]
                exact ENNReal.ofReal_le_ofReal hsumToreal
          _ = ENNReal.ofReal ((max 1 ‖C1‖) ^ st * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u1 0)) + M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u2 0))) ^ 2) := by rw [ENNReal.ofReal_mul hcnonneg]
      have hb := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hcnonneg (sq_nonneg _))).mp hmain
      calc ‖Γih (LG x u1) + Γih (LG x u2)‖ ^ 2
          ≤ (max 1 ‖C1‖) ^ st * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u1 0)) + M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u2 0))) ^ 2 := hb
        _ ≤ (max 1 ‖C1‖) ^ st * (2 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u1 0)) + M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u2 0)))) ^ 2 := by
              apply mul_le_mul_of_nonneg_left _ hcnonneg
              nlinarith [sq_nonneg (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u1 0)) + M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u2 0)))]
    have hA_nonneg : (0:ℝ) ≤ ENNReal.toReal (HScaleDist bH mu (α - s) y 0) := ENNReal.toReal_nonneg
    have hPhi_id : Phi Γih LG u1 x y - Phi Γih LG u2 x y =
        (1/2:ℝ) * (‖Γih (LG x u1)‖ ^ 2 - ‖Γih (LG x u2)‖ ^ 2) -
          inner ℝ (Γih y) (Γih (LG x u1) - Γih (LG x u2)) := by
      unfold Phi
      rw [inner_sub_right]
      ring
    split_ifs with hfin
    · have hA := hA3 x u1 u2 hu1 hu2 huc
      rw [← hUDeq] at hA
      have hRHS : ENNReal.ofReal (M2 (ENNReal.toReal (UScaleDist e lam (1 - st) u1 0)) (ENNReal.toReal (UScaleDist e lam (1 - st) u2 0))) * UScaleDist e lam (1 - st) u1 u2 = ENNReal.ofReal V := by
        rw [hVdef]
        conv_lhs => rw [← ENNReal.ofReal_toReal hU_ne]
        rw [← ENNReal.ofReal_mul (hM2_nonneg _ _)]
      rw [hRHS, hlin_u] at hA
      have hHNb : ((HScaleNorm bH mu st (Γih (LG x u1) - Γih (LG x u2))) ^ (1/2:ℝ)).toReal ≤ V :=
        ENNReal.toReal_le_of_le_ofReal hVnn hA
      have hD_ne : (HScaleNorm bH mu st (Γih (LG x u1 - LG x u2))) ^ (1/2:ℝ) ≠ ⊤ := by
        rw [hlin_u]
        exact ne_of_lt (lt_of_le_of_lt hA ENNReal.ofReal_lt_top)
      have hb := hinner_gen y (Γih (LG x u1 - LG x u2)) hy hD_ne
      rw [dif_pos hfin] at hb
      rw [hlin_u] at hb
      have h3 : |inner ℝ (Γih y) (Γih (LG x u1) - Γih (LG x u2))| ≤
          (max 1 (Real.rpow (Classical.choose (statopia_math_node_2268300080_7eda57a7 H Γ hΓ_inj Γh hΓh_sq Γih hΓih_left ιH bH mu hmu_pos hfin)) (2 + st + |α - s|))) * ENNReal.toReal (HScaleDist bH mu (α - s) y 0) * V :=
        le_trans hb (mul_le_mul_of_nonneg_left hHNb (mul_nonneg (le_trans zero_le_one (le_max_left 1 _)) hA_nonneg))
      have hKnn : (0:ℝ) ≤ max 1 (Real.rpow (Classical.choose (statopia_math_node_2268300080_7eda57a7 H Γ hΓ_inj Γh hΓh_sq Γih hΓih_left ιH bH mu hmu_pos hfin)) (2 + st + |α - s|)) := le_trans zero_le_one (le_max_left 1 _)
      have hmain := statopia_math_node_1768585877_01a1f85c H (Γih (LG x u1)) (Γih (LG x u2)) (Γih y)
        ((max 1 ‖C1‖) ^ st) (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u1 0)) + M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u2 0))) (max 1 (Real.rpow (Classical.choose (statopia_math_node_2268300080_7eda57a7 H Γ hΓ_inj Γh hΓh_sq Γih hΓih_left ιH bH mu hmu_pos hfin)) (2 + st + |α - s|)))
        (ENNReal.toReal (HScaleDist bH mu (α - s) y 0)) V hcnonneg (add_nonneg (hM1_nonneg _) (hM1_nonneg _)) hKnn hA_nonneg hVnn h1 h2 h3
      rw [hPhi_id]
      rw [mul_assoc, ← hVdef]
      exact hmain
    · have h3 : |inner ℝ (Γih y) (Γih (LG x u1) - Γih (LG x u2))| ≤ C1c * ENNReal.toReal (HScaleDist bH mu (α - s) y 0) * V := by
        have hA := hA3 x u1 u2 hu1 hu2 huc
        rw [← hUDeq] at hA
        have hRHS : ENNReal.ofReal (M2 (ENNReal.toReal (UScaleDist e lam (1 - st) u1 0)) (ENNReal.toReal (UScaleDist e lam (1 - st) u2 0))) * UScaleDist e lam (1 - st) u1 u2 = ENNReal.ofReal V := by
          rw [hVdef]
          conv_lhs => rw [← ENNReal.ofReal_toReal hU_ne]
          rw [← ENNReal.ofReal_mul (hM2_nonneg _ _)]
        rw [hRHS, hlin_u] at hA
        have hHNb : ((HScaleNorm bH mu st (Γih (LG x u1) - Γih (LG x u2))) ^ (1/2:ℝ)).toReal ≤ V :=
          ENNReal.toReal_le_of_le_ofReal hVnn hA
        have hD_ne : (HScaleNorm bH mu st (Γih (LG x u1) - Γih (LG x u2))) ^ (1/2:ℝ) ≠ ⊤ :=
          ne_of_lt (lt_of_le_of_lt hA ENNReal.ofReal_lt_top)
        have hA1y := hA1 hfin y (α - s1 - 1) hy (Int.floor_le (α - s1 - 1)) (by linarith)
        have hA1b := hA1y.2.2.2.1
        have hAsub : HScale bH mu (-st) (Γih y) := hA1y.1
        have hW := statopia_math_node_54049410_53411e5b H ιH bH mu hmu_pos st (Γih y) (Γih (LG x u1) - Γih (LG x u2))
        have hX1_ne : (HScaleNorm bH mu (α - s) y) ^ (1/2:ℝ) ≠ ⊤ :=
          ne_of_lt (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ne_of_lt hy))
        have hA1_ne : (HScaleNorm bH mu (-st) (Γih y)) ^ (1/2:ℝ) ≠ ⊤ :=
          ne_of_lt (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ne_of_lt hAsub))
        have hX1eq : (HScaleNorm bH mu (α - s) y) ^ (1/2:ℝ) =
            ENNReal.ofReal ((HScaleNorm bH mu (α - s) y) ^ (1/2:ℝ)).toReal :=
          (ENNReal.ofReal_toReal hX1_ne).symm
        have hA1eq : (HScaleNorm bH mu (-st) (Γih y)) ^ (1/2:ℝ) =
            ENNReal.ofReal ((HScaleNorm bH mu (-st) (Γih y)) ^ (1/2:ℝ)).toReal :=
          (ENNReal.ofReal_toReal hA1_ne).symm
        have hDeq : (HScaleNorm bH mu st (Γih (LG x u1) - Γih (LG x u2))) ^ (1/2:ℝ) =
            ENNReal.ofReal ((HScaleNorm bH mu st (Γih (LG x u1) - Γih (LG x u2))) ^ (1/2:ℝ)).toReal :=
          (ENNReal.ofReal_toReal hD_ne).symm
        have hA1real : ((HScaleNorm bH mu (-st) (Γih y)) ^ (1/2:ℝ)).toReal ≤
            C1c * ((HScaleNorm bH mu (α - s) y) ^ (1/2:ℝ)).toReal := by
          have h := hA1b
          rw [hX1eq, ← ENNReal.ofReal_mul (le_of_lt hC1c)] at h
          exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg (le_of_lt hC1c) ENNReal.toReal_nonneg) h
        have hWreal : |inner ℝ (Γih y) (Γih (LG x u1) - Γih (LG x u2))| ≤
            ((HScaleNorm bH mu (-st) (Γih y)) ^ (1/2:ℝ)).toReal *
              ((HScaleNorm bH mu st (Γih (LG x u1) - Γih (LG x u2))) ^ (1/2:ℝ)).toReal := by
          have h := hW
          rw [hA1eq, hDeq, ← ENNReal.ofReal_mul (show (0:ℝ) ≤ ((HScaleNorm bH mu (-st) (Γih y)) ^ (1/2:ℝ)).toReal from ENNReal.toReal_nonneg)] at h
          have h2 := ENNReal.toReal_le_of_le_ofReal (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) h
          rwa [ENNReal.toReal_ofReal (abs_nonneg _)] at h2
        have hHX : ENNReal.toReal (HScaleDist bH mu (α - s) y 0) = ((HScaleNorm bH mu (α - s) y) ^ (1/2:ℝ)).toReal := by
          unfold HScaleDist; rw [sub_zero]
        rw [hHX]
        calc |inner ℝ (Γih y) (Γih (LG x u1) - Γih (LG x u2))|
            ≤ ((HScaleNorm bH mu (-st) (Γih y)) ^ (1/2:ℝ)).toReal *
                ((HScaleNorm bH mu st (Γih (LG x u1) - Γih (LG x u2))) ^ (1/2:ℝ)).toReal := hWreal
          _ ≤ (C1c * ((HScaleNorm bH mu (α - s) y) ^ (1/2:ℝ)).toReal) * V :=
                mul_le_mul hA1real hHNb ENNReal.toReal_nonneg (mul_nonneg (le_of_lt hC1c) ENNReal.toReal_nonneg)
      have hmain := statopia_math_node_1768585877_01a1f85c H (Γih (LG x u1)) (Γih (LG x u2)) (Γih y)
        ((max 1 ‖C1‖) ^ st) (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u1 0)) + M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u2 0))) C1c
        (ENNReal.toReal (HScaleDist bH mu (α - s) y 0)) V hcnonneg (add_nonneg (hM1_nonneg _) (hM1_nonneg _)) (le_of_lt hC1c) hA_nonneg hVnn h1 h2 h3
      rw [hPhi_id]
      rw [mul_assoc, ← hVdef]
      exact hmain
  · split_ifs with hfin
    · have hw : HScale bH mu (α - s) (y' - y) :=
        statopia_math_node_3264912868_3df235ee H ιH bH mu hmu_pos (α - s) y' y hy' hy
      have hlin6 : Γih (y' - y) = Γih y' - Γih y :=
        hΓih_sub y' y (hHsub y' hy') (hHsub y hy)
      have hPhi_id6 : Phi Γih LG u x y - Phi Γih LG u x y' =
          inner ℝ (Γih (y' - y)) (Γih (LG x u)) := by
        unfold Phi
        rw [hlin6, inner_sub_left]
        ring
      have hHX : ENNReal.toReal (HScaleDist bH mu (α - s) y y') =
          (HScaleDist bH mu (α - s) (y' - y) 0).toReal := by
        have hneg2 : HScaleNorm bH mu (α - s) (y - y') = HScaleNorm bH mu (α - s) (y' - y) := by
          rw [show y - y' = -(y' - y) from (neg_sub y' y).symm]
          unfold HScaleNorm
          apply tsum_congr
          intro i
          rw [inner_neg_right, neg_sq]
        unfold HScaleDist
        rw [sub_zero, hneg2]
      have hb := hinner_bound (y' - y) hw
      rw [dif_pos hfin] at hb
      rw [hPhi_id6, hHX]
      exact hb
    · have hw : HScale bH mu (α - s) (y' - y) :=
        statopia_math_node_3264912868_3df235ee H ιH bH mu hmu_pos (α - s) y' y hy' hy
      have hlin6 : Γih (y' - y) = Γih y' - Γih y :=
        hΓih_sub y' y (hHsub y' hy') (hHsub y hy)
      have hA1w := hA1 hfin (y' - y) (α - s1 - 1) hw (Int.floor_le (α - s1 - 1)) (by linarith)
      have hA1b := hA1w.2.2.2.1
      have hAsub : HScale bH mu (-st) (Γih (y' - y)) := hA1w.1
      have hW := statopia_math_node_54049410_53411e5b H ιH bH mu hmu_pos st (Γih (y' - y)) (Γih (LG x u))
      have hA2hu := hA2 x u hu
      have hX1_ne : (HScaleNorm bH mu (α - s) (y' - y)) ^ (1/2:ℝ) ≠ ⊤ :=
        ne_of_lt (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ne_of_lt hw))
      have hA1_ne : (HScaleNorm bH mu (-st) (Γih (y' - y))) ^ (1/2:ℝ) ≠ ⊤ :=
        ne_of_lt (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ne_of_lt hAsub))
      have hB1_ne : (HScaleNorm bH mu st (Γih (LG x u))) ^ (1/2:ℝ) ≠ ⊤ :=
        ne_of_lt (lt_of_le_of_lt hA2hu ENNReal.ofReal_lt_top)
      have hX1eq : (HScaleNorm bH mu (α - s) (y' - y)) ^ (1/2:ℝ) =
          ENNReal.ofReal ((HScaleNorm bH mu (α - s) (y' - y)) ^ (1/2:ℝ)).toReal :=
        (ENNReal.ofReal_toReal hX1_ne).symm
      have hA1eq : (HScaleNorm bH mu (-st) (Γih (y' - y))) ^ (1/2:ℝ) =
          ENNReal.ofReal ((HScaleNorm bH mu (-st) (Γih (y' - y))) ^ (1/2:ℝ)).toReal :=
        (ENNReal.ofReal_toReal hA1_ne).symm
      have hB1eq : (HScaleNorm bH mu st (Γih (LG x u))) ^ (1/2:ℝ) =
          ENNReal.ofReal ((HScaleNorm bH mu st (Γih (LG x u))) ^ (1/2:ℝ)).toReal :=
        (ENNReal.ofReal_toReal hB1_ne).symm
      have hA1real : ((HScaleNorm bH mu (-st) (Γih (y' - y))) ^ (1/2:ℝ)).toReal ≤
          C1c * ((HScaleNorm bH mu (α - s) (y' - y)) ^ (1/2:ℝ)).toReal := by
        have h := hA1b
        rw [hX1eq, ← ENNReal.ofReal_mul (le_of_lt hC1c)] at h
        exact ENNReal.toReal_le_of_le_ofReal
          (mul_nonneg (le_of_lt hC1c) ENNReal.toReal_nonneg) h
      have hA2real : ((HScaleNorm bH mu st (Γih (LG x u))) ^ (1/2:ℝ)).toReal ≤
          M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) :=
        ENNReal.toReal_le_of_le_ofReal (hM1_nonneg _) hA2hu
      have hWreal : |inner ℝ (Γih (y' - y)) (Γih (LG x u))| ≤
          ((HScaleNorm bH mu (-st) (Γih (y' - y))) ^ (1/2:ℝ)).toReal *
            ((HScaleNorm bH mu st (Γih (LG x u))) ^ (1/2:ℝ)).toReal := by
        have h := hW
        rw [hA1eq, hB1eq,
          ← ENNReal.ofReal_mul
            (show (0:ℝ) ≤ ((HScaleNorm bH mu (-st) (Γih (y' - y))) ^ (1/2:ℝ)).toReal
              from ENNReal.toReal_nonneg)] at h
        have h2 := ENNReal.toReal_le_of_le_ofReal
          (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) h
        rwa [ENNReal.toReal_ofReal (abs_nonneg _)] at h2
      have hHX : ENNReal.toReal (HScaleDist bH mu (α - s) y y') =
          ((HScaleNorm bH mu (α - s) (y' - y)) ^ (1/2:ℝ)).toReal := by
        have hneg2 : HScaleNorm bH mu (α - s) (y - y') = HScaleNorm bH mu (α - s) (y' - y) := by
          rw [show y - y' = -(y' - y) from (neg_sub y' y).symm]
          unfold HScaleNorm
          apply tsum_congr
          intro i
          rw [inner_neg_right, neg_sq]
        unfold HScaleDist
        rw [hneg2]
      have hPhi_id6 : Phi Γih LG u x y - Phi Γih LG u x y' =
          inner ℝ (Γih (y' - y)) (Γih (LG x u)) := by
        unfold Phi
        rw [hlin6, inner_sub_left]
        ring
      rw [hPhi_id6, hHX]
      calc |inner ℝ (Γih (y' - y)) (Γih (LG x u))|
          ≤ ((HScaleNorm bH mu (-st) (Γih (y' - y))) ^ (1/2:ℝ)).toReal *
              ((HScaleNorm bH mu st (Γih (LG x u))) ^ (1/2:ℝ)).toReal := hWreal
        _ ≤ (C1c * ((HScaleNorm bH mu (α - s) (y' - y)) ^ (1/2:ℝ)).toReal) *
              M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) :=
              mul_le_mul hA1real hA2real ENNReal.toReal_nonneg
                (mul_nonneg (le_of_lt hC1c) ENNReal.toReal_nonneg)
  · have hstn : 0 ≤ st := le_trans hs0_nonneg (le_of_lt hst_gt)
    have hMge1 : 1 ≤ max 1 ‖C1‖ := le_max_left 1 _
    have hMpos : (0:ℝ) < max 1 ‖C1‖ := lt_of_lt_of_le one_pos hMge1
    have hcnonneg : (0:ℝ) ≤ (max 1 ‖C1‖) ^ st := Real.rpow_nonneg (le_of_lt hMpos) st
    have hM1u_nonneg : (0:ℝ) ≤ M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := hM1_nonneg _
    have hA_nonneg : (0:ℝ) ≤ ENNReal.toReal (HScaleDist bH mu (α - s) y 0) := ENNReal.toReal_nonneg
    have hlin : Γih (LG x u - LG x' u) = Γih (LG x u) - Γih (LG x' u) :=
      hΓih_sub (LG x u) (LG x' u) (hLG_all_range x u hu) (hLG_all_range x' u hu)
    set V : ℝ := ENNReal.toReal (HScaleDist bH mu st (Γih (LG x u - LG x' u)) 0) with hVdef
    have hVnn : 0 ≤ V := by rw [hVdef]; exact ENNReal.toReal_nonneg
    have hVeq : V = ((HScaleNorm bH mu st (Γih (LG x u) - Γih (LG x' u))) ^ (1/2:ℝ)).toReal := by
      rw [hVdef]; unfold HScaleDist; rw [sub_zero, hlin]
    have hV2 : V ^ 2 = (HScaleNorm bH mu st (Γih (LG x u) - Γih (LG x' u))).toReal := by
      rw [hVeq, ← ENNReal.toReal_rpow]
      exact sq_half _ ENNReal.toReal_nonneg
    have h1 : ‖Γih (LG x u) - Γih (LG x' u)‖ ^ 2 ≤ (max 1 ‖C1‖) ^ st * V ^ 2 := by
      have hspec := statopia_math_node_3476376768_6d4cc185 H ιH bH mu (max 1 ‖C1‖) hmu_pos hMge1 hmu_le st hstn (Γih (LG x u) - Γih (LG x' u))
      have hspec' : ENNReal.ofReal (‖Γih (LG x u) - Γih (LG x' u)‖ ^ 2) ≤
          ENNReal.ofReal ((max 1 ‖C1‖) ^ st) * HScaleNorm bH mu st (Γih (LG x u) - Γih (LG x' u)) := hspec
      have hmain : ENNReal.ofReal (‖Γih (LG x u) - Γih (LG x' u)‖ ^ 2) ≤
          ENNReal.ofReal ((max 1 ‖C1‖) ^ st * V ^ 2) := by
        calc ENNReal.ofReal (‖Γih (LG x u) - Γih (LG x' u)‖ ^ 2)
            ≤ ENNReal.ofReal ((max 1 ‖C1‖) ^ st) * HScaleNorm bH mu st (Γih (LG x u) - Γih (LG x' u)) := hspec'
          _ = ENNReal.ofReal ((max 1 ‖C1‖) ^ st) * ENNReal.ofReal ((HScaleNorm bH mu st (Γih (LG x u) - Γih (LG x' u))).toReal) := by rw [ENNReal.ofReal_toReal hXfin]
          _ = ENNReal.ofReal ((max 1 ‖C1‖) ^ st) * ENNReal.ofReal (V ^ 2) := by rw [← hV2]
          _ = ENNReal.ofReal ((max 1 ‖C1‖) ^ st * V ^ 2) := by rw [ENNReal.ofReal_mul hcnonneg]
      exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hcnonneg (sq_nonneg _))).mp hmain
    have h2 : ‖Γih (LG x u) + Γih (LG x' u)‖ ^ 2 ≤ (max 1 ‖C1‖) ^ st * (2 * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2 := by
      have hsum12 : (HScaleNorm bH mu st (Γih (LG x u) + Γih (LG x' u))) ^ (1/2:ℝ) ≤
          ENNReal.ofReal (2 * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) := by
        refine le_trans (statopia_math_node_3002875505_b32dcfa2 H ιH bH mu hmu_pos st hstn (Γih (LG x u)) (Γih (LG x' u))) ?_
        refine le_trans (add_le_add (hA2 x u hu) (hA2 x' u hu)) ?_
        rw [← ENNReal.ofReal_add (hM1_nonneg _) (hM1_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        linarith
      have hsum_ne : HScaleNorm bH mu st (Γih (LG x u) + Γih (LG x' u)) ≠ ⊤ := by
        intro htop
        rw [htop, ENNReal.top_rpow_of_pos (show (0:ℝ) < 1/2 by norm_num)] at hsum12
        exact (not_le.mpr ENNReal.ofReal_lt_top) hsum12
      have hsumToreal : (HScaleNorm bH mu st (Γih (LG x u) + Γih (LG x' u))).toReal ≤
          (2 * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2 := by
        have h12 : (HScaleNorm bH mu st (Γih (LG x u) + Γih (LG x' u))).toReal ^ (1/2:ℝ) ≤
            2 * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := by
          have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsum12
          rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (hM1_nonneg _))] at h
          exact h
        calc (HScaleNorm bH mu st (Γih (LG x u) + Γih (LG x' u))).toReal
            = ((HScaleNorm bH mu st (Γih (LG x u) + Γih (LG x' u))).toReal ^ (1/2:ℝ)) ^ 2 := (sq_half _ ENNReal.toReal_nonneg).symm
          _ ≤ (2 * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2 := by
                simpa only [pow_two] using mul_self_le_mul_self (Real.rpow_nonneg ENNReal.toReal_nonneg (1/2:ℝ)) h12
      have hspec2 := statopia_math_node_3476376768_6d4cc185 H ιH bH mu (max 1 ‖C1‖) hmu_pos hMge1 hmu_le st hstn (Γih (LG x u) + Γih (LG x' u))
      have hspec2' : ENNReal.ofReal (‖Γih (LG x u) + Γih (LG x' u)‖ ^ 2) ≤
          ENNReal.ofReal ((max 1 ‖C1‖) ^ st) * HScaleNorm bH mu st (Γih (LG x u) + Γih (LG x' u)) := hspec2
      have hmain : ENNReal.ofReal (‖Γih (LG x u) + Γih (LG x' u)‖ ^ 2) ≤
          ENNReal.ofReal ((max 1 ‖C1‖) ^ st * (2 * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2) := by
        calc ENNReal.ofReal (‖Γih (LG x u) + Γih (LG x' u)‖ ^ 2)
            ≤ ENNReal.ofReal ((max 1 ‖C1‖) ^ st) * HScaleNorm bH mu st (Γih (LG x u) + Γih (LG x' u)) := hspec2'
          _ ≤ ENNReal.ofReal ((max 1 ‖C1‖) ^ st) * ENNReal.ofReal ((2 * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2) := by
                gcongr
                rw [← ENNReal.ofReal_toReal hsum_ne]
                exact ENNReal.ofReal_le_ofReal hsumToreal
          _ = ENNReal.ofReal ((max 1 ‖C1‖) ^ st * (2 * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2) := by rw [ENNReal.ofReal_mul hcnonneg]
      exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hcnonneg (sq_nonneg _))).mp hmain
    have hPhi_id : Phi Γih LG u x y - Phi Γih LG u x' y =
        (1/2:ℝ) * (‖Γih (LG x u)‖ ^ 2 - ‖Γih (LG x' u)‖ ^ 2) -
          inner ℝ (Γih y) (Γih (LG x u) - Γih (LG x' u)) := by
      unfold Phi
      rw [inner_sub_right]
      ring
    split_ifs with hfin
    · have hD_ne : (HScaleNorm bH mu st (Γih (LG x u - LG x' u))) ^ (1/2:ℝ) ≠ ⊤ := by
        rw [hlin]
        exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hXfin
      have hb := hinner_gen y (Γih (LG x u - LG x' u)) hy hD_ne
      rw [dif_pos hfin] at hb
      rw [hlin, ← hVeq] at hb
      have hKnn : (0:ℝ) ≤ max 1 (Real.rpow (Classical.choose (statopia_math_node_2268300080_7eda57a7 H Γ hΓ_inj Γh hΓh_sq Γih hΓih_left ιH bH mu hmu_pos hfin)) (2 + st + |α - s|)) := le_trans zero_le_one (le_max_left 1 _)
      have hmain := statopia_math_node_1768585877_01a1f85c H (Γih (LG x u)) (Γih (LG x' u)) (Γih y)
        ((max 1 ‖C1‖) ^ st) (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) (max 1 (Real.rpow (Classical.choose (statopia_math_node_2268300080_7eda57a7 H Γ hΓ_inj Γh hΓh_sq Γih hΓih_left ιH bH mu hmu_pos hfin)) (2 + st + |α - s|)))
        (ENNReal.toReal (HScaleDist bH mu (α - s) y 0)) V hcnonneg hM1u_nonneg hKnn hA_nonneg hVnn h1 h2 hb
      rw [hPhi_id]
      exact hmain
    · have h3 : |inner ℝ (Γih y) (Γih (LG x u) - Γih (LG x' u))| ≤
          C1c * ENNReal.toReal (HScaleDist bH mu (α - s) y 0) * V := by
        have hA1y := hA1 hfin y (α - s1 - 1) hy (Int.floor_le (α - s1 - 1)) (by linarith)
        have hA1b := hA1y.2.2.2.1
        have hAsub : HScale bH mu (-st) (Γih y) := hA1y.1
        have hW := statopia_math_node_54049410_53411e5b H ιH bH mu hmu_pos st (Γih y) (Γih (LG x u) - Γih (LG x' u))
        have hX1_ne : (HScaleNorm bH mu (α - s) y) ^ (1/2:ℝ) ≠ ⊤ :=
          ne_of_lt (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ne_of_lt hy))
        have hA1_ne : (HScaleNorm bH mu (-st) (Γih y)) ^ (1/2:ℝ) ≠ ⊤ :=
          ne_of_lt (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ne_of_lt hAsub))
        have hD_ne : (HScaleNorm bH mu st (Γih (LG x u) - Γih (LG x' u))) ^ (1/2:ℝ) ≠ ⊤ :=
          ENNReal.rpow_ne_top_of_nonneg (by norm_num) hXfin
        have hX1eq : (HScaleNorm bH mu (α - s) y) ^ (1/2:ℝ) =
            ENNReal.ofReal ((HScaleNorm bH mu (α - s) y) ^ (1/2:ℝ)).toReal :=
          (ENNReal.ofReal_toReal hX1_ne).symm
        have hA1eq : (HScaleNorm bH mu (-st) (Γih y)) ^ (1/2:ℝ) =
            ENNReal.ofReal ((HScaleNorm bH mu (-st) (Γih y)) ^ (1/2:ℝ)).toReal :=
          (ENNReal.ofReal_toReal hA1_ne).symm
        have hDeq : (HScaleNorm bH mu st (Γih (LG x u) - Γih (LG x' u))) ^ (1/2:ℝ) = ENNReal.ofReal V := by
          rw [hVeq]
          exact (ENNReal.ofReal_toReal hD_ne).symm
        have hA1real : ((HScaleNorm bH mu (-st) (Γih y)) ^ (1/2:ℝ)).toReal ≤
            C1c * ((HScaleNorm bH mu (α - s) y) ^ (1/2:ℝ)).toReal := by
          have h := hA1b
          rw [hX1eq, ← ENNReal.ofReal_mul (le_of_lt hC1c)] at h
          exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg (le_of_lt hC1c) ENNReal.toReal_nonneg) h
        have hWreal : |inner ℝ (Γih y) (Γih (LG x u) - Γih (LG x' u))| ≤
            ((HScaleNorm bH mu (-st) (Γih y)) ^ (1/2:ℝ)).toReal * V := by
          have h := hW
          rw [hA1eq, hDeq, ← ENNReal.ofReal_mul (show (0:ℝ) ≤ ((HScaleNorm bH mu (-st) (Γih y)) ^ (1/2:ℝ)).toReal from ENNReal.toReal_nonneg)] at h
          have h2 := ENNReal.toReal_le_of_le_ofReal (mul_nonneg ENNReal.toReal_nonneg hVnn) h
          rwa [ENNReal.toReal_ofReal (abs_nonneg _)] at h2
        have hHX : ENNReal.toReal (HScaleDist bH mu (α - s) y 0) = ((HScaleNorm bH mu (α - s) y) ^ (1/2:ℝ)).toReal := by
          unfold HScaleDist; rw [sub_zero]
        rw [hHX]
        calc |inner ℝ (Γih y) (Γih (LG x u) - Γih (LG x' u))|
            ≤ ((HScaleNorm bH mu (-st) (Γih y)) ^ (1/2:ℝ)).toReal * V := hWreal
          _ ≤ (C1c * ((HScaleNorm bH mu (α - s) y) ^ (1/2:ℝ)).toReal) * V :=
                mul_le_mul_of_nonneg_right hA1real hVnn
      have hmain := statopia_math_node_1768585877_01a1f85c H (Γih (LG x u)) (Γih (LG x' u)) (Γih y)
        ((max 1 ‖C1‖) ^ st) (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) C1c
        (ENNReal.toReal (HScaleDist bH mu (α - s) y 0)) V hcnonneg hM1u_nonneg (le_of_lt hC1c) hA_nonneg hVnn h1 h2 h3
      rw [hPhi_id]
      exact hmain
  · have hst_nonneg : 0 ≤ st := le_trans hs0_nonneg (le_of_lt hst_gt)
    have hneg : ∀ v : H, HScaleNorm bH mu st (-v) = HScaleNorm bH mu st v := by
      intro v
      unfold HScaleNorm
      apply tsum_congr
      intro i
      rw [inner_neg_right, neg_sq]
    have hlin : Γih (LG x u - LG x' u) = Γih (LG x u) - Γih (LG x' u) :=
      hΓih_sub (LG x u) (LG x' u) (hLG_all_range x u hu) (hLG_all_range x' u hu)
    have hsub := statopia_math_node_3002875505_b32dcfa2 H ιH bH mu hmu_pos st hst_nonneg
      (Γih (LG x u)) (-(Γih (LG x' u)))
    rw [hneg (Γih (LG x' u)), ← sub_eq_add_neg, ← hlin] at hsub
    have hfin : (HScaleNorm bH mu st (Γih (LG x u - LG x' u))) ^ (1/2:ℝ) ≤
        ENNReal.ofReal (2 * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) := by
      refine le_trans hsub ?_
      calc (HScaleNorm bH mu st (Γih (LG x u))) ^ (1/2:ℝ) +
            (HScaleNorm bH mu st (Γih (LG x' u))) ^ (1/2:ℝ)
          ≤ ENNReal.ofReal (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) +
              ENNReal.ofReal (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) :=
              add_le_add (hA2 x u hu) (hA2 x' u hu)
        _ = ENNReal.ofReal (2 * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) := by
              rw [← ENNReal.ofReal_add (hM1_nonneg _) (hM1_nonneg _)]
              congr 1
              ring
    have hH : HScaleDist bH mu st (Γih (LG x u - LG x' u)) 0 =
        (HScaleNorm bH mu st (Γih (LG x u - LG x' u))) ^ (1/2:ℝ) := by
      unfold HScaleDist
      rw [sub_zero]
    rw [hH]
    calc ((HScaleNorm bH mu st (Γih (LG x u - LG x' u))) ^ (1/2:ℝ)).toReal
        ≤ (ENNReal.ofReal (2 * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)))).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top hfin
      _ = 2 * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) :=
            ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (hM1_nonneg _))
  /- @proof-region region.target-node.session.5178d8803b63248c end -/

end Statlib.Imported
end

