import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_1182065402_10a004d7_cff08bd3
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3551296407_58969dcf_1b749c74

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
theorem statopia_math_node_3975929643_b00873c3 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (X : Type*) [TopologicalSpace X]
    (Γih : H → H) (LG : X → U → H)
    (e : HilbertBasis ℕ ℝ U) (lam : ℕ → ℝ)
    (ιH : Type*) [Preorder ιH] (bH : HilbertBasis ιH ℝ H) (mu : ιH → ℝ)
    (hmu_pos : ∀ i : ιH, 0 < mu i)
    (M1 : ℝ → ℝ) (hM1_mono : Monotone M1) (hM1_nonneg : ∀ r : ℝ, 0 ≤ M1 r)
    (s st alpha : ℝ)
    (m : ℕ) (hm : 0 < m)
    (beta : ℝ) (hbeta : 0 < beta)
    (mubar kappa : ℝ) (hmubar : 1 ≤ mubar) (hkappa : 0 ≤ kappa)
    (h6 : ∀ (x x' : X) (y y' : H), HScale bH mu (alpha - s) y → HScale bH mu (alpha - s) y' →
      ∀ u : U, UScale e lam (1 - st) u →
      |Phi Γih LG u x y - Phi Γih LG u x y'| ≤
        kappa * ENNReal.toReal (HScaleDist bH mu (alpha - s) y y') *
          M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)))
    (h7 : ∀ (x x' : X) (y y' : H), HScale bH mu (alpha - s) y → HScale bH mu (alpha - s) y' →
      ∀ u : U, UScale e lam (1 - st) u →
      |Phi Γih LG u x y - Phi Γih LG u x' y| ≤
        (Real.rpow mubar st * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) +
          kappa * ENNReal.toReal (HScaleDist bH mu (alpha - s) y 0)) *
          ENNReal.toReal (HScaleDist bH mu st (Γih (LG x u - LG x' u)) 0))
    (h8 : ∀ (x x' : X) (y y' : H), HScale bH mu (alpha - s) y → HScale bH mu (alpha - s) y' →
      ∀ u : U, UScale e lam (1 - st) u →
      ENNReal.toReal (HScaleDist bH mu st (Γih (LG x u - LG x' u)) 0) ≤
        2 * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))), (∀ (D1 D2 : Fin m → X × H),
        (∀ j : Fin m, HScale bH mu (alpha - s) (D1 j).2) →
        (∀ j : Fin m, HScale bH mu (alpha - s) (D2 j).2) →
        ∀ u : U, UScale e lam (1 - st) u →
        ENNReal.ofReal
            |(beta / (m : ℝ)) * potSum Γih LG D1 u - (beta / (m : ℝ)) * potSum Γih LG D2 u| ≤
          ENNReal.ofReal (beta / (m : ℝ)) *
            ∑ j : Fin m,
              (ENNReal.ofReal kappa * HScaleDist bH mu (alpha - s) (D2 j).2 (D1 j).2 *
                  ENNReal.ofReal (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) +
                (ENNReal.ofReal (Real.rpow mubar st) *
                    ENNReal.ofReal (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) +
                  ENNReal.ofReal kappa * HScaleDist bH mu (alpha - s) (D1 j).2 0) *
                  HScaleDist bH mu st (Γih (LG ((D1 j).1) u - LG ((D2 j).1) u)) 0)) ∧
      (∀ (r : ℝ), 0 ≤ r → ∀ (D1 D2 : Fin m → X × H),
        (∀ j : Fin m, HScale bH mu (alpha - s) (D1 j).2) →
        (∀ j : Fin m, HScale bH mu (alpha - s) (D2 j).2) →
        (∀ j : Fin m, HScaleDist bH mu (alpha - s) (D1 j).2 0 ≤ ENNReal.ofReal r) →
        (∀ j : Fin m, HScaleDist bH mu (alpha - s) (D2 j).2 0 ≤ ENNReal.ofReal r) →
        ∀ u : U, UScale e lam (1 - st) u →
        |(beta / (m : ℝ)) * potSum Γih LG D1 u - (beta / (m : ℝ)) * potSum Γih LG D2 u| ≤
          beta * (4 * kappa * r + 2 * Real.rpow mubar st) *
            (1 + (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2)) ∧
      (∀ (hcont : ∀ (x' : X) (u : U), UScale e lam (1 - st) u →
          Tendsto (fun x : X => (HScaleNorm bH mu st (Γih (LG x u - LG x' u))) ^ (1 / 2 : ℝ))
            (𝓝 x') (𝓝 0)),
        ∀ (Dn : ℕ → Fin m → X × H) (D : Fin m → X × H),
        (∀ (n : ℕ) (j : Fin m), HScale bH mu (alpha - s) ((Dn n j).2)) →
        (∀ j : Fin m, HScale bH mu (alpha - s) (D j).2) →
        Tendsto Dn atTop
          (dataNhds (fun z : H => (HScaleNorm bH mu (alpha - s) z) ^ (1 / 2 : ℝ))
            (HScale bH mu (alpha - s)) D) →
        ∀ u : U, UScale e lam (1 - st) u →
        Tendsto (fun n : ℕ => (beta / (m : ℝ)) * potSum Γih LG (Dn n) u) atTop
                    (𝓝 ((beta / (m : ℝ)) * potSum Γih LG D u))) := by
  /- @proof-region region.target-node.session.5a37bca7c73bd95b begin -/
  intro U instU1 instU2 instU3 H instH1 instH2 instH3 X instX Γih LG e lam ιH instI bH mu hmu_pos
    M1 hM1_mono hM1_nonneg s st α m hm β hβ mubar kappa hmubar hkappa h6 h7 h8
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hcoefpos : 0 < β / (m : ℝ) := div_pos hβ hmR
  have hcoef : 0 ≤ β / (m : ℝ) := le_of_lt hcoefpos
  refine ⟨?_, ?_, ?_⟩
  · intro D1 D2 hD1 hD2 u hU
    set Mv : ℝ := M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) with hMv
    have hMv0 : 0 ≤ Mv := hM1_nonneg _
    have hmul3 : ∀ (d : ℝ≥0∞) (c1 c2 : ℝ), 0 ≤ c1 → 0 ≤ c2 →
        ENNReal.ofReal (c1 * d.toReal * c2) ≤ ENNReal.ofReal c1 * d * ENNReal.ofReal c2 := by
      intro d c1 c2 h1 h2
      rw [ENNReal.ofReal_mul (mul_nonneg h1 ENNReal.toReal_nonneg), ENNReal.ofReal_mul h1]
      exact mul_le_mul_right' (mul_le_mul_left' ENNReal.ofReal_toReal_le _) _
    have key : ∀ j : Fin m,
        ENNReal.ofReal |Phi Γih LG u (D1 j).1 (D1 j).2 - Phi Γih LG u (D2 j).1 (D2 j).2| ≤
          ENNReal.ofReal kappa * HScaleDist bH mu (α - s) (D2 j).2 (D1 j).2 * ENNReal.ofReal Mv +
            (ENNReal.ofReal (mubar ^ st) * ENNReal.ofReal Mv +
                ENNReal.ofReal kappa * HScaleDist bH mu (α - s) (D1 j).2 0) *
              HScaleDist bH mu st (Γih (LG (D1 j).1 u - LG (D2 j).1 u)) 0 := by
      intro j
      by_cases hmem : HScale bH mu (α - s) (D1 j).2 ∧ HScale bH mu (α - s) (D2 j).2
      · obtain ⟨h1, h2⟩ := hmem
        have hb6 := h6 (D2 j).1 (D2 j).1 (D2 j).2 (D1 j).2 h2 h1 u hU
        have hb7 := h7 (D1 j).1 (D2 j).1 (D1 j).2 (D1 j).2 h1 h1 u hU
        rw [← hMv] at hb6 hb7
        have hms : 0 ≤ mubar ^ st := Real.rpow_nonneg (by linarith) st
        have ht2 : |Phi Γih LG u (D1 j).1 (D1 j).2 - Phi Γih LG u (D2 j).1 (D2 j).2| ≤
            kappa * ENNReal.toReal (HScaleDist bH mu (α - s) (D2 j).2 (D1 j).2) * Mv +
              (mubar ^ st * Mv +
                  kappa * ENNReal.toReal (HScaleDist bH mu (α - s) (D1 j).2 0)) *
                ENNReal.toReal (HScaleDist bH mu st (Γih (LG (D1 j).1 u - LG (D2 j).1 u)) 0) := by
          have hsp : |Phi Γih LG u (D1 j).1 (D1 j).2 - Phi Γih LG u (D2 j).1 (D2 j).2| ≤
              |Phi Γih LG u (D2 j).1 (D1 j).2 - Phi Γih LG u (D2 j).1 (D2 j).2| +
                |Phi Γih LG u (D1 j).1 (D1 j).2 - Phi Γih LG u (D2 j).1 (D1 j).2| := by
            have h := abs_add_le
              (Phi Γih LG u (D2 j).1 (D1 j).2 - Phi Γih LG u (D2 j).1 (D2 j).2)
              (Phi Γih LG u (D1 j).1 (D1 j).2 - Phi Γih LG u (D2 j).1 (D1 j).2)
            have he : (Phi Γih LG u (D2 j).1 (D1 j).2 - Phi Γih LG u (D2 j).1 (D2 j).2) +
                (Phi Γih LG u (D1 j).1 (D1 j).2 - Phi Γih LG u (D2 j).1 (D1 j).2) =
                Phi Γih LG u (D1 j).1 (D1 j).2 - Phi Γih LG u (D2 j).1 (D2 j).2 := by abel
            rwa [he] at h
          refine le_trans hsp (add_le_add ?_ hb7)
          rw [abs_sub_comm]
          exact hb6
        have hS0 : 0 ≤ mubar ^ st * Mv +
            kappa * ENNReal.toReal (HScaleDist bH mu (α - s) (D1 j).2 0) :=
          add_nonneg (mul_nonneg hms hMv0) (mul_nonneg hkappa ENNReal.toReal_nonneg)
        calc ENNReal.ofReal _ ≤ ENNReal.ofReal
              (kappa * ENNReal.toReal (HScaleDist bH mu (α - s) (D2 j).2 (D1 j).2) * Mv +
                (mubar ^ st * Mv +
                    kappa * ENNReal.toReal (HScaleDist bH mu (α - s) (D1 j).2 0)) *
                  ENNReal.toReal (HScaleDist bH mu st (Γih (LG (D1 j).1 u - LG (D2 j).1 u)) 0)) :=
            ENNReal.ofReal_le_ofReal ht2
          _ = ENNReal.ofReal (kappa * ENNReal.toReal (HScaleDist bH mu (α - s) (D2 j).2 (D1 j).2) * Mv) +
                ENNReal.ofReal ((mubar ^ st * Mv +
                    kappa * ENNReal.toReal (HScaleDist bH mu (α - s) (D1 j).2 0)) *
                  ENNReal.toReal (HScaleDist bH mu st (Γih (LG (D1 j).1 u - LG (D2 j).1 u)) 0)) :=
            ENNReal.ofReal_add (mul_nonneg (mul_nonneg hkappa ENNReal.toReal_nonneg) hMv0)
              (mul_nonneg hS0 ENNReal.toReal_nonneg)
          _ ≤ (ENNReal.ofReal kappa * HScaleDist bH mu (α - s) (D2 j).2 (D1 j).2 *
                ENNReal.ofReal Mv) +
                ((ENNReal.ofReal (mubar ^ st) * ENNReal.ofReal Mv +
                    ENNReal.ofReal kappa * HScaleDist bH mu (α - s) (D1 j).2 0) *
                  HScaleDist bH mu st (Γih (LG (D1 j).1 u - LG (D2 j).1 u)) 0) := by
            refine add_le_add (hmul3 _ kappa Mv hkappa hMv0) ?_
            rw [ENNReal.ofReal_mul hS0]
            refine mul_le_mul' ?_ ENNReal.ofReal_toReal_le
            rw [ENNReal.ofReal_add (mul_nonneg hms hMv0)
              (mul_nonneg hkappa ENNReal.toReal_nonneg)]
            exact add_le_add (le_of_eq (ENNReal.ofReal_mul hms)) (by
              rw [ENNReal.ofReal_mul hkappa]
              exact mul_le_mul_left' ENNReal.ofReal_toReal_le _)
      · exact absurd ⟨hD1 j, hD2 j⟩ hmem
    have hsumofReal : ENNReal.ofReal
        (∑ j : Fin m,
          |Phi Γih LG u (D1 j).1 (D1 j).2 - Phi Γih LG u (D2 j).1 (D2 j).2|) =
        ∑ j : Fin m,
          ENNReal.ofReal |Phi Γih LG u (D1 j).1 (D1 j).2 - Phi Γih LG u (D2 j).1 (D2 j).2| := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro j _
      exact abs_nonneg _
    have hmain : |(β / (m : ℝ)) * potSum Γih LG D1 u - (β / (m : ℝ)) * potSum Γih LG D2 u| ≤
        (β / (m : ℝ)) * ∑ j : Fin m,
          |Phi Γih LG u (D1 j).1 (D1 j).2 - Phi Γih LG u (D2 j).1 (D2 j).2| := by
      have hrw : (β / (m : ℝ)) * potSum Γih LG D1 u - (β / (m : ℝ)) * potSum Γih LG D2 u =
          (β / (m : ℝ)) * (potSum Γih LG D1 u - potSum Γih LG D2 u) := by ring
      rw [hrw, abs_mul, abs_of_nonneg hcoef]
      refine mul_le_mul_of_nonneg_left ?_ hcoef
      simp only [potSum]
      rw [← Finset.sum_sub_distrib]
      exact Finset.abs_sum_le_sum_abs _ _
    calc ENNReal.ofReal
          |(β / (m : ℝ)) * potSum Γih LG D1 u - (β / (m : ℝ)) * potSum Γih LG D2 u|
        ≤ ENNReal.ofReal ((β / (m : ℝ)) * ∑ j : Fin m,
          |Phi Γih LG u (D1 j).1 (D1 j).2 - Phi Γih LG u (D2 j).1 (D2 j).2|) :=
          ENNReal.ofReal_le_ofReal hmain
      _ = ENNReal.ofReal (β / (m : ℝ)) * ENNReal.ofReal
            (∑ j : Fin m,
              |Phi Γih LG u (D1 j).1 (D1 j).2 - Phi Γih LG u (D2 j).1 (D2 j).2|) :=
          ENNReal.ofReal_mul hcoef
      _ = ENNReal.ofReal (β / (m : ℝ)) * ∑ j : Fin m,
            ENNReal.ofReal
              |Phi Γih LG u (D1 j).1 (D1 j).2 - Phi Γih LG u (D2 j).1 (D2 j).2| := by
          rw [hsumofReal]
      _ ≤ ENNReal.ofReal (β / (m : ℝ)) * ∑ j : Fin m,
            (ENNReal.ofReal kappa * HScaleDist bH mu (α - s) (D2 j).2 (D1 j).2 *
                ENNReal.ofReal Mv +
              (ENNReal.ofReal (mubar ^ st) * ENNReal.ofReal Mv +
                  ENNReal.ofReal kappa * HScaleDist bH mu (α - s) (D1 j).2 0) *
                HScaleDist bH mu st (Γih (LG (D1 j).1 u - LG (D2 j).1 u)) 0) :=
          mul_le_mul_left' (Finset.sum_le_sum fun j _ => key j) _
  · intro r hr D1 D2 hD1 hD2 hr1 hr2 u hU
    set Mv : ℝ := M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) with hMv
    have hMv0 : 0 ≤ Mv := hM1_nonneg _
    have hms : 0 ≤ mubar ^ st := Real.rpow_nonneg (by linarith) st
    have key : ∀ j : Fin m,
        |Phi Γih LG u (D1 j).1 (D1 j).2 - Phi Γih LG u (D2 j).1 (D2 j).2| ≤
          (4 * kappa * r + 2 * mubar ^ st) * (1 + Mv ^ 2) := by
      intro j
      have hb6 := h6 (D2 j).1 (D2 j).1 (D2 j).2 (D1 j).2 (hD2 j) (hD1 j) u hU
      have hb7 := h7 (D1 j).1 (D2 j).1 (D1 j).2 (D1 j).2 (hD1 j) (hD1 j) u hU
      have hb8 := h8 (D1 j).1 (D2 j).1 (D1 j).2 (D2 j).2 (hD1 j) (hD2 j) u hU
      rw [← hMv] at hb6 hb7 hb8
      have ht2 : |Phi Γih LG u (D1 j).1 (D1 j).2 - Phi Γih LG u (D2 j).1 (D2 j).2| ≤
          kappa * ENNReal.toReal (HScaleDist bH mu (α - s) (D2 j).2 (D1 j).2) * Mv +
            (mubar ^ st * Mv +
                kappa * ENNReal.toReal (HScaleDist bH mu (α - s) (D1 j).2 0)) *
              ENNReal.toReal (HScaleDist bH mu st (Γih (LG (D1 j).1 u - LG (D2 j).1 u)) 0) := by
        have hsp : |Phi Γih LG u (D1 j).1 (D1 j).2 - Phi Γih LG u (D2 j).1 (D2 j).2| ≤
            |Phi Γih LG u (D2 j).1 (D1 j).2 - Phi Γih LG u (D2 j).1 (D2 j).2| +
              |Phi Γih LG u (D1 j).1 (D1 j).2 - Phi Γih LG u (D2 j).1 (D1 j).2| := by
          have h := abs_add_le
            (Phi Γih LG u (D2 j).1 (D1 j).2 - Phi Γih LG u (D2 j).1 (D2 j).2)
            (Phi Γih LG u (D1 j).1 (D1 j).2 - Phi Γih LG u (D2 j).1 (D1 j).2)
          have he : (Phi Γih LG u (D2 j).1 (D1 j).2 - Phi Γih LG u (D2 j).1 (D2 j).2) +
              (Phi Γih LG u (D1 j).1 (D1 j).2 - Phi Γih LG u (D2 j).1 (D1 j).2) =
              Phi Γih LG u (D1 j).1 (D1 j).2 - Phi Γih LG u (D2 j).1 (D2 j).2 := by abel
          rwa [he] at h
        refine le_trans hsp (add_le_add ?_ hb7)
        rw [abs_sub_comm]
        exact hb6
      have hd2 : (HScaleDist bH mu (α - s) (D2 j).2 (D1 j).2).toReal ≤ 2 * r := by
        have htri := statopia_math_node_1182065402_10a004d7 bH mu hmu_pos (α - s) (D1 j).2
          (D2 j).2 (ne_of_lt (hD1 j)) (ne_of_lt (hD2 j))
        have h1 : (HScaleDist bH mu (α - s) (D2 j).2 0).toReal ≤ r :=
          ENNReal.toReal_le_of_le_ofReal hr (hr2 j)
        have h2 : (HScaleDist bH mu (α - s) (D1 j).2 0).toReal ≤ r :=
          ENNReal.toReal_le_of_le_ofReal hr (hr1 j)
        linarith
      have hd1 : (HScaleDist bH mu (α - s) (D1 j).2 0).toReal ≤ r :=
        ENNReal.toReal_le_of_le_ofReal hr (hr1 j)
      have haj : (HScaleDist bH mu st (Γih (LG (D1 j).1 u - LG (D2 j).1 u)) 0).toReal ≤
          2 * Mv := hb8
      have hAstep : kappa * ENNReal.toReal (HScaleDist bH mu (α - s) (D2 j).2 (D1 j).2) * Mv ≤
          2 * (kappa * r) * Mv := by
        have h1 : kappa * ENNReal.toReal (HScaleDist bH mu (α - s) (D2 j).2 (D1 j).2) ≤
            kappa * (2 * r) := mul_le_mul_of_nonneg_left hd2 hkappa
        have h2 : kappa * ENNReal.toReal (HScaleDist bH mu (α - s) (D2 j).2 (D1 j).2) * Mv ≤
            (kappa * (2 * r)) * Mv := mul_le_mul_of_nonneg_right h1 hMv0
        linarith [h2]
      have hCstep : mubar ^ st * Mv +
            kappa * ENNReal.toReal (HScaleDist bH mu (α - s) (D1 j).2 0) ≤
          mubar ^ st * Mv + kappa * r := by
        have h := mul_le_mul_of_nonneg_left hd1 hkappa
        linarith [h]
      have hBstep : (mubar ^ st * Mv +
            kappa * ENNReal.toReal (HScaleDist bH mu (α - s) (D1 j).2 0)) *
            ENNReal.toReal (HScaleDist bH mu st (Γih (LG (D1 j).1 u - LG (D2 j).1 u)) 0) ≤
          (mubar ^ st * Mv + kappa * r) * (2 * Mv) := by
        refine mul_le_mul hCstep haj ENNReal.toReal_nonneg ?_
        have h1 : 0 ≤ mubar ^ st * Mv := mul_nonneg hms hMv0
        have h2 : 0 ≤ kappa * r := mul_nonneg hkappa hr
        linarith [h1, h2]
      have hbound : kappa * ENNReal.toReal (HScaleDist bH mu (α - s) (D2 j).2 (D1 j).2) * Mv +
            (mubar ^ st * Mv +
                kappa * ENNReal.toReal (HScaleDist bH mu (α - s) (D1 j).2 0)) *
              ENNReal.toReal (HScaleDist bH mu st (Γih (LG (D1 j).1 u - LG (D2 j).1 u)) 0) ≤
          4 * kappa * r * Mv + 2 * mubar ^ st * Mv ^ 2 := by
        have he : (mubar ^ st * Mv + kappa * r) * (2 * Mv) =
            2 * (mubar ^ st * Mv ^ 2) + 2 * (kappa * r) * Mv := by ring
        linarith [hAstep, hBstep, he]
      have hfin : 4 * kappa * r * Mv + 2 * mubar ^ st * Mv ^ 2 ≤
          (4 * kappa * r + 2 * mubar ^ st) * (1 + Mv ^ 2) := by
        have hMv1 : Mv ≤ 1 + Mv ^ 2 := by nlinarith [hMv0, sq_nonneg (Mv - 1)]
        have hMv2 : Mv ^ 2 ≤ 1 + Mv ^ 2 := by nlinarith [sq_nonneg Mv]
        have hk : 0 ≤ 4 * kappa * r := by nlinarith [hkappa, hr]
        have hmu2 : 0 ≤ 2 * mubar ^ st := by nlinarith [hms]
        have e1 : 4 * kappa * r * Mv ≤ 4 * kappa * r * (1 + Mv ^ 2) :=
          mul_le_mul_of_nonneg_left hMv1 hk
        have e2 : 2 * mubar ^ st * Mv ^ 2 ≤ 2 * mubar ^ st * (1 + Mv ^ 2) :=
          mul_le_mul_of_nonneg_left hMv2 hmu2
        have e3 : (4 * kappa * r + 2 * mubar ^ st) * (1 + Mv ^ 2) =
            4 * kappa * r * (1 + Mv ^ 2) + 2 * mubar ^ st * (1 + Mv ^ 2) := by ring
        linarith [e1, e2, e3]
      linarith [ht2, hbound, hfin]
    have hmain : |(β / (m : ℝ)) * potSum Γih LG D1 u - (β / (m : ℝ)) * potSum Γih LG D2 u| ≤
        (β / (m : ℝ)) * ∑ j : Fin m, ((4 * kappa * r + 2 * mubar ^ st) * (1 + Mv ^ 2)) := by
      have hrw : (β / (m : ℝ)) * potSum Γih LG D1 u - (β / (m : ℝ)) * potSum Γih LG D2 u =
          (β / (m : ℝ)) * (potSum Γih LG D1 u - potSum Γih LG D2 u) := by ring
      rw [hrw, abs_mul, abs_of_nonneg hcoef]
      refine mul_le_mul_of_nonneg_left ?_ hcoef
      simp only [potSum]
      rw [← Finset.sum_sub_distrib]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      exact Finset.sum_le_sum fun j _ => key j
    have hmain' : |(β / (m : ℝ)) * potSum Γih LG D1 u - (β / (m : ℝ)) * potSum Γih LG D2 u| ≤
        β * (4 * kappa * r + 2 * mubar ^ st) * (1 + Mv ^ 2) := by
      have hgoalEq : (β / (m : ℝ)) *
            ∑ j : Fin m, ((4 * kappa * r + 2 * mubar ^ st) * (1 + Mv ^ 2)) =
          β * (4 * kappa * r + 2 * mubar ^ st) * (1 + Mv ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
      linarith [hmain, hgoalEq]
    exact hmain'
  · intro hcont Dn D hmem hD hT u hU
    set Mv : ℝ := M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) with hMv
    have hMv0 : 0 ≤ Mv := hM1_nonneg _
    have hms : 0 ≤ mubar ^ st := Real.rpow_nonneg (by linarith) st
    rw [dataNhds] at hT
    have hd2 : ∀ j : Fin m, Tendsto (fun n : ℕ =>
        (HScaleDist bH mu (α - s) ((Dn n) j).2 ((D j).2)).toReal) atTop (𝓝 0) := by
      intro j
      have h1 := (tendsto_inf.1 ((tendsto_iInf.1 hT) j)).2
      have hcomp : Tendsto (fun n : ℕ => ((Dn n) j).2) atTop
          (scaleNhds (fun z : H => (HScaleNorm bH mu (α - s) z) ^ (1 / 2 : ℝ))
            (HScale bH mu (α - s)) ((D j).2)) := by
        simpa using Filter.tendsto_comap_iff.1 h1
      rw [scaleNhds] at hcomp
      have hprinc : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
          (HScaleDist bH mu (α - s) ((Dn n) j).2 ((D j).2)) ≤ ENNReal.ofReal δ := by
        intro δ hδ
        have hmem' := Filter.tendsto_principal.1 ((tendsto_iInf.1 hcomp) ⟨δ, hδ⟩)
        filter_upwards [hmem'] with n hn
        have h2 : (HScaleNorm bH mu (α - s) (((Dn n) j).2 - (D j).2)) ^ (1 / 2 : ℝ) <
            ENNReal.ofReal δ := by
          simpa using hn.2
        simpa [HScaleDist] using le_of_lt h2
      rw [tendsto_order]
      refine ⟨fun b hb => Filter.Eventually.of_forall fun n => ?_, fun b hb => ?_⟩
      · exact lt_of_lt_of_le hb ENNReal.toReal_nonneg
      · have hb2 : (0 : ℝ) < b / 2 := by linarith
        filter_upwards [hprinc (b / 2) hb2] with n hn
        have hle := ENNReal.toReal_le_of_le_ofReal (le_of_lt hb2) hn
        linarith
    have ha : ∀ j : Fin m, Tendsto (fun n : ℕ =>
        (HScaleDist bH mu st (Γih (LG ((Dn n) j).1 u - LG ((D j).1) u)) 0).toReal) atTop (𝓝 0) := by
      intro j
      have hx : Tendsto (fun n : ℕ => ((Dn n) j).1) atTop (𝓝 ((D j).1)) := by
        have h1 := (tendsto_inf.1 ((tendsto_iInf.1 hT) j)).1
        have h2 := Filter.tendsto_comap_iff.1 h1
        simpa using h2
      have hc := (hcont ((D j).1) u hU).comp hx
      have hE : Tendsto (fun n : ℕ =>
          (HScaleDist bH mu st (Γih (LG ((Dn n) j).1 u - LG ((D j).1) u)) 0)) atTop (𝓝 0) := by
        simpa [HScaleDist, sub_zero] using hc
      have hle : ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ n : ℕ in atTop,
          (HScaleDist bH mu st (Γih (LG ((Dn n) j).1 u - LG ((D j).1) u)) 0) ≤ ε :=
        ENNReal.tendsto_nhds_zero.1 hE
      rw [tendsto_order]
      refine ⟨fun b hb => Filter.Eventually.of_forall fun n => ?_, fun b hb => ?_⟩
      · exact lt_of_lt_of_le hb ENNReal.toReal_nonneg
      · have hb2 : (0 : ℝ) < b / 2 := by linarith
        have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (b / 2) := ENNReal.ofReal_pos.2 hb2
        filter_upwards [hle (ENNReal.ofReal (b / 2)) hpos] with n hn
        have hle' := ENNReal.toReal_le_of_le_ofReal (le_of_lt hb2) hn
        linarith
    have hbd : ∀ (j : Fin m) (n : ℕ),
        |Phi Γih LG u ((Dn n) j).1 ((Dn n) j).2 - Phi Γih LG u (D j).1 (D j).2| ≤
          kappa * (HScaleDist bH mu (α - s) ((Dn n) j).2 ((D j).2)).toReal * Mv +
            (mubar ^ st * Mv + kappa * (HScaleDist bH mu (α - s) (D j).2 0).toReal) *
              (HScaleDist bH mu st (Γih (LG ((Dn n) j).1 u - LG ((D j).1) u)) 0).toReal := by
      intro j n
      have hb6 := h6 ((Dn n) j).1 ((Dn n) j).1 ((Dn n) j).2 ((D j).2) (hmem n j) (hD j) u hU
      have hb7 := h7 ((Dn n) j).1 ((D j).1) ((D j).2) ((D j).2) (hD j) (hD j) u hU
      rw [← hMv] at hb6 hb7
      have hsp : |Phi Γih LG u ((Dn n) j).1 ((Dn n) j).2 - Phi Γih LG u (D j).1 (D j).2| ≤
          |Phi Γih LG u ((Dn n) j).1 ((Dn n) j).2 - Phi Γih LG u ((Dn n) j).1 ((D j).2)| +
            |Phi Γih LG u ((Dn n) j).1 ((D j).2) - Phi Γih LG u (D j).1 ((D j).2)| := by
        have h := abs_add_le
          (Phi Γih LG u ((Dn n) j).1 ((Dn n) j).2 - Phi Γih LG u ((Dn n) j).1 ((D j).2))
          (Phi Γih LG u ((Dn n) j).1 ((D j).2) - Phi Γih LG u (D j).1 ((D j).2))
        have he : (Phi Γih LG u ((Dn n) j).1 ((Dn n) j).2 - Phi Γih LG u ((Dn n) j).1 ((D j).2)) +
            (Phi Γih LG u ((Dn n) j).1 ((D j).2) - Phi Γih LG u (D j).1 ((D j).2)) =
            Phi Γih LG u ((Dn n) j).1 ((Dn n) j).2 - Phi Γih LG u (D j).1 (D j).2 := by abel
        rwa [he] at h
      exact le_trans hsp (add_le_add hb6 hb7)
    have hterm : ∀ j : Fin m, Tendsto (fun n : ℕ =>
        |Phi Γih LG u ((Dn n) j).1 ((Dn n) j).2 - Phi Γih LG u (D j).1 (D j).2|)
        atTop (𝓝 0) := by
      intro j
      have hnull : Tendsto (fun n : ℕ =>
          kappa * (HScaleDist bH mu (α - s) ((Dn n) j).2 ((D j).2)).toReal * Mv +
            (mubar ^ st * Mv + kappa * (HScaleDist bH mu (α - s) (D j).2 0).toReal) *
              (HScaleDist bH mu st (Γih (LG ((Dn n) j).1 u - LG ((D j).1) u)) 0).toReal)
          atTop (𝓝 0) := by
        have h1 : Tendsto (fun n : ℕ =>
            kappa * (HScaleDist bH mu (α - s) ((Dn n) j).2 ((D j).2)).toReal * Mv)
            atTop (𝓝 0) := by
          have h := ((hd2 j).const_mul kappa).mul_const Mv
          simpa using h
        have h2 : Tendsto (fun n : ℕ =>
            (mubar ^ st * Mv + kappa * (HScaleDist bH mu (α - s) (D j).2 0).toReal) *
              (HScaleDist bH mu st (Γih (LG ((Dn n) j).1 u - LG ((D j).1) u)) 0).toReal)
            atTop (𝓝 0) := by
          have h := (ha j).const_mul
            (mubar ^ st * Mv + kappa * (HScaleDist bH mu (α - s) (D j).2 0).toReal)
          simpa using h
        simpa using h1.add h2
      exact squeeze_zero (fun n => abs_nonneg _) (fun n => hbd j n) hnull
    have hsum : Tendsto (fun n : ℕ => ∑ j : Fin m,
        |Phi Γih LG u ((Dn n) j).1 ((Dn n) j).2 - Phi Γih LG u (D j).1 (D j).2|)
        atTop (𝓝 0) := by
      have h := tendsto_finset_sum (s := (Finset.univ : Finset (Fin m))) (fun j _ => hterm j)
      simpa using h
    have hΔ : ∀ n : ℕ,
        |(β / (m : ℝ)) * potSum Γih LG (Dn n) u - (β / (m : ℝ)) * potSum Γih LG D u| ≤
          (β / (m : ℝ)) * ∑ j : Fin m,
            |Phi Γih LG u ((Dn n) j).1 ((Dn n) j).2 - Phi Γih LG u (D j).1 (D j).2| := by
      intro n
      have hrw : (β / (m : ℝ)) * potSum Γih LG (Dn n) u - (β / (m : ℝ)) * potSum Γih LG D u =
          (β / (m : ℝ)) * (potSum Γih LG (Dn n) u - potSum Γih LG D u) := by ring
      rw [hrw, abs_mul, abs_of_nonneg hcoef]
      refine mul_le_mul_of_nonneg_left ?_ hcoef
      simp only [potSum]
      rw [← Finset.sum_sub_distrib]
      exact Finset.abs_sum_le_sum_abs _ _
    have habs : Tendsto (fun n : ℕ =>
        |(β / (m : ℝ)) * potSum Γih LG (Dn n) u - (β / (m : ℝ)) * potSum Γih LG D u|)
        atTop (𝓝 0) := by
      refine squeeze_zero (fun n => abs_nonneg _) hΔ ?_
      have h := hsum.const_mul (β / (m : ℝ))
      simpa using h
    have hΔ0 : Tendsto (fun n : ℕ =>
        (β / (m : ℝ)) * potSum Γih LG (Dn n) u - (β / (m : ℝ)) * potSum Γih LG D u)
        atTop (𝓝 0) := by
      rw [tendsto_order]
      refine ⟨fun b hb => ?_, fun b hb => ?_⟩
      · have hε := (tendsto_order.1 habs).2 (-b) (by linarith)
        filter_upwards [hε] with n hn
        have h1 := (abs_lt.1 hn).1
        linarith
      · have hε := (tendsto_order.1 habs).2 b hb
        filter_upwards [hε] with n hn
        have h1 := (abs_lt.1 hn).2
        linarith
    have hconst : Tendsto (fun _ : ℕ => (β / (m : ℝ)) * potSum Γih LG D u) atTop
        (𝓝 ((β / (m : ℝ)) * potSum Γih LG D u)) := tendsto_const_nhds
    have hfin := hconst.add hΔ0
    have hfun : (fun n : ℕ => (β / (m : ℝ)) * potSum Γih LG D u +
        ((β / (m : ℝ)) * potSum Γih LG (Dn n) u - (β / (m : ℝ)) * potSum Γih LG D u))
        = fun n : ℕ => (β / (m : ℝ)) * potSum Γih LG (Dn n) u := by
      funext n
      ring
    rw [hfun] at hfin
    simpa using hfin
  /- @proof-region region.target-node.session.5a37bca7c73bd95b end -/

end Statlib.Imported
end

