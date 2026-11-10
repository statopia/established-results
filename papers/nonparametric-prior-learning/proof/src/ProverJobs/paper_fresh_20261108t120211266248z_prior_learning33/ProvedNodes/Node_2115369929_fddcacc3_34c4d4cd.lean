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
theorem statopia_math_node_2115369929_fddcacc3 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [MeasurableSpace U] [BorelSpace U]
    (e : HilbertBasis ℕ ℝ U) (lam : ℕ → ℝ)
    (hlam_pos : ∀ k : ℕ, 0 < lam k) (hlam_anti : Antitone lam) (hlam_sum : Summable lam)
    (s0 : ℝ) (hs0_nonneg : 0 ≤ s0) (hs0_lt : s0 < 1)
    (hs0_trace : ∀ t : ℝ, s0 < t → Summable (fun k : ℕ => Real.rpow (lam k) t))
    (Nc : ℕ) (hNc : 0 < Nc) (theta2 : Fin Nc → ℝ)
    (C0th : (Fin Nc → ℝ) → U →L[ℝ] U)
    (hC0th_basis : ∀ k : ℕ, C0th theta2 (e k) = priorEigen lam Nc theta2 k • e k),
    (∀ v : U, UScale e lam 2 v → UScale e lam 1 v) ∧
      (∀ (f : U) (P : Measure U) [IsProbabilityMeasure P],
        (∀ v : U, ∫ u, inner ℝ v u ∂P = inner ℝ v f) →
        (∀ v w : U,
          ∫ u, (inner ℝ v u - inner ℝ v f) * (inner ℝ w u - inner ℝ w f) ∂P
            = inner ℝ v (C0th theta2 w)) →
        (∀ v : U, Integrable (fun u : U => inner ℝ v u) P) →
        (∀ v w : U,
          Integrable (fun u : U =>
            (inner ℝ v u - inner ℝ v f) * (inner ℝ w u - inner ℝ w f)) P) →
        ∀ sigma : ℝ, s0 < sigma → sigma ≤ 1 → UScale e lam 1 f →
          P (UScale e lam (1 - sigma)) = 1) := by
  /- @proof-region region.target-node.session.79fb8e01b33b6a0b begin -/
  intro U hNAG hIPS hCS hMS hBS e lam hlam_pos hlam_anti hlam_sum s0 hs0_nonneg hs0_lt hs0_trace Nc hNc theta2 C0th hC0th_basis
  refine ⟨?_, ?_⟩
  · intro v hv
    have hkey : UScaleNorm e lam 1 v ≤ ENNReal.ofReal (lam 0) * UScaleNorm e lam 2 v := by
      unfold UScaleNorm
      rw [← ENNReal.tsum_mul_left]
      refine ENNReal.tsum_le_tsum fun k => ?_
      have hp : (0:ℝ) < lam k := hlam_pos k
      have hx : (0:ℝ) ≤ (inner ℝ (e k) v) ^ 2 := sq_nonneg _
      have h1 : Real.rpow (lam k) (-(1:ℝ)) = lam k * Real.rpow (lam k) (-(2:ℝ)) := by
        have h := Real.rpow_add hp (-(2:ℝ)) (1:ℝ)
        rw [show (-(2:ℝ)) + 1 = -(1:ℝ) by norm_num, Real.rpow_one, mul_comm] at h
        exact h
      have hq : (0:ℝ) ≤ Real.rpow (lam k) (-(2:ℝ)) * (inner ℝ (e k) v) ^ 2 :=
        mul_nonneg (Real.rpow_nonneg hp.le (-(2:ℝ))) hx
      have hle : Real.rpow (lam k) (-(1:ℝ)) * (inner ℝ (e k) v) ^ 2
          ≤ lam 0 * (Real.rpow (lam k) (-(2:ℝ)) * (inner ℝ (e k) v) ^ 2) := by
        rw [h1, mul_assoc]
        exact mul_le_mul_of_nonneg_right (hlam_anti (Nat.zero_le k)) hq
      calc ENNReal.ofReal (Real.rpow (lam k) (-(1:ℝ)) * (inner ℝ (e k) v) ^ 2)
          ≤ ENNReal.ofReal (lam 0 * (Real.rpow (lam k) (-(2:ℝ)) * (inner ℝ (e k) v) ^ 2)) :=
            (ENNReal.ofReal_le_ofReal_iff
              (p := Real.rpow (lam k) (-(1:ℝ)) * (inner ℝ (e k) v) ^ 2)
              (q := lam 0 * (Real.rpow (lam k) (-(2:ℝ)) * (inner ℝ (e k) v) ^ 2))
              (mul_nonneg (hlam_pos 0).le hq)).2 hle
        _ = ENNReal.ofReal (lam 0) *
              ENNReal.ofReal (Real.rpow (lam k) (-(2:ℝ)) * (inner ℝ (e k) v) ^ 2) :=
            ENNReal.ofReal_mul' (p := lam 0)
              (q := Real.rpow (lam k) (-(2:ℝ)) * (inner ℝ (e k) v) ^ 2) hq
    exact lt_of_le_of_lt hkey (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hv)
  · intro f P hP hmean hcov hint1 hint2 sigma hσ0 hσ1 hf
    haveI : IsProbabilityMeasure P := hP
    have hmeas_term : ∀ k : ℕ, Measurable (fun u : U =>
        ENNReal.ofReal (Real.rpow (lam k) (-(1 - sigma)) * (inner ℝ (e k) u) ^ 2)) := by
      intro k
      have hc : Continuous fun u : U => inner ℝ (e k) u := continuous_const.inner continuous_id
      exact (continuous_const.mul (hc.pow 2)).measurable.ennreal_ofReal
    have hg : Measurable fun u : U => UScaleNorm e lam (1 - sigma) u := by
      unfold UScaleNorm
      exact Measurable.ennreal_tsum hmeas_term
    have hton : ∫⁻ u, UScaleNorm e lam (1 - sigma) u ∂P
        = ∑' k : ℕ, ∫⁻ u,
            ENNReal.ofReal (Real.rpow (lam k) (-(1 - sigma)) * (inner ℝ (e k) u) ^ 2) ∂P := by
      unfold UScaleNorm
      exact MeasureTheory.lintegral_tsum (fun k => (hmeas_term k).aemeasurable)
    have hterm : ∀ k : ℕ, ∫⁻ u,
        ENNReal.ofReal (Real.rpow (lam k) (-(1 - sigma)) * (inner ℝ (e k) u) ^ 2) ∂P
        = ENNReal.ofReal (Real.rpow (lam k) (-(1 - sigma)) *
            (priorEigen lam Nc theta2 k + (inner ℝ (e k) f) ^ 2)) := by
      intro k
      have hNint : Integrable (fun u : U => inner ℝ (e k) u) P := hint1 (e k)
      have hA : Integrable (fun u : U =>
          (inner ℝ (e k) u - inner ℝ (e k) f) * (inner ℝ (e k) u - inner ℝ (e k) f)) P :=
        hint2 (e k) (e k)
      have hB : Integrable (fun u : U =>
          (2 * inner ℝ (e k) f) * inner ℝ (e k) u) P := hNint.const_mul _
      have hC : Integrable (fun u : U => inner ℝ (e k) f * inner ℝ (e k) f) P := integrable_const _
      have hpt : ∀ u : U, (inner ℝ (e k) u) ^ 2
          = (inner ℝ (e k) u - inner ℝ (e k) f) * (inner ℝ (e k) u - inner ℝ (e k) f)
            + (2 * inner ℝ (e k) f) * inner ℝ (e k) u
            - inner ℝ (e k) f * inner ℝ (e k) f := by
        intro u
        ring
      have hN2int : Integrable (fun u : U => (inner ℝ (e k) u) ^ 2) P := by
        rw [show (fun u : U => (inner ℝ (e k) u) ^ 2) = (fun u : U =>
            (inner ℝ (e k) u - inner ℝ (e k) f) * (inner ℝ (e k) u - inner ℝ (e k) f)
            + (2 * inner ℝ (e k) f) * inner ℝ (e k) u
            - inner ℝ (e k) f * inner ℝ (e k) f) from funext hpt]
        exact (hA.add hB).sub hC
      have hconst : ∀ c : ℝ, ∫ u : U, c ∂P = c := by
        intro c
        rw [MeasureTheory.integral_const]
        have h1 : P.real Set.univ = 1 := by simp [MeasureTheory.Measure.real]
        rw [h1, one_smul]
      have hXXval : ∫ u, (inner ℝ (e k) u - inner ℝ (e k) f) *
          (inner ℝ (e k) u - inner ℝ (e k) f) ∂P = priorEigen lam Nc theta2 k := by
        have hk : inner ℝ (e k) (e k) = 1 :=
          inner_self_eq_one_of_norm_eq_one (e.orthonormal.norm_eq_one k)
        rw [hcov (e k) (e k), hC0th_basis k, real_inner_smul_right, hk, mul_one]
      have hBval : ∫ u, (2 * inner ℝ (e k) f) * inner ℝ (e k) u ∂P
          = (2 * inner ℝ (e k) f) * inner ℝ (e k) f := by
        rw [MeasureTheory.integral_const_mul, hmean (e k)]
      have hAB : Integrable (fun u : U =>
          (inner ℝ (e k) u - inner ℝ (e k) f) * (inner ℝ (e k) u - inner ℝ (e k) f)
            + (2 * inner ℝ (e k) f) * inner ℝ (e k) u) P := hA.add hB
      have hAddEq : ∫ u, ((inner ℝ (e k) u - inner ℝ (e k) f) * (inner ℝ (e k) u - inner ℝ (e k) f)
            + (2 * inner ℝ (e k) f) * inner ℝ (e k) u) ∂P
          = (∫ u, (inner ℝ (e k) u - inner ℝ (e k) f) * (inner ℝ (e k) u - inner ℝ (e k) f) ∂P)
            + ∫ u, (2 * inner ℝ (e k) f) * inner ℝ (e k) u ∂P :=
        MeasureTheory.integral_add hA hB
      have hN2val : ∫ u, (inner ℝ (e k) u) ^ 2 ∂P
          = priorEigen lam Nc theta2 k + (inner ℝ (e k) f) ^ 2 := by
        calc ∫ u, (inner ℝ (e k) u) ^ 2 ∂P
            = ∫ u, ((inner ℝ (e k) u - inner ℝ (e k) f) * (inner ℝ (e k) u - inner ℝ (e k) f)
                + (2 * inner ℝ (e k) f) * inner ℝ (e k) u
                - inner ℝ (e k) f * inner ℝ (e k) f) ∂P := by
              rw [show (fun u : U => (inner ℝ (e k) u) ^ 2) = (fun u : U =>
                  (inner ℝ (e k) u - inner ℝ (e k) f) * (inner ℝ (e k) u - inner ℝ (e k) f)
                  + (2 * inner ℝ (e k) f) * inner ℝ (e k) u
                  - inner ℝ (e k) f * inner ℝ (e k) f) from funext hpt]
          _ = (∫ u, ((inner ℝ (e k) u - inner ℝ (e k) f) * (inner ℝ (e k) u - inner ℝ (e k) f)
                + (2 * inner ℝ (e k) f) * inner ℝ (e k) u) ∂P)
              - ∫ u, inner ℝ (e k) f * inner ℝ (e k) f ∂P :=
              MeasureTheory.integral_sub hAB hC
          _ = ((∫ u, (inner ℝ (e k) u - inner ℝ (e k) f) *
                  (inner ℝ (e k) u - inner ℝ (e k) f) ∂P)
                + ∫ u, (2 * inner ℝ (e k) f) * inner ℝ (e k) u ∂P)
              - ∫ u, inner ℝ (e k) f * inner ℝ (e k) f ∂P := by
              rw [hAddEq]
          _ = (priorEigen lam Nc theta2 k + (2 * inner ℝ (e k) f) * inner ℝ (e k) f)
              - inner ℝ (e k) f * inner ℝ (e k) f := by
              rw [hXXval, hBval, hconst]
          _ = priorEigen lam Nc theta2 k + (inner ℝ (e k) f) ^ 2 := by ring
      have hprodint : Integrable (fun u : U =>
          Real.rpow (lam k) (-(1 - sigma)) * (inner ℝ (e k) u) ^ 2) P := hN2int.const_mul _
      have hprodnn : ∀ᵐ u ∂P,
          (0:ℝ) ≤ Real.rpow (lam k) (-(1 - sigma)) * (inner ℝ (e k) u) ^ 2 :=
        Filter.Eventually.of_forall fun u =>
          mul_nonneg (Real.rpow_nonneg (hlam_pos k).le _) (sq_nonneg _)
      calc ∫⁻ u, ENNReal.ofReal (Real.rpow (lam k) (-(1 - sigma)) * (inner ℝ (e k) u) ^ 2) ∂P
          = ENNReal.ofReal (∫ u,
              Real.rpow (lam k) (-(1 - sigma)) * (inner ℝ (e k) u) ^ 2 ∂P) :=
            (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hprodint hprodnn).symm
        _ = ENNReal.ofReal (Real.rpow (lam k) (-(1 - sigma)) *
              ∫ u, (inner ℝ (e k) u) ^ 2 ∂P) := by
            rw [MeasureTheory.integral_const_mul]
        _ = ENNReal.ofReal (Real.rpow (lam k) (-(1 - sigma)) *
              (priorEigen lam Nc theta2 k + (inner ℝ (e k) f) ^ 2)) := by
            rw [hN2val]
    have hsum : ∑' k : ℕ, ENNReal.ofReal (Real.rpow (lam k) (-(1 - sigma)) *
        (priorEigen lam Nc theta2 k + (inner ℝ (e k) f) ^ 2)) < ⊤ := by
      have hσnn : (0:ℝ) ≤ sigma := by linarith
      have hpe_nn : ∀ k : ℕ, (0:ℝ) ≤ priorEigen lam Nc theta2 k := by
        intro k
        unfold priorEigen
        split_ifs with h
        · exact (Real.exp_pos _).le
        · exact (hlam_pos k).le
      have hsumNN : (0:ℝ) ≤ ∑ j ∈ Finset.range Nc,
          Real.rpow (lam j) (-1) * priorEigen lam Nc theta2 j :=
        Finset.sum_nonneg (fun j _ =>
          mul_nonneg (Real.rpow_nonneg (hlam_pos j).le (-1)) (hpe_nn j))
      set Kb : ℝ := (∑ j ∈ Finset.range Nc,
          Real.rpow (lam j) (-1) * priorEigen lam Nc theta2 j) + 1
            + Real.rpow (lam 0) sigma with hKbdef
      have hMnn : (0:ℝ) ≤ Real.rpow (lam 0) sigma :=
        Real.rpow_nonneg (hlam_pos 0).le sigma
      have hKbM : Real.rpow (lam 0) sigma ≤ Kb := by
        rw [hKbdef]; linarith
      have hKb1 : (1:ℝ) ≤ Kb := by
        rw [hKbdef]; linarith
      have hKbk : ∀ k : ℕ, k < Nc →
          Real.rpow (lam k) (-1) * priorEigen lam Nc theta2 k ≤ Kb := by
        intro k hk
        have hmem : k ∈ Finset.range Nc := Finset.mem_range.mpr hk
        have hs := Finset.single_le_sum
          (s := Finset.range Nc)
          (f := fun j : ℕ => Real.rpow (lam j) (-1) * priorEigen lam Nc theta2 j)
          (fun j _ => mul_nonneg (Real.rpow_nonneg (hlam_pos j).le (-1)) (hpe_nn j)) hmem
        rw [hKbdef]; linarith
      have hfac : ∀ k : ℕ, Real.rpow (lam k) (-(1 - sigma))
          = Real.rpow (lam k) (-1) * Real.rpow (lam k) sigma := by
        intro k
        have h := Real.rpow_add (hlam_pos k) (-(1:ℝ)) sigma
        rw [show -(1:ℝ) + sigma = -(1 - sigma) by ring] at h
        exact h
      have hsig : ∀ k : ℕ, Real.rpow (lam k) (-(1 - sigma)) * lam k
          = Real.rpow (lam k) sigma := by
        intro k
        have h := Real.rpow_add (hlam_pos k) (-(1 - sigma)) (1:ℝ)
        rw [show -(1 - sigma) + 1 = sigma by ring, Real.rpow_one] at h
        exact h.symm
      have hmB : ∀ k : ℕ, Real.rpow (lam k) (-(1 - sigma)) * (inner ℝ (e k) f) ^ 2
          ≤ Kb * (Real.rpow (lam k) (-1) * (inner ℝ (e k) f) ^ 2) := by
        intro k
        have hle : Real.rpow (lam k) (-(1 - sigma)) ≤ Kb * Real.rpow (lam k) (-1) := by
          rw [hfac k]
          calc Real.rpow (lam k) (-1) * Real.rpow (lam k) sigma
              ≤ Real.rpow (lam k) (-1) * Real.rpow (lam 0) sigma :=
                mul_le_mul_of_nonneg_left
                  (Real.rpow_le_rpow (hlam_pos k).le (hlam_anti (Nat.zero_le k)) hσnn)
                  (Real.rpow_nonneg (hlam_pos k).le (-1))
            _ = Real.rpow (lam 0) sigma * Real.rpow (lam k) (-1) := mul_comm _ _
            _ ≤ Kb * Real.rpow (lam k) (-1) :=
                mul_le_mul_of_nonneg_right hKbM (Real.rpow_nonneg (hlam_pos k).le (-1))
        calc Real.rpow (lam k) (-(1 - sigma)) * (inner ℝ (e k) f) ^ 2
            ≤ (Kb * Real.rpow (lam k) (-1)) * (inner ℝ (e k) f) ^ 2 :=
              mul_le_mul_of_nonneg_right hle (sq_nonneg _)
          _ = Kb * (Real.rpow (lam k) (-1) * (inner ℝ (e k) f) ^ 2) := by ring
      have hdom : ∀ k : ℕ, Real.rpow (lam k) (-(1 - sigma)) *
            (priorEigen lam Nc theta2 k + (inner ℝ (e k) f) ^ 2)
          ≤ Kb * (Real.rpow (lam k) sigma
              + Real.rpow (lam k) (-1) * (inner ℝ (e k) f) ^ 2) := by
        intro k
        have h1 : Real.rpow (lam k) (-(1 - sigma)) * priorEigen lam Nc theta2 k
            ≤ Kb * Real.rpow (lam k) sigma := by
          by_cases hk : k < Nc
          · have hc : priorEigen lam Nc theta2 k = Real.exp (theta2 ⟨k, hk⟩) := by
              unfold priorEigen
              exact dif_pos hk
            have hkb : Real.rpow (lam k) (-1) * Real.exp (theta2 ⟨k, hk⟩) ≤ Kb := by
              have h := hKbk k hk
              rwa [hc] at h
            rw [hfac k, hc]
            calc Real.rpow (lam k) (-1) * Real.rpow (lam k) sigma * Real.exp (theta2 ⟨k, hk⟩)
                = Real.rpow (lam k) sigma *
                    (Real.rpow (lam k) (-1) * Real.exp (theta2 ⟨k, hk⟩)) := by ring
              _ ≤ Real.rpow (lam k) sigma * Kb :=
                  mul_le_mul_of_nonneg_left hkb (Real.rpow_nonneg (hlam_pos k).le sigma)
              _ = Kb * Real.rpow (lam k) sigma := by ring
          · have hc : priorEigen lam Nc theta2 k = lam k := by
              unfold priorEigen
              exact dif_neg hk
            rw [hc, hsig k]
            simpa using mul_le_mul_of_nonneg_right hKb1
              (Real.rpow_nonneg (hlam_pos k).le sigma)
        have h2 := hmB k
        calc Real.rpow (lam k) (-(1 - sigma)) *
              (priorEigen lam Nc theta2 k + (inner ℝ (e k) f) ^ 2)
            = Real.rpow (lam k) (-(1 - sigma)) * priorEigen lam Nc theta2 k
              + Real.rpow (lam k) (-(1 - sigma)) * (inner ℝ (e k) f) ^ 2 := by ring
          _ ≤ Kb * Real.rpow (lam k) sigma
              + Kb * (Real.rpow (lam k) (-1) * (inner ℝ (e k) f) ^ 2) := add_le_add h1 h2
          _ = Kb * (Real.rpow (lam k) sigma
              + Real.rpow (lam k) (-1) * (inner ℝ (e k) f) ^ 2) := by ring
      have hA : ∑' k : ℕ, ENNReal.ofReal (Real.rpow (lam k) sigma) < ⊤ :=
        Summable.tsum_ofReal_lt_top (hs0_trace sigma hσ0)
      have hB : ∑' k : ℕ,
          ENNReal.ofReal (Real.rpow (lam k) (-1) * (inner ℝ (e k) f) ^ 2) < ⊤ := hf
      have hstep : ∀ k : ℕ, ENNReal.ofReal (Real.rpow (lam k) (-(1 - sigma)) *
            (priorEigen lam Nc theta2 k + (inner ℝ (e k) f) ^ 2))
          ≤ ENNReal.ofReal Kb * (ENNReal.ofReal (Real.rpow (lam k) sigma)
              + ENNReal.ofReal (Real.rpow (lam k) (-1) * (inner ℝ (e k) f) ^ 2)) := by
        intro k
        have hq : (0:ℝ) ≤ Real.rpow (lam k) sigma
            + Real.rpow (lam k) (-1) * (inner ℝ (e k) f) ^ 2 :=
          add_nonneg (Real.rpow_nonneg (hlam_pos k).le sigma)
            (mul_nonneg (Real.rpow_nonneg (hlam_pos k).le (-1)) (sq_nonneg _))
        calc ENNReal.ofReal (Real.rpow (lam k) (-(1 - sigma)) *
              (priorEigen lam Nc theta2 k + (inner ℝ (e k) f) ^ 2))
            ≤ ENNReal.ofReal (Kb * (Real.rpow (lam k) sigma
                + Real.rpow (lam k) (-1) * (inner ℝ (e k) f) ^ 2)) :=
              ENNReal.ofReal_le_ofReal (hdom k)
          _ = ENNReal.ofReal Kb * ENNReal.ofReal (Real.rpow (lam k) sigma
                + Real.rpow (lam k) (-1) * (inner ℝ (e k) f) ^ 2) :=
              ENNReal.ofReal_mul' (p := Kb)
                (q := Real.rpow (lam k) sigma
                  + Real.rpow (lam k) (-1) * (inner ℝ (e k) f) ^ 2) hq
          _ = ENNReal.ofReal Kb * (ENNReal.ofReal (Real.rpow (lam k) sigma)
                + ENNReal.ofReal (Real.rpow (lam k) (-1) * (inner ℝ (e k) f) ^ 2)) := by
              have hp1 : (0:ℝ) ≤ Real.rpow (lam k) sigma :=
                Real.rpow_nonneg (hlam_pos k).le sigma
              have hp2 : (0:ℝ) ≤ Real.rpow (lam k) (-1) * (inner ℝ (e k) f) ^ 2 :=
                mul_nonneg (Real.rpow_nonneg (hlam_pos k).le (-1)) (sq_nonneg _)
              rw [ENNReal.ofReal_add (p := Real.rpow (lam k) sigma)
                (q := Real.rpow (lam k) (-1) * (inner ℝ (e k) f) ^ 2) hp1 hp2]
      calc ∑' k : ℕ, ENNReal.ofReal (Real.rpow (lam k) (-(1 - sigma)) *
            (priorEigen lam Nc theta2 k + (inner ℝ (e k) f) ^ 2))
          ≤ ∑' k : ℕ, ENNReal.ofReal Kb * (ENNReal.ofReal (Real.rpow (lam k) sigma)
              + ENNReal.ofReal (Real.rpow (lam k) (-1) * (inner ℝ (e k) f) ^ 2)) :=
            ENNReal.tsum_le_tsum hstep
        _ = ENNReal.ofReal Kb * ∑' k : ℕ, (ENNReal.ofReal (Real.rpow (lam k) sigma)
              + ENNReal.ofReal (Real.rpow (lam k) (-1) * (inner ℝ (e k) f) ^ 2)) :=
            ENNReal.tsum_mul_left
        _ = ENNReal.ofReal Kb * ((∑' k : ℕ, ENNReal.ofReal (Real.rpow (lam k) sigma))
              + ∑' k : ℕ,
                ENNReal.ofReal (Real.rpow (lam k) (-1) * (inner ℝ (e k) f) ^ 2)) := by
            rw [ENNReal.tsum_add]
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr ⟨hA, hB⟩)
    have hlt : ∫⁻ u, UScaleNorm e lam (1 - sigma) u ∂P < ⊤ := by
      rw [hton, tsum_congr hterm]
      exact hsum
    have hae : ∀ᵐ u ∂P, UScaleNorm e lam (1 - sigma) u < ⊤ :=
      MeasureTheory.ae_lt_top hg (ne_of_lt hlt)
    have hnull : P (UScale e lam (1 - sigma))ᶜ = 0 := by
      have h := hae
      rw [MeasureTheory.ae_iff] at h
      simpa [UScale, Set.compl_setOf] using h
    have hset : MeasurableSet (UScale e lam (1 - sigma)) := hg measurableSet_Iio
    have hfin : P (UScale e lam (1 - sigma)) + P (UScale e lam (1 - sigma))ᶜ = P Set.univ :=
      MeasureTheory.measure_add_measure_compl hset
    rw [hnull, add_zero, measure_univ] at hfin
    exact hfin
  /- @proof-region region.target-node.session.79fb8e01b33b6a0b end -/

end Statlib.Imported
end

