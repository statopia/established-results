import Lean
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_ca782bc74b0775d6b6b6
import ProverJobs.ResidualE2ESupport20261106.M_c5aeedf2f1c047528231
import ProverJobs.ResidualE2ESupport20261106.M_6e66486fda8ddfafb658

namespace PaperProofTasks.ResidualE2ESupport20261106

namespace ResidualLoss20261106
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.ResidualLoss20261106.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_1891546014_cda991f2 : ∀ (D : ℝ) (hD : 0 < D),
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (m n T : ℕ) (hn : 2 ≤ n) (hnm : n ≤ m) (hT : 1 ≤ T)
        (OmF : Matrix (Fin m) (Fin n) ℝ),
        (∀ (i : Fin m) (j : Fin n), OmF i j = 0 ∨ OmF i j = 1) →
        ∀ (μG : Measure (Matrix (Fin m) (Fin n) ℝ)) [instMuG : IsProbabilityMeasure μG],
          IsStdGaussianMatrixLaw μG →
            (∀ (i : Fin n), Integrable (fun G : Matrix (Fin m) (Fin n) ℝ =>
              sv hnm (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • G)) i) μG) →
              ∀ {Ωg : Type*} [instOg : MeasurableSpace Ωg] (μg : Measure Ωg)
                [instMug : IsProbabilityMeasure μg]
                (G : Ωg → Fin T → Matrix (Fin m) (Fin n) ℝ),
                IsGaussianDrawsLaw μg G →
                  μg {s : Ωg | ∀ (i : Fin n),
                        |lambdaHat hnm OmF (G s) i - lambdaCirc hnm μG OmF i|
                          ≤ C * Real.sqrt (Real.log (n : ℝ) / ((m : ℝ) * (T : ℝ)))} ≥
                    ENNReal.ofReal (1 - c * (n : ℝ).rpow (-D)) := by
  /- @proof-region region.target-node.session.122b9241730e1504 begin -/
  intro D hD
  refine ⟨2, 4 * Real.sqrt (D + 3), (by norm_num : (0:ℝ) < 2), ?_, ?_⟩
  · have hD3 : (0:ℝ) < D + 3 := by linarith
    have hs : (0:ℝ) < Real.sqrt (D + 3) := Real.sqrt_pos.mpr hD3
    linarith
  · intro m n T hn hnm hT OmF hbin μG instMuG hgauss hint Ωg instOg μg instMug G hdraws
    let tD : ℝ := (4 * Real.sqrt (D + 3)) * Real.sqrt (Real.log (n:ℝ) / ((m:ℝ) * (T:ℝ)))
    have htDval : tD = (4 * Real.sqrt (D + 3)) * Real.sqrt (Real.log (n:ℝ) / ((m:ℝ) * (T:ℝ))) := rfl
    have hn1 : (1:ℝ) ≤ (n:ℝ) := by
      have h2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      linarith
    have hnpos : (0:ℝ) < (n:ℝ) := by linarith
    have hmpos : (0:ℝ) < (m:ℝ) := by
      have h2 : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast (le_trans hn hnm)
      linarith
    have hTpos : (0:ℝ) < (T:ℝ) := by
      have h1 : (1:ℝ) ≤ (T:ℝ) := by exact_mod_cast hT
      linarith
    have hmTpos : (0:ℝ) < (m:ℝ) * (T:ℝ) := mul_pos hmpos hTpos
    have hmTne : ((m:ℝ) * (T:ℝ)) ≠ 0 := ne_of_gt hmTpos
    have hlog_nonneg : (0:ℝ) ≤ Real.log (n:ℝ) := Real.log_nonneg hn1
    have hD3le : (0:ℝ) ≤ D + 3 := by linarith
    have htD_nonneg : 0 ≤ tD := by
      rw [htDval]
      exact mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    have hchild : ∀ i : Fin n, μg {s : Ωg | tD ≤ |lambdaHat hnm OmF (G s) i - lambdaCirc hnm μG OmF i|} ≤ ENNReal.ofReal (2 * Real.exp (-(tD ^ 2 * ((m:ℝ) * (T:ℝ))) / 2)) :=
      fun i => statopia_math_node_3461429018_ebf22525 D hD m n T hn hnm hT OmF hbin μG hgauss Ωg μg G hdraws i tD htD_nonneg
    have htDsq : tD ^ 2 = 16 * (D + 3) * (Real.log (n:ℝ) / ((m:ℝ) * (T:ℝ))) := by
      rw [htDval, mul_pow, mul_pow, Real.sq_sqrt hD3le, Real.sq_sqrt (div_nonneg hlog_nonneg (le_of_lt hmTpos))]
      ring
    have hexp : -(tD ^ 2 * ((m:ℝ) * (T:ℝ))) / 2 = -(8 * (D + 3) * Real.log (n:ℝ)) := by
      have h : (tD ^ 2 * ((m:ℝ) * (T:ℝ))) / 2 = 8 * (D + 3) * Real.log (n:ℝ) := by
        rw [htDsq]
        field_simp [hmTne]
        ring
      have heq1 : -(tD ^ 2 * ((m:ℝ) * (T:ℝ))) / 2 = -((tD ^ 2 * ((m:ℝ) * (T:ℝ))) / 2) := by ring
      rw [heq1, h]
    have hchild' : ∀ i : Fin n, μg {s : Ωg | tD ≤ |lambdaHat hnm OmF (G s) i - lambdaCirc hnm μG OmF i|} ≤ ENNReal.ofReal (2 * Real.exp (-(8 * (D + 3) * Real.log (n:ℝ)))) := by
      intro i
      have h := hchild i
      rw [hexp] at h
      exact h
    have hbound : (n:ℝ) * (2 * Real.exp (-(8 * (D + 3) * Real.log (n:ℝ)))) ≤ 2 * Real.rpow (n:ℝ) (-D) := by
      show (n:ℝ) * (2 * Real.exp (-(8 * (D + 3) * Real.log (n:ℝ)))) ≤ 2 * (n:ℝ) ^ (-D)
      have hexp_eq : Real.exp (-(8 * (D + 3) * Real.log (n:ℝ))) = (n:ℝ) ^ (-(8 * (D + 3))) := by
        rw [Real.rpow_def_of_pos hnpos]
        congr 1
        ring
      rw [hexp_eq]
      have heq2 : (n:ℝ) * (2 * (n:ℝ) ^ (-(8 * (D + 3)))) = 2 * ((n:ℝ) * (n:ℝ) ^ (-(8 * (D + 3)))) := by ring
      rw [heq2]
      have hn_rpow : (n:ℝ) * (n:ℝ) ^ (-(8 * (D + 3))) = (n:ℝ) ^ (1 + -(8 * (D + 3))) := by
        rw [Real.rpow_add hnpos, Real.rpow_one]
      rw [hn_rpow]
      have hexp_le : 1 + -(8 * (D + 3)) ≤ -D := by linarith
      have hr : (n:ℝ) ^ (1 + -(8 * (D + 3))) ≤ (n:ℝ) ^ (-D) := Real.rpow_le_rpow_of_exponent_le hn1 hexp_le
      linarith [hr]
    let good : Set Ωg := {s : Ωg | ∀ i : Fin n, |lambdaHat hnm OmF (G s) i - lambdaCirc hnm μG OmF i| ≤ tD}
    let bad : Set Ωg := {s : Ωg | ∃ i : Fin n, tD < |lambdaHat hnm OmF (G s) i - lambdaCirc hnm μG OmF i|}
    have hgb : good = badᶜ := by
      show {s : Ωg | ∀ i : Fin n, |lambdaHat hnm OmF (G s) i - lambdaCirc hnm μG OmF i| ≤ tD} = {s : Ωg | ∃ i : Fin n, tD < |lambdaHat hnm OmF (G s) i - lambdaCirc hnm μG OmF i|}ᶜ
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_exists, not_lt]
    have hbad_eq : bad = ⋃ i : Fin n, {s : Ωg | tD < |lambdaHat hnm OmF (G s) i - lambdaCirc hnm μG OmF i|} := by
      show {s : Ωg | ∃ i : Fin n, tD < |lambdaHat hnm OmF (G s) i - lambdaCirc hnm μG OmF i|} = ⋃ i : Fin n, {s : Ωg | tD < |lambdaHat hnm OmF (G s) i - lambdaCirc hnm μG OmF i|}
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    have hbad_le : μg bad ≤ ENNReal.ofReal (2 * Real.rpow (n:ℝ) (-D)) := by
      rw [hbad_eq]
      calc μg (⋃ i : Fin n, {s : Ωg | tD < |lambdaHat hnm OmF (G s) i - lambdaCirc hnm μG OmF i|})
          ≤ ∑' i : Fin n, μg {s : Ωg | tD < |lambdaHat hnm OmF (G s) i - lambdaCirc hnm μG OmF i|} := measure_iUnion_le _
        _ = ∑ i : Fin n, μg {s : Ωg | tD < |lambdaHat hnm OmF (G s) i - lambdaCirc hnm μG OmF i|} := by rw [tsum_fintype]
        _ ≤ ∑ i : Fin n, μg {s : Ωg | tD ≤ |lambdaHat hnm OmF (G s) i - lambdaCirc hnm μG OmF i|} := by
              apply Finset.sum_le_sum
              intro i _
              apply measure_mono
              intro x hx
              simp only [Set.mem_setOf_eq] at hx ⊢
              exact le_of_lt hx
        _ ≤ ∑ i : Fin n, ENNReal.ofReal (2 * Real.exp (-(8 * (D + 3) * Real.log (n:ℝ)))) := by
              apply Finset.sum_le_sum
              intro i _
              exact hchild' i
        _ = ENNReal.ofReal ((n:ℝ) * (2 * Real.exp (-(8 * (D + 3) * Real.log (n:ℝ))))) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
        _ ≤ ENNReal.ofReal (2 * Real.rpow (n:ℝ) (-D)) := by
              apply ENNReal.ofReal_le_ofReal
              exact hbound
    have hOne : (1 : ENNReal) ≤ μg bad + μg good := by
      have hunion : μg Set.univ ≤ μg bad + μg good := by
        have h := measure_union_le (μ := μg) bad good
        rwa [show bad ∪ good = Set.univ from by rw [hgb]; simp] at h
      rwa [measure_univ] at hunion
    have htwo : (1:ENNReal) ≤ μg good + ENNReal.ofReal (2 * Real.rpow (n:ℝ) (-D)) := by
      calc (1:ENNReal) ≤ μg bad + μg good := hOne
        _ ≤ ENNReal.ofReal (2 * Real.rpow (n:ℝ) (-D)) + μg good := add_le_add hbad_le (le_refl (μg good))
        _ = μg good + ENNReal.ofReal (2 * Real.rpow (n:ℝ) (-D)) := add_comm _ _
    have hthree : (1:ENNReal) - ENNReal.ofReal (2 * Real.rpow (n:ℝ) (-D)) ≤ μg good := tsub_le_iff_right.mpr htwo
    have hb_nonneg : (0:ℝ) ≤ 2 * Real.rpow (n:ℝ) (-D) := mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg n) (-D))
    have hofsub : ENNReal.ofReal (1 - 2 * Real.rpow (n:ℝ) (-D)) = (1:ENNReal) - ENNReal.ofReal (2 * Real.rpow (n:ℝ) (-D)) := by
      rw [ENNReal.ofReal_sub (1:ℝ) hb_nonneg, ENNReal.ofReal_one]
    rw [hofsub]
    exact hthree
  /- @proof-region region.target-node.session.122b9241730e1504 end -/

end Statlib.Imported

end

#print axioms Statlib.Imported.statopia_math_node_1891546014_cda991f2


