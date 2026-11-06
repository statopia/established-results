import Lean
import ProverJobs.ResidualE2ESupport20261106.ExternalNodes.Node_3965994620e137a49900
import ProverJobs.ResidualE2ESupport20261106.M_dd508d27ad365f443d21

namespace PaperProofTasks.ResidualE2ESupport20261106
open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
set_option autoImplicit false in
theorem statopia_math_node_1024439655_0419b336 : ∀ (D0 : ℝ) (hD0 : 0 < D0)
    (rhoMinus : ℝ) (hrhoMinus_pos : 0 < rhoMinus) (hrhoMinus_le : rhoMinus ≤ 1)
    (Kt : ℝ) (hKt : 0 < Kt)
    (alpha0 : ℝ) (halpha0 : 15 < alpha0)
    (CD : ℝ) (hCD : max (Kt * (D0 + 12)) (D0 + 20) ≤ CD)
    (D : ℝ) (hD : 0 < D),
    ∃ M1 : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (hnm : n ≤ m) (hM1 : M1 ≤ m)
        (hrho_lo : rhoMinus ≤ (n : ℝ) / (m : ℝ))
        (hrho_hi : (n : ℝ) / (m : ℝ) ≤ 1)
        {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (A : Ω → Matrix (Fin m) (Fin n) ℝ)
        (hA_meas : ∀ (i : Fin m) (j : Fin n), Measurable (fun ω => A ω i j))
        (hA_int : ∀ (i : Fin m) (j : Fin n),
          Integrable (fun ω => A ω i j) μ ∧ Integrable (fun ω => (A ω i j) ^ 2) μ)
        (hA_indep : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => A ω ij.1 ij.2) μ)
        (hA_mean : ∀ (i : Fin m) (j : Fin n), ∫ (ω : Ω), A ω i j ∂μ = 0)
        (hA_var : ∀ (i : Fin m) (j : Fin n), ∫ (ω : Ω), (A ω i j) ^ 2 ∂μ = 1 / (m : ℝ))
        (hA_bound : ∀ (ω : Ω) (i : Fin m) (j : Fin n),
          |A ω i j| ≤ 3 * (2 * CD + 10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4)
            * Real.rpow (Real.log (m : ℝ)) (1 - alpha0 / 2)),
        μ {ω : Ω | svals (A ω) ⟨n - 1, by omega⟩ <
              1 - Real.sqrt ((n : ℝ) / (m : ℝ)) - 1 * deltaM m} ≤
          ENNReal.ofReal (c * Real.rpow (n : ℝ) (-D)) := by
  intro D0 hD0 rhoMinus hrhoMinus_pos hrhoMinus_le Kt hKt alpha0 halpha0 CD hCD D hD
  obtain ⟨Cbv, hCbv, hbvh⟩ := ResidualSparseRepair20261106.bvh_lower_edge
  obtain ⟨M1, hdef, hrate⟩ :=
    statopia_math_node_1258620162_ba622d86 Cbv CD Kt D0 alpha0 D
      hCbv hD0 hKt halpha0 hD
  refine ⟨M1, 10 ^ 6, by norm_num, ?_⟩
  intro m n hm hn hnm hM1 hrho_lo hrho_hi Ω hmΩ μ hμ A hmeas hint hindep hzero hsecond hamp
  let R : ℝ := 3 * (2 * CD + 10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4)
    * Real.rpow (Real.log (m : ℝ)) (1 - alpha0 / 2)
  let tau : ℝ := max 1 ((D + 2) * Real.log (m : ℝ))
  have hCD0 : 0 ≤ CD := by
    have h := le_trans (le_max_right (Kt * (D0 + 12)) (D0 + 20)) hCD
    linarith
  have hR : 0 ≤ R := by
    dsimp only [R]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (add_nonneg (mul_nonneg (by norm_num) hCD0) (by positivity)))
      (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))) _)
  have hbound : ∀ᵐ ω ∂μ, ∀ i j, |A ω i j| ≤ R :=
    Filter.Eventually.of_forall (fun ω i j => hamp ω i j)
  have htail := hbvh m n hm (by omega) hnm μ A hmeas hint hindep hzero hsecond R hR
    hbound tau (le_trans zero_le_one (le_max_left _ _))
  have he := hdef m hM1
  change 3 * Cbv *
      (Real.rpow (m : ℝ) (-(1 / 4)) * Real.rpow (Real.log (m : ℝ)) (3 / 4)
        + Real.rpow (m : ℝ) (-(1 / 2)) * Real.sqrt tau
        + Real.rpow R (1 / 3) * Real.rpow tau (2 / 3) + R * tau)
    ≤ 1 * deltaM m at he
  exact le_trans (MeasureTheory.measure_mono (fun ω hω =>
      lt_of_lt_of_le hω (sub_le_sub_left he (1 - Real.sqrt ((n : ℝ) / (m : ℝ))))))
    (le_trans htail (ENNReal.ofReal_le_ofReal (hrate m n hM1 hn hnm)))

#print axioms statopia_math_node_1024439655_0419b336
end Statlib.Imported

