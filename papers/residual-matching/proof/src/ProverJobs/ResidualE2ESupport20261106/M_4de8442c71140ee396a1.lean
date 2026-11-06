import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_655541399eba6e711ce1
import ProverJobs.ResidualE2ESupport20261106.M_bcfb3463e23dcbde575f
import ProverJobs.ResidualE2ESupport20261106.M_2612e4165e00836a6f19
import ProverJobs.ResidualE2ESupport20261106.M_1826cf4a199ca47d64c5

namespace PaperProofTasks.ResidualE2ESupport20261106
open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_2003834469_81c5daa0 : ∀ (D0 : ℝ) (hD0 : 0 < D0)
    (rhoMinus : ℝ) (hrhoMinus_pos : 0 < rhoMinus) (hrhoMinus_le : rhoMinus ≤ 1)
    (Kt : ℝ) (hKt : 0 < Kt)
    (alpha0 : ℝ) (halpha0 : 15 < alpha0)
    (CD : ℝ) (hCD : max (Kt * (D0 + 12)) (D0 + 20) ≤ CD),
    ∃ M1 : ℕ,
      ∀ (m n : ℕ) (hm : 2 ≤ m) (hn : 1 ≤ n) (hnm : n ≤ m) (hM1 : M1 ≤ m)
        (hrho_lo : rhoMinus ≤ (n : ℝ) / (m : ℝ))
        (hrho_hi : (n : ℝ) / (m : ℝ) ≤ 1)
        (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
        (hsparse : Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p),
      ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (XT Mask : Ω → Matrix (Fin m) (Fin n) ℝ),
        (∀ (i : Fin m) (j : Fin n), Measurable fun ω => XT ω i j) →
        (∀ (i : Fin m) (j : Fin n), Integrable (fun ω => XT ω i j) μ) →
        (∀ (i : Fin m) (j : Fin n), Integrable (fun ω => (XT ω i j) ^ 2) μ) →
        (∀ (i : Fin m) (j : Fin n), Measurable fun ω => Mask ω i j) →
        (∀ (i : Fin m) (j : Fin n) (ω : Ω), Mask ω i j = 0 ∨ Mask ω i j = 1) →
        (∀ (i : Fin m) (j : Fin n), μ {ω | Mask ω i j = 1} = ENNReal.ofReal p) →
        iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => XT ω ij.1 ij.2) μ →
        iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Mask ω ij.1 ij.2) μ →
        IndepFun (fun ω (ij : Fin m × Fin n) => XT ω ij.1 ij.2)
          (fun ω (ij : Fin m × Fin n) => Mask ω ij.1 ij.2) μ →
        (∀ (i : Fin m) (j : Fin n), ∫ ω, XT ω i j ∂μ = 0) →
        (∀ (i : Fin m) (j : Fin n), ∫ ω, (XT ω i j) ^ 2 ∂μ = 1) →
        (let L : ℝ := CD * Real.log ((m : ℝ) * (n : ℝ)) +
            10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4;
          ∀ (ω : Ω) (i : Fin m) (j : Fin n), |XT ω i j| ≤ 3 * L) →
        μ {ω | 1 + Real.sqrt ((n : ℝ) / (m : ℝ)) + 1 * deltaM m <
              svals (maskedScaled p (XT ω) (Mask ω)) ⟨0, by omega⟩} +
          μ {ω | svals (maskedScaled p (XT ω) (Mask ω)) ⟨n - 1, by omega⟩ <
              1 - Real.sqrt ((n : ℝ) / (m : ℝ)) - 1 * deltaM m} ≤
        ENNReal.ofReal (Real.rpow (n : ℝ) (-(D0 + 4))) := by
  /- @proof-region region.target-node.session.a2da7b662417055c begin -/
  intro D0 hD0 rhoMinus hrhoMinus_pos hrhoMinus_le Kt hKt alpha0 halpha0 CD hCD
  obtain ⟨M1top, htop_thm⟩ :=
    statopia_math_node_3249198672_935a9270 D0 hD0 rhoMinus hrhoMinus_pos hrhoMinus_le
      Kt hKt alpha0 halpha0 CD hCD
  obtain ⟨M1low, hbot_thm⟩ :=
    statopia_math_node_1642389212_296f47d2 D0 hD0 rhoMinus hrhoMinus_pos hrhoMinus_le
      Kt hKt alpha0 halpha0 CD hCD
  refine ⟨max M1top M1low, ?_⟩
  intro m n hm hn hnm hM1 hrho_lo hrho_hi p hp0 hp1 hsparse
  intro Ω hΩ μ hμ XT Mask hXTmeas hXTint hXTint2 hMaskmeas hMask01 hMaskprob
    hXTindep hMaskindep hIndep hXTmean hXT2 hL
  have hM1top : M1top ≤ m := le_trans (le_max_left _ _) hM1
  have hM1low : M1low ≤ m := le_trans (le_max_right _ _) hM1
  have htop :
      μ {ω | 1 + Real.sqrt ((n : ℝ) / (m : ℝ)) + 1 * deltaM m <
            svals (maskedScaled p (XT ω) (Mask ω)) ⟨0, by omega⟩}
        ≤ ENNReal.ofReal (Real.rpow (n : ℝ) (-(D0 + 4)) / 2) :=
    htop_thm m n hm hn hnm hM1top hrho_lo hrho_hi p hp0 hp1 hsparse μ XT Mask
      (CD * Real.log ((m : ℝ) * (n : ℝ)) +
        (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) rfl
      hXTmeas hXTint hXTint2 hMaskmeas hMask01 hMaskprob hXTindep hMaskindep hIndep
      hXTmean hXT2 hL
  have hbot :
      μ {ω | svals (maskedScaled p (XT ω) (Mask ω)) ⟨n - 1, by omega⟩ <
            1 - Real.sqrt ((n : ℝ) / (m : ℝ)) - 1 * deltaM m}
        ≤ ENNReal.ofReal (Real.rpow (n : ℝ) (-(D0 + 4)) / 2) :=
    hbot_thm m n hm hn hnm hM1low hrho_lo hrho_hi p hp0 hp1 hsparse μ XT Mask
      hXTmeas hXTint hXTint2 hXTindep hXTmean hXT2 hMaskmeas hMask01 hMaskprob
      hMaskindep hIndep hL
  refine le_trans (add_le_add htop hbot) ?_
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hr : (0 : ℝ) ≤ Real.rpow (n : ℝ) (-(D0 + 4)) :=
    Real.rpow_nonneg (le_of_lt hnpos) _
  have hhalves_nn : (0 : ℝ) ≤ Real.rpow (n : ℝ) (-(D0 + 4)) / 2 := div_nonneg hr (by norm_num)
  have hadd : Real.rpow (n : ℝ) (-(D0 + 4)) / 2 + Real.rpow (n : ℝ) (-(D0 + 4)) / 2
      = Real.rpow (n : ℝ) (-(D0 + 4)) := by ring
  exact le_of_eq (by rw [← ENNReal.ofReal_add hhalves_nn hhalves_nn, hadd])

  /- @proof-region region.target-node.session.a2da7b662417055c end -/

#print axioms statopia_math_node_2003834469_81c5daa0
end Statlib.Imported

