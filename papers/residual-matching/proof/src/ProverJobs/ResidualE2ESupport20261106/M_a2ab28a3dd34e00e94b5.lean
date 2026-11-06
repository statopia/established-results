import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_4d45e28b5bdc9d435f78
import ProverJobs.ResidualE2ESupport20261106.M_b6ae51ab65a12eb9f42d
import ProverJobs.ResidualE2ESupport20261106.M_c718d57024d01dc0fdcc

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
theorem statopia_math_node_3027071526_9b78d881 : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (hN : 1 ≤ N)
    (X Y : Ω → Fin N → ℝ)
    (hX_meas : ∀ k : Fin N, Measurable fun ω => X ω k)
    (hY_meas : ∀ k : Fin N, Measurable fun ω => Y ω k)
    (hX_sq : ∀ k : Fin N, Integrable (fun ω => (X ω k) ^ 2) μ)
    (hY_sq : ∀ k : Fin N, Integrable (fun ω => (Y ω k) ^ 2) μ)
    (hX_gauss : ∀ a : Fin N → ℝ, ∃ v : NNReal,
      Measure.map (fun ω => ∑ k : Fin N, a k * X ω k) μ = gaussianReal 0 v)
    (hY_gauss : ∀ a : Fin N → ℝ, ∃ v : NNReal,
      Measure.map (fun ω => ∑ k : Fin N, a k * Y ω k) μ = gaussianReal 0 v)

    (hIndep : IndepFun X Y μ)
    (hincr : ∀ k l : Fin N,
      (∫ ω, X ω k * X ω k ∂μ) + (∫ ω, X ω l * X ω l ∂μ)
          - 2 * (∫ ω, X ω k * X ω l ∂μ)
        ≤ (∫ ω, Y ω k * Y ω k ∂μ) + (∫ ω, Y ω l * Y ω l ∂μ)
          - 2 * (∫ ω, Y ω k * Y ω l ∂μ)),
    ∫ ω, (⨆ k : Fin N, X ω k) ∂μ ≤ ∫ ω, (⨆ k : Fin N, Y ω k) ∂μ := by
  /- @proof-region region.target-node.session.b1439ae2b044255c begin -/
  classical
  intro Ω _ μ _ N hN X Y hX_meas hY_meas hX_sq hY_sq hX_gauss hY_gauss hIndep hincr
  refine statopia_math_node_466340105_bd7fbf52 μ N hN X Y hX_gauss hY_gauss ?_
  intro β hβ
  let φ : ℝ → ℝ := fun t : ℝ => ∫ ω, Statlib.StatFoundation.Convergence.smoothMax β
      (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) ∂μ
  obtain ⟨hcont, hdiff, hnonneg⟩ :=
    statopia_math_node_2689151497_94127261 μ N hN X Y hX_meas hY_meas hX_sq hY_sq
      hX_gauss hY_gauss hIndep hincr β hβ
  have hleft : ∀ b : ℝ, 0 < b → b < 1 → φ 0 ≤ φ b := by
    intro b hb0 hb1
    obtain ⟨c, hc, hcs⟩ := exists_deriv_eq_slope φ hb0
      (hcont.mono (Set.Icc_subset_Icc le_rfl hb1.le))
      (fun x hx => (hdiff x ⟨hx.1, lt_trans hx.2 hb1⟩).differentiableWithinAt)
    have hd : 0 ≤ deriv φ c := hnonneg c ⟨hc.1, lt_trans hc.2 hb1⟩
    rw [hcs] at hd
    have hbpos : (0 : ℝ) < b - 0 := by linarith
    have hle := (le_div_iff₀ hbpos).mp hd
    linarith
  have hright : ∀ b : ℝ, 0 < b → b < 1 → φ b ≤ φ 1 := by
    intro b hb0 hb1
    obtain ⟨c, hc, hcs⟩ := exists_deriv_eq_slope φ hb1
      (hcont.mono (Set.Icc_subset_Icc hb0.le le_rfl))
      (fun x hx => (hdiff x ⟨lt_trans hb0 hx.1, hx.2⟩).differentiableWithinAt)
    have hd : 0 ≤ deriv φ c := hnonneg c ⟨lt_trans hb0 hc.1, hc.2⟩
    rw [hcs] at hd
    have hbpos : (0 : ℝ) < 1 - b := by linarith
    have hle := (le_div_iff₀ hbpos).mp hd
    linarith
  have hφ0 : φ 0 = ∫ ω, Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (X ω)) ∂μ := by
    dsimp only [φ]
    simp
  have hφ1 : φ 1 = ∫ ω, Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (Y ω)) ∂μ := by
    dsimp only [φ]
    simp
  rw [← hφ0, ← hφ1]
  exact le_trans (hleft (1 / 2) (by norm_num) (by norm_num))
    (hright (1 / 2) (by norm_num) (by norm_num))
  /- @proof-region region.target-node.session.b1439ae2b044255c end -/

end Statlib.Imported

