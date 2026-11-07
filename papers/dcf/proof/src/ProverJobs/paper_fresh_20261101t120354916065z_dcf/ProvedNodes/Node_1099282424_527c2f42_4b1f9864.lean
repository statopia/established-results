import Statlib.HighDim.MatrixCompletion.FiniteCoordinateTailUnion
import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
import Statlib.StatFoundation.RandomVariable.SubExponential.subexp_mgf_le_of_sq_subgaussian
import Statlib.StatFoundation.RandomVariable.SubGaussian.subgaussian_mgf_mono_param
import Lean
import ProverJobs.paper_fresh_20261101t120354916065z_dcf.Vocabulary
import ProverJobs.paper_fresh_20261101t120354916065z_dcf.Base

namespace PaperProofTasks.paper_fresh_20261101t120354916065z_dcf

open MeasureTheory ProbabilityTheory
open Statlib.StatFoundation.RandomVariable.Gaussian
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261101t120354916065z_dcf.Statlib.Imported

open MeasureTheory ProbabilityTheory
open Statlib.StatFoundation.RandomVariable.Gaussian
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_1099282424_527c2f42 : ∀ (p : ℕ) (hp : 1 ≤ p) (C : ℝ) (hC : 0 < C)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Fin p → Ω → ℝ) (hZ : ∀ j, Measurable (Z j))
    (sigma : Fin p → ℝ) (hsigma_nonneg : ∀ j, 0 ≤ sigma j)
    (hsigma_le : ∀ j, sigma j ≤ C)
    (hlaw : ∀ j, Measure.map (Z j) P = gaussianReal 0 ⟨sigma j, hsigma_nonneg j⟩),
    Measurable (fun ω => ⨆ j : Fin p, |Z j ω|) ∧
      (∀ ω, 0 ≤ (⨆ j : Fin p, |Z j ω|)) ∧
        ∀ s : ℝ, 0 ≤ s →
          P {ω : Ω | s < ⨆ j : Fin p, |Z j ω|} ≤
            ENNReal.ofReal (2 * (p : ℝ) * Real.exp (-(s ^ 2) / (2 * C))) := by
  /- @proof-region region.target-node.session.1d0d7e513091066d begin -/
  intro p hp C hC Ω _hΩ P _hP Z hZ sigma hsigma_nonneg hsigma_le hlaw
  haveI hne : Nonempty (Fin p) := ⟨⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hp⟩⟩
  have hCnn : (0 : ℝ) ≤ C := le_of_lt hC
  have hp_nonneg : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have habs : ∀ j : Fin p, Measurable (fun ω => |Z j ω|) := fun j =>
    continuous_abs.measurable.comp (hZ j)
  have hsup_meas : Measurable (fun ω => ⨆ j : Fin p, |Z j ω|) :=
    Measurable.iSup (f := fun j : Fin p => fun ω => |Z j ω|) habs
  refine ⟨hsup_meas, ?_, ?_⟩
  · intro ω
    exact Real.iSup_nonneg (fun j => abs_nonneg (Z j ω))
  · intro s hs
    have hper : ∀ i : Fin p, P {ω : Ω | s ≤ |Z i ω|} ≤
        ENNReal.ofReal (2 * Real.exp (-(s ^ 2) / (2 * C))) := by
      intro i
      have hsb : HasSubgaussianMGF (Z i) ⟨C, hCnn⟩ P :=
        Statlib.StatFoundation.RandomVariable.SubGaussian.subgaussian_mgf_mono_param
          (Z := Z i) (c := ⟨sigma i, hsigma_nonneg i⟩) (C := ⟨C, hCnn⟩) (μ := P)
          (hsigma_le i) (by
            have hgauss : HasSubgaussianMGF (fun x : ℝ => x) ⟨sigma i, hsigma_nonneg i⟩
                (gaussianReal 0 ⟨sigma i, hsigma_nonneg i⟩) := by
              constructor
              · intro t
                exact ProbabilityTheory.integrable_exp_mul_gaussianReal t
              · intro t
                rw [ProbabilityTheory.mgf_fun_id_gaussianReal]
                simp
            exact ProbabilityTheory.HasSubgaussianMGF.of_map (X := fun x : ℝ => x) (Y := Z i)
              (hZ i).aemeasurable (by rw [hlaw i]; exact hgauss))
      have htail :=
        Statlib.StatFoundation.RandomVariable.SubExponential.sub_gauss_tail_abs
          (μ := P) (X := Z i) (c := ⟨C, hCnn⟩) (ε := s) hsb hs
      have hconv : P {ω : Ω | s ≤ |Z i ω|} =
          ENNReal.ofReal (P.real {ω : Ω | s ≤ |Z i ω|}) := by
        rw [show P.real {ω : Ω | s ≤ |Z i ω|} = (P {ω : Ω | s ≤ |Z i ω|}).toReal from rfl,
          ENNReal.ofReal_toReal (measure_ne_top P _)]
      rw [hconv]
      exact ENNReal.ofReal_le_ofReal htail
    have hunion :=
      Statlib.HighDim.MatrixCompletion.finite_coordinate_tail_union (I := Fin p) P Z s
        (2 * Real.exp (-(s ^ 2) / (2 * C))) hper
    have hsub : {ω : Ω | s < ⨆ j : Fin p, |Z j ω|} ⊆ {ω : Ω | ∃ i : Fin p, s ≤ |Z i ω|} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      by_contra h
      push_neg at h
      exact absurd hω (not_lt.mpr (ciSup_le (fun i => le_of_lt (h i))))
    calc P {ω : Ω | s < ⨆ j : Fin p, |Z j ω|}
        ≤ P {ω : Ω | ∃ i : Fin p, s ≤ |Z i ω|} := measure_mono hsub
      _ ≤ Fintype.card (Fin p) • ENNReal.ofReal (2 * Real.exp (-(s ^ 2) / (2 * C))) := hunion
      _ = ENNReal.ofReal (2 * (p : ℝ) * Real.exp (-(s ^ 2) / (2 * C))) := by
            have hcast : (p : ENNReal) = ENNReal.ofReal (p : ℝ) := by simp
            rw [Fintype.card_fin, nsmul_eq_mul, hcast, ← ENNReal.ofReal_mul hp_nonneg]
            congr 1
            ring
  /- @proof-region region.target-node.session.1d0d7e513091066d end -/

end Statlib.Imported

