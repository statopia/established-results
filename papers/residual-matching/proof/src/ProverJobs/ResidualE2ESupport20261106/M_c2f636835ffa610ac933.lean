import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.SoftThresholdDenoisingHelpers
import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Lean
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_ca782bc74b0775d6b6b6
import ProverJobs.ResidualE2ESupport20261106.M_c5aeedf2f1c047528231

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
theorem statopia_math_node_1703810688_a15f7ece : ∀ (m n : ℕ) (hnm : n ≤ m)
    {Ω : Type*} [MeasurableSpace Ω]
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hA : ∀ i : Fin m, ∀ j : Fin n, Measurable (fun ω => A ω i j))
    (i : Fin n),
    Measurable (fun ω => sv hnm (A ω) i) := by
  /- @proof-region region.target-node.session.66e98542776316f0 begin -/
  intro m n hnm OmS _ A hA i
  have hkey : ∀ X Y : Matrix (Fin m) (Fin n) ℝ,
      |sv hnm X i - sv hnm Y i| ≤
        Statlib.HighDim.MatrixAnalysis.opNorm (X - Y) +
          Statlib.HighDim.MatrixAnalysis.opNorm (Y - X) := by
    intro X Y
    have hYX : Y + (X - Y) = X := by abel
    have hXY : X + (Y - X) = Y := by abel
    have h1 : sv hnm X i ≤
        sv hnm Y i + Statlib.HighDim.MatrixAnalysis.opNorm (X - Y) := by
      have h := Statlib.HighDim.MatrixAnalysis.rectangular_singularValues_weyl_upper Y
        (X - Y) (Fin.castLE (le_min hnm le_rfl) i)
      rw [hYX] at h
      exact h
    have h2 : sv hnm Y i ≤
        sv hnm X i + Statlib.HighDim.MatrixAnalysis.opNorm (Y - X) := by
      have h := Statlib.HighDim.MatrixAnalysis.rectangular_singularValues_weyl_upper X
        (Y - X) (Fin.castLE (le_min hnm le_rfl) i)
      rw [hXY] at h
      exact h
    have hnn : 0 ≤ Statlib.HighDim.MatrixAnalysis.opNorm (Y - X) :=
      Statlib.HighDim.MatrixAnalysis.opNorm_nonneg (Y - X)
    have hnn2 : 0 ≤ Statlib.HighDim.MatrixAnalysis.opNorm (X - Y) :=
      Statlib.HighDim.MatrixAnalysis.opNorm_nonneg (X - Y)
    rw [abs_sub_le_iff]
    constructor <;> linarith
  have hbound : ∀ E : Matrix (Fin m) (Fin n) ℝ,
      Statlib.HighDim.MatrixAnalysis.opNorm E ≤
        Real.sqrt (∑ a, ∑ b, (E a b) ^ 2) := by
    intro E
    simp only [Statlib.HighDim.MatrixAnalysis.opNorm]
    refine ContinuousLinearMap.opNorm_le_of_unit_norm (Real.sqrt_nonneg _) ?_
    intro x hx
    change ‖(Matrix.toEuclideanLin E) x‖ ≤ Real.sqrt (∑ a, ∑ b, (E a b) ^ 2)
    have hx1 : (Matrix.toEuclideanLin E) x = WithLp.toLp 2 (E.mulVec x.ofLp) := by
      simpa using Matrix.toEuclideanLin_apply_piLp_toLp E x.ofLp
    have hx2 : ‖(Matrix.toEuclideanLin E) x‖ ^ 2 =
        ∑ a, ((E.mulVec x.ofLp) a) ^ 2 := by
      rw [hx1, EuclideanSpace.norm_sq_eq]
      simp
    have hrow : ∀ a : Fin m, ((E.mulVec x.ofLp) a) ^ 2 ≤
        (∑ b, (E a b) ^ 2) * (∑ b, (x.ofLp b) ^ 2) := by
      intro a
      have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
        (fun b => E a b) (fun b => x.ofLp b)
      have hmv : (E.mulVec x.ofLp) a = ∑ b, E a b * x.ofLp b := rfl
      rw [hmv]
      simpa using h
    have hsum : ∑ a, ((E.mulVec x.ofLp) a) ^ 2 ≤
        (∑ a, ∑ b, (E a b) ^ 2) * (∑ b, (x.ofLp b) ^ 2) := by
      calc ∑ a, ((E.mulVec x.ofLp) a) ^ 2
          ≤ ∑ a, (∑ b, (E a b) ^ 2) * (∑ b, (x.ofLp b) ^ 2) :=
            Finset.sum_le_sum fun a _ => hrow a
        _ = (∑ a, ∑ b, (E a b) ^ 2) * (∑ b, (x.ofLp b) ^ 2) := by
            rw [Finset.sum_mul]
    have hxn : ∑ b, (x.ofLp b) ^ 2 = 1 := by
      have h := EuclideanSpace.norm_sq_eq x
      simp only [Real.norm_eq_abs, sq_abs] at h
      rw [← h, hx]
      norm_num
    have hmain : ‖(Matrix.toEuclideanLin E) x‖ ^ 2 ≤ ∑ a, ∑ b, (E a b) ^ 2 := by
      rw [hx2]
      calc ∑ a, ((E.mulVec x.ofLp) a) ^ 2
          ≤ (∑ a, ∑ b, (E a b) ^ 2) * (∑ b, (x.ofLp b) ^ 2) := hsum
        _ = ∑ a, ∑ b, (E a b) ^ 2 := by rw [hxn, mul_one]
    calc ‖(Matrix.toEuclideanLin E) x‖
        = Real.sqrt (‖(Matrix.toEuclideanLin E) x‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (∑ a, ∑ b, (E a b) ^ 2) := Real.sqrt_le_sqrt hmain
  have hcont : Continuous fun X : Matrix (Fin m) (Fin n) ℝ => sv hnm X i := by
    have hneg : ∀ E : Matrix (Fin m) (Fin n) ℝ,
        Statlib.HighDim.MatrixAnalysis.opNorm (-E) =
          Statlib.HighDim.MatrixAnalysis.opNorm E := by
      intro E
      simp only [Statlib.HighDim.MatrixAnalysis.opNorm, map_neg, norm_neg]
    have hsqcont : ∀ Y : Matrix (Fin m) (Fin n) ℝ,
        Continuous fun X : Matrix (Fin m) (Fin n) ℝ =>
          ∑ a, ∑ b, (X a b - Y a b) ^ 2 := by
      intro Y
      refine continuous_finset_sum _ fun a _ => ?_
      refine continuous_finset_sum _ fun b _ => ?_
      have hproj : Continuous fun X : Matrix (Fin m) (Fin n) ℝ => X a b :=
        continuous_apply_apply a b
      exact (hproj.sub continuous_const).pow 2
    rw [continuous_iff_continuousAt]
    intro Y
    refine Metric.tendsto_nhds.mpr ?_
    intro ε hε
    have hopen : IsOpen {X : Matrix (Fin m) (Fin n) ℝ |
        ∑ a, ∑ b, (X a b - Y a b) ^ 2 < (ε / 4) ^ 2} :=
      isOpen_Iio.preimage (hsqcont Y)
    have hY : Y ∈ {X : Matrix (Fin m) (Fin n) ℝ |
        ∑ a, ∑ b, (X a b - Y a b) ^ 2 < (ε / 4) ^ 2} := by
      have hpos : (0 : ℝ) < (ε / 4) ^ 2 := pow_pos (by linarith) 2
      simpa using hpos
    filter_upwards [hopen.mem_nhds hY] with X hX
    rw [Real.dist_eq]
    have hop : Statlib.HighDim.MatrixAnalysis.opNorm (Y - X) =
        Statlib.HighDim.MatrixAnalysis.opNorm (X - Y) := by
      rw [← neg_sub X Y]
      exact hneg (X - Y)
    have hsub : ∀ (a : Fin m) (b : Fin n), (X - Y) a b = X a b - Y a b :=
      fun a b => rfl
    have hbX : Statlib.HighDim.MatrixAnalysis.opNorm (X - Y) ≤
        Real.sqrt (∑ a, ∑ b, (X a b - Y a b) ^ 2) := by
      simpa only [hsub] using hbound (X - Y)
    have hbY : Statlib.HighDim.MatrixAnalysis.opNorm (Y - X) ≤
        Real.sqrt (∑ a, ∑ b, (X a b - Y a b) ^ 2) := by
      rw [hop]
      exact hbX
    have hsqrt : Real.sqrt (∑ a, ∑ b, (X a b - Y a b) ^ 2) ≤ ε / 4 := by
      calc Real.sqrt (∑ a, ∑ b, (X a b - Y a b) ^ 2)
          ≤ Real.sqrt ((ε / 4) ^ 2) := Real.sqrt_le_sqrt (le_of_lt hX)
        _ = ε / 4 := Real.sqrt_sq (by linarith)
    calc |sv hnm X i - sv hnm Y i|
        ≤ Statlib.HighDim.MatrixAnalysis.opNorm (X - Y) +
            Statlib.HighDim.MatrixAnalysis.opNorm (Y - X) := hkey X Y
      _ ≤ Real.sqrt (∑ a, ∑ b, (X a b - Y a b) ^ 2) +
            Real.sqrt (∑ a, ∑ b, (X a b - Y a b) ^ 2) := by linarith [hbX, hbY]
      _ = 2 * Real.sqrt (∑ a, ∑ b, (X a b - Y a b) ^ 2) := by rw [two_mul]
      _ < ε := by linarith
  have hmeas : Measurable fun ω => A ω :=
    measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr (hA j)
  exact hcont.measurable.comp hmeas
  /- @proof-region region.target-node.session.66e98542776316f0 end -/

end Statlib.Imported

end

#print axioms Statlib.Imported.statopia_math_node_1703810688_a15f7ece


