import Lean
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.Vocabulary
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.Base

namespace PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315

open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported

noncomputable section
universe u
open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_2670649085_3064904c : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (hZ : Measurable Z) (hZint : Integrable Z μ)
    (c : ℝ) (hZdev : Integrable (fun ω => |Z ω - c| ^ 3) μ),
    MemLp Z 2 μ ∧
      (∀ {ι : Type} (W : ι → Ω → ℝ), (∀ i, Measurable (W i)) →
        (∀ i, Integrable (W i) μ) → ∀ d : ι → ℝ,
        (∀ i, Integrable (fun ω => |W i ω - d i| ^ 3) μ) → ∀ i, MemLp (W i) 2 μ) ∧
      (∀ (n m p : ℕ) (μX μY : Fin p → ℝ)
        (X : Fin n → Ω → (Fin p → ℝ)) (Y : Fin m → Ω → (Fin p → ℝ))
        (F : Fin n → Ω → (Fin p → ℝ)) (G : Fin m → Ω → (Fin p → ℝ)),
        (∀ i j, Measurable (fun ω => X i ω j)) →
        (∀ i j, Measurable (fun ω => Y i ω j)) →
        (∀ i j, Measurable (fun ω => F i ω j)) →
        (∀ i j, Measurable (fun ω => G i ω j)) →
        (∀ i j, Integrable (fun ω => X i ω j) μ) →
        (∀ i j, Integrable (fun ω => Y i ω j) μ) →
        (∀ i j, Integrable (fun ω => F i ω j) μ) →
        (∀ i j, Integrable (fun ω => G i ω j) μ) →
        (∀ i j, Integrable (fun ω => |X i ω j - μX j| ^ 3) μ) →
        (∀ i j, Integrable (fun ω => |Y i ω j - μY j| ^ 3) μ) →
        (∀ i j, Integrable (fun ω => |F i ω j - μX j| ^ 3) μ) →
        (∀ i j, Integrable (fun ω => |G i ω j - μY j| ^ 3) μ) →
        (∀ i j, MemLp (fun ω => X i ω j) 2 μ) ∧
          (∀ i j, MemLp (fun ω => Y i ω j) 2 μ) ∧
          (∀ i j, MemLp (fun ω => F i ω j) 2 μ) ∧
          (∀ i j, MemLp (fun ω => G i ω j) 2 μ)) := by
  /- @proof-region region.target-node.session.d335132584e6de59 begin -/
  intro Ω _ μ _ Z hZ hZint c hZdev
  have key : ∀ (W : Ω → ℝ), Measurable W → Integrable W μ →
      ∀ d : ℝ, Integrable (fun ω => |W ω - d| ^ 3) μ → MemLp W 2 μ := by
    intro W hWm _hWint d hWdev
    refine (MeasureTheory.memLp_two_iff_integrable_sq hWm.aestronglyMeasurable).2 ?_
    have hbd : ∀ x : ℝ, x ^ 2 ≤ 2 * d ^ 2 + 2 + 2 * |x - d| ^ 3 := by
      intro x
      have h1 : |x| ≤ |x - d| + |d| := by
        simpa using abs_add_le (x - d) d
      have hx2 : |x| ^ 2 = x ^ 2 := by
        rw [pow_two, pow_two, ← abs_mul, abs_of_nonneg (mul_self_nonneg x)]
      have hd : |d| ^ 2 = d ^ 2 := by
        rw [pow_two, pow_two, ← abs_mul, abs_of_nonneg (mul_self_nonneg d)]
      have h2 : |x| ^ 2 ≤ (|x - d| + |d|) ^ 2 := by
        nlinarith [h1, abs_nonneg x, abs_nonneg (x - d), abs_nonneg d]
      have h3 : (|x - d| + |d|) ^ 2 ≤ 2 * |x - d| ^ 2 + 2 * |d| ^ 2 := by
        nlinarith [sq_nonneg (|x - d| - |d|)]
      have h4 : |x - d| ^ 2 ≤ 1 + |x - d| ^ 3 := by
        have hs : (0 : ℝ) ≤ |x - d| := abs_nonneg _
        by_cases hle : (|x - d| ≤ 1)
        · have h2' : |x - d| ^ 2 ≤ 1 := by nlinarith [hs, hle]
          nlinarith [h2', hs]
        · have hlt : 1 < |x - d| := not_le.mp hle
          have h3' : |x - d| ^ 2 ≤ |x - d| ^ 3 := by nlinarith [hs, hlt]
          nlinarith [h3']
      nlinarith [h2, h3, h4, hx2, hd]
    have hsqm : MeasureTheory.AEStronglyMeasurable (fun ω => W ω ^ 2) μ := by
      simpa [pow_two] using (hWm.mul hWm).aestronglyMeasurable
    have hg : Integrable (fun ω => (2 * d ^ 2 + 2) + 2 * |W ω - d| ^ 3) μ :=
      (integrable_const (2 * d ^ 2 + 2)).add (hWdev.const_mul 2)
    refine hg.mono' hsqm ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (W ω))]
    exact hbd (W ω)
  refine ⟨key Z hZ hZint c hZdev, ?_, ?_⟩
  · intro ι W hWm hWi d hWd i
    exact key (W i) (hWm i) (hWi i) (d i) (hWd i)
  · intro n m p μX μY X Y F G hXm hYm hFm hGm hXi hYi hFi hGi hX3 hY3 hF3 hG3
    exact ⟨fun i j => key (fun ω => X i ω j) (hXm i j) (hXi i j) (μX j) (hX3 i j),
      fun i j => key (fun ω => Y i ω j) (hYm i j) (hYi i j) (μY j) (hY3 i j),
      fun i j => key (fun ω => F i ω j) (hFm i j) (hFi i j) (μX j) (hF3 i j),
      fun i j => key (fun ω => G i ω j) (hGm i j) (hGi i j) (μY j) (hG3 i j)⟩
  /- @proof-region region.target-node.session.d335132584e6de59 end -/

end Statlib.Imported

end

