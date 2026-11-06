import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053

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
theorem statopia_math_node_1895661039_5283179a : ∀ (m n : ℕ) (ν : Measure (Matrix (Fin m) (Fin n) ℝ)) [IsProbabilityMeasure ν]
    (i : Fin m) (j : Fin n) (L b c : ℝ)
    (hvar : ∫ x, (x i j) ^ 2 ∂ν = 1)
    (hb : b = ∫ x, x i j * (if |x i j| ≤ L then (1 : ℝ) else 0) ∂ν)
    (hc : c = Real.sqrt (∫ x, (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0) - b) ^ 2 ∂ν)),
    c ^ 2 ≤ 1 := by
  /- @proof-region region.target-node.session.b0d99818f951431a begin -/
  intro m n ν _ i j L b c hvar hb hc
  have hfint : Integrable (fun x : Matrix (Fin m) (Fin n) ℝ => (x i j) ^ 2) ν := by
    by_contra h
    rw [MeasureTheory.integral_undef h] at hvar
    exact zero_ne_one hvar
  set Y : Matrix (Fin m) (Fin n) ℝ → ℝ :=
    fun x => x i j * (if |x i j| ≤ L then (1 : ℝ) else 0) with hYdef
  have hYeq : ∀ x : Matrix (Fin m) (Fin n) ℝ, Y x = if |x i j| ≤ L then x i j else 0 := by
    intro x
    by_cases h : (|x i j| ≤ L)
    · simp [hYdef, h]
    · simp [hYdef, h]
  have hφ : Measurable (fun x : Matrix (Fin m) (Fin n) ℝ => x i j) :=
    (measurable_pi_apply j).comp (measurable_pi_apply i)
  have hseteq : {x : Matrix (Fin m) (Fin n) ℝ | |x i j| ≤ L}
      = (fun x : Matrix (Fin m) (Fin n) ℝ => x i j) ⁻¹' Set.Icc (-L) L := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Icc, abs_le]
  have hset : MeasurableSet {x : Matrix (Fin m) (Fin n) ℝ | |x i j| ≤ L} := by
    rw [hseteq]
    exact (isClosed_Icc.measurableSet).preimage hφ
  have hYasind : (fun x : Matrix (Fin m) (Fin n) ℝ =>
      x i j * (if |x i j| ≤ L then (1 : ℝ) else 0))
      = Set.indicator {x : Matrix (Fin m) (Fin n) ℝ | |x i j| ≤ L} (fun x => x i j) := by
    funext x
    rw [Set.indicator_apply]
    by_cases h : (|x i j| ≤ L)
    · simp [h]
    · simp [h]
  have hYmeas : Measurable Y := by
    rw [hYdef, hYasind]
    exact Measurable.indicator hφ hset
  have hY2meas : Measurable (fun x : Matrix (Fin m) (Fin n) ℝ => (Y x) ^ 2) := by
    have h : Measurable (fun x : Matrix (Fin m) (Fin n) ℝ => Y x * Y x) := hYmeas.mul hYmeas
    simpa [pow_two] using h
  have hYsqle : ∀ x : Matrix (Fin m) (Fin n) ℝ, (Y x) ^ 2 ≤ (x i j) ^ 2 := by
    intro x
    rw [hYeq x]
    split_ifs with h
    · exact le_rfl
    · nlinarith [sq_nonneg (x i j)]
  have hY2int : Integrable (fun x : Matrix (Fin m) (Fin n) ℝ => (Y x) ^ 2) ν :=
    MeasureTheory.Integrable.mono' hfint hY2meas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Y x))]
        exact hYsqle x)
  have hYint : Integrable Y ν := by
    have hmaj : Integrable (fun x : Matrix (Fin m) (Fin n) ℝ => (Y x) ^ 2 + 1) ν :=
      hY2int.add (integrable_const (1 : ℝ))
    refine MeasureTheory.Integrable.mono' hmaj hYmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [sq_nonneg (Y x - 1 / 2), sq_nonneg (Y x + 1 / 2)]
  have hcsq : c ^ 2 = ∫ x : Matrix (Fin m) (Fin n) ℝ, (Y x - b) ^ 2 ∂ν := by
    have hcongr : ∫ x : Matrix (Fin m) (Fin n) ℝ,
          (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0) - b) ^ 2 ∂ν
        = ∫ x : Matrix (Fin m) (Fin n) ℝ, (Y x - b) ^ 2 ∂ν := by
      have h : (fun x : Matrix (Fin m) (Fin n) ℝ =>
            (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0) - b) ^ 2)
          = fun x : Matrix (Fin m) (Fin n) ℝ => (Y x - b) ^ 2 := by
        funext x
        simp only [hYdef]
      rw [h]
    rw [hc, hcongr]
    exact Real.sq_sqrt (integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun x => sq_nonneg (Y x - b)))
  have hexp : ∫ x : Matrix (Fin m) (Fin n) ℝ, (Y x - b) ^ 2 ∂ν
      = ∫ x : Matrix (Fin m) (Fin n) ℝ, (Y x) ^ 2 ∂ν - b ^ 2 := by
    have h2bY : Integrable (fun x : Matrix (Fin m) (Fin n) ℝ => 2 * b * Y x) ν :=
      hYint.const_mul (2 * b)
    have hb2 : Integrable (fun _ : Matrix (Fin m) (Fin n) ℝ => b ^ 2) ν :=
      integrable_const (b ^ 2)
    have hkey : (fun x : Matrix (Fin m) (Fin n) ℝ => (Y x - b) ^ 2)
        = fun x : Matrix (Fin m) (Fin n) ℝ => (Y x) ^ 2 - 2 * b * Y x + b ^ 2 := by
      funext x
      ring
    have e2 : ∫ x : Matrix (Fin m) (Fin n) ℝ, ((Y x) ^ 2 - 2 * b * Y x + b ^ 2) ∂ν
        = (∫ x : Matrix (Fin m) (Fin n) ℝ, ((Y x) ^ 2 - 2 * b * Y x) ∂ν)
          + ∫ x : Matrix (Fin m) (Fin n) ℝ, b ^ 2 ∂ν :=
      integral_add (hY2int.sub h2bY) hb2
    have e3 : ∫ x : Matrix (Fin m) (Fin n) ℝ, ((Y x) ^ 2 - 2 * b * Y x) ∂ν
        = ∫ x : Matrix (Fin m) (Fin n) ℝ, (Y x) ^ 2 ∂ν
          - ∫ x : Matrix (Fin m) (Fin n) ℝ, 2 * b * Y x ∂ν :=
      integral_sub hY2int h2bY
    have e4 : ∫ x : Matrix (Fin m) (Fin n) ℝ, 2 * b * Y x ∂ν
        = 2 * b * ∫ x : Matrix (Fin m) (Fin n) ℝ, Y x ∂ν :=
      integral_const_mul (2 * b) Y
    have hb2v : ∫ x : Matrix (Fin m) (Fin n) ℝ, b ^ 2 ∂ν = b ^ 2 := by simp
    rw [hkey, e2, e3, e4, hb2v, ← hb]
    ring
  have hY2le : ∫ x : Matrix (Fin m) (Fin n) ℝ, (Y x) ^ 2 ∂ν ≤ 1 := by
    have hmono : ∫ x : Matrix (Fin m) (Fin n) ℝ, (Y x) ^ 2 ∂ν
        ≤ ∫ x : Matrix (Fin m) (Fin n) ℝ, (x i j) ^ 2 ∂ν :=
      MeasureTheory.integral_mono_ae hY2int hfint
        (Filter.Eventually.of_forall fun x => hYsqle x)
    rw [hvar] at hmono
    exact hmono
  have hfin : ∫ x : Matrix (Fin m) (Fin n) ℝ, (Y x - b) ^ 2 ∂ν ≤ 1 := by
    rw [hexp]
    nlinarith [hY2le, sq_nonneg b]
  linarith [hcsq, hfin]
  /- @proof-region region.target-node.session.b0d99818f951431a end -/

end Statlib.Imported

