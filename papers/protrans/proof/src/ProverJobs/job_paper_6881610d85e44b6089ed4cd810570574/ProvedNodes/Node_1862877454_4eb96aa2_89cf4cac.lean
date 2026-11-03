import Lean
import ProverJobs.job_paper_6881610d85e44b6089ed4cd810570574.Vocabulary
import ProverJobs.job_paper_6881610d85e44b6089ed4cd810570574.Base
import ProverJobs.job_paper_6881610d85e44b6089ed4cd810570574.ProvedNodes.Node_318020560_e6aa841c_ea8ebcaa

namespace PaperProofTasks.job_paper_6881610d85e44b6089ed4cd810570574

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open _root_.PaperProofTasks.job_paper_6881610d85e44b6089ed4cd810570574.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped ENNReal
universe u
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))

set_option autoImplicit false in
theorem statopia_math_node_1862877454_4eb96aa2 : ∀ (c : ℝ) (hc : 0 < c)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z Z2 : Ω → ℝ) (hZ : Measurable Z) (hZ2 : Measurable Z2)
    (hInt_pos : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * Z ω)) μ)
    (hInt_neg : ∀ t : ℝ, Integrable (fun ω => Real.exp (-t * Z ω)) μ)
    (hMGF_pos : ∀ t : ℝ, ∫ ω, Real.exp (t * Z ω) ∂μ ≤ Real.exp (c * t ^ 2 / 2))
    (hMGF_neg : ∀ t : ℝ, ∫ ω, Real.exp (-t * Z ω) ∂μ ≤ Real.exp (c * t ^ 2 / 2))
    (hInt_pos2 : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * Z2 ω)) μ)
    (hInt_neg2 : ∀ t : ℝ, Integrable (fun ω => Real.exp (-t * Z2 ω)) μ)
    (hMGF_pos2 : ∀ t : ℝ, ∫ ω, Real.exp (t * Z2 ω) ∂μ ≤ Real.exp (c * t ^ 2 / 2))
    (hMGF_neg2 : ∀ t : ℝ, ∫ ω, Real.exp (-t * Z2 ω) ∂μ ≤ Real.exp (c * t ^ 2 / 2))
    (r : ℕ) (hr : 2 ≤ r),
    ∫⁻ ω, ENNReal.ofReal (|Z ω * Z2 ω| ^ r) ∂μ ≤
      ENNReal.ofReal
        ((2 * (Real.sqrt (2 * c * Real.exp 1)) ^ 2 * (r : ℝ)) ^ r) := by
  /- @proof-region region.target-node.session.4889cb7f29bbb24b begin -/
  intro c hc Ω hΩ μ hμ Z Z2 hZ hZ2 hint_pos hint_neg hint_pos_Z2 hint_neg_Z2
    hbound_pos hbound_neg hbound_pos_Z2 hbound_neg_Z2 r hr
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  let M0 : ℝ := (Real.sqrt (2 * c * Real.exp 1) * Real.sqrt (2 * (r : ℝ))) ^ (2 * r)
  have hM0def : M0 = (Real.sqrt (2 * c * Real.exp 1) * Real.sqrt (2 * (r : ℝ))) ^ (2 * r) := rfl
  have hZb : ∫⁻ ω, ENNReal.ofReal (|Z ω| ^ (2 * r)) ∂μ ≤ ENNReal.ofReal M0 := by
    rw [hM0def]
    apply statopia_math_node_318020560_e6aa841c
    all_goals first | assumption | exact hr1
  have hZ2b : ∫⁻ ω, ENNReal.ofReal (|Z2 ω| ^ (2 * r)) ∂μ ≤ ENNReal.ofReal M0 := by
    rw [hM0def]
    apply statopia_math_node_318020560_e6aa841c
    all_goals first | assumption | exact hr1
  have hM0nn : (0:ℝ) ≤ M0 := by
    rw [hM0def]
    exact pow_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) _
  have hmeasZ : Measurable fun ω => ENNReal.ofReal (|Z ω| ^ (2 * r)) := by
    measurability
  have hmeasZ2 : Measurable fun ω => ENNReal.ofReal (|Z2 ω| ^ (2 * r)) := by
    measurability
  have hpt : ∀ ω : Ω, ENNReal.ofReal (|Z ω * Z2 ω| ^ r) ≤
      (ENNReal.ofReal (|Z ω| ^ (2 * r)) + ENNReal.ofReal (|Z2 ω| ^ (2 * r))) * (2:ℝ≥0∞)⁻¹ := by
    intro ω
    rw [abs_mul, mul_pow]
    have ha : (0:ℝ) ≤ |Z ω| ^ (2 * r) := pow_nonneg (abs_nonneg _) _
    have hb : (0:ℝ) ≤ |Z2 ω| ^ (2 * r) := pow_nonneg (abs_nonneg _) _
    have hreal : |Z ω| ^ r * |Z2 ω| ^ r ≤
        (|Z ω| ^ (2 * r) + |Z2 ω| ^ (2 * r)) * (2:ℝ)⁻¹ := by
      have hsq : 2 * (|Z ω| ^ r) * (|Z2 ω| ^ r) ≤ (|Z ω| ^ r) ^ 2 + (|Z2 ω| ^ r) ^ 2 := by
        nlinarith [sq_nonneg (|Z ω| ^ r - |Z2 ω| ^ r)]
      have e1 : (|Z ω| ^ r) ^ 2 = |Z ω| ^ (2 * r) := by
        rw [← pow_mul, Nat.mul_comm r 2]
      have e2 : (|Z2 ω| ^ r) ^ 2 = |Z2 ω| ^ (2 * r) := by
        rw [← pow_mul, Nat.mul_comm r 2]
      rw [e1, e2] at hsq
      linarith
    have s1 : ENNReal.ofReal ((|Z ω| ^ (2 * r) + |Z2 ω| ^ (2 * r)) * (2:ℝ)⁻¹)
        = ENNReal.ofReal (|Z ω| ^ (2 * r) + |Z2 ω| ^ (2 * r)) *
          ENNReal.ofReal ((2:ℝ)⁻¹) :=
      ENNReal.ofReal_mul (add_nonneg ha hb)
    have s2 : ENNReal.ofReal (|Z ω| ^ (2 * r) + |Z2 ω| ^ (2 * r))
        = ENNReal.ofReal (|Z ω| ^ (2 * r)) + ENNReal.ofReal (|Z2 ω| ^ (2 * r)) :=
      ENNReal.ofReal_add ha hb
    have s3 : ENNReal.ofReal ((2:ℝ)⁻¹) = (2:ℝ≥0∞)⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 2), ENNReal.ofReal_ofNat]
    calc ENNReal.ofReal (|Z ω| ^ r * |Z2 ω| ^ r)
        ≤ ENNReal.ofReal ((|Z ω| ^ (2 * r) + |Z2 ω| ^ (2 * r)) * (2:ℝ)⁻¹) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (|Z ω| ^ (2 * r) + |Z2 ω| ^ (2 * r)) *
            ENNReal.ofReal ((2:ℝ)⁻¹) := s1
      _ = (ENNReal.ofReal (|Z ω| ^ (2 * r)) + ENNReal.ofReal (|Z2 ω| ^ (2 * r))) *
            ENNReal.ofReal ((2:ℝ)⁻¹) := by rw [s2]
      _ = (ENNReal.ofReal (|Z ω| ^ (2 * r)) + ENNReal.ofReal (|Z2 ω| ^ (2 * r))) *
            (2:ℝ≥0∞)⁻¹ := by rw [s3]
  have hint1 : ∫⁻ ω, ENNReal.ofReal (|Z ω * Z2 ω| ^ r) ∂μ ≤
      ∫⁻ ω, (ENNReal.ofReal (|Z ω| ^ (2 * r)) + ENNReal.ofReal (|Z2 ω| ^ (2 * r))) *
        (2:ℝ≥0∞)⁻¹ ∂μ :=
    lintegral_mono hpt
  have hsplit : ∫⁻ ω, (ENNReal.ofReal (|Z ω| ^ (2 * r)) +
        ENNReal.ofReal (|Z2 ω| ^ (2 * r))) * (2:ℝ≥0∞)⁻¹ ∂μ
      = (∫⁻ ω, ENNReal.ofReal (|Z ω| ^ (2 * r)) ∂μ +
          ∫⁻ ω, ENNReal.ofReal (|Z2 ω| ^ (2 * r)) ∂μ) * (2:ℝ≥0∞)⁻¹ := by
    have h1 : ∫⁻ ω, (ENNReal.ofReal (|Z ω| ^ (2 * r)) +
          ENNReal.ofReal (|Z2 ω| ^ (2 * r))) * (2:ℝ≥0∞)⁻¹ ∂μ
        = (∫⁻ ω, (ENNReal.ofReal (|Z ω| ^ (2 * r)) +
            ENNReal.ofReal (|Z2 ω| ^ (2 * r))) ∂μ) * (2:ℝ≥0∞)⁻¹ :=
      lintegral_mul_const ((2:ℝ≥0∞)⁻¹) (hmeasZ.add hmeasZ2)
    have h2 : ∫⁻ ω, (ENNReal.ofReal (|Z ω| ^ (2 * r)) +
          ENNReal.ofReal (|Z2 ω| ^ (2 * r))) ∂μ
        = ∫⁻ ω, ENNReal.ofReal (|Z ω| ^ (2 * r)) ∂μ +
          ∫⁻ ω, ENNReal.ofReal (|Z2 ω| ^ (2 * r)) ∂μ :=
      lintegral_add_left hmeasZ _
    rw [h1, h2]
  have hMM : (ENNReal.ofReal M0 + ENNReal.ofReal M0) * (2:ℝ≥0∞)⁻¹ = ENNReal.ofReal M0 := by
    have s1 : ENNReal.ofReal M0 + ENNReal.ofReal M0 = ENNReal.ofReal (M0 + M0) :=
      (ENNReal.ofReal_add hM0nn hM0nn).symm
    have s2 : ENNReal.ofReal ((2:ℝ)⁻¹) = (2:ℝ≥0∞)⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 2), ENNReal.ofReal_ofNat]
    have s3 : ENNReal.ofReal (M0 + M0) * ENNReal.ofReal ((2:ℝ)⁻¹) =
        ENNReal.ofReal ((M0 + M0) * (2:ℝ)⁻¹) :=
      (ENNReal.ofReal_mul (p := M0 + M0) (q := (2:ℝ)⁻¹) (by linarith)).symm
    have s4 : (M0 + M0) * (2:ℝ)⁻¹ = M0 := by ring
    rw [s1, ← s2, s3, s4]
  have hfinal : (∫⁻ ω, ENNReal.ofReal (|Z ω| ^ (2 * r)) ∂μ +
      ∫⁻ ω, ENNReal.ofReal (|Z2 ω| ^ (2 * r)) ∂μ) * (2:ℝ≥0∞)⁻¹ ≤ ENNReal.ofReal M0 := by
    have h : ∫⁻ ω, ENNReal.ofReal (|Z ω| ^ (2 * r)) ∂μ +
        ∫⁻ ω, ENNReal.ofReal (|Z2 ω| ^ (2 * r)) ∂μ ≤
        ENNReal.ofReal M0 + ENNReal.ofReal M0 :=
      add_le_add hZb hZ2b
    calc (∫⁻ ω, ENNReal.ofReal (|Z ω| ^ (2 * r)) ∂μ +
          ∫⁻ ω, ENNReal.ofReal (|Z2 ω| ^ (2 * r)) ∂μ) * (2:ℝ≥0∞)⁻¹
        ≤ (ENNReal.ofReal M0 + ENNReal.ofReal M0) * (2:ℝ≥0∞)⁻¹ := by gcongr
      _ = ENNReal.ofReal M0 := hMM
  have hkey : M0 = ((2 * (Real.sqrt (2 * c * Real.exp 1)) ^ 2 * (r : ℝ)) ^ r) := by
    rw [hM0def]
    have hr2 : (Real.sqrt (2 * (r : ℝ))) ^ 2 = 2 * (r : ℝ) :=
      Real.sq_sqrt (by positivity)
    have h1 : (Real.sqrt (2 * c * Real.exp 1) * Real.sqrt (2 * (r : ℝ))) ^ (2 * r)
        = ((Real.sqrt (2 * c * Real.exp 1) * Real.sqrt (2 * (r : ℝ))) ^ 2) ^ r :=
      pow_mul _ 2 r
    rw [h1, mul_pow, hr2]
    congr 1
    ring
  calc ∫⁻ ω, ENNReal.ofReal (|Z ω * Z2 ω| ^ r) ∂μ
      ≤ ∫⁻ ω, (ENNReal.ofReal (|Z ω| ^ (2 * r)) + ENNReal.ofReal (|Z2 ω| ^ (2 * r))) *
          (2:ℝ≥0∞)⁻¹ ∂μ := hint1
    _ = (∫⁻ ω, ENNReal.ofReal (|Z ω| ^ (2 * r)) ∂μ +
          ∫⁻ ω, ENNReal.ofReal (|Z2 ω| ^ (2 * r)) ∂μ) * (2:ℝ≥0∞)⁻¹ := hsplit
    _ ≤ ENNReal.ofReal M0 := hfinal
    _ = ENNReal.ofReal ((2 * (Real.sqrt (2 * c * Real.exp 1)) ^ 2 * (r : ℝ)) ^ r) := by
      rw [hkey]
  /- @proof-region region.target-node.session.4889cb7f29bbb24b end -/

end Statlib.Imported

