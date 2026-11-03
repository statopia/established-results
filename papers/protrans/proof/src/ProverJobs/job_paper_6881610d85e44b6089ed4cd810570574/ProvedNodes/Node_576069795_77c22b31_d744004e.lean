import Statlib.StatFoundation.BasicAnalysis.ENNRealBridge
import Lean
import ProverJobs.job_paper_6881610d85e44b6089ed4cd810570574.Vocabulary
import ProverJobs.job_paper_6881610d85e44b6089ed4cd810570574.Base
import ProverJobs.job_paper_6881610d85e44b6089ed4cd810570574.ProvedNodes.Node_1862877454_4eb96aa2_89cf4cac

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
theorem statopia_math_node_576069795_77c22b31 : ∀ (c : ℝ) (hc : 0 < c)
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
    (hInt_prod : Integrable (fun ω => Z ω * Z2 ω) μ)
    (r : ℕ) (hr : 2 ≤ r),
    ∫⁻ ω, ENNReal.ofReal
        (|Z ω * Z2 ω - ∫ ω', Z ω' * Z2 ω' ∂μ| ^ r) ∂μ
      ≤ ENNReal.ofReal ((r.factorial : ℝ) * (8 * c * (Real.exp 1) ^ 2) ^ r) := by
  /- @proof-region region.target-node.session.f370e5947570c220 begin -/
  intro c hc Ω _ μ _ Z Z2 hZ hZ2 hint_pos hint_neg hbound_pos hbound_neg
    hint_pos_Z2 hint_neg_Z2 hbound_pos_Z2 hbound_neg_Z2 hprod r hr
  set m : ℝ := ∫ ω', Z ω' * Z2 ω' ∂μ with hm_def
  set B : ℝ := 8 * c * (Real.exp 1) ^ 2 with hB_def
  have huncentered :
      ∫⁻ ω, ENNReal.ofReal (|Z ω * Z2 ω| ^ r) ∂μ
        ≤ ENNReal.ofReal (((4 * c * Real.exp 1) * (r : ℝ)) ^ r) := by
    have hbase := statopia_math_node_1862877454_4eb96aa2
      (Ω := Ω) (c := c) (hc := hc) (μ := μ) (Z := Z) (Z2 := Z2) (hZ := hZ) (hZ2 := hZ2)
      (hInt_pos := hint_pos) (hInt_neg := hint_neg)
      (hMGF_pos := hbound_pos) (hMGF_neg := hbound_neg)
      (hInt_pos2 := hint_pos_Z2) (hInt_neg2 := hint_neg_Z2)
      (hMGF_pos2 := hbound_pos_Z2) (hMGF_neg2 := hbound_neg_Z2)
      (r := r) (hr := hr)
    have harg : (2 * (Real.sqrt (2 * c * Real.exp 1)) ^ 2 * (r : ℝ))
        = (4 * c * Real.exp 1) * (r : ℝ) := by
      rw [Real.sq_sqrt (by positivity)]
      ring
    simpa only [harg] using hbase
  set A : ℝ := (4 * c * Real.exp 1) * (r : ℝ) with hA_def
  have hA_nonneg : 0 ≤ A := by rw [hA_def]; positivity
  have hB_nonneg : 0 ≤ B := by rw [hB_def]; positivity
  have hmeas_abs_pow : AEStronglyMeasurable (fun ω => |Z ω * Z2 ω| ^ r) μ := by
    have h : Measurable (fun ω => |Z ω * Z2 ω| ^ r) := by fun_prop
    exact h.aestronglyMeasurable
  have hnn_abs_pow : 0 ≤ᵐ[μ] (fun ω => |Z ω * Z2 ω| ^ r) :=
    Filter.Eventually.of_forall (fun ω => pow_nonneg (abs_nonneg _) r)
  have hlint_ne_top : ∫⁻ ω, ENNReal.ofReal (|Z ω * Z2 ω| ^ r) ∂μ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top huncentered
  have hInt_pow : Integrable (fun ω => |Z ω * Z2 ω| ^ r) μ :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmeas_abs_pow hnn_abs_pow).mp
      hlint_ne_top
  have hUnc_real : ∫ ω, |Z ω * Z2 ω| ^ r ∂μ ≤ A ^ r := by
    rw [Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.integral_eq_lintegral_toReal_of_nonneg
      hnn_abs_pow hInt_pow]
    calc (∫⁻ ω, ENNReal.ofReal (|Z ω * Z2 ω| ^ r) ∂μ).toReal
        ≤ (ENNReal.ofReal (A ^ r)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top huncentered
      _ = A ^ r := ENNReal.toReal_ofReal (pow_nonneg hA_nonneg r)
  have hJensen : (∫ ω, |Z ω * Z2 ω| ∂μ) ^ r ≤ ∫ ω, |Z ω * Z2 ω| ^ r ∂μ := by
    have hconv : ConvexOn ℝ (Set.Ici (0:ℝ)) (fun t : ℝ => t ^ r) :=
      (convexOn_pow r : ConvexOn ℝ (Set.Ici (0:ℝ)) (fun t : ℝ => t ^ r))
    have hint2 : Integrable ((fun t : ℝ => t ^ r) ∘ (fun ω => |Z ω * Z2 ω|)) μ := by
      simpa [Function.comp_def] using hInt_pow
    have hmain := hconv.map_integral_le (continuous_pow r).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall (fun ω => Set.mem_Ici.mpr (abs_nonneg _))) hprod.abs hint2
    simpa [Function.comp_def] using hmain
  have hm_pow : |m| ^ r ≤ A ^ r := by
    have hle : |m| ≤ ∫ ω, |Z ω * Z2 ω| ∂μ := by
      have h := MeasureTheory.abs_integral_le_integral_abs (μ := μ) (f := fun ω => Z ω * Z2 ω)
      simpa [hm_def] using h
    calc |m| ^ r ≤ (∫ ω, |Z ω * Z2 ω| ∂μ) ^ r :=
          pow_le_pow_left₀ (abs_nonneg m) hle r
      _ ≤ A ^ r := le_trans hJensen hUnc_real
  have hpt : ∀ ω, |Z ω * Z2 ω - m| ^ r ≤ (2:ℝ) ^ (r-1) * (|Z ω * Z2 ω| ^ r + |m| ^ r) := by
    have hsplit : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
        (x + y) ^ r ≤ (2:ℝ) ^ (r-1) * (x ^ r + y ^ r) := by
      intro x y hx hy
      have hconv : ConvexOn ℝ (Set.Ici (0:ℝ)) (fun t : ℝ => t ^ r) :=
        (convexOn_pow r : ConvexOn ℝ (Set.Ici (0:ℝ)) (fun t : ℝ => t ^ r))
      have h2 := hconv.2 (x := x) (Set.mem_Ici.mpr hx) (y := y) (Set.mem_Ici.mpr hy)
        (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1/2:ℝ) + 1/2 = 1)
      simp only [smul_eq_mul] at h2
      have ha1 : (1/2:ℝ) * x + (1/2:ℝ) * y = (x + y) / 2 := by ring
      have ha2 : (1/2:ℝ) * x ^ r + (1/2:ℝ) * y ^ r = (x ^ r + y ^ r) / 2 := by ring
      rw [ha1, ha2] at h2
      have hkey : (x + y) ^ r = (2:ℝ) ^ r * ((x + y) / 2) ^ r := by
        rw [← mul_pow, show (2:ℝ) * ((x + y) / 2) = x + y from by ring]
      rw [hkey]
      have h2r : (2:ℝ) ^ r * ((x + y) / 2) ^ r ≤ (2:ℝ) ^ r * ((x ^ r + y ^ r) / 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      have h3 : (2:ℝ) ^ r * ((x ^ r + y ^ r) / 2) = (2:ℝ) ^ (r-1) * (x ^ r + y ^ r) := by
        have hp2 : (2:ℝ) ^ (r-1) * 2 = 2 ^ r := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ r)]
        have hp : (2:ℝ) ^ r = 2 * (2:ℝ) ^ (r-1) := by rw [← hp2]; ring
        rw [hp]; ring
      linarith [h2r, h3]
    intro ω
    have h1 : |Z ω * Z2 ω - m| ≤ |Z ω * Z2 ω| + |m| := by
      rw [sub_eq_add_neg]
      simpa using abs_add_le (Z ω * Z2 ω) (-m)
    calc |Z ω * Z2 ω - m| ^ r
        ≤ (|Z ω * Z2 ω| + |m|) ^ r := pow_le_pow_left₀ (abs_nonneg _) h1 r
      _ ≤ (2:ℝ) ^ (r-1) * (|Z ω * Z2 ω| ^ r + |m| ^ r) :=
          hsplit _ _ (abs_nonneg _) (abs_nonneg _)
  have hg_meas : AEStronglyMeasurable (fun ω => |Z ω * Z2 ω - m| ^ r) μ := by
    have h : Measurable (fun ω => |Z ω * Z2 ω - m| ^ r) := by fun_prop
    exact h.aestronglyMeasurable
  have hdom_int : Integrable (fun ω => (2:ℝ) ^ (r-1) * (|Z ω * Z2 ω| ^ r + |m| ^ r)) μ := by
    apply Integrable.const_mul
    exact hInt_pow.add (integrable_const (|m| ^ r))
  have hg_int : Integrable (fun ω => |Z ω * Z2 ω - m| ^ r) μ := by
    apply Integrable.mono' hdom_int hg_meas
    filter_upwards with ω
    rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) r)]
    exact hpt ω
  have hconst_nonneg : (0:ℝ) ≤ (2:ℝ) ^ (r-1) := by positivity
  have hconst_int : ∫ ω, (|m| ^ r : ℝ) ∂μ = |m| ^ r := by
    rw [MeasureTheory.integral_const]; simp
  have hconst_le : ((8 * c * Real.exp 1) * (r:ℝ)) ^ r ≤ (r.factorial:ℝ) * B ^ r := by
    have hfac : ((r:ℝ) / Real.exp 1) ^ r ≤ (r.factorial:ℝ) := by
      rw [div_pow]
      have h1 := Real.pow_div_factorial_le_exp (r:ℝ) (by positivity) r
      have hexp : Real.exp (r:ℝ) = (Real.exp 1) ^ r := by rw [← Real.exp_nat_mul, mul_one]
      rw [hexp] at h1
      rw [div_le_iff₀ (by positivity : (0:ℝ) < (r.factorial:ℝ))] at h1
      rw [div_le_iff₀ (pow_pos (Real.exp_pos 1) r)]
      rw [mul_comm ((r.factorial:ℝ)) ((Real.exp 1) ^ r)]
      exact h1
    have hB_eq : (8 * c * Real.exp 1) * (r:ℝ) = B * ((r:ℝ) / Real.exp 1) := by
      rw [hB_def]; field_simp
    rw [hB_eq, mul_pow B ((r:ℝ) / Real.exp 1) r]
    calc B ^ r * ((r:ℝ) / Real.exp 1) ^ r
        ≤ B ^ r * (r.factorial:ℝ) := mul_le_mul_of_nonneg_left hfac (pow_nonneg hB_nonneg r)
      _ = (r.factorial:ℝ) * B ^ r := by ring
  have hmain_real : ∫ ω, |Z ω * Z2 ω - m| ^ r ∂μ ≤ (r.factorial:ℝ) * B ^ r := by
    have hstep : ∫ ω, |Z ω * Z2 ω - m| ^ r ∂μ ≤ (2:ℝ) ^ (r-1) * (A ^ r + A ^ r) := by
      calc ∫ ω, |Z ω * Z2 ω - m| ^ r ∂μ
          ≤ ∫ ω, (2:ℝ) ^ (r-1) * (|Z ω * Z2 ω| ^ r + |m| ^ r) ∂μ :=
            integral_mono hg_int hdom_int hpt
        _ = (2:ℝ) ^ (r-1) * (∫ ω, |Z ω * Z2 ω| ^ r ∂μ + |m| ^ r) := by
            rw [MeasureTheory.integral_const_mul,
              MeasureTheory.integral_add hInt_pow (integrable_const (|m| ^ r)), hconst_int]
        _ ≤ (2:ℝ) ^ (r-1) * (A ^ r + A ^ r) :=
            mul_le_mul_of_nonneg_left (by linarith [hUnc_real, hm_pow]) hconst_nonneg
    refine le_trans hstep ?_
    have hfin : (2:ℝ) ^ (r-1) * (A ^ r + A ^ r) ≤ (r.factorial:ℝ) * B ^ r := by
      rw [hA_def]
      have hp : (2:ℝ) ^ (r-1) * 2 = 2 ^ r := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ r)]
      have hkey :
          (2:ℝ) ^ (r-1) *
              (((4 * c * Real.exp 1) * (r:ℝ)) ^ r + ((4 * c * Real.exp 1) * (r:ℝ)) ^ r)
            = ((8 * c * Real.exp 1) * (r:ℝ)) ^ r := by
        have h2A : (2:ℝ) * ((4 * c * Real.exp 1) * (r:ℝ)) = (8 * c * Real.exp 1) * (r:ℝ) := by
          ring
        rw [← h2A, mul_pow (2:ℝ) ((4 * c * Real.exp 1) * (r:ℝ)) r]
        calc (2:ℝ) ^ (r-1) *
              (((4 * c * Real.exp 1) * (r:ℝ)) ^ r + ((4 * c * Real.exp 1) * (r:ℝ)) ^ r)
            = (2:ℝ) ^ (r-1) * 2 * ((4 * c * Real.exp 1) * (r:ℝ)) ^ r := by ring
          _ = (2:ℝ) ^ r * ((4 * c * Real.exp 1) * (r:ℝ)) ^ r := by rw [hp]
      rw [hkey]
      exact hconst_le
    exact hfin
  have hg_lint :
      ∫⁻ ω, ENNReal.ofReal (|Z ω * Z2 ω - m| ^ r) ∂μ
        = ENNReal.ofReal (∫ ω, |Z ω * Z2 ω - m| ^ r ∂μ) := by
    have h := MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (f := fun ω => |Z ω * Z2 ω - m| ^ r) hg_int
      (Filter.Eventually.of_forall (fun ω => pow_nonneg (abs_nonneg _) r))
    simpa using h.symm
  rw [hg_lint]
  refine ENNReal.ofReal_le_ofReal hmain_real
  /- @proof-region region.target-node.session.f370e5947570c220 end -/

end Statlib.Imported

