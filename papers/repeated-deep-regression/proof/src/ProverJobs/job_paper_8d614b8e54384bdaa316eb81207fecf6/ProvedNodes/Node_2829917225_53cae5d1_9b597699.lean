import ProverJobs.paper_fresh_20261030t103504286z_deep_regression.ProofSupport.PointwiseSeparability
import Lean
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.Vocabulary
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.Base
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.ProvedNodes.Node_1390765457_210d1e15_5d8f5653
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.ProvedNodes.Node_3098222659_8397580a_5211a45a
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.ExternalNodes.Node_c0ecbd1554064cc7a262

namespace PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6



open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
open _root_.PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
noncomputable section
set_option maxHeartbeats 1000000

set_option autoImplicit false in
theorem statopia_math_node_2829917225_53cae5d1 : ∀ (B1 : ℝ) (hB1 : 0 < B1)
    {Ωs : Type*} [MeasurableSpace Ωs]
    (PX : Measure Ωs) (hPX : IsProbabilityMeasure PX)
    (f0 : Ωs → ℝ) (F : Set (Ωs → ℝ))
    (hf0_meas : Measurable f0)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (hf0_bound : ∀ x : Ωs, |f0 x| ≤ B1)
    (hF_bound : ∀ f ∈ F, ∀ x : Ωs, |f x| ≤ B1)
    (hF_int : ∀ f ∈ F, Integrable (fun x : Ωs => (f x - f0 x) ^ 2) PX)
    {Ωrand : Type*} [MeasurableSpace Ωrand]
    (P : Measure Ωrand) (hP : IsProbabilityMeasure P)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (X : Fin n → Fin m → Ωrand → Ωs)
    (hX_meas : ∀ p : Fin n × Fin m, Measurable (X p.1 p.2))
    (hX_law : ∀ p : Fin n × Fin m, Measure.map (X p.1 p.2) P = PX)
    (hX_indep : iIndepFun (fun p : Fin n × Fin m => X p.1 p.2) P)
    (sigma : Fin n → Fin m → Ωrand → ℝ)
    (hsigma_meas : ∀ p : Fin n × Fin m, Measurable (sigma p.1 p.2))
    (hsigma_law : ∀ p : Fin n × Fin m, Measure.map (sigma p.1 p.2) P = rademacherLaw)
    (hsigma_indep : iIndepFun (fun p : Fin n × Fin m => sigma p.1 p.2) P)
    (hsigma_indep_X : IndepFun (fun ω => fun p : Fin n × Fin m => sigma p.1 p.2 ω)
      (fun ω => fun p : Fin n × Fin m => X p.1 p.2 ω) P)
    (phi : ℝ → ℝ) (rstar : ℝ)
    (hfix : IsRademacherFixedPoint F PX f0 X sigma P phi rstar)
    (r : ℝ) (hr : rstar ≤ r)
    (t : ℝ) (ht : 0 < t)
    (hF_sep : PointwiseSeparable F),
    ENNReal.ofReal (1 - Real.exp (-t)) ≤
      P {ω : Ωrand | ∀ f ∈ F,
        |predError PX f0 f - empSqDisc X f0 ω f| ≤
          (160 * B1 * phi r / r +
              Real.sqrt (8 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ) * r)) +
              140 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ) * r)) *
            (predError PX f0 f + r)} := by
  /- @proof-region region.target-node.session.3326edc4ebe89b08 begin -/
  intro B1 hB1 Ωs _ PX _ f0 F hf0_meas hF_meas hf0_bound hF_bound hF_int Ωrand _ P _ n m hn hm X hX_meas hX_law hX_indep sigma hsigma_meas hsigma_law hsigma_indep hsigma_indep_X phi rstar hfix r hr t ht hF_sep
  set D : ℝ := 160 * B1 * phi r / r + Real.sqrt (8 * B1 ^ 2 * t / (((n : ℝ) * (m : ℝ)) * r)) + 140 * B1 ^ 2 * t / (((n : ℝ) * (m : ℝ)) * r) with hD
  have hne : P {ω | ∀ f ∈ F, |predError PX f0 f - empSqDisc X f0 ω f| ≤ D * (predError PX f0 f + r)} ≠ ⊤ :=
    (measure_ne_top P _)
  have hposr : 0 < r := lt_of_lt_of_le hfix.1 hr
  have hN : ((n : ℝ) * (m : ℝ)) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hn.ne') (by exact_mod_cast hm.ne')
  have hident : ∀ (f : Ωs → ℝ) (ω : Ωrand),
      ((n : ℝ) * (m : ℝ))⁻¹ *
          (∑ i : Fin n, ∑ j : Fin m,
            (predError PX f0 f - (f (X i j ω) - f0 (X i j ω)) ^ 2) / (predError PX f0 f + r))
        = (predError PX f0 f - empSqDisc X f0 ω f) / (predError PX f0 f + r) := by
    intro f ω
    by_cases ha : predError PX f0 f + r = 0
    · simp [ha]
    · have hS : ∑ i : Fin n, ∑ j : Fin m, (f (X i j ω) - f0 (X i j ω)) ^ 2
          = ((n : ℝ) * (m : ℝ)) * empSqDisc X f0 ω f := by
        simp only [empSqDisc]
        rw [← mul_assoc, mul_inv_cancel₀ hN, one_mul]
      have hdiv : ∑ i : Fin n, ∑ j : Fin m,
            (predError PX f0 f - (f (X i j ω) - f0 (X i j ω)) ^ 2) / (predError PX f0 f + r)
          = (∑ i : Fin n, ∑ j : Fin m,
              (predError PX f0 f - (f (X i j ω) - f0 (X i j ω)) ^ 2)) / (predError PX f0 f + r) := by
        simp only [← Finset.sum_div]
      have hsumconst : ∑ i : Fin n, ∑ j : Fin m, predError PX f0 f
          = predError PX f0 f * ((n : ℝ) * (m : ℝ)) := by
        simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        ring
      have hsub : ∑ i : Fin n, ∑ j : Fin m,
            (predError PX f0 f - (f (X i j ω) - f0 (X i j ω)) ^ 2)
          = predError PX f0 f * ((n : ℝ) * (m : ℝ))
            - ∑ i : Fin n, ∑ j : Fin m, (f (X i j ω) - f0 (X i j ω)) ^ 2 := by
        rw [show ∑ i : Fin n, ∑ j : Fin m,
              (predError PX f0 f - (f (X i j ω) - f0 (X i j ω)) ^ 2)
            = (∑ i : Fin n, ∑ j : Fin m, predError PX f0 f)
              - ∑ i : Fin n, ∑ j : Fin m, (f (X i j ω) - f0 (X i j ω)) ^ 2 from by
              simp only [Finset.sum_sub_distrib]]
        rw [hsumconst]
      rw [hdiv, hsub, hS]
      field_simp [ha, hN]
  have hstep : ∀ f ∈ F, ∀ ω : Ωrand,
      (|((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          (predError PX f0 f - (f (X i j ω) - f0 (X i j ω)) ^ 2) / (predError PX f0 f + r)| ≤ D) →
      |predError PX f0 f - empSqDisc X f0 ω f| ≤ D * (predError PX f0 f + r) := by
    intro f hf ω hbound
    have hnonneg : 0 ≤ predError PX f0 f := by
      show 0 ≤ ∫ x, (f x - f0 x) ^ 2 ∂PX
      exact integral_nonneg (fun x => sq_nonneg (f x - f0 x))
    have hden : 0 < predError PX f0 f + r := by linarith
    rw [hident f ω, abs_div, abs_of_pos hden] at hbound
    rwa [div_le_iff₀ hden] at hbound
  have hmono : P.real {ω | ∀ f ∈ F,
        |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          (predError PX f0 f - (f (X i j ω) - f0 (X i j ω)) ^ 2) / (predError PX f0 f + r)| ≤ D}
      ≤ P.real {ω | ∀ f ∈ F, |predError PX f0 f - empSqDisc X f0 ω f| ≤ D * (predError PX f0 f + r)} :=
    ENNReal.toReal_mono hne
      (measure_mono (fun ω hω f hf => hstep f hf ω (hω f hf)))
  have hpeel := statopia_math_node_3098222659_8397580a B1 hB1 PX f0 F hf0_meas hF_meas hf0_bound hF_bound hF_int P n m hn hm X hX_meas hX_law hX_indep sigma hsigma_meas hsigma_law hsigma_indep hsigma_indep_X phi rstar hfix r hr
  have hbracket :
      160 * B1 * phi r / r + Real.sqrt (8 * (B1 ^ 2 / r) * t / (((n * m : ℕ) : ℝ)))
        + 35 * (4 * B1 ^ 2 / r) * t / (((n * m : ℕ) : ℝ))
      = 160 * B1 * phi r / r + Real.sqrt (8 * B1 ^ 2 * t / (((n : ℝ) * (m : ℝ)) * r))
        + 140 * B1 ^ 2 * t / (((n : ℝ) * (m : ℝ)) * r) := by
    have h1 : Real.sqrt (8 * (B1 ^ 2 / r) * t / (((n * m : ℕ) : ℝ)))
        = Real.sqrt (8 * B1 ^ 2 * t / (((n : ℝ) * (m : ℝ)) * r)) := by
      congr 1
      rw [Nat.cast_mul]
      field_simp [hposr.ne', hN] <;> ring
    have h2 : 35 * (4 * B1 ^ 2 / r) * t / (((n * m : ℕ) : ℝ))
        = 140 * B1 ^ 2 * t / (((n : ℝ) * (m : ℝ)) * r) := by
      rw [Nat.cast_mul]
      field_simp [hposr.ne', hN] <;> ring
    rw [h1, h2]
  have hPXuniv : PX.real (Set.univ : Set Ωs) = 1 := by
    show (PX Set.univ).toReal = 1
    rw [measure_univ, ENNReal.toReal_one]
  have hterm_le : ∀ f ∈ F, ∀ x : Ωs,
      |(predError PX f0 f - (f x - f0 x) ^ 2) / (predError PX f0 f + r)| ≤ 4 * B1 ^ 2 / r := by
    intro f hf x
    have ha0 : 0 ≤ predError PX f0 f := by
      show 0 ≤ ∫ y, (f y - f0 y) ^ 2 ∂PX
      exact integral_nonneg (fun y => sq_nonneg (f y - f0 y))
    have hxi_le : ∀ y : Ωs, (f y - f0 y) ^ 2 ≤ 4 * B1 ^ 2 := by
      intro y
      have h1 : |f y - f0 y| ≤ 2 * B1 := by
        calc |f y - f0 y| = |f y + -(f0 y)| := by rw [sub_eq_add_neg]
          _ ≤ |f y| + |-(f0 y)| := abs_add_le _ _
          _ = |f y| + |f0 y| := by rw [abs_neg]
          _ ≤ B1 + B1 := add_le_add (hF_bound f hf y) (hf0_bound y)
          _ = 2 * B1 := by ring
      nlinarith [abs_le.mp h1, hB1]
    have ha4 : predError PX f0 f ≤ 4 * B1 ^ 2 := by
      show ∫ y, (f y - f0 y) ^ 2 ∂PX ≤ 4 * B1 ^ 2
      have hmono := integral_mono (hF_int f hf) (integrable_const (4 * B1 ^ 2)) hxi_le
      simp only [integral_const, hPXuniv, one_smul, smul_eq_mul, mul_one, one_mul] at hmono
      exact hmono
    have hden : 0 < predError PX f0 f + r := by linarith
    have hb : |predError PX f0 f - (f x - f0 x) ^ 2| ≤ 4 * B1 ^ 2 := by
      rw [abs_le]
      constructor <;> nlinarith [ha0, ha4, hxi_le x]
    rw [abs_div, abs_of_pos hden]
    field_simp [hden.ne', hposr.ne']
    nlinarith [hb, ha0, hposr, mul_nonneg (sub_nonneg.mpr hb) (le_of_lt hposr),
      mul_nonneg (by positivity : (0 : ℝ) ≤ 4 * B1 ^ 2) ha0]
  have hratio_bound : ∀ f ∈ F, ∀ ω : Ωrand,
      |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
        (predError PX f0 f - (f (X i j ω) - f0 (X i j ω)) ^ 2) / (predError PX f0 f + r)|
        ≤ 4 * B1 ^ 2 / r := by
    intro f hf ω
    have hNpos : (0 : ℝ) < (n : ℝ) * (m : ℝ) := by
      have h1 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have h2 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      exact mul_pos h1 h2
    have hterm_sum : ∑ i : Fin n, ∑ j : Fin m, (4 * B1 ^ 2 / r)
        = ((n : ℝ) * (m : ℝ)) * (4 * B1 ^ 2 / r) := by
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      ring
    rw [abs_mul, abs_of_pos (inv_pos.mpr hNpos)]
    calc ((n : ℝ) * (m : ℝ))⁻¹ *
          |∑ i : Fin n, ∑ j : Fin m,
            (predError PX f0 f - (f (X i j ω) - f0 (X i j ω)) ^ 2) / (predError PX f0 f + r)|
        ≤ ((n : ℝ) * (m : ℝ))⁻¹ * (∑ i : Fin n, ∑ j : Fin m, (4 * B1 ^ 2 / r)) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt (inv_pos.mpr hNpos))
          calc |∑ i : Fin n, ∑ j : Fin m,
                (predError PX f0 f - (f (X i j ω) - f0 (X i j ω)) ^ 2) / (predError PX f0 f + r)|
              ≤ ∑ i : Fin n, |∑ j : Fin m,
                  (predError PX f0 f - (f (X i j ω) - f0 (X i j ω)) ^ 2) / (predError PX f0 f + r)| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ i : Fin n, ∑ j : Fin m,
                  |(predError PX f0 f - (f (X i j ω) - f0 (X i j ω)) ^ 2) / (predError PX f0 f + r)| :=
                Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
            _ ≤ ∑ i : Fin n, ∑ j : Fin m, (4 * B1 ^ 2 / r) :=
                Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm_le f hf (X i j ω)))
      _ = 4 * B1 ^ 2 / r := by
          rw [hterm_sum]
          field_simp [hN, hposr.ne'] <;> ring
  have hTalagrand : 1 - Real.exp (-t) ≤ P.real {ω | ∀ f ∈ F,
        |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          (predError PX f0 f - (f (X i j ω) - f0 (X i j ω)) ^ 2) / (predError PX f0 f + r)| ≤ D} := by
    by_cases hF0 : F = ∅
    · have hset : {ω : Ωrand | ∀ f ∈ F,
          |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
            (predError PX f0 f - (f (X i j ω) - f0 (X i j ω)) ^ 2) / (predError PX f0 f + r)| ≤ D} = Set.univ := by
        ext ω
        simp [hF0]
      have huniv : P.real (Set.univ : Set Ωrand) = 1 := by
        show (P Set.univ).toReal = 1
        rw [measure_univ, ENNReal.toReal_one]
      rw [hset, huniv]
      linarith [Real.exp_pos (-t)]
    · have hFne : F.Nonempty := Set.nonempty_iff_ne_empty.mpr hF0
      have hExtD : 1 - Real.exp (-t) ≤ P.real {ω : Ωrand | ⨆ f : ↥F,
          |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
            (predError PX f0 f.val - (f.val (X i j ω) - f0 (X i j ω)) ^ 2) / (predError PX f0 f.val + r)| ≤ D} := by
          let Er : ℝ := sSup {v : ℝ | ∃ Fs : Finset (Ωs → ℝ), (Fs : Set (Ωs → ℝ)) ⊆ F ∧
            v = ∫ ω, sSup ((fun f : Ωs → ℝ =>
              |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
                (predError PX f0 f - (f (X i j ω) - f0 (X i j ω)) ^ 2) / (predError PX f0 f + r)|)
              '' (Fs : Set (Ωs → ℝ))) ∂P}
          have hEbound : Er ≤ 80 * B1 * phi r / r := hpeel
          have hBD : 2 * Er + Real.sqrt (8 * (B1 ^ 2 / r) * t / (((n * m : ℕ) : ℝ)))
              + 35 * (4 * B1 ^ 2 / r) * t / (((n * m : ℕ) : ℝ)) ≤ D := by
            have h2 : 2 * Er ≤ 160 * B1 * phi r / r := by
              have hEr := hEbound
              rw [le_div_iff₀ hposr] at hEr ⊢
              nlinarith [hEr]
            rw [hD, ← hbracket]
            linarith [h2]
          have hExt : 1 - Real.exp (-t) ≤ P.real {ω : Ωrand | ⨆ f : ↥F,
              |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
                (predError PX f0 f.val - (f.val (X i j ω) - f0 (X i j ω)) ^ 2) / (predError PX f0 f.val + r)|
              ≤ 2 * Er + Real.sqrt (8 * (B1 ^ 2 / r) * t / (((n * m : ℕ) : ℝ)))
                + 35 * (4 * B1 ^ 2 / r) * t / (((n * m : ℕ) : ℝ))} := by
            let e : Fin (n * m) ≃ Fin n × Fin m := (finProdFinEquiv (m := n) (n := m)).symm
            let W : Fin (n * m) → ↥F → Ωrand → ℝ := fun k f ω =>
              (predError PX f0 f.val - (f.val (X (e k).1 (e k).2 ω) - f0 (X (e k).1 (e k).2 ω)) ^ 2) / (predError PX f0 f.val + r)
            have hWbd : ∀ (k : Fin (n * m)) (f : ↥F) (ω : Ωrand), |W k f ω| ≤ 4 * B1 ^ 2 / r :=
              fun k f ω => hterm_le f.val f.property (X (e k).1 (e k).2 ω)
            have hWmeas : ∀ (i : Fin (n * m)) (f : ↥F), Measurable (W i f) := by
              intro i f
              have hx : Measurable (fun ω : Ωrand => f.val (X (e i).1 (e i).2 ω)) :=
                (hF_meas f.val f.property).comp (hX_meas (e i))
              have hy : Measurable (fun ω : Ωrand => f0 (X (e i).1 (e i).2 ω)) :=
                hf0_meas.comp (hX_meas (e i))
              have hz2 : Measurable (fun ω : Ωrand => (f.val (X (e i).1 (e i).2 ω) - f0 (X (e i).1 (e i).2 ω)) ^ 2) := by
                simpa only [pow_two] using (hx.sub hy).mul (hx.sub hy)
              exact ((measurable_const : Measurable (fun _ : Ωrand => predError PX f0 f.val)).sub hz2).div
                (measurable_const : Measurable (fun _ : Ωrand => predError PX f0 f.val + r))
            have hcenter : ∀ (i : Fin (n * m)) (f : ↥F), ∫ ω, W i f ω ∂P = 0 := by
              intro i f
              have hPuniv : P.real (Set.univ : Set Ωrand) = 1 := by
                show (P Set.univ).toReal = 1
                rw [measure_univ, ENNReal.toReal_one]
              have hξint : Integrable (fun x : Ωs => (f.val x - f0 x) ^ 2) PX := hF_int f.val f.property
              have hξae : AEStronglyMeasurable (fun x : Ωs => (f.val x - f0 x) ^ 2) (Measure.map (X (e i).1 (e i).2) P) := by
                rw [hX_law (e i)]; exact hξint.aestronglyMeasurable
              have hmapi : ∫ ω, (f.val (X (e i).1 (e i).2 ω) - f0 (X (e i).1 (e i).2 ω)) ^ 2 ∂P = predError PX f0 f.val := by
                rw [← integral_map (hX_meas (e i)).aemeasurable hξae, hX_law (e i)]
                rfl
              have hcompint : Integrable (fun ω : Ωrand => (f.val (X (e i).1 (e i).2 ω) - f0 (X (e i).1 (e i).2 ω)) ^ 2) P :=
                (integrable_map_measure hξae (hX_meas (e i)).aemeasurable).mp ((hX_law (e i)).symm ▸ hξint)
              have hsub : ∫ ω, (predError PX f0 f.val - (f.val (X (e i).1 (e i).2 ω) - f0 (X (e i).1 (e i).2 ω)) ^ 2) ∂P = 0 := by
                rw [integral_sub (integrable_const _) hcompint, hmapi]
                have hc : ∫ ω, predError PX f0 f.val ∂P = predError PX f0 f.val := by
                  simp only [integral_const, hPuniv, one_smul, smul_eq_mul, mul_one, one_mul]
                rw [hc, sub_self]
              rw [show (fun ω => W i f ω) = (fun ω : Ωrand => (predError PX f0 f.val - (f.val (X (e i).1 (e i).2 ω) - f0 (X (e i).1 (e i).2 ω)) ^ 2) / (predError PX f0 f.val + r)) from rfl,
                integral_div, hsub]
              exact zero_div _
            have hC : (0:ℝ) ≤ 4 * B1 ^ 2 / r := by positivity
            have hint : ∀ (i : Fin (n * m)) (f : ↥F), Integrable (W i f) P := by
              intro i f
              refine Integrable.of_bound (hWmeas i f).aestronglyMeasurable (4 * B1 ^ 2 / r) ?_
              filter_upwards with ω
              rw [Real.norm_eq_abs]
              exact hWbd i f ω
            have hint2 : ∀ (i : Fin (n * m)) (f : ↥F), Integrable (fun ω => W i f ω ^ 2) P := by
              intro i f
              have hmeas2 : AEStronglyMeasurable (fun ω : Ωrand => W i f ω ^ 2) P := by
                have hm : Measurable (fun ω : Ωrand => W i f ω * W i f ω) := (hWmeas i f).mul (hWmeas i f)
                simpa only [pow_two] using hm.aestronglyMeasurable
              refine Integrable.of_bound hmeas2 ((4 * B1 ^ 2 / r) ^ 2) ?_
              filter_upwards with ω
              have hb := abs_le.mp (hWbd i f ω)
              rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
              nlinarith [hb.1, hb.2, hC,
                mul_nonneg (by linarith [hb.2] : (0:ℝ) ≤ 4 * B1 ^ 2 / r - W i f ω)
                  (by linarith [hb.1] : (0:ℝ) ≤ 4 * B1 ^ 2 / r + W i f ω)]
            have hvar : ∀ (i : Fin (n * m)) (f : ↥F), ∫ ω, W i f ω ^ 2 ∂P ≤ B1 ^ 2 / r := by
              intro i f
              have hPuniv : P.real (Set.univ : Set Ωrand) = 1 := by
                show (P Set.univ).toReal = 1
                rw [measure_univ, ENNReal.toReal_one]
              have hξint : Integrable (fun x : Ωs => (f.val x - f0 x) ^ 2) PX := hF_int f.val f.property
              have hξmeas : Measurable (fun x : Ωs => (f.val x - f0 x) ^ 2) := by
                simpa only [pow_two] using ((hF_meas f.val f.property).sub hf0_meas).mul ((hF_meas f.val f.property).sub hf0_meas)
              have hξnn : ∀ x : Ωs, 0 ≤ (f.val x - f0 x) ^ 2 := fun x => sq_nonneg _
              have hξle : ∀ x : Ωs, (f.val x - f0 x) ^ 2 ≤ 4 * B1 ^ 2 := by
                intro y
                have h1 : |f.val y - f0 y| ≤ 2 * B1 := by
                  calc |f.val y - f0 y| = |f.val y + -(f0 y)| := by rw [sub_eq_add_neg]
                    _ ≤ |f.val y| + |-(f0 y)| := abs_add_le _ _
                    _ = |f.val y| + |f0 y| := by rw [abs_neg]
                    _ ≤ B1 + B1 := add_le_add (hF_bound f.val f.property y) (hf0_bound y)
                    _ = 2 * B1 := by ring
                nlinarith [abs_le.mp h1, hB1]
              have ha0 : 0 ≤ predError PX f0 f.val := by
                show 0 ≤ ∫ x, (f.val x - f0 x) ^ 2 ∂PX
                exact integral_nonneg (fun x => sq_nonneg _)
              have ha4 : predError PX f0 f.val ≤ 4 * B1 ^ 2 := by
                show ∫ x, (f.val x - f0 x) ^ 2 ∂PX ≤ 4 * B1 ^ 2
                have hmono := integral_mono hξint (integrable_const (4 * B1 ^ 2)) hξle
                simp only [integral_const, hPXuniv, one_smul, smul_eq_mul, mul_one, one_mul] at hmono
                exact hmono
              have hcoef : |4 * B1 ^ 2 - 2 * predError PX f0 f.val| ≤ 4 * B1 ^ 2 := by
                rw [abs_le]; constructor <;> nlinarith [ha0, ha4]
              have hξbd : ∀ x : Ωs, |(f.val x - f0 x) ^ 2| ≤ 4 * B1 ^ 2 := by
                intro x
                rw [abs_of_nonneg (hξnn x)]
                exact hξle x
              have hpt : ∀ x : Ωs, (predError PX f0 f.val - (f.val x - f0 x) ^ 2) ^ 2
                  ≤ predError PX f0 f.val ^ 2 + (4 * B1 ^ 2 - 2 * predError PX f0 f.val) * ((f.val x - f0 x) ^ 2) := by
                intro x
                have hnn := hξnn x
                have hle := hξle x
                nlinarith [hnn, hle]
              have htermC_int : Integrable (fun x : Ωs => (4 * B1 ^ 2 - 2 * predError PX f0 f.val) * ((f.val x - f0 x) ^ 2)) PX := by
                have hmeas : Measurable (fun x : Ωs => (4 * B1 ^ 2 - 2 * predError PX f0 f.val) * ((f.val x - f0 x) ^ 2)) :=
                  (measurable_const : Measurable (fun _ : Ωs => 4 * B1 ^ 2 - 2 * predError PX f0 f.val)).mul hξmeas
                refine Integrable.of_bound hmeas.aestronglyMeasurable ((4 * B1 ^ 2) * (4 * B1 ^ 2)) ?_
                filter_upwards with x
                rw [Real.norm_eq_abs, abs_mul]
                exact mul_le_mul hcoef (hξbd x) (abs_nonneg _) (by positivity)
              have hint_rhs : Integrable (fun x : Ωs => predError PX f0 f.val ^ 2 + (4 * B1 ^ 2 - 2 * predError PX f0 f.val) * ((f.val x - f0 x) ^ 2)) PX := by
                have hmeas : Measurable (fun x : Ωs => predError PX f0 f.val ^ 2 + (4 * B1 ^ 2 - 2 * predError PX f0 f.val) * ((f.val x - f0 x) ^ 2)) :=
                  (measurable_const : Measurable (fun _ : Ωs => predError PX f0 f.val ^ 2)).add
                    ((measurable_const : Measurable (fun _ : Ωs => 4 * B1 ^ 2 - 2 * predError PX f0 f.val)).mul hξmeas)
                refine Integrable.of_bound hmeas.aestronglyMeasurable (32 * B1 ^ 4) ?_
                filter_upwards with x
                rw [Real.norm_eq_abs]
                have hb1 : predError PX f0 f.val ^ 2 ≤ 16 * B1 ^ 4 := by nlinarith [ha0, ha4]
                have hb2 : |(4 * B1 ^ 2 - 2 * predError PX f0 f.val) * ((f.val x - f0 x) ^ 2)| ≤ 16 * B1 ^ 4 := by
                  rw [abs_mul]
                  calc |4 * B1 ^ 2 - 2 * predError PX f0 f.val| * |(f.val x - f0 x) ^ 2|
                      ≤ (4 * B1 ^ 2) * (4 * B1 ^ 2) := mul_le_mul hcoef (hξbd x) (abs_nonneg _) (by positivity)
                    _ = 16 * B1 ^ 4 := by ring
                calc |predError PX f0 f.val ^ 2 + (4 * B1 ^ 2 - 2 * predError PX f0 f.val) * ((f.val x - f0 x) ^ 2)|
                    ≤ |predError PX f0 f.val ^ 2| + |(4 * B1 ^ 2 - 2 * predError PX f0 f.val) * ((f.val x - f0 x) ^ 2)| := abs_add_le _ _
                  _ = predError PX f0 f.val ^ 2 + |(4 * B1 ^ 2 - 2 * predError PX f0 f.val) * ((f.val x - f0 x) ^ 2)| := by rw [abs_of_nonneg (sq_nonneg _)]
                  _ ≤ 16 * B1 ^ 4 + 16 * B1 ^ 4 := by linarith [hb1, hb2]
                  _ = 32 * B1 ^ 4 := by ring
              have heq : ∫ x, (predError PX f0 f.val ^ 2 + (4 * B1 ^ 2 - 2 * predError PX f0 f.val) * ((f.val x - f0 x) ^ 2)) ∂PX
                  = 4 * B1 ^ 2 * predError PX f0 f.val - predError PX f0 f.val ^ 2 := by
                rw [integral_add (integrable_const (predError PX f0 f.val ^ 2)) htermC_int, integral_const_mul]
                simp only [integral_const, predError, hPXuniv, one_smul, smul_eq_mul, mul_one, one_mul]
                ring
              have hnum : ∫ x, (predError PX f0 f.val - (f.val x - f0 x) ^ 2) ^ 2 ∂PX ≤ 4 * B1 ^ 2 * predError PX f0 f.val := by
                have hmono := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => sq_nonneg (predError PX f0 f.val - (f.val x - f0 x) ^ 2))) hint_rhs (Filter.Eventually.of_forall hpt)
                linarith [hmono, heq, sq_nonneg (predError PX f0 f.val)]
              have hW2 : ∫ ω, W i f ω ^ 2 ∂P
                  = (∫ x, (predError PX f0 f.val - (f.val x - f0 x) ^ 2) ^ 2 ∂PX) / (predError PX f0 f.val + r) ^ 2 := by
                have h1 : ∀ ω : Ωrand, W i f ω ^ 2
                    = (predError PX f0 f.val - (f.val (X (e i).1 (e i).2 ω) - f0 (X (e i).1 (e i).2 ω)) ^ 2) ^ 2 / (predError PX f0 f.val + r) ^ 2 := by
                  intro ω
                  rw [show W i f ω = (predError PX f0 f.val - (f.val (X (e i).1 (e i).2 ω) - f0 (X (e i).1 (e i).2 ω)) ^ 2) / (predError PX f0 f.val + r) from rfl, div_pow]
                rw [integral_congr_ae (Filter.Eventually.of_forall h1), integral_div]
                congr 1
                have hξ2meas : Measurable (fun x : Ωs => (predError PX f0 f.val - (f.val x - f0 x) ^ 2) ^ 2) := by
                  have hsub : Measurable (fun x : Ωs => predError PX f0 f.val - (f.val x - f0 x) ^ 2) :=
                    (measurable_const : Measurable (fun _ : Ωs => predError PX f0 f.val)).sub hξmeas
                  simpa only [pow_two] using hsub.mul hsub
                have hξ2ae : AEStronglyMeasurable (fun x : Ωs => (predError PX f0 f.val - (f.val x - f0 x) ^ 2) ^ 2) (Measure.map (X (e i).1 (e i).2) P) := by
                  rw [hX_law (e i)]; exact hξ2meas.aestronglyMeasurable
                rw [← integral_map (hX_meas (e i)).aemeasurable hξ2ae, hX_law (e i)]
              rw [hW2]
              have hden2 : (0:ℝ) < (predError PX f0 f.val + r) ^ 2 := by
                have hpos : 0 < predError PX f0 f.val + r := by linarith [ha0, hposr]
                positivity
              rw [div_le_iff₀ hden2, show (B1 ^ 2 / r) * (predError PX f0 f.val + r) ^ 2 = B1 ^ 2 * (predError PX f0 f.val + r) ^ 2 / r by ring_nf, le_div_iff₀ hposr]
              nlinarith [hnum, ha0, hposr, sq_nonneg (B1 * (predError PX f0 f.val - r))]
            have hnm : 0 < n * m := Nat.mul_pos hn hm
            have hWind : iIndepFun (fun (i : Fin (n * m)) (ω : Ωrand) (f : ↥F) => W i f ω) P := by
              have hX_indep' : iIndepFun (fun i : Fin (n * m) => X (e i).1 (e i).2) P :=
                iIndepFun.precomp e.injective hX_indep
              have hg : ∀ (i : Fin (n * m)), Measurable (fun (x : Ωs) (f : ↥F) =>
                  (predError PX f0 f.val - (f.val x - f0 x) ^ 2) / (predError PX f0 f.val + r)) := by
                intro i
                rw [measurable_pi_iff]
                intro f
                have h1 : Measurable (fun x : Ωs => f.val x) := hF_meas f.val f.property
                have hz2 : Measurable (fun x : Ωs => (f.val x - f0 x) ^ 2) := by
                  simpa only [pow_two] using (h1.sub hf0_meas).mul (h1.sub hf0_meas)
                exact ((measurable_const : Measurable (fun _ : Ωs => predError PX f0 f.val)).sub hz2).div
                  (measurable_const : Measurable (fun _ : Ωs => predError PX f0 f.val + r))
              have hcomp := iIndepFun.comp hX_indep' (fun (i : Fin (n * m)) (x : Ωs) (f : ↥F) =>
                  (predError PX f0 f.val - (f.val x - f0 x) ^ 2) / (predError PX f0 f.val + r)) hg
              exact hcomp
            have hsepW : ∃ s : Set ↥F, s.Countable ∧ ∀ ω,
                (⨆ f : ↥F, |(1 / ((n * m : ℕ) : ℝ)) * ∑ i, W i f ω|) ≤
                  ⨆ f : s, |(1 / ((n * m : ℕ) : ℝ)) * ∑ i, W i f.1 ω| := by
              exact normalized_squared_process_separable PX F f0 B1 hB1 hf0_meas hF_meas
                hf0_bound hF_bound hF_int hF_sep (n * m)
                (fun i ω => X (e i).1 (e i).2 ω) r hposr
            have hexternal := PaperProofTasks.job_paper_383d12cb48d74c8f98648c6beef78bb3.Statlib.Imported.paper_383d12cb48d74c8f98648c6beef78bb3 hnm W hWmeas hWind (4 * B1 ^ 2 / r) (B1 ^ 2 / r) t hWbd hC hint hcenter hint2 hvar (by positivity : (0:ℝ) ≤ B1 ^ 2 / r) hsepW
            refine le_trans hexternal (ENNReal.toReal_mono (measure_ne_top P _) (measure_mono ?_))
            intro ω hω
            simp only [Set.mem_setOf_eq] at hω ⊢
            have havg : ∀ (f : ↥F) (ω : Ωrand),
                |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
                  (predError PX f0 f.val - (f.val (X i j ω) - f0 (X i j ω)) ^ 2) / (predError PX f0 f.val + r)|
                = |(1 / ↑(n * m)) * ∑ k : Fin (n * m), W k f ω| := by
              intro f ω
              congr 1
              have hsum : ∑ k : Fin (n * m), W k f ω
                  = ∑ i : Fin n, ∑ j : Fin m, (predError PX f0 f.val - (f.val (X i j ω) - f0 (X i j ω)) ^ 2) / (predError PX f0 f.val + r) := by
                have h1 : ∑ k : Fin (n * m), W k f ω = ∑ p : Fin n × Fin m, W (e.symm p) f ω := by
                  rw [show ∑ k : Fin (n * m), W k f ω = ∑ k : Fin (n * m), W (e.symm (e k)) f ω from by
                    apply Finset.sum_congr rfl
                    intro k _
                    rw [Equiv.symm_apply_apply]]
                  exact Equiv.sum_comp e (fun p => W (e.symm p) f ω)
                rw [h1, Fintype.sum_prod_type]
                apply Finset.sum_congr rfl
                intro i _
                apply Finset.sum_congr rfl
                intro j _
                simp only [W, Equiv.apply_symm_apply]
              rw [hsum, show (1 : ℝ) / ↑(n * m) = ((n : ℝ) * (m : ℝ))⁻¹ from by
                rw [Nat.cast_mul, one_div]]
            rw [show (⨆ f : ↥F, |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m, (predError PX f0 f.val - (f.val (X i j ω) - f0 (X i j ω)) ^ 2) / (predError PX f0 f.val + r)|)
                = (⨆ f : ↥F, |(1 / ↑(n * m)) * ∑ k : Fin (n * m), W k f ω|) from iSup_congr (fun f => havg f ω)]
            exact le_trans hω (by
              have hkey : PaperProofTasks.job_paper_383d12cb48d74c8f98648c6beef78bb3.Statlib.Imported.expectedSup P (fun f ω' => |1 / ↑(n * m) * ∑ i, W i f ω'|) ≤ Er := by
                classical
                rw [show PaperProofTasks.job_paper_383d12cb48d74c8f98648c6beef78bb3.Statlib.Imported.expectedSup P (fun f ω' => |1 / ↑(n * m) * ∑ i, W i f ω'|) = sSup (Set.range (fun s : {s : Finset ↥F // s.Nonempty} => ∫ ω, s.1.sup' s.2 (fun f => |1 / ↑(n * m) * ∑ i, W i f ω|) ∂P)) from rfl]
                have hbddS : BddAbove {v : ℝ | ∃ Fs : Finset (Ωs → ℝ), (Fs : Set (Ωs → ℝ)) ⊆ F ∧
                    v = ∫ ω, sSup ((fun f : Ωs → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m, (predError PX f0 f - (f (X i j ω) - f0 (X i j ω)) ^ 2) / (predError PX f0 f + r)|) '' (Fs : Set (Ωs → ℝ))) ∂P} := by
                  refine ⟨4 * B1 ^ 2 / r, ?_⟩
                  rintro v ⟨Fs, hFs, rfl⟩
                  have hbnd_pt : ∀ ω, sSup ((fun f : Ωs → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m, (predError PX f0 f - (f (X i j ω) - f0 (X i j ω)) ^ 2) / (predError PX f0 f + r)|) '' (Fs : Set (Ωs → ℝ))) ≤ 4 * B1 ^ 2 / r := by
                    intro ω
                    exact Real.sSup_le (fun x hx => by rcases hx with ⟨f, hf, rfl⟩; exact hratio_bound f (hFs hf) ω) (by positivity)
                  have hnn_pt : ∀ ω, 0 ≤ sSup ((fun f : Ωs → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m, (predError PX f0 f - (f (X i j ω) - f0 (X i j ω)) ^ 2) / (predError PX f0 f + r)|) '' (Fs : Set (Ωs → ℝ))) := by
                    intro ω
                    rcases Finset.eq_empty_or_nonempty Fs with hE | hne
                    · rw [hE, Finset.coe_empty, Set.image_empty, Real.sSup_empty]
                    · obtain ⟨b, hb⟩ := hne
                      exact le_trans (abs_nonneg _) (le_csSup ⟨4 * B1 ^ 2 / r, fun x hx => by rcases hx with ⟨f, hf, rfl⟩; exact hratio_bound f (hFs hf) ω⟩ ⟨b, hb, rfl⟩)
                  calc ∫ ω, sSup ((fun f : Ωs → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m, (predError PX f0 f - (f (X i j ω) - f0 (X i j ω)) ^ 2) / (predError PX f0 f + r)|) '' (Fs : Set (Ωs → ℝ))) ∂P
                      ≤ ∫ ω, (4 * B1 ^ 2 / r) ∂P := integral_mono_of_nonneg (Filter.Eventually.of_forall hnn_pt) (integrable_const _) (Filter.Eventually.of_forall hbnd_pt)
                    _ = 4 * B1 ^ 2 / r := by
                        rw [integral_const]
                        have hPuniv : P.real (Set.univ : Set Ωrand) = 1 := by
                          show (P Set.univ).toReal = 1
                          rw [measure_univ, ENNReal.toReal_one]
                        rw [hPuniv, one_smul]
                have hsup'_eq : ∀ (t : Finset ↥F) (ht : t.Nonempty) (g : ↥F → ℝ), t.sup' ht g = sSup (g '' ↑t) := by
                  intro t ht g
                  refine le_antisymm ?_ ?_
                  · rw [Finset.sup'_le_iff]
                    intro b hb
                    exact le_csSup ⟨t.sup' ht g, fun x hx => by rcases hx with ⟨c, hc, rfl⟩; exact Finset.le_sup' g hc⟩ ⟨b, hb, rfl⟩
                  · apply csSup_le
                    · obtain ⟨b, hb⟩ := ht; exact ⟨g b, b, hb, rfl⟩
                    · rintro x ⟨b, hb, rfl⟩; exact Finset.le_sup' g hb
                rcases hFne with ⟨g0, hg0⟩
                refine csSup_le ⟨_, ⟨⟨{⟨g0, hg0⟩}, by simp⟩, rfl⟩⟩ ?_
                rintro y ⟨⟨Fs, hne⟩, rfl⟩
                refine le_csSup hbddS ⟨Fs.image Subtype.val, ?_, ?_⟩
                · intro x hx
                  rw [Finset.mem_coe, Finset.mem_image] at hx
                  obtain ⟨f, -, hfx⟩ := hx
                  rw [← hfx]
                  exact f.property
                · rw [show (fun s : {s : Finset ↥F // s.Nonempty} => ∫ ω, s.1.sup' s.2 (fun f => |1 / ↑(n * m) * ∑ i, W i f ω|) ∂P) ⟨Fs, hne⟩ = ∫ ω, Fs.sup' hne (fun f => |1 / ↑(n * m) * ∑ i, W i f ω|) ∂P from rfl]
                  apply integral_congr_ae
                  filter_upwards with ω
                  rw [hsup'_eq Fs hne (fun f : ↥F => |1 / ↑(n * m) * ∑ i, W i f ω|)]
                  congr 1
                  rw [Finset.coe_image, Set.image_image]
                  congr 1
                  funext f
                  exact (havg f ω).symm
              linarith [hkey])
          exact le_trans hExt (ENNReal.toReal_mono (measure_ne_top P _) (measure_mono (fun ω hω => le_trans hω hBD)))
      have hsub : {ω : Ωrand | ⨆ f : ↥F,
            |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
              (predError PX f0 f.val - (f.val (X i j ω) - f0 (X i j ω)) ^ 2) / (predError PX f0 f.val + r)| ≤ D}
          ⊆ {ω : Ωrand | ∀ f ∈ F,
            |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
              (predError PX f0 f - (f (X i j ω) - f0 (X i j ω)) ^ 2) / (predError PX f0 f + r)| ≤ D} := by
        intro ω hω f hf
        have hbdd : BddAbove (Set.range (fun g : ↥F =>
            |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
              (predError PX f0 g.val - (g.val (X i j ω) - f0 (X i j ω)) ^ 2) / (predError PX f0 g.val + r)|)) :=
          ⟨4 * B1 ^ 2 / r, by rintro _ ⟨g, rfl⟩; exact hratio_bound g.val g.property ω⟩
        exact le_trans (le_ciSup hbdd ⟨f, hf⟩) hω
      calc 1 - Real.exp (-t)
          ≤ P.real {ω : Ωrand | ⨆ f : ↥F,
              |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
                (predError PX f0 f.val - (f.val (X i j ω) - f0 (X i j ω)) ^ 2) / (predError PX f0 f.val + r)| ≤ D} := hExtD
        _ ≤ P.real {ω : Ωrand | ∀ f ∈ F,
              |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
                (predError PX f0 f - (f (X i j ω) - f0 (X i j ω)) ^ 2) / (predError PX f0 f + r)| ≤ D} :=
            ENNReal.toReal_mono (measure_ne_top P _) (measure_mono hsub)
  have hmain : 1 - Real.exp (-t) ≤ (P {ω | ∀ f ∈ F, |predError PX f0 f - empSqDisc X f0 ω f| ≤ D * (predError PX f0 f + r)}).toReal :=
    le_trans hTalagrand hmono
  calc ENNReal.ofReal (1 - Real.exp (-t))
      ≤ ENNReal.ofReal ((P {ω | ∀ f ∈ F, |predError PX f0 f - empSqDisc X f0 ω f| ≤ D * (predError PX f0 f + r)}).toReal) := ENNReal.ofReal_le_ofReal hmain
    _ = P {ω | ∀ f ∈ F, |predError PX f0 f - empSqDisc X f0 ω f| ≤ D * (predError PX f0 f + r)} := MeasureTheory.ofReal_measureReal hne
  /- @proof-region region.target-node.session.3326edc4ebe89b08 end -/

end

end Statlib.Imported

