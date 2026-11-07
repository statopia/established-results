import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Lean
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.Vocabulary
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.Base
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.ExternalNodes.Node_de79d78c6a944a25a489

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
theorem statopia_math_node_1420745056_d05a4859 : ∀ (k n : ℕ) (hk : 0 < k) (hn : 0 < n)
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μX : Fin k → ℝ) (X F : Fin n → Ω → (Fin k → ℝ))
    (hF_meas : ∀ i : Fin n, Measurable (F i))
    (hF_gauss : ∀ i : Fin n, IsGaussian (Measure.map (F i) P))
    (hF_mean : ∀ (i : Fin n) (j : Fin k), ∫ ω, F i ω j ∂P = μX j)
    (hcov_match : ∀ (i : Fin n) (j l : Fin k),
      ∫ ω, (F i ω j - μX j) * (F i ω l - μX l) ∂P
        = ∫ ω, (X i ω j - μX j) * (X i ω l - μX l) ∂P)
    (hX_int : ∀ (i : Fin n) (j l : Fin k),
      Integrable (fun ω => (X i ω j - μX j) * (X i ω l - μX l)) P)
    (hF_int : ∀ (i : Fin n) (j l : Fin k),
      Integrable (fun ω => (F i ω j - μX j) * (F i ω l - μX l)) P),
    ∀ i : Fin n,
      Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector P
        (fun ω j => F i ω j - μX j)
        (PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported.covX
          P μX X i) := by
  /- @proof-region region.target-node.session.5f8346e6ce316497 begin -/
  intro k n hk hn Ω hΩ P hP μX X F hF_meas hF_gauss hF_mean hF_cov hX_int hF_int i
  constructor
  case measurable => exact (hF_meas i).sub measurable_const
  case integrable_exp =>
    intro u
    let L : (Fin k → ℝ) →L[ℝ] ℝ :=
      ∑ j : Fin k, u j • (ContinuousLinearMap.proj j : (Fin k → ℝ) →L[ℝ] ℝ)
    let Z : Ω → ℝ := fun ω => ∑ j, u j * F i ω j
    let c : ℝ := ∑ j, u j * μX j
    have hL_apply : ∀ x : Fin k → ℝ, L x = ∑ j, u j * x j := by
      intro x
      simp [L]
    have hZ_meas : Measurable Z := by
      measurability
    have hZ_gauss : IsGaussian (Measure.map Z P) := by
      haveI : IsGaussian (Measure.map (F i) P) := hF_gauss i
      have hmap : Measure.map Z P = Measure.map L (Measure.map (F i) P) := by
        have hcomp : (L ∘ F i) = Z := by
          funext ω
          simp [Z, hL_apply]
        rw [← hcomp]
        exact (Measure.map_map (L.continuous.measurable) (hF_meas i)).symm
      rw [hmap]
      exact ProbabilityTheory.isGaussian_map L
    haveI : IsGaussian (Measure.map Z P) := hZ_gauss
    obtain ⟨C, hCpos, hCintZ⟩ :=
      ProbabilityTheory.IsGaussian.exists_integrable_exp_sq (Measure.map Z P)
    have hExpBound : ∀ x : ℝ,
        Real.exp x ≤ Real.exp (1 / (4 * C)) * Real.exp (C * ‖x‖ ^ 2) := by
      intro x
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hnorm : ‖x‖ ^ 2 = x ^ 2 := by
        simp [Real.norm_eq_abs, sq_abs]
      rw [hnorm]
      field_simp [hCpos.ne']
      nlinarith [sq_nonneg (2 * C * x - 1)]
    have hExpIntZ : Integrable (fun x : ℝ => Real.exp x) (Measure.map Z P) := by
      refine (hCintZ.const_mul (Real.exp (1 / (4 * C)))).mono ?_ ?_
      · exact Real.continuous_exp.aestronglyMeasurable
      · filter_upwards with x
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _),
          Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))]
        exact hExpBound x
    have hExpIntP : Integrable (fun ω => Real.exp (Z ω)) P :=
      hExpIntZ.comp_measurable hZ_meas
    have htarget_eq : (fun ω => Real.exp (∑ j, u j * (F i ω j - μX j)))
        = (fun ω => Real.exp (-c) * Real.exp (Z ω)) := by
      funext ω
      have hsum : ∑ j, u j * (F i ω j - μX j) = Z ω - c := by
        simp [Z, c, Finset.sum_sub_distrib, mul_sub]
      rw [hsum, sub_eq_add_neg, Real.exp_add]
      ring
    rw [htarget_eq]
    exact hExpIntP.const_mul (Real.exp (-c))
  case mgf_eq =>
    intro u
    let L : (Fin k → ℝ) →L[ℝ] ℝ :=
      ∑ j : Fin k, u j • (ContinuousLinearMap.proj j : (Fin k → ℝ) →L[ℝ] ℝ)
    let Z : Ω → ℝ := fun ω => ∑ j, u j * F i ω j
    let c : ℝ := ∑ j, u j * μX j
    let Q : ℝ := ∑ a : Fin k, ∑ b : Fin k,
      u a * PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported.covX
        P μX X i a b * u b
    have hL_apply : ∀ x : Fin k → ℝ, L x = ∑ j, u j * x j := by
      intro x
      simp [L]
    have hZ_meas : Measurable Z := by
      measurability
    have hmap : Measure.map Z P = Measure.map L (Measure.map (F i) P) := by
      have hcomp : (L ∘ F i) = Z := by
        funext ω
        simp [Z, hL_apply]
      rw [← hcomp]
      exact (Measure.map_map (L.continuous.measurable) (hF_meas i)).symm
    have hZ_gauss : IsGaussian (Measure.map Z P) := by
      haveI : IsGaussian (Measure.map (F i) P) := hF_gauss i
      rw [hmap]
      exact ProbabilityTheory.isGaussian_map L
    haveI : IsGaussian (Measure.map Z P) := hZ_gauss
    let m : ℝ := ∫ x, id x ∂(Measure.map Z P)
    let v : NNReal := Var[id; Measure.map Z P].toNNReal
    have hZ_eq : Measure.map Z P = gaussianReal m v :=
      ProbabilityTheory.IsGaussian.eq_gaussianReal _ hZ_gauss
    have hmgfZ : mgf Z P 1 = Real.exp (m * 1 + (v : ℝ) * 1 ^ 2 / 2) :=
      ProbabilityTheory.mgf_gaussianReal hZ_eq 1
    have hmgfZ' : ∫ ω, Real.exp (Z ω) ∂P = Real.exp (m + (v : ℝ) / 2) := by
      simpa [mgf, one_mul, pow_two] using hmgfZ
    have hmean_coord : ∀ j : Fin k,
        (∫ y : Fin k → ℝ, y ∂(Measure.map (F i) P)) j = μX j := by
      intro j
      haveI : IsGaussian (Measure.map (F i) P) := hF_gauss i
      have hproj := ProbabilityTheory.IsGaussian.integral_dual
        (μ := Measure.map (F i) P)
        (L := (ContinuousLinearMap.proj j : (Fin k → ℝ) →L[ℝ] ℝ))
      change ((ContinuousLinearMap.proj j : (Fin k → ℝ) →L[ℝ] ℝ)
        (∫ y : Fin k → ℝ, y ∂(Measure.map (F i) P))) = μX j
      rw [← hproj]
      change ∫ y : Fin k → ℝ, y j ∂(Measure.map (F i) P) = μX j
      rw [MeasureTheory.integral_map (μ := P) (φ := F i)
        (f := fun y : Fin k → ℝ => y j) (hF_meas i).aemeasurable
        (measurable_pi_apply j).aestronglyMeasurable]
      exact hF_mean i j
    have hm : m = c := by
      haveI : IsGaussian (Measure.map (F i) P) := hF_gauss i
      dsimp [m, c]
      calc
        ∫ x, id x ∂(Measure.map Z P)
            = ∫ x, id x ∂(Measure.map L (Measure.map (F i) P)) := by rw [hmap]
        _ = ∫ y, L y ∂(Measure.map (F i) P) := by
              simpa using (MeasureTheory.integral_map (μ := Measure.map (F i) P) (φ := L)
                (f := fun x : ℝ => x) L.continuous.measurable.aemeasurable
                measurable_id.aestronglyMeasurable)
        _ = L (∫ y, y ∂(Measure.map (F i) P)) := by
              exact ProbabilityTheory.IsGaussian.integral_dual
                (μ := Measure.map (F i) P) L
        _ = ∑ j, u j * (∫ y, y ∂(Measure.map (F i) P)) j := by
              rw [hL_apply]
        _ = ∑ j, u j * μX j := by
              apply Finset.sum_congr rfl
              intro j _
              rw [hmean_coord j]
        _ = c := by rfl
    have hVarEq : Var[id; Measure.map Z P] = Q := by
      rw [ProbabilityTheory.variance_eq_integral (measurable_id.aemeasurable)]
      rw [show (∫ x, id x ∂(Measure.map Z P)) = c from hm]
      simp only [id_eq]
      rw [MeasureTheory.integral_map (μ := P) (φ := Z)
        (f := fun x : ℝ => (x - c) ^ 2) hZ_meas.aemeasurable (by fun_prop)]
      dsimp [Q]
      have hZc : ∀ ω, Z ω - c = ∑ j, u j * (F i ω j - μX j) := by
        intro ω
        simp [Z, c, Finset.sum_sub_distrib, mul_sub]
      simp_rw [hZc]
      have hsquare : ∀ ω,
          (∑ j, u j * (F i ω j - μX j)) ^ 2
            = ∑ a : Fin k, ∑ b : Fin k,
                (u a * (F i ω a - μX a)) * (u b * (F i ω b - μX b)) := by
        intro ω
        simp [sq, Finset.sum_mul_sum]
      simp_rw [hsquare]
      have hInt_term : ∀ a b : Fin k,
          Integrable (fun ω => (u a * (F i ω a - μX a)) * (u b * (F i ω b - μX b))) P := by
        intro a b
        have h := (hF_int i a b).const_mul (u a * u b)
        simpa [mul_assoc, mul_comm, mul_left_comm] using h
      have hInt_inner : ∀ a : Fin k,
          Integrable (fun ω => ∑ b : Fin k,
            (u a * (F i ω a - μX a)) * (u b * (F i ω b - μX b))) P := by
        intro a
        classical
        refine Finset.induction_on (Finset.univ : Finset (Fin k)) ?_ ?_
        · simp
        · intro b s hb ih
          simp_rw [Finset.sum_insert hb]
          exact (hInt_term a b).add ih
      rw [MeasureTheory.integral_finset_sum Finset.univ]
      · apply Finset.sum_congr rfl
        intro a _
        rw [MeasureTheory.integral_finset_sum Finset.univ]
        · apply Finset.sum_congr rfl
          intro b _
          have hterm : ∫ ω, (u a * (F i ω a - μX a)) * (u b * (F i ω b - μX b)) ∂P
              = (u a * u b) * ∫ ω, (F i ω a - μX a) * (F i ω b - μX b) ∂P := by
            rw [show (fun ω => (u a * (F i ω a - μX a)) * (u b * (F i ω b - μX b)))
                  = (fun ω => (u a * u b) * ((F i ω a - μX a) * (F i ω b - μX b))) by
                funext ω
                ring]
            simpa [smul_eq_mul] using
              (MeasureTheory.integral_const_mul (u a * u b)
                (fun ω => (F i ω a - μX a) * (F i ω b - μX b)))
          rw [hterm, hF_cov i a b]
          simp [PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported.covX]
          ring
        · intro b _
          exact hInt_term a b
      · intro a _
        exact hInt_inner a
    have hQ_nonneg : 0 ≤ Q := by
      have hVar_nonneg : 0 ≤ Var[id; Measure.map Z P] := by
        rw [ProbabilityTheory.variance_eq_integral (measurable_id.aemeasurable)]
        exact integral_nonneg (fun x => sq_nonneg _)
      rw [hVarEq] at hVar_nonneg
      exact hVar_nonneg
    have hv : (v : ℝ) = Q := by
      dsimp [v]
      rw [hVarEq, max_eq_left hQ_nonneg]
    obtain ⟨C, hCpos, hCintZ⟩ :=
      ProbabilityTheory.IsGaussian.exists_integrable_exp_sq (Measure.map Z P)
    have hExpBound : ∀ x : ℝ,
        Real.exp x ≤ Real.exp (1 / (4 * C)) * Real.exp (C * ‖x‖ ^ 2) := by
      intro x
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hnorm : ‖x‖ ^ 2 = x ^ 2 := by
        simp [Real.norm_eq_abs, sq_abs]
      rw [hnorm]
      field_simp [hCpos.ne']
      nlinarith [sq_nonneg (2 * C * x - 1)]
    have hExpIntZ : Integrable (fun x : ℝ => Real.exp x) (Measure.map Z P) := by
      refine (hCintZ.const_mul (Real.exp (1 / (4 * C)))).mono ?_ ?_
      · exact Real.continuous_exp.aestronglyMeasurable
      · filter_upwards with x
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _),
          Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))]
        exact hExpBound x
    have hExpIntP : Integrable (fun ω => Real.exp (Z ω)) P :=
      hExpIntZ.comp_measurable hZ_meas
    have htarget_eq : (fun ω => Real.exp (∑ j, u j * (F i ω j - μX j)))
        = (fun ω => Real.exp (-c) * Real.exp (Z ω)) := by
      funext ω
      have hsum : ∑ j, u j * (F i ω j - μX j) = Z ω - c := by
        simp [Z, c, Finset.sum_sub_distrib, mul_sub]
      rw [hsum, sub_eq_add_neg, Real.exp_add]
      ring
    rw [htarget_eq]
    calc
      ∫ ω, Real.exp (-c) * Real.exp (Z ω) ∂P
          = Real.exp (-c) * ∫ ω, Real.exp (Z ω) ∂P := by
              simpa [smul_eq_mul] using
                (MeasureTheory.integral_const_mul (Real.exp (-c))
                  (fun ω => Real.exp (Z ω)))
      _ = Real.exp (-c) * Real.exp (m + (v : ℝ) / 2) := by rw [hmgfZ']
      _ = Real.exp (Q / 2) := by
            rw [hm, hv, ← Real.exp_add]
            congr 1
            ring
  /- @proof-region region.target-node.session.5f8346e6ce316497 end -/

end Statlib.Imported

end

