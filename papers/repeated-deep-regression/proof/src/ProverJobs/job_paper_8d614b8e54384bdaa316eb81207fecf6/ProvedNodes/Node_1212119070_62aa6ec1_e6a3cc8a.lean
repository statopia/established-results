import Lean
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.Vocabulary
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.Base
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.ProvedNodes.Node_2785853616_1d52636d_2cae0d02
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.ProvedNodes.Node_2829917225_53cae5d1_9b597699

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
theorem statopia_math_node_1212119070_62aa6ec1 : ∀ (d : ℕ) (hd : 0 < d) (Ωs : Set (Fin d → ℝ)) (hΩs : Ωs ⊆ unitCube d)
    (PX : Measure ↥Ωs) (hPX_prob : IsProbabilityMeasure PX)
    (hPX_ac : PX ≪ Measure.comap Subtype.val (volume : Measure (Fin d → ℝ)))
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (Ωrand : Type*) [MeasurableSpace Ωrand] (P : Measure Ωrand)
    (hP_prob : IsProbabilityMeasure P)
    (f0 : ↥Ωs → ℝ) (F : Set (↥Ωs → ℝ))
    (fhat : Ωrand → ↥Ωs → ℝ)
    (Z : Fin n → Ωrand → ↥Ωs → ℝ)
    (X : Fin n → Fin m → Ωrand → ↥Ωs)
    (eps : Fin n → Fin m → Ωrand → ℝ)
    (sigma : Fin n → Fin m → Ωrand → ℝ)
    (B1 B2 B3 : ℝ) (hB1 : 0 < B1)
    (hB2_nn : 0 ≤ B2) (hB2_ne : B2 ≠ 0) (hB3_nn : 0 ≤ B3) (hB3_ne : B3 ≠ 0)
    (phi : ℝ → ℝ) (rstar : ℝ)
    (hZ_meas : ∀ i : Fin n, Measurable (Z i))
    (hZ_iid_law : ∀ i i' : Fin n, IdentDistrib (Z i) (Z i') P P)
    (hZ_indep : iIndepFun Z P)
    (hX_meas : ∀ p : Fin n × Fin m, Measurable (X p.1 p.2))
    (hX_law : ∀ p : Fin n × Fin m, Measure.map (X p.1 p.2) P = PX)
    (hX_indep : iIndepFun (fun p : Fin n × Fin m => X p.1 p.2) P)
    (hZX_indep : IndepFun (fun ω => fun p : Fin n × Fin m => X p.1 p.2 ω)
      (fun ω => fun i : Fin n => Z i ω) P)
    (heps_meas : ∀ p : Fin n × Fin m, Measurable (eps p.1 p.2))
    (heps_indep : iIndepFun (fun p : Fin n × Fin m => eps p.1 p.2) P)
    (hsigma_meas : ∀ p : Fin n × Fin m, Measurable (sigma p.1 p.2))
    (hsigma_law : ∀ p : Fin n × Fin m, Measure.map (sigma p.1 p.2) P = rademacherLaw)
    (hsigma_indep : iIndepFun (fun p : Fin n × Fin m => sigma p.1 p.2) P)
    (hsigma_indep_data : IndepFun (fun ω => fun p : Fin n × Fin m => sigma p.1 p.2 ω)
      (fun ω => ((fun p : Fin n × Fin m => X p.1 p.2 ω),
        ((fun i : Fin n => Z i ω),
         (fun p : Fin n × Fin m => eps p.1 p.2 ω)))) P)
    (hZ_int : ∀ (i : Fin n), ∀ᵐ x ∂PX, Integrable (fun ω => Z i ω x) P)
    (hf0_def : ∀ (i : Fin n), ∀ᵐ x ∂PX, f0 x = ∫ ω, Z i ω x ∂P)
    (hf0_bound : ∀ x : ↥Ωs, |f0 x| ≤ B1)
    (hF_bound : ∀ f ∈ F, ∀ x : ↥Ωs, |f x| ≤ B1)
    (hf0_meas : Measurable f0)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (hF_int : ∀ f ∈ F, Integrable (fun x => (f x - f0 x) ^ 2) PX)
    (hF_star : StarConvex ℝ f0 F)
    (hfhat_int : ∀ᵐ ω ∂P, Integrable (fun x => (fhat ω x - f0 x) ^ 2) PX)
    (hfhat_meas : AEMeasurable (Function.uncurry fhat) (P.prod PX))
    (hU_cont : ∀ i : Fin n, ∀ᵐ ω ∂P, ∀ᵐ x ∂PX, ContinuousAt (deviations Z f0 ω i) x)
    (hU_tail_int : ∀ p : Fin n × Fin m,
      Integrable (fun ω => Real.exp (|deviations Z f0 ω p.1 (X p.1 p.2 ω) / B2|)) P)
    (hU_tail : ∀ p : Fin n × Fin m,
      ∫ ω, Real.exp (|deviations Z f0 ω p.1 (X p.1 p.2 ω) / B2|) ∂P ≤ 1)
    (heps_tail_int : ∀ p : Fin n × Fin m,
      Integrable (fun ω => Real.exp (|eps p.1 p.2 ω / B3|)) P)
    (heps_tail : ∀ p : Fin n × Fin m,
      ∫ ω, Real.exp (|eps p.1 p.2 ω / B3|) ∂P ≤ 1)
    (hRad_int : ∀ (r : ℝ) (Fs : Finset (↥Ωs → ℝ)),
      (Fs : Set (↥Ωs → ℝ)) ⊆ localizedClass F PX f0 r →
      Integrable (fun ω => rademacherFiniteSup X f0 sigma ω Fs) P)
    (hfhat : ∀ᵐ ω ∂P, fhat ω ∈ F ∧ ∀ f ∈ F,
      lsqCriterion (responses Z X eps) X ω (fhat ω) ≤
        lsqCriterion (responses Z X eps) X ω f)
    (hfix : IsRademacherFixedPoint F PX f0 X sigma P phi rstar)
    (c38 c39 : ℝ) (hc38 : c38 = (2 : ℝ) ^ 24) (hc39 : c39 = (2 : ℝ) ^ 12)
    (t : ℝ) (ht : 0 < t)
    (hregime : rstar ≤ 2 * c38 * B1 ^ 2 * rstar + 2 * c39 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ)))
    (hF_sep : PointwiseSeparable F),
    P {ω : Ωrand |
        |predError PX f0 (fhat ω) - empSqDisc X f0 ω (fhat ω)| ≤
          (1 / 2 : ℝ) * predError PX f0 (fhat ω) + c38 * B1 ^ 2 * rstar +
            c39 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ))}ᶜ ≤
      ENNReal.ofReal (Real.exp (-t)) := by
  /- @proof-region region.target-node.session.3bf5374a5a24f29c begin -/
  intro d hd Ωs hΩs PX hPX_prob hPX_ac n m hn hm Ωrand msΩrand P hP_prob
    f0 F fhat Z X eps sigma B1 B2 B3 hB1 hB2_nn hB2_ne hB3_nn hB3_ne phi rstar
    hZ_meas hZ_iid_law hZ_indep hX_meas hX_law hX_indep hZX_indep heps_meas heps_indep
    hsigma_meas hsigma_law hsigma_indep hsigma_indep_data hZ_int hf0_def hf0_bound
    hF_bound hf0_meas hF_meas hF_int hF_star hfhat_int hfhat_meas hU_cont hU_tail_int
    hU_tail heps_tail_int heps_tail hRad_int hfhat hfix c38 c39 hc38 hc39 t ht hregime hF_sep
  letI := msΩrand
  haveI hPp : IsProbabilityMeasure P := hP_prob
  set r1 : ℝ := 2 * c38 * B1 ^ 2 * rstar + 2 * c39 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ)) with hr1
  have hr1_ge : rstar ≤ r1 := by rw [hr1]; exact hregime
  have hr1_pos : 0 < r1 := lt_of_lt_of_le hfix.1 hr1_ge
  have hsigmaX : IndepFun (fun ω : Ωrand => fun p : Fin n × Fin m => sigma p.1 p.2 ω)
      (fun ω : Ωrand => fun p : Fin n × Fin m => X p.1 p.2 ω) P := by
    have h := hsigma_indep_data.comp measurable_id measurable_fst
    simpa [Function.comp] using h
  have hdep := statopia_math_node_2829917225_53cae5d1 B1 hB1 PX hPX_prob f0 F hf0_meas hF_meas
    hf0_bound hF_bound hF_int P hP_prob n m hn hm X hX_meas hX_law hX_indep sigma hsigma_meas
    hsigma_law hsigma_indep hsigmaX phi rstar hfix r1 hr1_ge t ht hF_sep
  set Dr : ℝ := 160 * B1 * phi r1 / r1 + Real.sqrt (8 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ) * r1)) + 140 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ) * r1) with hDr
  set Eset : Set Ωrand := {ω : Ωrand | ∀ f ∈ F,
    |predError PX f0 f - empSqDisc X f0 ω f| ≤ Dr * (predError PX f0 f + r1)} with hEset
  set S : Set Ωrand := {ω : Ωrand |
    |predError PX f0 (fhat ω) - empSqDisc X f0 ω (fhat ω)| ≤
      (1 / 2 : ℝ) * predError PX f0 (fhat ω) + c38 * B1 ^ 2 * rstar +
        c39 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ))} with hS
  set A : Set Ωrand := {ω : Ωrand | fhat ω ∈ F} with hA
  have hnullA : P Aᶜ = 0 := by
    have hnull : P {ω : Ωrand | ¬ (fhat ω ∈ F ∧ ∀ f ∈ F,
        lsqCriterion (responses Z X eps) X ω (fhat ω) ≤
          lsqCriterion (responses Z X eps) X ω f)} = 0 := by
      simpa only [Set.compl_setOf] using (MeasureTheory.mem_ae_iff.mp hfhat)
    have hsub : Aᶜ ⊆ {ω : Ωrand | ¬ (fhat ω ∈ F ∧ ∀ f ∈ F,
        lsqCriterion (responses Z X eps) X ω (fhat ω) ≤
          lsqCriterion (responses Z X eps) X ω f)} := by
      intro ω hω
      rw [hA] at hω
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hω ⊢
      exact fun h => hω h.1
    refine le_antisymm ?_ (zero_le _)
    rw [← hnull]
    exact measure_mono hsub
  have hDle : Dr ≤ 1 / 2 := by
    rw [hDr]
    exact statopia_math_node_2785853616_1d52636d B1 hB1 phi rstar hfix.1 hfix.2.1 hfix.2.2.1
      c38 c39 hc38 hc39 n m hn hm t ht r1 hr1 hr1_ge
  have hmeasS : NullMeasurableSet S P := by
    haveI hPXinst : IsProbabilityMeasure PX := hPX_prob
    have hAEM : AEMeasurable (fun ω : Ωrand => predError PX f0 (fhat ω)) P := by
      have hAE : AEStronglyMeasurable (fun ω : Ωrand => predError PX f0 (fhat ω)) P := by
        have hdiff : AEMeasurable (fun p : Ωrand × ↥Ωs => Function.uncurry fhat p - f0 p.2)
            (P.prod PX) :=
          hfhat_meas.sub (hf0_meas.comp measurable_snd).aemeasurable
        have hmul : AEStronglyMeasurable
            (fun p : Ωrand × ↥Ωs =>
              (Function.uncurry fhat p - f0 p.2) * (Function.uncurry fhat p - f0 p.2))
            (P.prod PX) :=
          hdiff.aestronglyMeasurable.mul hdiff.aestronglyMeasurable
        have h := MeasureTheory.AEStronglyMeasurable.integral_prod_right' (μ := P) (ν := PX) hmul
        simpa [predError, Function.uncurry, pow_two] using h
      exact hAE.aemeasurable
    have hdevp : ∀ p : Fin n × Fin m, ∀ᵐ ω ∂P, deviations Z f0 ω p.1 (X p.1 p.2 ω) = 0 := by
      intro p
      have hfi : Integrable (fun ω => Real.exp (|deviations Z f0 ω p.1 (X p.1 p.2 ω) / B2|)) P :=
        hU_tail_int p
      have hle : ∫ ω, Real.exp (|deviations Z f0 ω p.1 (X p.1 p.2 ω) / B2|) ∂P ≤ 1 := hU_tail p
      have h1 : Integrable (fun ω => Real.exp (|deviations Z f0 ω p.1 (X p.1 p.2 ω) / B2|) - 1) P :=
        hfi.sub (integrable_const (1:ℝ))
      have hexp_all : ∀ ω : Ωrand, (1:ℝ) ≤ Real.exp (|deviations Z f0 ω p.1 (X p.1 p.2 ω) / B2|) := by
        intro ω
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (abs_nonneg _)
      have hnn : 0 ≤ (fun ω => Real.exp (|deviations Z f0 ω p.1 (X p.1 p.2 ω) / B2|) - 1) :=
        fun ω => by
          show (0:ℝ) ≤ Real.exp (|deviations Z f0 ω p.1 (X p.1 p.2 ω) / B2|) - 1
          have h := hexp_all ω
          linarith
      have hzi : ∫ ω, (Real.exp (|deviations Z f0 ω p.1 (X p.1 p.2 ω) / B2|) - 1) ∂P = 0 := by
        have hnnint : 0 ≤ ∫ ω, (Real.exp (|deviations Z f0 ω p.1 (X p.1 p.2 ω) / B2|) - 1) ∂P :=
          MeasureTheory.integral_nonneg (fun ω => by
            show (0:ℝ) ≤ Real.exp (|deviations Z f0 ω p.1 (X p.1 p.2 ω) / B2|) - 1
            have h := hexp_all ω
            linarith)
        have hupp : ∫ ω, (Real.exp (|deviations Z f0 ω p.1 (X p.1 p.2 ω) / B2|) - 1) ∂P ≤ 0 := by
          rw [integral_sub hfi (integrable_const (1:ℝ))]
          have hone : ∫ _ω : Ωrand, (1:ℝ) ∂P = 1 := by simp
          rw [hone]; linarith
        linarith
      have hzeq : (fun ω => Real.exp (|deviations Z f0 ω p.1 (X p.1 p.2 ω) / B2|) - 1) =ᵐ[P] 0 :=
        (MeasureTheory.integral_eq_zero_iff_of_nonneg hnn h1).mp hzi
      filter_upwards [hzeq] with ω hω
      have hω' : Real.exp (|deviations Z f0 ω p.1 (X p.1 p.2 ω) / B2|) - 1 = 0 := by simpa using hω
      have hexp1 : Real.exp (|deviations Z f0 ω p.1 (X p.1 p.2 ω) / B2|) = 1 := by linarith
      have habs : |deviations Z f0 ω p.1 (X p.1 p.2 ω) / B2| = 0 :=
        Real.exp_injective (by
          rw [Real.exp_zero]; exact hexp1)
      have hdiv : deviations Z f0 ω p.1 (X p.1 p.2 ω) / B2 = 0 := abs_eq_zero.mp habs
      rcases div_eq_zero_iff.mp hdiv with h | h
      · exact h
      · exact absurd h hB2_ne
    have hepsp : ∀ p : Fin n × Fin m, ∀ᵐ ω ∂P, eps p.1 p.2 ω = 0 := by
      intro p
      have hfi : Integrable (fun ω => Real.exp (|eps p.1 p.2 ω / B3|)) P := heps_tail_int p
      have hle : ∫ ω, Real.exp (|eps p.1 p.2 ω / B3|) ∂P ≤ 1 := heps_tail p
      have h1 : Integrable (fun ω => Real.exp (|eps p.1 p.2 ω / B3|) - 1) P :=
        hfi.sub (integrable_const (1:ℝ))
      have hexp_all : ∀ ω : Ωrand, (1:ℝ) ≤ Real.exp (|eps p.1 p.2 ω / B3|) := by
        intro ω
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (abs_nonneg _)
      have hnn : 0 ≤ (fun ω => Real.exp (|eps p.1 p.2 ω / B3|) - 1) :=
        fun ω => by
          show (0:ℝ) ≤ Real.exp (|eps p.1 p.2 ω / B3|) - 1
          have h := hexp_all ω
          linarith
      have hzi : ∫ ω, (Real.exp (|eps p.1 p.2 ω / B3|) - 1) ∂P = 0 := by
        have hnnint : 0 ≤ ∫ ω, (Real.exp (|eps p.1 p.2 ω / B3|) - 1) ∂P :=
          MeasureTheory.integral_nonneg (fun ω => by
            show (0:ℝ) ≤ Real.exp (|eps p.1 p.2 ω / B3|) - 1
            have h := hexp_all ω
            linarith)
        have hupp : ∫ ω, (Real.exp (|eps p.1 p.2 ω / B3|) - 1) ∂P ≤ 0 := by
          rw [integral_sub hfi (integrable_const (1:ℝ))]
          have hone : ∫ _ω : Ωrand, (1:ℝ) ∂P = 1 := by simp
          rw [hone]; linarith
        linarith
      have hzeq : (fun ω => Real.exp (|eps p.1 p.2 ω / B3|) - 1) =ᵐ[P] 0 :=
        (MeasureTheory.integral_eq_zero_iff_of_nonneg hnn h1).mp hzi
      filter_upwards [hzeq] with ω hω
      have hω' : Real.exp (|eps p.1 p.2 ω / B3|) - 1 = 0 := by simpa using hω
      have hexp1 : Real.exp (|eps p.1 p.2 ω / B3|) = 1 := by linarith
      have habs : |eps p.1 p.2 ω / B3| = 0 :=
        Real.exp_injective (by
          rw [Real.exp_zero]; exact hexp1)
      have hdiv : eps p.1 p.2 ω / B3 = 0 := abs_eq_zero.mp habs
      rcases div_eq_zero_iff.mp hdiv with h | h
      · exact h
      · exact absurd h hB3_ne
    have hdev : ∀ᵐ ω ∂P, ∀ p : Fin n × Fin m, deviations Z f0 ω p.1 (X p.1 p.2 ω) = 0 :=
      MeasureTheory.ae_all_iff.mpr hdevp
    have heps : ∀ᵐ ω ∂P, ∀ p : Fin n × Fin m, eps p.1 p.2 ω = 0 :=
      MeasureTheory.ae_all_iff.mpr hepsp
    have hT : NullMeasurableSet {ω : Ωrand | predError PX f0 (fhat ω) ≤ r1} P :=
      hAEM.nullMeasurableSet_preimage measurableSet_Iic
    have hST : S =ᵐ[P] {ω : Ωrand | predError PX f0 (fhat ω) ≤ r1} := by
      filter_upwards [hdev, heps, hfhat] with ω hdevω hepsω hhatω
      have hf0F : f0 ∈ F := hF_star.mem ⟨fhat ω, hhatω.1⟩
      have hlsq : ∀ g : ↥Ωs → ℝ, lsqCriterion (responses Z X eps) X ω g = empSqDisc X f0 ω g := by
        intro g
        unfold lsqCriterion empSqDisc
        congr 1
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        have hdevij : deviations Z f0 ω i (X i j ω) = 0 := hdevω (i, j)
        have h1 : Z i ω (X i j ω) - f0 (X i j ω) = 0 := by simpa [deviations] using hdevij
        have h2 : eps i j ω = 0 := hepsω (i, j)
        have hZeq : Z i ω (X i j ω) = f0 (X i j ω) := by linarith
        have hresp : responses Z X eps i j ω = f0 (X i j ω) := by
          simp only [responses, hZeq, h2, add_zero]
        rw [hresp]; ring
      have hempf0 : empSqDisc X f0 ω f0 = 0 := by
        unfold empSqDisc; simp
      have hempnn : 0 ≤ empSqDisc X f0 ω (fhat ω) := by
        unfold empSqDisc
        apply mul_nonneg
        · exact inv_nonneg.mpr (mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg m))
        · apply Finset.sum_nonneg; intro i _
          apply Finset.sum_nonneg; intro j _
          positivity
      have hempzero : empSqDisc X f0 ω (fhat ω) = 0 := by
        have hle : empSqDisc X f0 ω (fhat ω) ≤ 0 := by
          calc empSqDisc X f0 ω (fhat ω) = lsqCriterion (responses Z X eps) X ω (fhat ω) :=
                (hlsq (fhat ω)).symm
            _ ≤ lsqCriterion (responses Z X eps) X ω f0 := hhatω.2 f0 hf0F
            _ = empSqDisc X f0 ω f0 := hlsq f0
            _ = 0 := hempf0
        linarith
      have hpA : 0 ≤ predError PX f0 (fhat ω) := by
        unfold predError
        exact MeasureTheory.integral_nonneg (fun x => sq_nonneg (fhat ω x - f0 x))
      have h2C : 2 * (c38 * B1 ^ 2 * rstar + c39 * B1 ^ 2 * t / ((n:ℝ)*(m:ℝ))) = r1 := by
        rw [hr1]; ring
      have key : (ω ∈ S) ↔ predError PX f0 (fhat ω) ≤ r1 := by
        rw [hS]
        simp only [Set.mem_setOf_eq]
        rw [hempzero, sub_zero, abs_of_nonneg hpA]
        constructor
        · intro hle
          have h2 : (1/2) * predError PX f0 (fhat ω) ≤
              c38 * B1 ^ 2 * rstar + c39 * B1 ^ 2 * t / ((n:ℝ)*(m:ℝ)) := by linarith
          calc predError PX f0 (fhat ω) = 2 * ((1/2) * predError PX f0 (fhat ω)) := by ring
            _ ≤ 2 * (c38 * B1 ^ 2 * rstar + c39 * B1 ^ 2 * t / ((n:ℝ)*(m:ℝ))) := by linarith
            _ = r1 := h2C
        · intro hle
          linarith [hle, h2C]
      exact propext key
    exact hT.congr hST.symm
  have hdep' : ENNReal.ofReal (1 - Real.exp (-t)) ≤ P Eset := by
    rw [hEset]
    simp only [hDr]
    exact hdep
  have hstep : ∀ p : ℝ, 0 ≤ p → Dr * (p + r1) ≤
      (1 / 2 : ℝ) * p + c38 * B1 ^ 2 * rstar + c39 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ)) := by
    intro p hp
    have hpr : 0 ≤ p + r1 := by linarith [hp, hr1_pos]
    calc Dr * (p + r1) ≤ (1 / 2) * (p + r1) := mul_le_mul_of_nonneg_right hDle hpr
      _ = (1 / 2) * p + c38 * B1 ^ 2 * rstar + c39 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ)) := by
          rw [hr1]; ring
  have hsub2 : Eset ∩ A ⊆ S := by
    intro ω hω
    rw [Set.mem_inter_iff] at hω
    obtain ⟨hωE, hωA⟩ := hω
    have hFmem : fhat ω ∈ F := by rw [hA] at hωA; simpa using hωA
    have hgood : |predError PX f0 (fhat ω) - empSqDisc X f0 ω (fhat ω)| ≤
        Dr * (predError PX f0 (fhat ω) + r1) := by
      have hE' : ∀ f ∈ F, |predError PX f0 f - empSqDisc X f0 ω f| ≤
          Dr * (predError PX f0 f + r1) := by
        rw [hEset] at hωE
        simpa using hωE
      exact hE' (fhat ω) hFmem
    have hpre : 0 ≤ predError PX f0 (fhat ω) := by
      unfold predError
      exact MeasureTheory.integral_nonneg (fun x => sq_nonneg (fhat ω x - f0 x))
    rw [hS]
    simp only [Set.mem_setOf_eq]
    exact le_trans hgood (hstep (predError PX f0 (fhat ω)) hpre)
  have hPS_lower : ENNReal.ofReal (1 - Real.exp (-t)) ≤ P S := by
    have hstep1 : P Eset ≤ P (Eset ∩ A) := by
      have hsub1 : Eset ⊆ (Eset ∩ A) ∪ Aᶜ := by
        intro ω hω
        by_cases hωA : ω ∈ A
        · exact Or.inl ⟨hω, hωA⟩
        · exact Or.inr hωA
      calc P Eset ≤ P ((Eset ∩ A) ∪ Aᶜ) := measure_mono hsub1
        _ ≤ P (Eset ∩ A) + P Aᶜ := measure_union_le _ _
        _ = P (Eset ∩ A) + 0 := by rw [hnullA]
        _ = P (Eset ∩ A) := add_zero _
    calc ENNReal.ofReal (1 - Real.exp (-t)) ≤ P Eset := hdep'
      _ ≤ P (Eset ∩ A) := hstep1
      _ ≤ P S := measure_mono hsub2
  have hexp_le : Real.exp (-t) ≤ 1 := by
    have h := Real.exp_le_exp.mpr (by linarith : -t ≤ 0)
    rwa [Real.exp_zero] at h
  have hexp_nonneg : 0 ≤ Real.exp (-t) := (Real.exp_pos (-t)).le
  have hone_sub : 0 ≤ 1 - Real.exp (-t) := by linarith [hexp_le]
  have hcompl : P S + P Sᶜ = 1 := by
    rw [MeasureTheory.measure_add_measure_compl₀ hmeasS, measure_univ]
  have hPS_top : P S ≠ ⊤ := by
    have h1 : P S ≤ 1 := by
      calc P S ≤ P Set.univ := measure_mono (Set.subset_univ S)
        _ = 1 := measure_univ
    exact ne_of_lt (lt_of_le_of_lt h1 ENNReal.one_lt_top)
  have hPSc_eq : P Sᶜ = 1 - P S :=
    ENNReal.eq_sub_of_add_eq hPS_top (by rw [add_comm]; exact hcompl)
  have hEd : ENNReal.ofReal (Real.exp (-t)) + ENNReal.ofReal (1 - Real.exp (-t)) = 1 := by
    rw [← ENNReal.ofReal_add hexp_nonneg hone_sub]
    have h1 : Real.exp (-t) + (1 - Real.exp (-t)) = 1 := by ring
    rw [h1, ENNReal.ofReal_one]
  have hdtop : ENNReal.ofReal (1 - Real.exp (-t)) ≠ ⊤ := by
    have hle : ENNReal.ofReal (1 - Real.exp (-t)) ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by linarith [hexp_nonneg])
    exact ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)
  have hone_sub_eq : 1 - ENNReal.ofReal (1 - Real.exp (-t)) = ENNReal.ofReal (Real.exp (-t)) :=
    (ENNReal.eq_sub_of_add_eq hdtop hEd).symm
  calc P Sᶜ = 1 - P S := hPSc_eq
    _ ≤ 1 - ENNReal.ofReal (1 - Real.exp (-t)) := tsub_le_tsub_left hPS_lower 1
    _ = ENNReal.ofReal (Real.exp (-t)) := hone_sub_eq
  /- @proof-region region.target-node.session.3bf5374a5a24f29c end -/

end

end Statlib.Imported

