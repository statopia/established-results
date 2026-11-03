import Lean
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.Vocabulary
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.ProvedNodes
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.Base

namespace PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
noncomputable section
set_option maxHeartbeats 1000000

theorem paper_8d614b8e54384bdaa316eb81207fecf6 :
    ∃ c38 c39 : ℝ, 0 < c38 ∧ 0 < c39 ∧
      ∀ (d : ℕ) (hd : 0 < d) (Ωs : Set (Fin d → ℝ)) (hΩs : Ωs ⊆ unitCube d)
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
        (phi : ℝ → ℝ) (rstar t : ℝ)
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
        (hregime : rstar ≤ 2 * c38 * B1 ^ 2 * rstar + 2 * c39 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ)))
        (hF_sep : PointwiseSeparable F),
        P ((lemmaS2Event PX f0 X fhat B1 rstar t c38 c39)ᶜ) ≤
          ENNReal.ofReal (Real.exp (-t))
:= by
  /- @proof-region region.root.cd8d294405d9 begin -/
  refine ⟨(2 : ℝ) ^ 24, (2 : ℝ) ^ 12, by norm_num, by norm_num, ?_⟩
  intro d hd Ωs hΩs PX hPX_prob hPX_ac n m hn hm Ωrand instΩ P hP_prob
  intro f0 F fhat Z X eps sigma B1 B2 B3 hB1 hB2_nn hB2_ne hB3_nn hB3_ne
  intro phi rstar t
  intro hZ_meas hZ_iid_law hZ_indep hX_meas hX_law hX_indep hZX_indep
  intro heps_meas heps_indep hsigma_meas hsigma_law hsigma_indep hsigma_indep_data
  intro hZ_int hf0_def hf0_bound hF_bound hf0_meas hF_meas hF_int hF_star
  intro hfhat_int hfhat_meas hU_cont
  intro hU_tail_int hU_tail heps_tail_int heps_tail hRad_int hfhat hfix hregime hF_sep
  by_cases ht : 0 < t
  · have hmain := statopia_math_node_1212119070_62aa6ec1 d hd Ωs hΩs PX hPX_prob hPX_ac n m
      hn hm Ωrand P hP_prob f0 F fhat Z X eps sigma B1 B2 B3 hB1 hB2_nn hB2_ne hB3_nn hB3_ne
      phi rstar hZ_meas hZ_iid_law hZ_indep hX_meas hX_law hX_indep hZX_indep heps_meas
      heps_indep hsigma_meas hsigma_law hsigma_indep hsigma_indep_data hZ_int hf0_def hf0_bound
      hF_bound hf0_meas hF_meas hF_int hF_star hfhat_int hfhat_meas hU_cont hU_tail_int hU_tail
      heps_tail_int heps_tail hRad_int hfhat hfix ((2 : ℝ) ^ 24) ((2 : ℝ) ^ 12) rfl rfl t ht
      hregime hF_sep
    have hsub : (lemmaS2Event PX f0 X fhat B1 rstar t ((2 : ℝ) ^ 24) ((2 : ℝ) ^ 12))ᶜ ⊆
        {ω : Ωrand | |predError PX f0 (fhat ω) - empSqDisc X f0 ω (fhat ω)| ≤
          1 / 2 * predError PX f0 (fhat ω) + 2 ^ 24 * B1 ^ 2 * rstar +
            2 ^ 12 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ))}ᶜ := by
      have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      have hN : (0 : ℝ) < (n : ℝ) * (m : ℝ) := mul_pos hn' hm'
      have hstep : 2 ^ 12 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ)) ≤
          2 ^ 12 * B1 ^ 2 * (t + 1) / ((n : ℝ) * (m : ℝ)) := by
        gcongr
        nlinarith [hB1, sq_nonneg B1]
      intro ω hω
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, lemmaS2Event] at hω ⊢
      exact fun hcon => hω (by linarith)
    exact le_trans (measure_mono hsub) hmain
  · have hexp : (1 : ℝ) ≤ Real.exp (-t) := by
      simpa using Real.exp_le_exp.mpr (show (0 : ℝ) ≤ -t by linarith)
    have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (-t)) := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hexp
    refine le_trans ?_ hone
    rw [← hP_prob.measure_univ]
    exact measure_mono (Set.subset_univ _)
  /- @proof-region region.root.cd8d294405d9 end -/

end

end Statlib.Imported

-- Paper root revision 41256e8e-e229-475b-af66-3ae9fd59b7d3

