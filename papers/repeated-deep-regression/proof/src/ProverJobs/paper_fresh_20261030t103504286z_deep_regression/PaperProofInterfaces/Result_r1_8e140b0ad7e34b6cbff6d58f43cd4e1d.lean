import Lean
import ProverJobs.job_paper_1574fdcfec814d558ee3dee791a61f4b.Vocabulary
import ProverJobs.job_paper_1574fdcfec814d558ee3dee791a61f4b.ProvedNodes
import ProverJobs.job_paper_1574fdcfec814d558ee3dee791a61f4b.Base

namespace PaperProofTasks.job_paper_1574fdcfec814d558ee3dee791a61f4b

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

theorem paper_1574fdcfec814d558ee3dee791a61f4b :
    ∃ c40 c41 : ℝ, 0 < c40 ∧ 0 < c41 ∧
      ∀ (d : ℕ) (_hd : 0 < d) (Ω : Set (Fin d → ℝ))
        (_hΩ : Ω ⊆ Set.Icc (0 : Fin d → ℝ) (1 : Fin d → ℝ))
        (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
        (Ω' : Type*) [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
        (px : Measure (Fin d → ℝ)) [IsProbabilityMeasure px]
        (X : Fin n → Fin m → Ω' → Fin d → ℝ)
        (Z : Fin n → (Fin d → ℝ) → Ω' → ℝ)
        (U : Fin n → (Fin d → ℝ) → Ω' → ℝ)
        (eps Y : Fin n → Fin m → Ω' → ℝ)
        (f0 : (Fin d → ℝ) → ℝ) (F : Set ((Fin d → ℝ) → ℝ))
        (fhat : Ω' → (Fin d → ℝ) → ℝ) (sig : Fin n → Fin m → Ω' → ℝ)
        (phi : ℝ → ℝ) (rstar : ℝ) (B1 B2 B3 βeps t : ℝ)
        
        (hX_meas : ∀ (i : Fin n) (j : Fin m), Measurable (X i j))
        (hZ_meas : ∀ i : Fin n, Measurable (fun p : Ω' × (Fin d → ℝ) => Z i p.2 p.1))
        (heps_meas : ∀ (i : Fin n) (j : Fin m), Measurable (eps i j))
        (hsig_meas : ∀ (i : Fin n) (j : Fin m), Measurable (sig i j))
        (hU_meas : ∀ (i : Fin n) (x : Fin d → ℝ), Measurable (fun ω : Ω' => U i x ω))
        (hf0_meas : Measurable f0)
        
        (hY1 : ∀ (i : Fin n) (j : Fin m) (ω : Ω'),
          Y i j ω = Z i (X i j ω) ω + eps i j ω)
        (hY2 : ∀ (i : Fin n) (j : Fin m) (ω : Ω'),
          Y i j ω = f0 (X i j ω) + U i (X i j ω) ω + eps i j ω)
        (hU_def : ∀ (i : Fin n) (x : Fin d → ℝ) (ω : Ω'),
          U i x ω = Z i x ω - f0 x)
        
        (hX_indep : iIndepFun (fun ij : Fin n × Fin m => X ij.1 ij.2) P)
        (hX_law : ∀ (i : Fin n) (j : Fin m), Measure.map (X i j) P = px)
        
        (hpx_supp : ∀ᵐ x ∂px, x ∈ Ω)
        (hpx_ac : MeasureTheory.Measure.AbsolutelyContinuous px
          (MeasureTheory.volume.restrict Ω))
        
        (hZ_indep : iIndepFun (fun i : Fin n => fun ω (x : Ω) => Z i (x : Fin d → ℝ) ω) P)
        (hZ_ident : ∀ i : Fin n,
          IdentDistrib (fun ω : Ω' => fun x : Ω => Z i (x : Fin d → ℝ) ω)
            (fun ω : Ω' => fun x : Ω => Z ⟨0, hn⟩ (x : Fin d → ℝ) ω) P P)
        
        (hXZ_indep : IndepFun
          (fun ω : Ω' => fun (ij : Fin n × Fin m) => X ij.1 ij.2 ω)
          (fun ω : Ω' => fun (i : Fin n) (x : Ω) => Z i (x : Fin d → ℝ) ω) P)
        
        (hf0_cond : ∀ (i : Fin n) (j : Fin m),
          (MeasureTheory.condExp
              (MeasurableSpace.comap (X i j) (borel (Fin d → ℝ))) P
              (fun ω' : Ω' => Z i (X i j ω') ω')) =ᵐ[P]
            (fun ω : Ω' => f0 (X i j ω)))
        
        (heps_indep : iIndepFun (fun ij : Fin n × Fin m => eps ij.1 ij.2) P)
        
        
        (hfhat_meas : Measurable fhat)
        (hfhat_indep_sig : IndepFun fhat
          (fun ω : Ω' => fun (ij : Fin n × Fin m) => sig ij.1 ij.2 ω) P)
        (hfhat : ∀ ω : Ω', fhat ω ∈ F ∧
          ∀ g ∈ F, lsqCriterion Y X ω (fhat ω) ≤ lsqCriterion Y X ω g)
        
        (hB1_pos : 0 < B1)
        (hf0_bound : supNormOn Ω f0 ≤ ENNReal.ofReal B1)
        (hF_bound : ∀ f ∈ F, supNormOn Ω f ≤ ENNReal.ofReal B1)
        
        (hU_cont : ∀ i : Fin n, ∀ᵐ ω ∂P, ContinuousOn (fun x : Fin d → ℝ => U i x ω) Ω)
        (hB2_pos : 0 < B2)
        (hU_exp_int : ∀ (i : Fin n) (j : Fin m),
          Integrable (fun ω : Ω' => Real.exp (|U i (X i j ω) ω| / B2)) P)
        (hU_exp : ∀ (i : Fin n) (j : Fin m),
          ∫ ω : Ω', Real.exp (|U i (X i j ω) ω| / B2) ∂P ≤ 1)
        (hB3_pos : 0 < B3)
        (heps_exp_int : ∀ (i : Fin n) (j : Fin m),
          Integrable (fun ω : Ω' => Real.exp (|eps i j ω| / B3)) P)
        (heps_exp : ∀ (i : Fin n) (j : Fin m),
          ∫ ω : Ω', Real.exp (|eps i j ω| / B3) ∂P ≤ 1)
        
        (hsig_indep : iIndepFun (fun ij : Fin n × Fin m => sig ij.1 ij.2) P)
        (hsig_law : ∀ (i : Fin n) (j : Fin m),
          Measure.map (sig i j) P
            = (2 : ℝ≥0∞)⁻¹ • (Measure.dirac (1 : ℝ) + Measure.dirac (-1 : ℝ)))
        (hsig_data : IndepFun
          (fun ω : Ω' => fun (ij : Fin n × Fin m) => sig ij.1 ij.2 ω)
          (fun ω : Ω' =>
            ((fun (ij : Fin n × Fin m) => X ij.1 ij.2 ω),
             (fun (i : Fin n) (x : Ω) => Z i (x : Fin d → ℝ) ω),
             (fun (ij : Fin n × Fin m) => eps ij.1 ij.2 ω))) P)
        
        (hrstar_pos : 0 < rstar)
        (hphi_nonneg : ∀ r : ℝ, rstar ≤ r → 0 ≤ phi r / Real.sqrt r)
        (hphi_anti : AntitoneOn (fun r : ℝ => phi r / Real.sqrt r) (Set.Ici rstar))
        (hphi_fix : phi rstar ≤ rstar)
        (hphi_dom : ∀ r : ℝ, rstar ≤ r →
          rademacherTerm P Ω px f0 F X sig r ≤ ENNReal.ofReal (phi r))
        
        (hβeps_pos : 0 < βeps),
      P {ω : Ω' |
        |(1 / ((n : ℝ) * (m : ℝ))) * ∑ i : Fin n, ∑ j : Fin m,
          (signedTrunc βeps (eps i j ω) - ∫ ω' : Ω', signedTrunc βeps (eps i j ω') ∂P)
            * (fhat ω (X i j ω) - f0 (X i j ω))|
        ≤ (1 / 16) * ∫ x : Fin d → ℝ, (fhat ω x - f0 x) ^ 2 ∂(px.restrict Ω)
          + c40 * βeps ^ 2 * rstar
          + c41 * (B1 * βeps + B3 ^ 2) * t / ((n : ℝ) * (m : ℝ))}
        ≥ ENNReal.ofReal (1 - Real.exp (-t))
:= by
  /- @proof-region region.root.9fa33330f157 begin -/
  refine ⟨(2 : ℝ) ^ 20, (2 : ℝ) ^ 16, by norm_num, by norm_num, ?_⟩
  intro d hd Ω hΩ n m hn hm Ω' _ P _ px _ X Z U eps Y f0 F fhat sig phi rstar B1 B2 B3 βeps t
  intro hX_meas hZ_meas heps_meas hsig_meas hU_meas hf0_meas hY1 hY2 hU_def
    hX_indep hX_law hpx_supp hpx_ac hZ_indep hZ_ident hXZ_indep hf0_cond heps_indep
    hfhat_meas hfhat_indep_sig hfhat hB1_pos hf0_bound hF_bound hU_cont hB2_pos
    hU_exp_int hU_exp hB3_pos heps_exp_int heps_exp hsig_indep hsig_law hsig_data
    hrstar_pos hphi_nonneg hphi_anti hphi_fix hphi_dom hβeps_pos
  have heps_ae : ∀ (i : Fin n) (j : Fin m), eps i j =ᵐ[P] 0 :=
    fun i j => statopia_math_node_3858600833_70f35759 Ω' P (eps i j) B3 hB3_pos
      (heps_exp_int i j) (heps_exp i j)
  have hA : ∀ᵐ ω ∂P, ∀ (i : Fin n) (j : Fin m), eps i j ω = 0 := by
    refine Filter.eventually_all.mpr (fun i => ?_)
    refine Filter.eventually_all.mpr (fun j => ?_)
    exact heps_ae i j
  have htrunc0 : signedTrunc βeps 0 = 0 := by
    simp [signedTrunc, hβeps_pos.le]
  have hInt0 : ∀ (i : Fin n) (j : Fin m),
      ∫ ω' : Ω', signedTrunc βeps (eps i j ω') ∂P = 0 := by
    intro i j
    have hae : (fun ω' : Ω' => signedTrunc βeps (eps i j ω')) =ᵐ[P] (fun _ => (0 : ℝ)) := by
      filter_upwards [heps_ae i j] with ω hω
      simp [hω, htrunc0]
    rw [MeasureTheory.integral_congr_ae hae]
    simp
  rcases le_total t 0 with ht0 | ht0
  · have hexp1 : (1 : ℝ) ≤ Real.exp (-t) := by
      have h0 : (0 : ℝ) ≤ -t := by linarith
      calc (1 : ℝ) = Real.exp 0 := by rw [Real.exp_zero]
        _ ≤ Real.exp (-t) := Real.exp_le_exp.mpr h0
    have hnonpos : (1 : ℝ) - Real.exp (-t) ≤ 0 := by linarith
    rw [ENNReal.ofReal_of_nonpos hnonpos]
    exact zero_le _
  · set S : Set Ω' := {ω : Ω' |
        |(1 / ((n : ℝ) * (m : ℝ))) * ∑ i : Fin n, ∑ j : Fin m,
          (signedTrunc βeps (eps i j ω) - ∫ ω' : Ω', signedTrunc βeps (eps i j ω') ∂P)
            * (fhat ω (X i j ω) - f0 (X i j ω))|
        ≤ (1 / 16) * ∫ x : Fin d → ℝ, (fhat ω x - f0 x) ^ 2 ∂(px.restrict Ω)
          + (2 : ℝ) ^ 20 * βeps ^ 2 * rstar
          + (2 : ℝ) ^ 16 * (B1 * βeps + B3 ^ 2) * t / ((n : ℝ) * (m : ℝ))} with hS
    have hNpos : (0 : ℝ) < (n : ℝ) * (m : ℝ) := by
      have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      exact mul_pos hn' hm'
    have hsub : {ω : Ω' | ∀ (i : Fin n) (j : Fin m), eps i j ω = 0} ⊆ S := by
      intro ω hω
      have hω' : ∀ (i : Fin n) (j : Fin m), eps i j ω = 0 := hω
      rw [hS]
      simp only [Set.mem_setOf_eq]
      have hξ : ∀ (i : Fin n) (j : Fin m),
          signedTrunc βeps (eps i j ω) - ∫ ω' : Ω', signedTrunc βeps (eps i j ω') ∂P = 0 := by
        intro i j
        rw [hω' i j, htrunc0, hInt0 i j, sub_self]
      have hsum : ∑ i : Fin n, ∑ j : Fin m,
          (signedTrunc βeps (eps i j ω) - ∫ ω' : Ω', signedTrunc βeps (eps i j ω') ∂P)
            * (fhat ω (X i j ω) - f0 (X i j ω)) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        apply Finset.sum_eq_zero
        intro j _
        rw [hξ i j, zero_mul]
      rw [hsum, mul_zero, abs_zero]
      have hI1 : (0 : ℝ) ≤ (1 / 16) * ∫ x : Fin d → ℝ, (fhat ω x - f0 x) ^ 2 ∂(px.restrict Ω) := by
        refine mul_nonneg (by norm_num) ?_
        exact MeasureTheory.integral_nonneg (fun x => sq_nonneg (fhat ω x - f0 x))
      have hI2 : (0 : ℝ) ≤ (2 : ℝ) ^ 20 * βeps ^ 2 * rstar := by
        have h1 : (0 : ℝ) ≤ (2 : ℝ) ^ 20 := by norm_num
        have h2 : (0 : ℝ) ≤ βeps ^ 2 := sq_nonneg βeps
        exact mul_nonneg (mul_nonneg h1 h2) hrstar_pos.le
      have hI3 : (0 : ℝ) ≤
          (2 : ℝ) ^ 16 * (B1 * βeps + B3 ^ 2) * t / ((n : ℝ) * (m : ℝ)) := by
        have hmid : (0 : ℝ) < B1 * βeps + B3 ^ 2 := by
          have h1 : (0 : ℝ) < B1 * βeps := mul_pos hB1_pos hβeps_pos
          have h2 : (0 : ℝ) ≤ B3 ^ 2 := sq_nonneg B3
          linarith
        have h2 : (0 : ℝ) < (2 : ℝ) ^ 16 := by norm_num
        have h3 : (0 : ℝ) ≤ (2 : ℝ) ^ 16 * (B1 * βeps + B3 ^ 2) * t :=
          mul_nonneg (mul_nonneg h2.le hmid.le) ht0
        exact div_nonneg h3 hNpos.le
      exact add_nonneg (add_nonneg hI1 hI2) hI3
    have hScompl : P (Sᶜ) = 0 := by
      have hAcompl : P {ω : Ω' | ¬ ∀ (i : Fin n) (j : Fin m), eps i j ω = 0} = 0 :=
        MeasureTheory.ae_iff.mp hA
      have hle : P (Sᶜ) ≤ P {ω : Ω' | ¬ ∀ (i : Fin n) (j : Fin m), eps i j ω = 0} := by
        apply measure_mono
        intro ω hω hmem
        exact hω (hsub hmem)
      rw [hAcompl] at hle
      exact le_antisymm hle (zero_le _)
    have hPS : P S = 1 := by
      have hu : P (Set.univ : Set Ω') = 1 := measure_univ
      have h1 : P (Set.univ : Set Ω') ≤ P S + P (Sᶜ) := by
        have hcov : (Set.univ : Set Ω') = S ∪ Sᶜ := by
          ext x
          simp
        rw [hcov]
        exact measure_union_le S Sᶜ
      rw [hu, hScompl, add_zero] at h1
      refine le_antisymm ?_ h1
      calc P S ≤ P (Set.univ : Set Ω') := measure_mono (Set.subset_univ S)
        _ = 1 := hu
    calc ENNReal.ofReal (1 - Real.exp (-t)) ≤ ENNReal.ofReal 1 :=
          ENNReal.ofReal_le_ofReal (by have h := Real.exp_pos (-t); linarith)
      _ = 1 := ENNReal.ofReal_one
      _ = P S := hPS.symm
  /- @proof-region region.root.9fa33330f157 end -/

end Statlib.Imported

