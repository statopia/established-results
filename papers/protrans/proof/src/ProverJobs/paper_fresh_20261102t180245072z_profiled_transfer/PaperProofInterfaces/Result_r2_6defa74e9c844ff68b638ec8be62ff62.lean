import Statlib.HighDim.CovarianceMatrix.SampleCovariance
import Statlib.HighDim.Regression.RandomDesignScore
import Statlib.HighDim.Vocabulary.RandomVector
import Statlib.StatFoundation.RandomVariable.SubGaussian.subgaussian_mgf_mono_param
import Lean
import ProverJobs.job_paper_5bfd1842871e4bc6b291fb4a9624d4b1.Vocabulary
import ProverJobs.job_paper_5bfd1842871e4bc6b291fb4a9624d4b1.ProvedNodes
import ProverJobs.job_paper_5bfd1842871e4bc6b291fb4a9624d4b1.Base

namespace PaperProofTasks.job_paper_5bfd1842871e4bc6b291fb4a9624d4b1

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))

theorem paper_5bfd1842871e4bc6b291fb4a9624d4b1
    (q : ℕ) (hq : 1 ≤ q) (L L_eps : NNReal) :
    ∀ c : ℝ, 0 < c →
      ∃ C_eps N_eps : ℝ, 0 < C_eps ∧ 0 < N_eps ∧
      ∀ (p : ℕ), 2 ≤ p →
      ∀ N : ℕ, 0 < N → N_eps * Real.log (p : ℝ) ≤ (N : ℝ) →
      ∀ (f : (Fin q → ℝ) → (Fin p → ℝ)) (σ : ℝ), 0 ≤ σ → Measurable f →
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (E : Ω → Fin N → Fin p → ℝ) (H : Ω → Fin N → Fin q → ℝ)
        (eps : Ω → Fin N → ℝ),
        
        (hindep : iIndepFun (fun i : Fin N => fun ω => ((E ω i, H ω i), eps ω i)) μ) →
        
        (hident : ∀ i j : Fin N,
          IdentDistrib (fun ω => (E ω i, H ω i)) (fun ω => (E ω j, H ω j)) μ μ) →
        
        (hE_meas : ∀ i j, Measurable (fun ω => E ω i j)) →
        (hH_meas : ∀ i k, Measurable (fun ω => H ω i k)) →
        (heps_meas : ∀ i, Measurable (fun ω => eps ω i)) →
        
        (hE_int : ∀ i j, Integrable (fun ω => E ω i j) μ) →
        (hH_int : ∀ i k, Integrable (fun ω => H ω i k) μ) →
        (hfH_int : ∀ i j, Integrable (fun ω => f (H ω i) j) μ) →
        (heps_int : ∀ i, Integrable (fun ω => eps ω i) μ) →
        (heps_sq_int : ∀ i, Integrable (fun ω => eps ω i ^ 2) μ) →
        (hEH_int : ∀ i j k, Integrable (fun ω => E ω i j * H ω i k) μ) →
        
        (hE_center : ∀ i j, ∫ ω, E ω i j ∂μ = 0) →
        (hH_center : ∀ i k, ∫ ω, H ω i k ∂μ = 0) →
        (hfH_center : ∀ i j, ∫ ω, f (H ω i) j ∂μ = 0) →
        
        
        (hE_subg : ∀ i j, HasSubgaussianMGF (fun ω => E ω i j) L μ) →
        (hH_subg : ∀ i k, HasSubgaussianMGF (fun ω => H ω i k) L μ) →
        (hfH_subg : ∀ i j, HasSubgaussianMGF (fun ω => f (H ω i) j) L μ) →
        
        (hEH_zero : ∀ i j k, ∫ ω, E ω i j * H ω i k ∂μ = 0) →
        
        
        (heps_center : ∀ i, ∫ ω, eps ω i ∂μ = 0) →
        (heps_var : ∀ i, ∫ ω, eps ω i ^ 2 ∂μ = σ ^ 2) →
        (heps_subg : ∀ i, HasSubgaussianMGF (fun ω => eps ω i) L_eps μ) →
        
        (heps_indep : ∀ i, IndepFun (fun ω => eps ω i) (fun ω => (E ω i, H ω i)) μ) →
        
        1 - Real.rpow (p : ℝ) (-c) / 20 ≤
          μ.real {ω | ‖(fun j : Fin p =>
              (1 / (N : ℝ)) * ∑ i : Fin N,
                errorNoiseDesign f H E ω i j * eps ω i)‖
            ≤ C_eps * Real.sqrt (Real.log (p : ℝ) / (N : ℝ))}
:= by
  /- @proof-region region.root.6c7d5f91d789 begin -/
  intro c hc
  obtain ⟨c₀, hc₀, hE3⟩ :=
    Statlib.HighDim.Regression.subgaussian_random_design_score_tail.{u_1}
  set σc : NNReal := ⟨Real.sqrt (max (4 * (L : ℝ)) 1), Real.sqrt_nonneg _⟩ with hσcdef
  set σε : NNReal := ⟨Real.sqrt (max (L_eps : ℝ) 1), Real.sqrt_nonneg _⟩ with hσedef
  have hσcval : (σc : ℝ) = Real.sqrt (max (4 * (L : ℝ)) 1) := by
    simp only [hσcdef, NNReal.coe_mk]
  have hσεval : (σε : ℝ) = Real.sqrt (max (L_eps : ℝ) 1) := by
    simp only [hσedef, NNReal.coe_mk]
  have hσcsq : ((σc : ℝ)) ^ 2 = max (4 * (L : ℝ)) 1 := by
    rw [hσcval, Real.sq_sqrt (le_trans zero_le_one (le_max_right (4 * (L : ℝ)) 1))]
  have hσesq : ((σε : ℝ)) ^ 2 = max (L_eps : ℝ) 1 := by
    rw [hσεval, Real.sq_sqrt (le_trans zero_le_one (le_max_right ((L_eps : ℝ)) 1))]
  have hσcpos : (0 : ℝ) < (σc : ℝ) := by
    have hn : (0 : ℝ) ≤ (σc : ℝ) := by rw [hσcval]; exact Real.sqrt_nonneg _
    have h1 : (1 : ℝ) ≤ (σc : ℝ) ^ 2 := by rw [hσcsq]; exact le_max_right _ _
    nlinarith [hn, h1]
  have hσεpos : (0 : ℝ) < (σε : ℝ) := by
    have hn : (0 : ℝ) ≤ (σε : ℝ) := by rw [hσεval]; exact Real.sqrt_nonneg _
    have h1 : (1 : ℝ) ≤ (σε : ℝ) ^ 2 := by rw [hσesq]; exact le_max_right _ _
    nlinarith [hn, h1]
  have hσcsqpos : (0 : ℝ) < (σc : ℝ) ^ 2 := pow_pos hσcpos 2
  have hσesqpos : (0 : ℝ) < (σε : ℝ) ^ 2 := pow_pos hσεpos 2
  have hσc_ge : 4 * (L : ℝ) ≤ (σc : ℝ) ^ 2 := by
    rw [hσcsq]; exact le_max_left _ _
  have hσε_ge : (L_eps : ℝ) ≤ (σε : ℝ) ^ 2 := by
    rw [hσesq]; exact le_max_left _ _
  set A : ℝ := 1 + c + Real.log 40 / Real.log 2 with hAdef
  have hApos : 0 < A := by
    have h1 : (0 : ℝ) < Real.log 40 := Real.log_pos (by norm_num)
    have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have h3 : 0 < Real.log 40 / Real.log 2 := div_pos h1 h2
    rw [hAdef]; linarith
  set C₀ : ℝ := A * (σc : ℝ) ^ 2 * (σε : ℝ) ^ 2 / c₀ with hC₀def
  have hC₀pos : 0 < C₀ := by
    rw [hC₀def]
    exact div_pos (mul_pos (mul_pos hApos hσcsqpos) hσesqpos) hc₀
  set C_eps : ℝ := Real.sqrt C₀ + 1 with hCepsdef
  have hCepspos : 0 < C_eps := by
    have h0 : (0 : ℝ) ≤ Real.sqrt C₀ := Real.sqrt_nonneg _
    rw [hCepsdef]; linarith
  have hCeps_ge : C₀ ≤ C_eps ^ 2 := by
    have h0 : (0 : ℝ) ≤ Real.sqrt C₀ := Real.sqrt_nonneg _
    have h1 : Real.sqrt C₀ ^ 2 = C₀ := Real.sq_sqrt (le_of_lt hC₀pos)
    rw [hCepsdef]
    nlinarith [h0, h1]
  set N_eps : ℝ := C_eps ^ 2 / ((σc : ℝ) ^ 2 * (σε : ℝ) ^ 2) with hNepsdef
  have hNepspos : 0 < N_eps := by
    rw [hNepsdef]
    exact div_pos (pow_pos hCepspos 2) (mul_pos hσcsqpos hσesqpos)
  refine ⟨C_eps, N_eps, hCepspos, hNepspos, ?_⟩
  intro p hp N hN hNlog f σ hσ hf
  intro Ω inst μ hprob E H eps
  intro hindep hident hE_meas hH_meas heps_meas
  intro hE_int hH_int hfH_int heps_int heps_sq_int hEH_int
  intro hE_center hH_center hfH_center
  intro hE_subg hH_subg hfH_subg hEH_zero
  intro heps_center heps_var heps_subg heps_indep
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hp_pos : 0 < p := by omega
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_pos
  have hlogp : 0 < Real.log (p : ℝ) := by
    apply Real.log_pos
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hratio : 0 < Real.log (p : ℝ) / (N : ℝ) := div_pos hlogp hNpos
  set t : ℝ := C_eps * Real.sqrt (Real.log (p : ℝ) / (N : ℝ)) with htdef
  have ht_nonneg : 0 ≤ t := by
    rw [htdef]
    exact mul_nonneg (le_of_lt hCepspos) (Real.sqrt_nonneg _)
  have htsq : t ^ 2 = C_eps ^ 2 * (Real.log (p : ℝ) / (N : ℝ)) := by
    rw [htdef, mul_pow, Real.sq_sqrt (le_of_lt hratio)]
  have htpos : 0 < t := by
    have hsqrtpos : 0 < Real.sqrt (Real.log (p : ℝ) / (N : ℝ)) := by
      have h := Real.sq_sqrt (le_of_lt hratio)
      rcases lt_or_eq_of_le (Real.sqrt_nonneg (Real.log (p : ℝ) / (N : ℝ))) with h1 | h1
      · exact h1
      · exfalso
        have hz : Real.sqrt (Real.log (p : ℝ) / (N : ℝ)) ^ 2 = 0 := by rw [h1.symm]; ring
        rw [h] at hz
        linarith [hratio]
    rw [htdef]
    exact mul_pos hCepspos hsqrtpos
  have h4L : (NNReal.sqrt L + NNReal.sqrt L) ^ 2 = 4 * L := by
    have hL : NNReal.sqrt L ^ 2 = L := NNReal.sq_sqrt L
    have hexp : (NNReal.sqrt L + NNReal.sqrt L) ^ 2 = 4 * NNReal.sqrt L ^ 2 := by ring
    rw [hexp, hL]
  have hcoord : ∀ (i : Fin N) (j : Fin p),
      HasSubgaussianMGF (fun ω => errorNoiseDesign f H E ω i j) (4 * L) μ := by
    intro i j
    have hadd : HasSubgaussianMGF (fun ω => f (H ω i) j + E ω i j)
        ((NNReal.sqrt L + NNReal.sqrt L) ^ 2) μ :=
      (hfH_subg i j).add (hE_subg i j)
    rw [h4L] at hadd
    refine hadd.congr ?_
    filter_upwards with ω
    simp only [errorNoiseDesign]
  let xj : Fin p → Fin N → Ω → EuclideanSpace ℝ (Fin 1) :=
    fun j i ω => WithLp.toLp 2 (fun _ : Fin 1 => errorNoiseDesign f H E ω i j)
  have hxj_meas : ∀ (j : Fin p) (i : Fin N), Measurable (xj j i) := by
    intro j i
    have hc : Measurable (fun ω : Ω => (fun _ : Fin 1 => errorNoiseDesign f H E ω i j)) := by
      rw [measurable_pi_iff]
      intro k
      have hfj : Measurable (fun h : Fin q → ℝ => f h j) := (measurable_pi_iff (g := f)).1 hf j
      have hH : Measurable (fun ω : Ω => H ω i) := by
        rw [measurable_pi_iff]; intro k'; exact hH_meas i k'
      have h1 : Measurable (fun ω : Ω => f (H ω i) j) := hfj.comp hH
      have h2 : Measurable (fun ω : Ω => E ω i j) := hE_meas i j
      have h3 := h1.add h2
      simpa [errorNoiseDesign] using h3
    have h5 : Measurable ((WithLp.toLp (2 : ENNReal)) ∘
        (fun ω : Ω => (fun _ : Fin 1 => errorNoiseDesign f H E ω i j))) :=
      (WithLp.measurable_toLp (2 : ENNReal) (Fin 1 → ℝ)).comp hc
    simpa [xj, Function.comp] using h5
  have hxj_isv : ∀ (j : Fin p) (i : Fin N),
      Statlib.HighDim.Vocabulary.IsSubGaussianVector (xj j i) σc μ := by
    intro j i
    refine statopia_math_node_2597002862_be175bfc μ 1 (xj j i) (4 * L) σc ?_ ?_
    · intro k
      refine (hcoord i j).congr ?_
      filter_upwards with ω
      simp only [xj, PiLp.toLp_apply]
    · have hcast : ((4 * L : NNReal) : ℝ) * ((1 : ℕ) : ℝ) = 4 * (L : ℝ) := by
        have h4 : ((4 : NNReal) : ℝ) = 4 := by norm_num
        rw [NNReal.coe_mul, h4, Nat.cast_one, mul_one]
      rw [hcast]
      exact hσc_ge
  have hnoise : ∀ i, HasSubgaussianMGF (fun ω => eps ω i) (σε ^ 2) μ := by
    intro i
    have hLe : L_eps ≤ σε ^ 2 := by
      rw [← NNReal.coe_le_coe, NNReal.coe_pow]
      exact hσε_ge
    exact Statlib.StatFoundation.RandomVariable.SubGaussian.subgaussian_mgf_mono_param hLe
      (heps_subg i)
  have hφ_meas : ∀ j : Fin p, Measurable (fun eh : (Fin p → ℝ) × (Fin q → ℝ) =>
      WithLp.toLp 2 (fun _ : Fin 1 => f eh.2 j + eh.1 j)) := by
    intro j
    have hfj : Measurable (fun h : Fin q → ℝ => f h j) := (measurable_pi_iff (g := f)).1 hf j
    have hev : Measurable (fun e : Fin p → ℝ => e j) :=
      (measurable_pi_iff (g := fun e : Fin p → ℝ => e)).1 measurable_id j
    have hscal : Measurable (fun eh : (Fin p → ℝ) × (Fin q → ℝ) => f eh.2 j + eh.1 j) :=
      (hfj.comp measurable_snd).add (hev.comp measurable_fst)
    have hcoordm : Measurable (fun eh : (Fin p → ℝ) × (Fin q → ℝ) =>
        (fun _ : Fin 1 => f eh.2 j + eh.1 j)) := by
      rw [measurable_pi_iff]
      intro k
      simpa using hscal
    simpa [Function.comp] using
      (WithLp.measurable_toLp (2 : ENNReal) (Fin 1 → ℝ)).comp hcoordm
  have hjointj : ∀ j : Fin p, iIndepFun (fun i ω => (xj j i ω, eps ω i)) μ := by
    intro j
    have hΨ : Measurable (fun z : ((Fin p → ℝ) × (Fin q → ℝ)) × ℝ =>
        ((fun eh : (Fin p → ℝ) × (Fin q → ℝ) =>
          WithLp.toLp 2 (fun _ : Fin 1 => f eh.2 j + eh.1 j)) z.1, z.2)) :=
      ((hφ_meas j).comp measurable_fst).prodMk measurable_snd
    have hres := hindep.comp (fun i (z : ((Fin p → ℝ) × (Fin q → ℝ)) × ℝ) =>
      ((fun eh : (Fin p → ℝ) × (Fin q → ℝ) =>
        WithLp.toLp 2 (fun _ : Fin 1 => f eh.2 j + eh.1 j)) z.1, z.2)) (fun i => hΨ)
    simpa [Function.comp, xj, errorNoiseDesign] using hres
  have hxij : ∀ (j : Fin p) (i : Fin N), (fun ω => xj j i ω) ⟂ᵢ[μ] (fun ω => eps ω i) := by
    intro j i
    have h1 : (fun ω => (E ω i, H ω i)) ⟂ᵢ[μ] (fun ω => eps ω i) := (heps_indep i).symm
    have h2 := h1.comp (hφ_meas j) measurable_id
    simpa [Function.comp, xj, errorNoiseDesign] using h2
  let Bad : Set Ω :=
    {ω : Ω | ∃ j : Fin p, |∑ i : Fin N, errorNoiseDesign f H E ω i j * eps ω i| / (N : ℝ) > t}
  let Good : Set Ω :=
    {ω : Ω | ‖(fun j : Fin p => 1 / (N : ℝ) * ∑ i : Fin N,
      errorNoiseDesign f H E ω i j * eps ω i)‖ ≤ t}
  have hSpos : 0 < (σc : ℝ) ^ 2 * (σε : ℝ) ^ 2 := mul_pos hσcsqpos hσesqpos
  have hA1 : C_eps ^ 2 * Real.log (p : ℝ) ≤ (N : ℝ) * ((σc : ℝ) ^ 2 * (σε : ℝ) ^ 2) := by
    have h' := hNlog
    rw [hNepsdef, div_mul_eq_mul_div] at h'
    exact (div_le_iff₀ hSpos).1 h'
  have hT_le : t ≤ (σc : ℝ) * (σε : ℝ) := by
    have hb : (0 : ℝ) < (σc : ℝ) * (σε : ℝ) := mul_pos hσcpos hσεpos
    have hsq : t ^ 2 ≤ ((σc : ℝ) * (σε : ℝ)) ^ 2 := by
      rw [htsq]
      rw [mul_pow]
      rw [← mul_div_assoc]
      rw [div_le_iff₀ hNpos]
      rw [mul_comm ((σc : ℝ) ^ 2 * (σε : ℝ) ^ 2) ((N : ℝ))]
      exact hA1
    nlinarith [ht_nonneg, le_of_lt hb, hsq]
  have hmin : min (t ^ 2 / ((σc : ℝ) ^ 2 * (σε : ℝ) ^ 2)) (t / ((σc : ℝ) * (σε : ℝ)))
      = t ^ 2 / ((σc : ℝ) ^ 2 * (σε : ℝ) ^ 2) := by
    have hb : (0 : ℝ) < (σc : ℝ) * (σε : ℝ) := mul_pos hσcpos hσεpos
    set b : ℝ := t / ((σc : ℝ) * (σε : ℝ)) with hbdef
    have hb1 : b ≤ 1 := by
      rw [hbdef, div_le_one hb]
      exact hT_le
    have hb0 : 0 ≤ b := by
      rw [hbdef]
      exact div_nonneg ht_nonneg (le_of_lt hb)
    have hsqe : ((σc : ℝ) * (σε : ℝ)) ^ 2 = (σc : ℝ) ^ 2 * (σε : ℝ) ^ 2 := by ring
    have hq : t ^ 2 / ((σc : ℝ) ^ 2 * (σε : ℝ) ^ 2) = b ^ 2 := by
      rw [hbdef, ← hsqe, div_pow]
    rw [hq]
    refine min_eq_left ?_
    calc b ^ 2 = b * b := pow_two b
      _ ≤ b * 1 := mul_le_mul_of_nonneg_left hb1 hb0
      _ = b := mul_one b
  have hexp0 : c₀ * (N : ℝ) * (t ^ 2 / ((σc : ℝ) ^ 2 * (σε : ℝ) ^ 2))
      = (c₀ * C_eps ^ 2 / ((σc : ℝ) ^ 2 * (σε : ℝ) ^ 2)) * Real.log (p : ℝ) := by
    have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNpos
    have hS0 : ((σc : ℝ) ^ 2 * (σε : ℝ) ^ 2) ≠ 0 := ne_of_gt hSpos
    rw [htsq]
    field_simp
  set α : ℝ := c₀ * C_eps ^ 2 / ((σc : ℝ) ^ 2 * (σε : ℝ) ^ 2) with hαdef
  have hα : 1 + c + Real.log 40 / Real.log 2 ≤ α := by
    have hAS : A * ((σc : ℝ) ^ 2 * (σε : ℝ) ^ 2) = c₀ * C₀ := by
      rw [hC₀def]
      field_simp
    have h2 : c₀ * C₀ ≤ c₀ * C_eps ^ 2 := by
      have hh := mul_le_mul_of_nonneg_left hCeps_ge (le_of_lt hc₀)
      linarith
    rw [hαdef, le_div_iff₀ hSpos, ← hAdef]
    linarith
  have harg : -(c₀ * (N : ℝ) * min (t ^ 2 / ((σc : ℝ) ^ 2 * (σε : ℝ) ^ 2))
        (t / ((σc : ℝ) * (σε : ℝ)))) = -(α * Real.log (p : ℝ)) := by
    rw [hmin, hexp0, hαdef]
  have hbad_j : ∀ j : Fin p,
      μ {ω : Ω | |∑ i : Fin N, errorNoiseDesign f H E ω i j * eps ω i| / (N : ℝ) > t}
        ≤ ENNReal.ofReal (2 * Real.exp (-c₀ * (N : ℝ) * min
            (t ^ 2 / ((σc : ℝ) ^ 2 * (σε : ℝ) ^ 2)) (t / ((σc : ℝ) * (σε : ℝ))))) := by
    intro j
    have hres := hE3 (m := N) (p := 1) hN (by norm_num : (0 : ℕ) < 1) μ (xj j)
      (fun i ω => eps ω i) (fun i => hxj_meas j i) (fun i => heps_meas i) (hjointj j)
      (hxij j) σc σε hσcpos hσεpos (fun i => hxj_isv j i) hnoise t htpos
    have hset : {ω : Ω | |∑ i : Fin N, errorNoiseDesign f H E ω i j * eps ω i| / (N : ℝ) > t}
        = {ω : Ω | ∃ j' : Fin 1,
            |∑ i : Fin N, (xj j i ω).ofLp j' * eps ω i| / (N : ℝ) > t} := by
      ext ω
      constructor
      · intro h
        exact ⟨0, by simpa only [xj, PiLp.toLp_apply] using h⟩
      · rintro ⟨k, hk⟩
        simpa only [xj, PiLp.toLp_apply] using hk
    rw [hset]
    refine le_trans hres (le_of_eq ?_)
    rw [Nat.cast_one, mul_one]
  have hunion : μ Bad ≤ ENNReal.ofReal ((p : ℝ) * (2 * Real.exp (-c₀ * (N : ℝ) *
      min (t ^ 2 / ((σc : ℝ) ^ 2 * (σε : ℝ) ^ 2)) (t / ((σc : ℝ) * (σε : ℝ)))))) := by
    have hBad_eq : Bad = ⋃ j ∈ (Finset.univ : Finset (Fin p)),
        {ω : Ω | |∑ i : Fin N, errorNoiseDesign f H E ω i j * eps ω i| / (N : ℝ) > t} := by
      ext ω
      simp [Bad, Set.mem_iUnion]
    rw [hBad_eq]
    have h1 : μ (⋃ j ∈ (Finset.univ : Finset (Fin p)),
        {ω : Ω | |∑ i : Fin N, errorNoiseDesign f H E ω i j * eps ω i| / (N : ℝ) > t})
        ≤ ∑ j ∈ (Finset.univ : Finset (Fin p)), μ {ω : Ω |
            |∑ i : Fin N, errorNoiseDesign f H E ω i j * eps ω i| / (N : ℝ) > t} :=
      measure_biUnion_finset_le (μ := μ) Finset.univ _
    have h2 : (∑ j ∈ (Finset.univ : Finset (Fin p)), μ {ω : Ω |
            |∑ i : Fin N, errorNoiseDesign f H E ω i j * eps ω i| / (N : ℝ) > t})
        ≤ ∑ _j ∈ (Finset.univ : Finset (Fin p)), ENNReal.ofReal (2 * Real.exp (-c₀ * (N : ℝ) *
            min (t ^ 2 / ((σc : ℝ) ^ 2 * (σε : ℝ) ^ 2)) (t / ((σc : ℝ) * (σε : ℝ))))) :=
      Finset.sum_le_sum (fun j _ => hbad_j j)
    refine le_trans (le_trans h1 h2) (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg p)]
  have hbad_le : μ Bad ≤ ENNReal.ofReal (Real.rpow (p : ℝ) (-c) / 20) := by
    refine le_trans hunion (ENNReal.ofReal_le_ofReal ?_)
    have hstep : (p : ℝ) * (2 * Real.exp (-(α * Real.log (p : ℝ))))
        = 2 * (p : ℝ) * Real.exp (-(α * Real.log (p : ℝ))) := by ring
    rw [show -c₀ * (N : ℝ) * min (t ^ 2 / ((σc : ℝ) ^ 2 * (σε : ℝ) ^ 2))
          (t / ((σc : ℝ) * (σε : ℝ))) = -(α * Real.log (p : ℝ)) from by
      rw [show -c₀ * (N : ℝ) * min (t ^ 2 / ((σc : ℝ) ^ 2 * (σε : ℝ) ^ 2))
            (t / ((σc : ℝ) * (σε : ℝ)))
          = -(c₀ * (N : ℝ) * min (t ^ 2 / ((σc : ℝ) ^ 2 * (σε : ℝ) ^ 2))
            (t / ((σc : ℝ) * (σε : ℝ)))) by ring, harg]]
    rw [hstep]
    exact statopia_math_node_1918606011_426b194d p hp c α hc hα
  have hrpownn : (0 : ℝ) ≤ Real.rpow (p : ℝ) (-c) / 20 := by
    rw [show Real.rpow (p : ℝ) (-c) = Real.exp (Real.log (p : ℝ) * (-c)) from
      Real.rpow_def_of_pos hpR (-c)]
    positivity
  have hreal : μ.real Bad ≤ Real.rpow (p : ℝ) (-c) / 20 :=
    ENNReal.toReal_le_of_le_ofReal hrpownn hbad_le
  have hBc : Badᶜ ⊆ Good := by
    intro ω hω
    simp only [Bad, Good, Set.mem_setOf_eq, Set.mem_compl_iff, not_exists, not_lt] at hω ⊢
    have hy : (fun j : Fin p => 1 / (N : ℝ) * ∑ i : Fin N,
          errorNoiseDesign f H E ω i j * eps ω i)
        = (fun j : Fin p => (∑ i : Fin N, errorNoiseDesign f H E ω i j * eps ω i) / (N : ℝ)) := by
      funext j
      ring
    rw [hy]
    haveI hnefin : Nonempty (Fin p) := ⟨⟨0, by omega⟩⟩
    rw [Statlib.HighDim.CovarianceMatrix.pi_real_norm_eq_sup_abs
      (f := fun j : Fin p => (∑ i : Fin N, errorNoiseDesign f H E ω i j * eps ω i) / (N : ℝ))]
    apply Finset.sup'_le
    intro j _
    rw [abs_div, abs_of_pos hNpos]
    exact hω j
  have hcover : (Set.univ : Set Ω) ⊆ Bad ∪ Good := by
    intro ω _
    by_cases h : ω ∈ Bad
    · exact Or.inl h
    · exact Or.inr (hBc h)
  have hfinBad : μ Bad ≠ ⊤ := by
    have h1 : μ Bad ≤ 1 := by
      rw [← measure_univ (μ := μ)]
      exact measure_mono (Set.subset_univ Bad)
    exact ne_top_of_le_ne_top (by norm_num) h1
  have hfinGood : μ Good ≠ ⊤ := by
    have h1 : μ Good ≤ 1 := by
      rw [← measure_univ (μ := μ)]
      exact measure_mono (Set.subset_univ Good)
    exact ne_top_of_le_ne_top (by norm_num) h1
  have hfinSum : μ Bad + μ Good ≠ ⊤ := by
    have h1 : μ Bad ≤ 1 := by
      rw [← measure_univ (μ := μ)]
      exact measure_mono (Set.subset_univ Bad)
    have h2 : μ Good ≤ 1 := by
      rw [← measure_univ (μ := μ)]
      exact measure_mono (Set.subset_univ Good)
    have h3 : μ Bad + μ Good ≤ 2 := by
      calc μ Bad + μ Good ≤ 1 + 1 := add_le_add h1 h2
        _ = 2 := by norm_num
    exact ne_top_of_le_ne_top (by norm_num) h3
  have hmain : (1 : ℝ) ≤ μ.real Bad + μ.real Good := by
    have hle : μ (Set.univ) ≤ μ Bad + μ Good :=
      le_trans (measure_mono hcover) (measure_union_le Bad Good)
    have h1 : (μ Set.univ).toReal ≤ (μ Bad).toReal + (μ Good).toReal := by
      have h0 := ENNReal.toReal_mono hfinSum hle
      rwa [ENNReal.toReal_add hfinBad hfinGood] at h0
    have h2 : (μ Set.univ).toReal = 1 := by rw [measure_univ, ENNReal.toReal_one]
    show (1 : ℝ) ≤ (μ Bad).toReal + (μ Good).toReal
    linarith
  show 1 - Real.rpow (p : ℝ) (-c) / 20 ≤ μ.real Good
  linarith [hmain, hreal]
  /- @proof-region region.root.6c7d5f91d789 end -/

end Statlib.Imported

-- Paper root revision ad9d2410-a2fc-4813-9169-f9a8fcf49bd7

