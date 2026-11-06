import Statlib.HighDim.MatrixAnalysis.SingularValueProperties
import Statlib.HighDim.Vocabulary.SVD
import Statlib.StatFoundation.Concentration.ExponentialType.hoeffding_bounded_sum_meas_abs_ge_le_two_exp
import Statlib.StatFoundation.RandomVariable.Gaussian.LogSobolev
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_66af32212b933e67d5b3
import ProverJobs.ResidualE2ESupport20261106.M_07619582e197b023f046
import ProverJobs.ResidualE2ESupport20261106.M_c6e6716ab874a75a3ac2
import ProverJobs.ResidualE2ESupport20261106.M_8a1ad6547a008d3ec6bd
import ProverJobs.ResidualE2ESupport20261106.M_6fabb3df45617e6d0e0d

namespace PaperProofTasks.ResidualE2ESupport20261106
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open _root_.PaperProofTasks.ResidualE2ESupport20261106.ResidualLoss20261106.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace ResidualLoss20261106.Statlib.Imported

set_option maxHeartbeats 4000000 in
set_option autoImplicit false in
theorem reference_all_alpha : ∀ (D rhoMin : ℝ) (hD : 0 < D) (hrhoMin : 0 < rhoMin),
    ∀ (alpha0 : ℝ), 15 < alpha0 →
        ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ m0 : ℕ,
          ∀ (m n : ℕ) (p : ℝ)
            {Ωs : Type*} [MeasurableSpace Ωs] (μΩ : Measure Ωs) [IsProbabilityMeasure μΩ]
            (Om : Ωs → Matrix (Fin m) (Fin n) ℝ)
            (μG : Measure (Matrix (Fin m) (Fin n) ℝ)) [IsProbabilityMeasure μG]
            (γ : Fin n → ℝ)
            (hm : m0 ≤ m) (hn : 2 ≤ n) (hnm : n ≤ m)
            (hp0 : 0 < p) (hp1 : p ≤ 1)
            (hrho_lo : rhoMin ≤ rho m n) (hrho_hi : rho m n ≤ 1)
            (hmp : Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p)
            (hγ : ∀ i : Fin n,
              (∫ x, nuRho (rho m n) x
                  ∂(volume.restrict (Set.Icc (γ i) (lambdaPlus (rho m n)))))
                = (((i : ℕ) : ℝ) + 1 - 1 / 2) / (n : ℝ))
            (hmask : IsBernoulliMask μΩ Om p)
            (hgauss : IsStdGaussianMatrixLaw μG),
            μΩ {s : Ωs | ∀ i : Fin n,
                  |lambdaCirc hnm μG (Om s) i - Real.sqrt p * γ i|
                    ≤ C * Real.sqrt p * deltaM m}
              ≥ ENNReal.ofReal (1 - c * ((n : ℝ) ^ ((-D): ℝ))) := by
  /- @proof-region region.target-node.session.271bda966c17c4a2 begin -/
  intro D rhoMin hD hrhoMin
  intro alpha0 h15
  obtain ⟨M0, hM0, C, c, hC, hc, hAtt⟩ :=
    _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.sparse_coarse_rigidity_all_alpha (2 * D + 8)
      (by linarith) rhoMin hrhoMin 2 (by norm_num) alpha0 h15
  obtain ⟨m0c, hm0c_ge, hm0c_spec⟩ :=
    statopia_math_node_1255057691_189df777 D hD rhoMin hrhoMin alpha0 (by linarith)
  refine ⟨2, C + 4 * Real.sqrt c / rhoMin, by norm_num,
    add_pos_of_pos_of_nonneg hC (by positivity), max (max M0 3) m0c, ?_⟩
  intro m n p Ωs _ μΩ _ Om μG _ gamma hm hn hnm hp0 hp1 hrho_lo hrho_hi hmp hquant hmask hgauss
  have hbig : max M0 3 ≤ m := le_trans (le_max_left (max M0 3) m0c) hm
  have hM0m : M0 ≤ m := le_trans (le_max_left M0 3) hbig
  have hm3 : 3 ≤ m := le_trans (le_max_right M0 3) hbig
  have hm0c : m0c ≤ m := le_trans (le_max_right (max M0 3) m0c) hm
  have hm1 : 1 ≤ m := by omega
  have hn1 : 1 ≤ n := by omega
  have hp0' : 0 ≤ p := le_of_lt hp0
  have hrigidPart := hAtt m n hm1 hn1 hM0m hrho_lo hrho_hi p hp0' hp1 hmp
    (μ := μΩ.prod μG)
    (Xi := fun ω : Ωs × Matrix (Fin m) (Fin n) ℝ => ω.2)
    (Mask := fun ω : Ωs × Matrix (Fin m) (Fin n) ℝ => Om ω.1)
  clear hAtt



  have hlog_pos : 0 < Real.log (m : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < m)
  have hdeltaM_pos : 0 < deltaM m := by
    simpa [deltaM] using inv_pos.mpr hlog_pos
  have hsqrtp_pos : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hgamma_le : ∀ i : Fin n, gamma i ≤ lambdaPlus (rho m n) := by
    intro i
    by_contra hcon
    push_neg at hcon
    have hz : (∫ x, nuRho (rho m n) x
        ∂(volume.restrict (Set.Icc (gamma i) (lambdaPlus (rho m n))))) = 0 := by
      have hempty : Set.Icc (gamma i) (lambdaPlus (rho m n)) = ∅ := by
        funext x
        apply propext
        constructor
        · intro hx
          linarith [hx.1, hx.2]
        · intro hx
          exact absurd hx (fun h => h)
      rw [hempty, Measure.restrict_empty]
      simp
    have hi := hquant i
    rw [hz] at hi
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hnum : (0 : ℝ) < ((i : ℕ) : ℝ) + 1 - 1 / 2 := by
      have hnn : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have hpos : (0 : ℝ) < (((i : ℕ) : ℝ) + 1 - 1 / 2) / (n : ℝ) := div_pos hnum hnpos
    linarith
  have hgamma_le_two : ∀ i : Fin n, gamma i ≤ 2 := by
    intro i
    have h1 : gamma i ≤ 1 + Real.sqrt (rho m n) := hgamma_le i
    have h2 : Real.sqrt (rho m n) ≤ 1 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hrho_hi
    linarith
  have hdeltaM_bridge :
      _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.deltaM m
        = deltaM m := rfl
  have hsv_vocab : ∀ (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n),
      sv hnm A i
        = Statlib.HighDim.Vocabulary.singularValues A (Fin.castLE (le_min hnm le_rfl) i) := by
    intro A i
    exact Statlib.HighDim.MatrixAnalysis.singularValues_eq_vocabulary A
      (Fin.castLE (le_min hnm le_rfl) i)
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hscale : (Real.sqrt (m : ℝ))⁻¹ = Real.sqrt p * (Real.sqrt ((m : ℝ) * p))⁻¹ := by
    rw [Real.sqrt_mul hm_pos.le]
    have h1 : Real.sqrt (m : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hm_pos).ne'
    have h2 : Real.sqrt p ≠ 0 := (Real.sqrt_pos.mpr hp0).ne'
    field_simp
  have hmaskop_eq : ∀ (O G : Matrix (Fin m) (Fin n) ℝ),
      maskOp O ((Real.sqrt (m : ℝ))⁻¹ • G)
        = Real.sqrt p •
            _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.maskedScaled
              p G O := by
    intro O G
    ext i j
    show O i j * ((Real.sqrt (m : ℝ))⁻¹ * G i j)
        = Real.sqrt p * (O i j * G i j / Real.sqrt ((m : ℝ) * p))
    rw [hscale]
    ring

  have hXi_meas' : ∀ (i : Fin m) (j : Fin n),
      Measurable fun ω : Ωs × Matrix (Fin m) (Fin n) ℝ => ω.2 i j := by
    intro i j
    have hcoord : Measurable fun A : Matrix (Fin m) (Fin n) ℝ => A i j :=
      (measurable_pi_apply j).comp (measurable_pi_apply i)
    exact hcoord.comp measurable_snd
  have hMask_meas' : ∀ (i : Fin m) (j : Fin n),
      Measurable fun ω : Ωs × Matrix (Fin m) (Fin n) ℝ => Om ω.1 i j := by
    intro i j
    exact (hmask.1 i j).comp measurable_fst
  have hMask_val' : ∀ (i : Fin m) (j : Fin n) (ω : Ωs × Matrix (Fin m) (Fin n) ℝ),
      Om ω.1 i j = 0 ∨ Om ω.1 i j = 1 := by
    intro i j ω
    exact hmask.2.1 ω.1 i j
  have hmap_snd : Measure.map (Prod.snd : Ωs × Matrix (Fin m) (Fin n) ℝ →
      Matrix (Fin m) (Fin n) ℝ) (μΩ.prod μG) = μG := by
    refine MeasureTheory.Measure.ext fun t ht => ?_
    have hstep : Measure.map (Prod.snd : Ωs × Matrix (Fin m) (Fin n) ℝ →
        Matrix (Fin m) (Fin n) ℝ) (μΩ.prod μG) t = (μΩ.prod μG) (Prod.snd ⁻¹' t) :=
      MeasureTheory.Measure.map_apply (f := Prod.snd) (s := t) measurable_snd ht
    rw [hstep, MeasureTheory.Measure.prod_apply (measurable_snd ht)]
    have hconst : ∀ x : Ωs, μG (Prod.mk x ⁻¹' (Prod.snd ⁻¹' t)) = μG t := by
      intro x
      have hset : Prod.mk x ⁻¹' (Prod.snd ⁻¹' t) = t := by
        ext y
        exact Iff.rfl
      rw [hset]
    simp only [hconst, MeasureTheory.lintegral_const, MeasureTheory.measure_univ, mul_one]

  have hmp_pos : (0 : ℝ) < (m : ℝ) * p := mul_pos hm_pos hp0



  have hmpq : ∀ i : Fin n,
      _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.mpQuantile
        (rho m n) n i = gamma i :=
    statopia_math_node_2169097838_d24405fa (rho m n) (lt_of_lt_of_le hrhoMin hrho_lo) hrho_hi
      n gamma hquant
  have hfunq : (fun i : Fin n =>
        _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.mpQuantile
          ((n : ℝ) / (m : ℝ)) n i) = gamma := by
    funext i
    exact hmpq i

  have hrho_m : rhoMin * (m : ℝ) ≤ (n : ℝ) :=
    (le_div_iff₀ hm_pos).mp (show rhoMin ≤ (n : ℝ) / (m : ℝ) from hrho_lo)
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn_ge_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hexp : ((n : ℝ) ^ ((-(2 * D + 8)): ℝ)) ≤ ((n : ℝ) ^ ((-D): ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hn_ge_one (by linarith)
  have hlvl : c * ((n : ℝ) ^ ((-(2 * D + 8)): ℝ))
      ≤ (max c 1 + 1) * ((n : ℝ) ^ ((-D): ℝ)) := by
    have h1 : c ≤ max c 1 + 1 := by
      have h := le_max_left c 1
      linarith
    have hmono : c * ((n : ℝ) ^ ((-(2 * D + 8)): ℝ)) ≤ c * ((n : ℝ) ^ ((-D): ℝ)) :=
      mul_le_mul_of_nonneg_left hexp hc.le
    have hmono2 : c * ((n : ℝ) ^ ((-D): ℝ)) ≤ (max c 1 + 1) * ((n : ℝ) ^ ((-D): ℝ)) :=
      mul_le_mul_of_nonneg_right h1 (Real.rpow_pos_of_pos hnpos (-D)).le
    linarith
  have hradius_pos : 0 < Real.sqrt p * deltaM m := mul_pos hsqrtp_pos hdeltaM_pos
  have hsqrtp_le_one : Real.sqrt p ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hp1
  have hdev_le : ∀ (A : Matrix (Fin m) (Fin n) ℝ) (K : ℝ),
      _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.maxDeviation
          (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.svals A)
          gamma ≤ K →
        ∀ i : Fin n,
          |_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.svals A i
            - gamma i| ≤ K := by
    intro A K hK i
    have hmem : |_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.svals
            A i - gamma i|
        ∈ Set.range (fun i : Fin n =>
            |_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.svals
              A i - gamma i|) := ⟨i, rfl⟩
    have hbdd : BddAbove (Set.range fun i : Fin n =>
        |_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.svals
          A i - gamma i|) := (Set.finite_range _).bddAbove
    have hK' : sSup (Set.range fun i : Fin n =>
        |_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.svals
          A i - gamma i|) ≤ K := hK
    exact le_trans (le_csSup hbdd hmem) hK'
  have hsv_nonneg : ∀ (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n), 0 ≤ sv hnm A i := by
    intro A i
    exact (Statlib.HighDim.MatrixAnalysis.singular_value_properties A
      (Or.inl ⟨0, by omega⟩)).2.1 (Fin.castLE (le_min hnm le_rfl) i)
  have hmask_abs_le : ∀ (s : Ωs) (i : Fin m) (j : Fin n), |Om s i j| ≤ 1 := by
    intro s i j
    rcases hmask.2.1 s i j with h | h
    · rw [h]
      norm_num
    · rw [h]
      norm_num
  have hsv_svals : ∀ (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n),
      sv hnm A i
        = _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.svals A i := by
    intro A i
    rw [hsv_vocab A i]
    simp only [
      _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.svals,
      Statlib.HighDim.Vocabulary.singularValues]
    congr 1


  have hμG_sq : ∀ (i : Fin m) (j : Fin n),
      Integrable (fun G : Matrix (Fin m) (Fin n) ℝ => G i j ^ 2) μG ∧
        ∫ G : Matrix (Fin m) (Fin n) ℝ, G i j ^ 2 ∂μG = 1 := by
    intro i j
    have hmeasi : Measurable fun A : Matrix (Fin m) (Fin n) ℝ => A i j :=
      (measurable_pi_apply j).comp (measurable_pi_apply i)
    have hbase : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) :=
      (MeasureTheory.memLp_two_iff_integrable_sq
          (measurable_id.aestronglyMeasurable)).mp
        (ProbabilityTheory.memLp_id_gaussianReal (μ := 0) (v := 1) 2)
    have hsq : (∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1)) = 1 := by
      have hpt : ∀ x : ℝ, ‖x‖ₑ ^ 2 = ENNReal.ofReal (x ^ 2) := by
        intro x
        rw [Real.enorm_eq_ofReal_abs, pow_two, ← ENNReal.ofReal_mul (abs_nonneg x),
          ← pow_two, sq_abs]
      have hOfReal : ENNReal.ofReal (∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1))
          = ∫⁻ x : ℝ, ENNReal.ofReal (x ^ 2) ∂(gaussianReal 0 1) :=
        MeasureTheory.ofReal_integral_eq_lintegral_ofReal hbase
          (Filter.Eventually.of_forall fun x => sq_nonneg x)
      have h0 : 0 ≤ ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1) :=
        integral_nonneg fun x => sq_nonneg x
      have hEV : (∫⁻ x : ℝ, ENNReal.ofReal (x ^ 2) ∂(gaussianReal 0 1))
          = ProbabilityTheory.evariance (fun x : ℝ => x) (gaussianReal 0 1) := by
        simp only [ProbabilityTheory.evariance, ProbabilityTheory.integral_id_gaussianReal,
          sub_zero]
        simp only [hpt]
      have hVar : (ProbabilityTheory.evariance (fun x : ℝ => x) (gaussianReal 0 1)).toReal
          = 1 := by
        simpa [ProbabilityTheory.variance] using
          ProbabilityTheory.variance_fun_id_gaussianReal (μ := 0) (v := 1)
      calc (∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1))
          = (ENNReal.ofReal (∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1))).toReal := by
            rw [ENNReal.toReal_ofReal h0]
        _ = (∫⁻ x : ℝ, ENNReal.ofReal (x ^ 2) ∂(gaussianReal 0 1)).toReal := by
            rw [hOfReal]
        _ = 1 := by rw [hEV, hVar]

    have hg : AEStronglyMeasurable (fun x : ℝ => x ^ 2)
        (MeasureTheory.Measure.map (fun A : Matrix (Fin m) (Fin n) ℝ => A i j) μG) := by
      rw [hgauss.1 i j]
      exact (continuous_pow 2).measurable.aestronglyMeasurable
    have hG : Integrable (fun x : ℝ => x ^ 2)
        (MeasureTheory.Measure.map (fun A : Matrix (Fin m) (Fin n) ℝ => A i j) μG) := by
      rw [hgauss.1 i j]
      exact hbase
    have hintg : Integrable (fun G : Matrix (Fin m) (Fin n) ℝ => G i j ^ 2) μG :=
      (MeasureTheory.integrable_map_measure
        (f := fun A : Matrix (Fin m) (Fin n) ℝ => A i j)
        (g := fun x : ℝ => x ^ 2) hg hmeasi.aemeasurable).mp hG
    refine ⟨hintg, ?_⟩
    have key : (∫ y : ℝ, y ^ 2
          ∂(MeasureTheory.Measure.map (fun A : Matrix (Fin m) (Fin n) ℝ => A i j) μG))
        = ∫ A : Matrix (Fin m) (Fin n) ℝ, A i j ^ 2 ∂μG :=
      MeasureTheory.integral_map hmeasi.aemeasurable hg
    rw [hgauss.1 i j, hsq] at key
    exact key.symm
  have hG_int : ∀ (i : Fin m) (j : Fin n),
      Integrable (fun A : Matrix (Fin m) (Fin n) ℝ => A i j) μG := by
    intro i j
    have hcoord : Measurable fun A : Matrix (Fin m) (Fin n) ℝ => A i j :=
      (measurable_pi_apply j).comp (measurable_pi_apply i)
    have hbound : Integrable
        (fun A : Matrix (Fin m) (Fin n) ℝ => A i j ^ 2 + 1) μG :=
      (hμG_sq i j).1.add (MeasureTheory.integrable_const 1)
    refine hbound.mono' hcoord.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun A => ?_
    rw [Real.norm_eq_abs]
    nlinarith [abs_nonneg (A i j), sq_abs (A i j), sq_nonneg (|A i j| - 1)]
  have hXi_int' : ∀ (i : Fin m) (j : Fin n),
      Integrable (fun ω : Ωs × Matrix (Fin m) (Fin n) ℝ => ω.2 i j) (μΩ.prod μG) := by
    intro i j
    have hcoord : Measurable fun A : Matrix (Fin m) (Fin n) ℝ => A i j :=
      (measurable_pi_apply j).comp (measurable_pi_apply i)
    have hg : AEStronglyMeasurable (fun A : Matrix (Fin m) (Fin n) ℝ => A i j)
        (Measure.map (Prod.snd : Ωs × Matrix (Fin m) (Fin n) ℝ →
          Matrix (Fin m) (Fin n) ℝ) (μΩ.prod μG)) := by
      rw [hmap_snd]
      exact hcoord.aestronglyMeasurable
    have hG : Integrable (fun A : Matrix (Fin m) (Fin n) ℝ => A i j)
        (Measure.map (Prod.snd : Ωs × Matrix (Fin m) (Fin n) ℝ →
          Matrix (Fin m) (Fin n) ℝ) (μΩ.prod μG)) := by
      rw [hmap_snd]
      exact hG_int i j
    exact (MeasureTheory.integrable_map_measure
      (f := (Prod.snd : Ωs × Matrix (Fin m) (Fin n) ℝ → Matrix (Fin m) (Fin n) ℝ))
      (g := fun A : Matrix (Fin m) (Fin n) ℝ => A i j)
      hg measurable_snd.aemeasurable).mp hG
  have hXi_sq_int' : ∀ (i : Fin m) (j : Fin n),
      Integrable (fun ω : Ωs × Matrix (Fin m) (Fin n) ℝ => ω.2 i j ^ 2) (μΩ.prod μG) := by
    intro i j
    have hcoord : Measurable fun A : Matrix (Fin m) (Fin n) ℝ => A i j :=
      (measurable_pi_apply j).comp (measurable_pi_apply i)
    have hsq : Measurable fun A : Matrix (Fin m) (Fin n) ℝ => A i j ^ 2 :=
      (continuous_pow 2).measurable.comp hcoord
    have hg : AEStronglyMeasurable (fun A : Matrix (Fin m) (Fin n) ℝ => A i j ^ 2)
        (Measure.map (Prod.snd : Ωs × Matrix (Fin m) (Fin n) ℝ →
          Matrix (Fin m) (Fin n) ℝ) (μΩ.prod μG)) := by
      rw [hmap_snd]
      exact hsq.aestronglyMeasurable
    have hG : Integrable (fun A : Matrix (Fin m) (Fin n) ℝ => A i j ^ 2)
        (Measure.map (Prod.snd : Ωs × Matrix (Fin m) (Fin n) ℝ →
          Matrix (Fin m) (Fin n) ℝ) (μΩ.prod μG)) := by
      rw [hmap_snd]
      exact (hμG_sq i j).1
    exact (MeasureTheory.integrable_map_measure
      (f := (Prod.snd : Ωs × Matrix (Fin m) (Fin n) ℝ → Matrix (Fin m) (Fin n) ℝ))
      (g := fun A : Matrix (Fin m) (Fin n) ℝ => A i j ^ 2)
      hg measurable_snd.aemeasurable).mp hG
  have hXi_mean' : ∀ (i : Fin m) (j : Fin n),
      ∫ ω : Ωs × Matrix (Fin m) (Fin n) ℝ, ω.2 i j ∂(μΩ.prod μG) = 0 := by
    intro i j
    have hcoord : Measurable fun A : Matrix (Fin m) (Fin n) ℝ => A i j :=
      (measurable_pi_apply j).comp (measurable_pi_apply i)
    have hmean : ∫ A : Matrix (Fin m) (Fin n) ℝ, A i j ∂μG = 0 := by
      have key : ∫ A : Matrix (Fin m) (Fin n) ℝ, A i j ∂μG
          = ∫ x : ℝ, x
              ∂(Measure.map (fun A : Matrix (Fin m) (Fin n) ℝ => A i j) μG) :=
        (MeasureTheory.integral_map (φ := fun A : Matrix (Fin m) (Fin n) ℝ => A i j)
          (f := fun x : ℝ => x) hcoord.aemeasurable
          measurable_id.aestronglyMeasurable).symm
      rw [key, hgauss.1 i j, ProbabilityTheory.integral_id_gaussianReal]
    have hkey : ∫ ω : Ωs × Matrix (Fin m) (Fin n) ℝ, ω.2 i j ∂(μΩ.prod μG)
        = ∫ A : Matrix (Fin m) (Fin n) ℝ, A i j
            ∂(Measure.map (Prod.snd : Ωs × Matrix (Fin m) (Fin n) ℝ →
              Matrix (Fin m) (Fin n) ℝ) (μΩ.prod μG)) :=
      (MeasureTheory.integral_map
        (φ := (Prod.snd : Ωs × Matrix (Fin m) (Fin n) ℝ → Matrix (Fin m) (Fin n) ℝ))
        (f := fun A : Matrix (Fin m) (Fin n) ℝ => A i j)
        measurable_snd.aemeasurable hcoord.aestronglyMeasurable).symm
    rw [hkey, hmap_snd, hmean]
  have hXi_var' : ∀ (i : Fin m) (j : Fin n),
      ∫ ω : Ωs × Matrix (Fin m) (Fin n) ℝ, ω.2 i j ^ 2 ∂(μΩ.prod μG) = 1 := by
    intro i j
    have hcoord : Measurable fun A : Matrix (Fin m) (Fin n) ℝ => A i j :=
      (measurable_pi_apply j).comp (measurable_pi_apply i)
    have hsq : Measurable fun A : Matrix (Fin m) (Fin n) ℝ => A i j ^ 2 :=
      (continuous_pow 2).measurable.comp hcoord
    have hkey : ∫ ω : Ωs × Matrix (Fin m) (Fin n) ℝ, ω.2 i j ^ 2 ∂(μΩ.prod μG)
        = ∫ A : Matrix (Fin m) (Fin n) ℝ, A i j ^ 2
            ∂(Measure.map (Prod.snd : Ωs × Matrix (Fin m) (Fin n) ℝ →
              Matrix (Fin m) (Fin n) ℝ) (μΩ.prod μG)) :=
      (MeasureTheory.integral_map
        (φ := (Prod.snd : Ωs × Matrix (Fin m) (Fin n) ℝ → Matrix (Fin m) (Fin n) ℝ))
        (f := fun A : Matrix (Fin m) (Fin n) ℝ => A i j ^ 2)
        measurable_snd.aemeasurable hsq.aestronglyMeasurable).symm
    rw [hkey, hmap_snd, (hμG_sq i j).2]
  have hMask_law' : ∀ (i : Fin m) (j : Fin n),
      (μΩ.prod μG) {ω : Ωs × Matrix (Fin m) (Fin n) ℝ | Om ω.1 i j = 1}
        = ENNReal.ofReal p := by
    intro i j
    have hmeas : MeasurableSet {ω : Ωs × Matrix (Fin m) (Fin n) ℝ | Om ω.1 i j = 1} :=
      (hMask_meas' i j) (measurableSet_singleton 1)
    rw [MeasureTheory.Measure.prod_apply_symm hmeas]
    have hconst : ∀ y : Matrix (Fin m) (Fin n) ℝ,
        μΩ ((fun x : Ωs => (x, y)) ⁻¹'
            {ω : Ωs × Matrix (Fin m) (Fin n) ℝ | Om ω.1 i j = 1})
          = μΩ {s : Ωs | Om s i j = 1} := by
      intro y
      have hset : (fun x : Ωs => (x, y)) ⁻¹'
            {ω : Ωs × Matrix (Fin m) (Fin n) ℝ | Om ω.1 i j = 1}
          = {s : Ωs | Om s i j = 1} := by
        ext x
        exact Iff.rfl
      rw [hset]
    simp only [hconst, MeasureTheory.lintegral_const, MeasureTheory.measure_univ, mul_one,
      hmask.2.2.1 i j]
  have hXi_indep' : iIndepFun (fun (ij : Fin m × Fin n)
      (ω : Ωs × Matrix (Fin m) (Fin n) ℝ) => ω.2 ij.1 ij.2) (μΩ.prod μG) := by
    have hcoordA : Measurable fun A : Matrix (Fin m) (Fin n) ℝ =>
        fun ij : Fin m × Fin n => A ij.1 ij.2 :=
      measurable_pi_iff.mpr fun ij =>
        (measurable_pi_apply ij.2).comp (measurable_pi_apply ij.1)
    have hfam : (fun ij : Fin m × Fin n =>
          Measure.map (fun ω : Ωs × Matrix (Fin m) (Fin n) ℝ => ω.2 ij.1 ij.2)
            (μΩ.prod μG))
        = fun ij : Fin m × Fin n =>
            Measure.map (fun A : Matrix (Fin m) (Fin n) ℝ => A ij.1 ij.2) μG := by
      funext ij
      have hg : Measurable fun A : Matrix (Fin m) (Fin n) ℝ => A ij.1 ij.2 :=
        (measurable_pi_apply ij.2).comp (measurable_pi_apply ij.1)
      calc Measure.map (fun ω : Ωs × Matrix (Fin m) (Fin n) ℝ => ω.2 ij.1 ij.2)
            (μΩ.prod μG)
          = Measure.map ((fun A : Matrix (Fin m) (Fin n) ℝ => A ij.1 ij.2) ∘ Prod.snd)
              (μΩ.prod μG) := rfl
        _ = Measure.map (fun A : Matrix (Fin m) (Fin n) ℝ => A ij.1 ij.2)
              (Measure.map (Prod.snd : Ωs × Matrix (Fin m) (Fin n) ℝ →
                Matrix (Fin m) (Fin n) ℝ) (μΩ.prod μG)) :=
            (Measure.map_map hg measurable_snd).symm
        _ = Measure.map (fun A : Matrix (Fin m) (Fin n) ℝ => A ij.1 ij.2) μG := by
            rw [hmap_snd]
    refine (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (fun ij : Fin m × Fin n => (hXi_meas' ij.1 ij.2).aemeasurable)).mpr ?_
    have hmap : Measure.map (fun ω : Ωs × Matrix (Fin m) (Fin n) ℝ =>
          fun ij : Fin m × Fin n => ω.2 ij.1 ij.2) (μΩ.prod μG)
        = Measure.map (fun A : Matrix (Fin m) (Fin n) ℝ =>
            fun ij : Fin m × Fin n => A ij.1 ij.2) μG := by
      calc Measure.map (fun ω : Ωs × Matrix (Fin m) (Fin n) ℝ =>
              fun ij : Fin m × Fin n => ω.2 ij.1 ij.2) (μΩ.prod μG)
          = Measure.map ((fun A : Matrix (Fin m) (Fin n) ℝ =>
              fun ij : Fin m × Fin n => A ij.1 ij.2) ∘ Prod.snd) (μΩ.prod μG) := rfl
        _ = Measure.map (fun A : Matrix (Fin m) (Fin n) ℝ =>
              fun ij : Fin m × Fin n => A ij.1 ij.2)
              (Measure.map (Prod.snd : Ωs × Matrix (Fin m) (Fin n) ℝ →
                Matrix (Fin m) (Fin n) ℝ) (μΩ.prod μG)) :=
            (Measure.map_map hcoordA measurable_snd).symm
        _ = Measure.map (fun A : Matrix (Fin m) (Fin n) ℝ =>
              fun ij : Fin m × Fin n => A ij.1 ij.2) μG := by
            rw [hmap_snd]
    rw [hmap, hfam]
    exact (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (fun ij : Fin m × Fin n =>
        ((measurable_pi_apply ij.2).comp (measurable_pi_apply ij.1)).aemeasurable)).mp hgauss.2

  have hmap_fst : Measure.map (Prod.fst : Ωs × Matrix (Fin m) (Fin n) ℝ →
      Ωs) (μΩ.prod μG) = μΩ := by
    refine MeasureTheory.Measure.ext fun t ht => ?_
    have hstep : Measure.map (Prod.fst : Ωs × Matrix (Fin m) (Fin n) ℝ → Ωs)
        (μΩ.prod μG) t = (μΩ.prod μG) (Prod.fst ⁻¹' t) :=
      MeasureTheory.Measure.map_apply (f := Prod.fst) (s := t) measurable_fst ht
    rw [hstep, MeasureTheory.Measure.prod_apply_symm (measurable_fst ht)]
    have hconst : ∀ y : Matrix (Fin m) (Fin n) ℝ,
        μΩ ((fun x : Ωs => (x, y)) ⁻¹' (Prod.fst ⁻¹' t)) = μΩ t := by
      intro y
      have hset : (fun x : Ωs => (x, y)) ⁻¹' (Prod.fst ⁻¹' t) = t := by
        ext x
        exact Iff.rfl
      rw [hset]
    simp only [hconst, MeasureTheory.lintegral_const, MeasureTheory.measure_univ, mul_one]
  have hMask_indep' : iIndepFun (fun (ij : Fin m × Fin n)
      (ω : Ωs × Matrix (Fin m) (Fin n) ℝ) => Om ω.1 ij.1 ij.2) (μΩ.prod μG) := by
    have hcoordB : Measurable fun s : Ωs => fun ij : Fin m × Fin n => Om s ij.1 ij.2 :=
      measurable_pi_iff.mpr fun ij => hmask.1 ij.1 ij.2
    have hfam : (fun ij : Fin m × Fin n =>
          Measure.map (fun ω : Ωs × Matrix (Fin m) (Fin n) ℝ => Om ω.1 ij.1 ij.2)
            (μΩ.prod μG))
        = fun ij : Fin m × Fin n => Measure.map (fun s : Ωs => Om s ij.1 ij.2) μΩ := by
      funext ij
      have hg : Measurable fun s : Ωs => Om s ij.1 ij.2 := hmask.1 ij.1 ij.2
      calc Measure.map (fun ω : Ωs × Matrix (Fin m) (Fin n) ℝ => Om ω.1 ij.1 ij.2)
            (μΩ.prod μG)
          = Measure.map ((fun s : Ωs => Om s ij.1 ij.2) ∘ Prod.fst) (μΩ.prod μG) := rfl
        _ = Measure.map (fun s : Ωs => Om s ij.1 ij.2)
              (Measure.map (Prod.fst : Ωs × Matrix (Fin m) (Fin n) ℝ → Ωs)
                (μΩ.prod μG)) :=
            (Measure.map_map hg measurable_fst).symm
        _ = Measure.map (fun s : Ωs => Om s ij.1 ij.2) μΩ := by
            rw [hmap_fst]
    refine (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (fun ij : Fin m × Fin n => (hMask_meas' ij.1 ij.2).aemeasurable)).mpr ?_
    have hmap : Measure.map (fun ω : Ωs × Matrix (Fin m) (Fin n) ℝ =>
          fun ij : Fin m × Fin n => Om ω.1 ij.1 ij.2) (μΩ.prod μG)
        = Measure.map (fun s : Ωs => fun ij : Fin m × Fin n => Om s ij.1 ij.2) μΩ := by
      calc Measure.map (fun ω : Ωs × Matrix (Fin m) (Fin n) ℝ =>
              fun ij : Fin m × Fin n => Om ω.1 ij.1 ij.2) (μΩ.prod μG)
          = Measure.map ((fun s : Ωs => fun ij : Fin m × Fin n => Om s ij.1 ij.2) ∘ Prod.fst)
              (μΩ.prod μG) := rfl
        _ = Measure.map (fun s : Ωs => fun ij : Fin m × Fin n => Om s ij.1 ij.2)
              (Measure.map (Prod.fst : Ωs × Matrix (Fin m) (Fin n) ℝ → Ωs)
                (μΩ.prod μG)) :=
            (Measure.map_map hcoordB measurable_fst).symm
        _ = Measure.map (fun s : Ωs => fun ij : Fin m × Fin n => Om s ij.1 ij.2) μΩ := by
            rw [hmap_fst]
    rw [hmap, hfam]
    exact (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (fun ij : Fin m × Fin n => (hmask.1 ij.1 ij.2).aemeasurable)).mp hmask.2.2.2
  have hIndep' : IndepFun
      (fun (ω : Ωs × Matrix (Fin m) (Fin n) ℝ) (ij : Fin m × Fin n) => ω.2 ij.1 ij.2)
      (fun (ω : Ωs × Matrix (Fin m) (Fin n) ℝ) (ij : Fin m × Fin n) => Om ω.1 ij.1 ij.2)
      (μΩ.prod μG) :=
    (ProbabilityTheory.indepFun_prod
      (X := fun s : Ωs => fun ij : Fin m × Fin n => Om s ij.1 ij.2)
      (Y := fun A : Matrix (Fin m) (Fin n) ℝ => fun ij : Fin m × Fin n => A ij.1 ij.2)
      (measurable_pi_iff.mpr fun ij => hmask.1 ij.1 ij.2)
      (measurable_pi_iff.mpr fun ij =>
        (measurable_pi_apply ij.2).comp (measurable_pi_apply ij.1))).symm
  have hgauss_tail1 : ∀ (t : ℝ), 0 < t →
      (gaussianReal 0 1) {y : ℝ | t < |y|}
        ≤ ENNReal.ofReal (2 * Real.exp (-t / 2)) := by
    intro t ht
    by_cases h1 : 1 ≤ t
    · have habs_int : Integrable (fun y : ℝ => Real.exp (t * |y|)) (gaussianReal 0 1) :=
        Statlib.StatFoundation.RandomVariable.Gaussian.integrable_exp_abs_gaussianReal 0 1 t
      have hexpint1 : ∫ y : ℝ, Real.exp (t * y) ∂(gaussianReal 0 1) = Real.exp (t ^ 2 / 2) := by
        have h := Statlib.StatFoundation.Statistics.Asymptotic.gaussianReal_integral_exp t 1
          (by norm_num : (0 : ℝ) ≤ 1)
        simpa using h
      have hexpint2 : ∫ y : ℝ, Real.exp (-(t * y)) ∂(gaussianReal 0 1) = Real.exp (t ^ 2 / 2) := by
        have h := Statlib.StatFoundation.Statistics.Asymptotic.gaussianReal_integral_exp (-t) 1
          (by norm_num : (0 : ℝ) ≤ 1)
        simpa using h
      have h1_int : Integrable (fun y : ℝ => Real.exp (t * y)) (gaussianReal 0 1) := by
        refine Integrable.mono' habs_int (Real.continuous_exp.measurable.comp
          (measurable_const.mul measurable_id)).aestronglyMeasurable ?_
        refine Filter.Eventually.of_forall fun y => ?_
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self y) ht.le)
      have h2_int : Integrable (fun y : ℝ => Real.exp (-(t * y))) (gaussianReal 0 1) := by
        refine Integrable.mono' habs_int (Real.continuous_exp.measurable.comp
          (measurable_const.mul measurable_id).neg).aestronglyMeasurable ?_
        refine Filter.Eventually.of_forall fun y => ?_
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        have harg : -(t * y) = t * (-y) := by ring
        rw [harg]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (neg_le_abs y) ht.le)
      have hpt : ∀ y : ℝ, Real.exp (t * |y|) ≤ Real.exp (t * y) + Real.exp (-(t * y)) := by
        intro y
        by_cases hy : 0 ≤ y
        · rw [abs_of_nonneg hy]
          linarith [Real.exp_pos (-(t * y))]
        · rw [abs_of_neg (not_le.mp hy)]
          have harg : Real.exp (t * -y) = Real.exp (-(t * y)) := by rw [mul_neg]
          rw [harg]
          linarith [Real.exp_pos (t * y)]
      have hmono : ∫ y : ℝ, Real.exp (t * |y|) ∂(gaussianReal 0 1)
          ≤ 2 * Real.exp (t ^ 2 / 2) := by
        have hsum : ∫ y : ℝ, (Real.exp (t * y) + Real.exp (-(t * y))) ∂(gaussianReal 0 1)
            = Real.exp (t ^ 2 / 2) + Real.exp (t ^ 2 / 2) := by
          rw [MeasureTheory.integral_add h1_int h2_int, hexpint1, hexpint2]
        calc ∫ y : ℝ, Real.exp (t * |y|) ∂(gaussianReal 0 1)
            ≤ ∫ y : ℝ, (Real.exp (t * y) + Real.exp (-(t * y))) ∂(gaussianReal 0 1) :=
              MeasureTheory.integral_mono habs_int (h1_int.add h2_int) hpt
          _ = 2 * Real.exp (t ^ 2 / 2) := by
              rw [hsum]
              ring
      have hmeasf : AEMeasurable (fun y : ℝ => ENNReal.ofReal (Real.exp (t * |y|)))
          (gaussianReal 0 1) :=
        (Real.continuous_exp.measurable.comp
          (measurable_const.mul continuous_abs.measurable)).ennreal_ofReal.aemeasurable
      have hmarkov := MeasureTheory.meas_ge_le_lintegral_div
        (μ := gaussianReal 0 1)
        (f := fun y : ℝ => ENNReal.ofReal (Real.exp (t * |y|)))
        (ε := ENNReal.ofReal (Real.exp (t * t))) hmeasf
        (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))) ENNReal.ofReal_ne_top
      have hlintegral : ∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (t * |y|)) ∂(gaussianReal 0 1)
          = ENNReal.ofReal (∫ y : ℝ, Real.exp (t * |y|) ∂(gaussianReal 0 1)) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal habs_int
          (Filter.Eventually.of_forall fun y => (Real.exp_pos _).le)).symm
      calc (gaussianReal 0 1) {y : ℝ | t < |y|}
          ≤ (gaussianReal 0 1) {y : ℝ | ENNReal.ofReal (Real.exp (t * t))
              ≤ ENNReal.ofReal (Real.exp (t * |y|))} := by
            refine measure_mono ?_
            intro y hy
            exact ENNReal.ofReal_le_ofReal
              (Real.exp_le_exp.mpr (le_of_lt (mul_lt_mul_of_pos_left hy ht)))
        _ ≤ (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (t * |y|)) ∂(gaussianReal 0 1))
              / ENNReal.ofReal (Real.exp (t * t)) := hmarkov
        _ ≤ ENNReal.ofReal (2 * Real.exp (t ^ 2 / 2)) / ENNReal.ofReal (Real.exp (t * t)) := by
            refine ENNReal.div_le_div_right ?_ _
            rw [hlintegral]
            exact ENNReal.ofReal_le_ofReal hmono
        _ ≤ ENNReal.ofReal (2 * Real.exp (-t / 2)) := by
            rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos (t * t))]
            refine ENNReal.ofReal_le_ofReal ?_
            have harg : (2 * Real.exp (t ^ 2 / 2)) / Real.exp (t * t)
                = 2 * Real.exp (-(t ^ 2 / 2)) := by
              rw [mul_div_assoc, ← Real.exp_sub,
                show t ^ 2 / 2 - t * t = -(t ^ 2 / 2) by ring]
            rw [harg]
            have hle : -(t ^ 2 / 2) ≤ -t / 2 := by
              have h2 : t ≤ t ^ 2 := by nlinarith [h1]
              linarith
            exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) (by norm_num)

    · push_neg at h1
      have hone : (1 : ℝ) ≤ 2 * Real.exp (-t / 2) := by
        have hx : -t / 2 + 1 ≤ Real.exp (-t / 2) := Real.add_one_le_exp _
        linarith
      refine le_trans (measure_mono (Set.subset_univ _)) ?_
      rw [measure_univ, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hone

  have hXi_tail' : ∀ (i : Fin m) (j : Fin n) (t : ℝ), 0 < t →
      (μΩ.prod μG) {ω : Ωs × Matrix (Fin m) (Fin n) ℝ | t < |ω.2 i j|}
        ≤ ENNReal.ofReal (2 * Real.exp (-t / 2)) := by
    intro i j t ht
    have hcoord : Measurable fun A : Matrix (Fin m) (Fin n) ℝ => A i j :=
      (measurable_pi_apply j).comp (measurable_pi_apply i)
    have hset : MeasurableSet {A : Matrix (Fin m) (Fin n) ℝ | t < |A i j|} :=
      measurableSet_lt measurable_const (continuous_abs.measurable.comp hcoord)
    have hprod : (μΩ.prod μG) {ω : Ωs × Matrix (Fin m) (Fin n) ℝ | t < |ω.2 i j|}
        = μG {A : Matrix (Fin m) (Fin n) ℝ | t < |A i j|} := by
      have hseteq : {ω : Ωs × Matrix (Fin m) (Fin n) ℝ | t < |ω.2 i j|}
          = Prod.snd ⁻¹' {A : Matrix (Fin m) (Fin n) ℝ | t < |A i j|} := rfl
      rw [hseteq,
        ← MeasureTheory.Measure.map_apply
          (f := (Prod.snd : Ωs × Matrix (Fin m) (Fin n) ℝ →
            Matrix (Fin m) (Fin n) ℝ))
          (s := {A : Matrix (Fin m) (Fin n) ℝ | t < |A i j|}) measurable_snd hset,
        hmap_snd]
    rw [hprod]
    have hmap1 : μG {A : Matrix (Fin m) (Fin n) ℝ | t < |A i j|}
        = (gaussianReal 0 1) {y : ℝ | t < |y|} := by
      have hseteq : {A : Matrix (Fin m) (Fin n) ℝ | t < |A i j|}
          = (fun A : Matrix (Fin m) (Fin n) ℝ => A i j) ⁻¹' {y : ℝ | t < |y|} := rfl
      rw [hseteq,
        ← MeasureTheory.Measure.map_apply
          (f := fun A : Matrix (Fin m) (Fin n) ℝ => A i j)
          (s := {y : ℝ | t < |y|}) hcoord
          (measurableSet_lt measurable_const continuous_abs.measurable),
        hgauss.1 i j]
    rw [hmap1]
    exact hgauss_tail1 t ht
  have hrigid := hrigidPart hXi_meas' hXi_int' hXi_sq_int' hXi_indep' hXi_mean' hXi_var'
    hXi_tail' hMask_meas' hMask_val' hMask_law' hMask_indep' hIndep'
  clear hrigidPart
  have hbad : (μΩ.prod μG) {ω : Ωs × Matrix (Fin m) (Fin n) ℝ |
      C * deltaM m <
        _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.maxDeviation
          (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.svals
            (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.maskedScaled
              p (ω.2) (Om ω.1)))
          (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.mpQuantile
            (rho m n) n)}
      ≤ ENNReal.ofReal (c * ((n : ℝ) ^ ((-(2 * D + 8)): ℝ))) :=
    hrigid.1











  have hOm_nonneg : ∀ (s : Ωs) (i : Fin m) (j : Fin n), 0 ≤ Om s i j := by
    intro s i j
    rcases hmask.2.1 s i j with h | h <;> rw [h] <;> norm_num
  have hOm_le_one : ∀ (s : Ωs) (i : Fin m) (j : Fin n), Om s i j ≤ 1 := by
    intro s i j
    rcases hmask.2.1 s i j with h | h <;> rw [h] <;> norm_num
  have hmask_center : ∀ (s : Ωs) (i : Fin m) (j : Fin n),
      -p ≤ Om s i j - p ∧ Om s i j - p ≤ 1 - p := by
    intro s i j
    have h1 := hOm_nonneg s i j
    have h2 := hOm_le_one s i j
    exact ⟨by linarith, by linarith⟩
  have hmask_mean : ∀ (i : Fin m) (j : Fin n), ∫ s : Ωs, Om s i j ∂μΩ = p := by
    intro i j
    have hset : MeasurableSet {s : Ωs | Om s i j = 1} :=
      (hmask.1 i j) (measurableSet_singleton 1)
    have hind : (fun s : Ωs => Om s i j)
        = Set.indicator {s : Ωs | Om s i j = 1} (fun _ => (1 : ℝ)) := by
      funext s
      by_cases hs : Om s i j = 1
      · rw [Set.indicator_of_mem (show s ∈ {t : Ωs | Om t i j = 1} from hs), hs]
      · rw [Set.indicator_of_notMem (show s ∉ {t : Ωs | Om t i j = 1} from hs)]
        rcases hmask.2.1 s i j with h | h
        · exact h
        · exact absurd h hs
    rw [hind, MeasureTheory.integral_indicator hset]
    have hreal : (∫ s : Ωs in {s : Ωs | Om s i j = 1}, (1 : ℝ) ∂μΩ)
        = (μΩ {s : Ωs | Om s i j = 1}).toReal := by
      rw [MeasureTheory.integral_const, MeasureTheory.Measure.real_def, smul_eq_mul, mul_one]
      simp
    rw [hreal, hmask.2.2.1 i j, ENNReal.toReal_ofReal hp0']
  have hOm_intble : ∀ (i : Fin m) (j : Fin n), Integrable (fun s : Ωs => Om s i j) μΩ := by
    intro i j
    refine Integrable.mono' (MeasureTheory.integrable_const (1 : ℝ))
      (hmask.1 i j).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun s => ?_
    rw [Real.norm_eq_abs]
    exact hmask_abs_le s i j
  have hmask_center_mean : ∀ (i : Fin m) (j : Fin n),
      ∫ s : Ωs, (Om s i j - p) ∂μΩ = 0 := by
    intro i j
    rw [MeasureTheory.integral_sub (hOm_intble i j) (MeasureTheory.integrable_const p),
      hmask_mean i j]
    simp
  have hmnR : (0 : ℝ) < (m : ℝ) * (n : ℝ) := mul_pos hm_pos hnpos
  have htpos : 0 < (m : ℝ) * (n : ℝ) * p := mul_pos hmnR hp0
  have hcardmn : (0 : ℝ) < ((m * n : ℕ) : ℝ) := by
    have h : 0 < m * n := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast h
  set e : Fin (m * n) ≃ Fin m × Fin n :=
    (Fintype.equivFinOfCardEq (α := Fin m × Fin n) (n := m * n) (by simp)).symm with he
  set X : Fin (m * n) → Ωs → ℝ := fun k s => Om s (e k).1 (e k).2 - p with hX
  have hX_meas : ∀ k : Fin (m * n), Measurable (X k) := by
    intro k
    exact (hmask.1 (e k).1 (e k).2).sub measurable_const
  have hX_bound : ∀ k : Fin (m * n), ∀ᵐ s ∂μΩ, (-p) ≤ X k s ∧ X k s ≤ 1 - p := by
    intro k
    exact Filter.Eventually.of_forall fun s => hmask_center s (e k).1 (e k).2
  have hX_mean : ∀ k : Fin (m * n), ∫ s : Ωs, X k s ∂μΩ = 0 := by
    intro k
    exact hmask_center_mean (e k).1 (e k).2
  have hX_var : ∑ k : Fin (m * n), ((1 - p) - (-p)) ^ 2 > 0 := by
    have hterm : ∀ k : Fin (m * n), ((1 - p) - (-p)) ^ 2 = (1 : ℝ) := fun k => by ring
    rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    simpa using hcardmn
  have hX_indep : iIndepFun X μΩ := by
    rw [ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro S sets hsets
    have hmeasshift : Measurable fun y : ℝ => y - p := measurable_id.sub measurable_const
    have hleft : (⋂ k ∈ S, (X k) ⁻¹' sets k)
        = ⋂ x ∈ S.image e,
            ((fun s : Ωs => Om s x.1 x.2)) ⁻¹'
              ((fun y : ℝ => y - p) ⁻¹' sets (e.symm x)) := by
      ext s
      simp only [Set.mem_iInter, Finset.mem_image, Set.mem_preimage, hX]
      constructor
      · intro h x hx
        obtain ⟨k, hk, rfl⟩ := hx
        simpa using h k hk
      · intro h k hk
        simpa using h (e k) ⟨k, hk, rfl⟩
    have hright : (∏ k ∈ S, μΩ ((X k) ⁻¹' sets k))
        = ∏ x ∈ S.image e, μΩ (((fun s : Ωs => Om s x.1 x.2)) ⁻¹'
            ((fun y : ℝ => y - p) ⁻¹' sets (e.symm x))) := by
      refine Finset.prod_bij (fun k _ => e k) ?_ ?_ ?_ ?_
      · intro k hk
        exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
      · intro k₁ _ k₂ _ hkk
        exact e.injective hkk
      · intro x hx
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
        exact ⟨k, hk, rfl⟩
      · intro k _
        have hsetk : (X k) ⁻¹' sets k
            = ((fun s : Ωs => Om s (e k).1 (e k).2)) ⁻¹'
                ((fun y : ℝ => y - p) ⁻¹' sets k) := by
          ext s
          simp only [Set.mem_preimage, hX]
        rw [Equiv.symm_apply_apply, hsetk]
    rw [hleft, hright]
    exact (ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul.mp hmask.2.2.2)
      (S.image e) (fun x hx => by
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
        simpa using (hsets k hk).preimage hmeasshift)
  have hXsum : ∀ (s : Ωs), (∑ k : Fin (m * n), X k s)
      = (∑ i, ∑ j, Om s i j) - (m : ℝ) * (n : ℝ) * p := by
    intro s
    have h1 : (∑ k : Fin (m * n), X k s)
        = ∑ x : Fin m × Fin n, (Om s x.1 x.2 - p) := by
      rw [← Equiv.sum_comp e.symm (fun k : Fin (m * n) => X k s)]
      exact Finset.sum_congr rfl fun x _ => by simp only [hX, Equiv.apply_symm_apply]
    have h2 : (∑ x : Fin m × Fin n, (Om s x.1 x.2 - p))
        = (∑ x : Fin m × Fin n, Om s x.1 x.2) - ∑ _x : Fin m × Fin n, p :=
      Finset.sum_sub_distrib (fun x : Fin m × Fin n => Om s x.1 x.2) (fun _ => p)
    have h3 : (∑ x : Fin m × Fin n, Om s x.1 x.2) = ∑ i, ∑ j, Om s i j :=
      Fintype.sum_prod_type (fun x : Fin m × Fin n => Om s x.1 x.2)
    have h4 : (∑ _x : Fin m × Fin n, p) = (m : ℝ) * (n : ℝ) * p := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
    rw [h1, h2, h3, h4]
  have hden : (∑ k : Fin (m * n), ((fun _ => 1 - p) k - (fun _ => -p) k) ^ 2)
      = (m : ℝ) * (n : ℝ) := by
    have hterm : ∀ k : Fin (m * n),
        ((fun _ => 1 - p) k - (fun _ => -p) k) ^ 2 = (1 : ℝ) := by
      intro k
      ring
    rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, mul_one]
  have href : μΩ {s : Ωs |
        (m : ℝ) * (n : ℝ) * p ≤ |(∑ i, ∑ j, Om s i j) - (m : ℝ) * (n : ℝ) * p|}
      ≤ ENNReal.ofReal
          (2 * Real.exp (-2 * ((m : ℝ) * (n : ℝ) * p) ^ 2 / ((m : ℝ) * (n : ℝ)))) := by
    have heq : {s : Ωs |
          (m : ℝ) * (n : ℝ) * p ≤ |(∑ i, ∑ j, Om s i j) - (m : ℝ) * (n : ℝ) * p|}
        = {s : Ωs | (m : ℝ) * (n : ℝ) * p ≤ |∑ k : Fin (m * n), X k s|} := by
      ext s
      simp only [Set.mem_setOf_eq, hXsum s]
    rw [heq]
    have hh :=
      Statlib.StatFoundation.Concentration.ExponentialType.hoeffding_bounded_sum_meas_abs_ge_le_two_exp
        μΩ (m * n) X (fun _ => -p) (fun _ => 1 - p) ((m : ℝ) * (n : ℝ) * p)
        hX_indep hX_meas hX_bound hX_mean htpos hX_var
    rw [hden] at hh
    exact hh
  have hmask_sum_meas : Measurable fun s : Ωs => ∑ i, ∑ j, Om s i j :=
    Finset.measurable_sum Finset.univ fun i _ =>
      Finset.measurable_sum Finset.univ fun j _ => hmask.1 i j
  have hmask_size_compl : μΩ {s : Ωs | (∑ i, ∑ j, Om s i j) ≤ 2 * ((m : ℝ) * (n : ℝ) * p)}ᶜ
      ≤ ENNReal.ofReal
          (2 * Real.exp (-2 * ((m : ℝ) * (n : ℝ) * p) ^ 2 / ((m : ℝ) * (n : ℝ)))) := by
    refine le_trans (measure_mono ?_) href
    intro s hs
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hs ⊢
    have h2 : (m : ℝ) * (n : ℝ) * p
        ≤ (∑ i, ∑ j, Om s i j) - (m : ℝ) * (n : ℝ) * p := by linarith
    exact le_trans h2 (le_abs_self _)
  have hSV_smul : ∀ (c : ℝ), 0 ≤ c → ∀ (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n),
      sv hnm (c • A) i = c * sv hnm A i := by
    intro c hc A i
    exact statopia_math_node_3980448475_62265ffe.1 (m := m) (n := n) A
      (Fin.castLE (le_min hnm le_rfl) i) c hc
  have hSV_meas : ∀ (i : Fin n),
      Measurable fun A : Matrix (Fin m) (Fin n) ℝ => sv hnm A i := by
    intro i
    exact statopia_math_node_3980448475_62265ffe.2 (m := m) (n := n)
      (Fin.castLE (le_min hnm le_rfl) i)

  have hLambda_masked : ∀ (s : Ωs) (i : Fin n),
      lambdaCirc hnm μG (Om s) i
        = Real.sqrt p * ∫ G : Matrix (Fin m) (Fin n) ℝ,
            sv hnm
              (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.maskedScaled
                p G (Om s)) i ∂μG := by
    intro s i
    calc lambdaCirc hnm μG (Om s) i
        = ∫ G : Matrix (Fin m) (Fin n) ℝ,
            sv hnm (maskOp (Om s) ((Real.sqrt (m : ℝ))⁻¹ • G)) i ∂μG := rfl
      _ = ∫ G : Matrix (Fin m) (Fin n) ℝ,
            sv hnm (Real.sqrt p •
              _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.maskedScaled
                p G (Om s)) i ∂μG := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun G => ?_)
            show sv hnm (maskOp (Om s) ((Real.sqrt (m : ℝ))⁻¹ • G)) i
              = sv hnm (Real.sqrt p •
                _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.maskedScaled
                  p G (Om s)) i
            rw [hmaskop_eq]
      _ = ∫ G : Matrix (Fin m) (Fin n) ℝ,
            Real.sqrt p * sv hnm
              (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.maskedScaled
                p G (Om s)) i ∂μG := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun G => ?_)
            exact hSV_smul (Real.sqrt p) hsqrtp_pos.le _ i
      _ = Real.sqrt p * ∫ G : Matrix (Fin m) (Fin n) ℝ,
            sv hnm
              (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.maskedScaled
                p G (Om s)) i ∂μG :=
            MeasureTheory.integral_const_mul _ _
  have hexp_arg : -2 * ((m : ℝ) * (n : ℝ) * p) ^ 2 / ((m : ℝ) * (n : ℝ))
      = -(2 * ((m : ℝ) * (n : ℝ) * p ^ 2)) := by
    have hmn_ne : ((m : ℝ) * (n : ℝ)) ≠ 0 := (mul_pos hm_pos hnpos).ne'
    field_simp
  have hmask_size_level :
      μΩ {s : Ωs | (∑ i, ∑ j, Om s i j) ≤ 2 * ((m : ℝ) * (n : ℝ) * p)}ᶜ
        ≤ ENNReal.ofReal (((n : ℝ) ^ ((-D): ℝ))) := by
    refine le_trans hmask_size_compl ?_
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hexp_arg]
    have hmain := hm0c_spec m n p hnm hm0c hrho_m hmp
    simpa only [mul_assoc] using hmain




  have hgamma_nonneg : ∀ i : Fin n, 0 ≤ gamma i := by
    obtain ⟨cRho, tRho, hcRho, htRho, hMP⟩ :=
      _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.statopia_math_node_2026933490_bd269a1d rhoMin hrhoMin
        (hrho_lo.trans hrho_hi)
    intro i
    have hmem := ((hMP (rho m n) hrho_lo hrho_hi).2.2.2.2.2.1 n hn1 i).1.1
    rw [hmpq i] at hmem
    have hsq : Real.sqrt (rho m n) ≤ 1 := by
      simpa using Real.sqrt_le_sqrt hrho_hi
    change 1 - Real.sqrt (rho m n) ≤ gamma i at hmem
    linarith
  let B : Set (Ωs × Matrix (Fin m) (Fin n) ℝ) :=
    {ω | C * deltaM m < _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.maxDeviation
      (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.svals (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.maskedScaled p ω.2 (Om ω.1))) gamma}
  have hBmeas : MeasurableSet B := by
    have hM : Measurable (fun ω : Ωs × Matrix (Fin m) (Fin n) ℝ =>
        _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.maskedScaled p ω.2 (Om ω.1)) := by
      refine measurable_pi_iff.mpr (fun i => measurable_pi_iff.mpr (fun j => ?_))
      exact ((hMask_meas' i j).mul (hXi_meas' i j)).div_const _
    have hS : ∀ i : Fin n, Measurable (fun ω : Ωs × Matrix (Fin m) (Fin n) ℝ =>
        _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.svals (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.maskedScaled p ω.2 (Om ω.1)) i) := by
      intro i
      simpa only [← hsv_svals] using (hSV_meas i).comp hM
    exact measurableSet_lt measurable_const
      (Measurable.iSup (fun i => ((hS i).sub_const (gamma i)).abs))
  have hBbound : (μΩ.prod μG) B ≤ ENNReal.ofReal (c * ((n : ℝ) ^ ((-(2 * D + 8)): ℝ))) := by
    have hfun : _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.mpQuantile (rho m n) n = gamma := funext hmpq
    simpa only [B, hfun] using hbad
  let f : Ωs → ℝ≥0∞ := fun s => μG (Prod.mk s ⁻¹' B)
  have hf : Measurable f := measurable_measure_prodMk_left hBmeas
  let q : ℝ := c * ((n : ℝ) ^ ((-(D + 8)): ℝ))
  have hqpos : 0 < q := mul_pos hc (Real.rpow_pos_of_pos hnpos _)
  have hqne : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr hqpos).ne'
  have hcondbad : μΩ {s | ENNReal.ofReal q < f s} ≤ ENNReal.ofReal (((n : ℝ) ^ ((-D): ℝ))) := by
    have hmark := meas_ge_le_lintegral_div (μ := μΩ) hf.aemeasurable hqne ENNReal.ofReal_ne_top
    have hprod : (∫⁻ s, f s ∂μΩ) = (μΩ.prod μG) B := (Measure.prod_apply hBmeas).symm
    have hratio : c * ((n : ℝ) ^ ((-(2 * D + 8)): ℝ)) / q = ((n : ℝ) ^ ((-D): ℝ)) := by
      dsimp only [q]
      rw [show -(2 * D + 8) = -D + -(D + 8) by ring, Real.rpow_add hnpos]
      field_simp
    calc
      μΩ {s | ENNReal.ofReal q < f s} ≤ μΩ {s | ENNReal.ofReal q ≤ f s} :=
        measure_mono fun s hs => (show ENNReal.ofReal q ≤ f s from le_of_lt hs)
      _ ≤ (∫⁻ s, f s ∂μΩ) / ENNReal.ofReal q := hmark
      _ ≤ ENNReal.ofReal (c * ((n : ℝ) ^ ((-(2 * D + 8)): ℝ))) / ENNReal.ofReal q := by
        rw [hprod]
        exact ENNReal.div_le_div_right hBbound _
      _ = ENNReal.ofReal (((n : ℝ) ^ ((-D): ℝ))) := by
        rw [← ENNReal.ofReal_div_of_pos hqpos, hratio]
  let E : Set Ωs := {s | (∑ i, ∑ j, Om s i j) ≤ 2 * ((m : ℝ) * (n : ℝ) * p)} ∩
    {s | f s ≤ ENNReal.ofReal q}
  have hE : MeasurableSet E := (measurableSet_le hmask_sum_meas measurable_const).inter
    (measurableSet_le hf measurable_const)
  have hEc : μΩ Eᶜ ≤ ENNReal.ofReal (2 * ((n : ℝ) ^ ((-D): ℝ))) := by
    have hcover : Eᶜ ⊆
        {s | (∑ i, ∑ j, Om s i j) ≤ 2 * ((m : ℝ) * (n : ℝ) * p)}ᶜ ∪
        {s | ENNReal.ofReal q < f s} := by
      intro s hs
      by_cases hsize : (∑ i, ∑ j, Om s i j) ≤ 2 * ((m : ℝ) * (n : ℝ) * p)
      · apply Or.inr
        change ENNReal.ofReal q < f s
        exact lt_of_not_ge (fun hh => hs ⟨hsize, hh⟩)
      · exact Or.inl hsize
    refine (measure_mono hcover).trans ((measure_union_le _ _).trans ?_)
    calc
      _ ≤ ENNReal.ofReal (((n : ℝ) ^ ((-D): ℝ))) +
          ENNReal.ofReal (((n : ℝ) ^ ((-D): ℝ))) := add_le_add hmask_size_level hcondbad
      _ = _ := by rw [← ENNReal.ofReal_add (Real.rpow_nonneg hnpos.le _) (Real.rpow_nonneg hnpos.le _)]; congr 1; ring
  have hsmall : Real.sqrt ((n : ℝ) * q) ≤ Real.sqrt c / rhoMin * deltaM m := by
    have hn_inv : ((n : ℝ) ^ ((-1): ℝ)) ≤ rhoMin⁻¹ * (m : ℝ)⁻¹ := by
      rw [Real.rpow_neg_one (n : ℝ)]
      have hnr : rhoMin * (m : ℝ) ≤ (n : ℝ) := hrho_m
      have hh := one_div_le_one_div_of_le (mul_pos hrhoMin hm_pos) hnr
      simpa only [one_div, mul_inv_rev, mul_comm] using hh
    have hrate : ((n : ℝ) ^ ((-(D + 7) / 2): ℝ)) ≤ ((n : ℝ) ^ ((-1): ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hn_ge_one (by linarith)
    have hmi : (m : ℝ)⁻¹ ≤ deltaM m := by
      have hh := one_div_le_one_div_of_le
        (Real.log_pos (by exact_mod_cast (by omega : 1 < m)))
        ((Real.log_le_sub_one_of_pos hm_pos).trans (sub_le_self _ zero_le_one))
      simpa only [one_div, deltaM] using hh
    have hsqrteq : Real.sqrt ((n : ℝ) * q) =
        Real.sqrt c * ((n : ℝ) ^ ((-(D + 7) / 2): ℝ)) := by
      dsimp only [q]
      rw [show (n : ℝ) * (c * ((n : ℝ) ^ ((-(D + 8)): ℝ))) =
          c * ((n : ℝ) ^ ((-(D + 7)): ℝ)) by
        calc (n : ℝ) * (c * ((n : ℝ) ^ ((-(D + 8)): ℝ)))
            = c * (((n : ℝ) ^ (1: ℝ)) * ((n : ℝ) ^ ((-(D + 8)): ℝ))) := by
              rw [Real.rpow_one (n : ℝ)]; ring
          _ = c * ((n : ℝ) ^ ((1 + -(D + 8)): ℝ)) := by rw [Real.rpow_add hnpos]
          _ = _ := by congr 2; ring]
      rw [Real.sqrt_mul hc.le]
      congr 1
      rw [Real.sqrt_eq_rpow (((n : ℝ) ^ ((-(D + 7)): ℝ))), ← Real.rpow_mul hnpos.le]
      congr 1
      ring
    rw [hsqrteq]
    have hh := mul_le_mul_of_nonneg_left
      (hrate.trans (hn_inv.trans (mul_le_mul_of_nonneg_left hmi (inv_nonneg.mpr hrhoMin.le))))
      (Real.sqrt_nonneg c)
    convert hh using 1 <;> ring
  have hsub : E ⊆ {s : Ωs | ∀ i : Fin n,
      |lambdaCirc hnm μG (Om s) i - Real.sqrt p * gamma i| ≤
        (C + 4 * Real.sqrt c / rhoMin) * Real.sqrt p * deltaM m} := by
    intro s hs i
    have hbg : μG {G | C * deltaM m < _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.maxDeviation
        (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.svals (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.maskedScaled p G (Om s))) gamma}
        ≤ ENNReal.ofReal q := hs.2
    have hbias := statopia_math_node_800008803_e75f9479 m n hnm p hp0 hp1 (Om s)
      (hOm_nonneg s) (hOm_le_one s) hs.1 μG (fun a b => (hμG_sq a b).1)
      (fun a b => (hμG_sq a b).2) gamma hgamma_nonneg hgamma_le_two C (deltaM m)
      hC.le hdeltaM_pos.le (fun G hh => hdev_le _ _ hh) q hqpos.le hbg i
    have heq : (∫ G : Matrix (Fin m) (Fin n) ℝ,
        _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.svals (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.maskedScaled p G (Om s)) i ∂μG)
        = ∫ G : Matrix (Fin m) (Fin n) ℝ,
            sv hnm (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.maskedScaled p G (Om s)) i ∂μG := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun G => (hsv_svals _ i).symm
    rw [heq] at hbias
    rw [hLambda_masked]
    have herr : C * deltaM m + 4 * Real.sqrt ((n : ℝ) * q) ≤
        (C + 4 * Real.sqrt c / rhoMin) * deltaM m := by
      calc C * deltaM m + 4 * Real.sqrt ((n : ℝ) * q)
          ≤ C * deltaM m + 4 * (Real.sqrt c / rhoMin * deltaM m) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left hsmall (by norm_num : (0 : ℝ) ≤ 4))
        _ = _ := by ring
    have hmul := mul_le_mul_of_nonneg_left (hbias.trans herr) (Real.sqrt_nonneg p)
    rw [← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg p)]
    nlinarith [hmul]
  have hmeasure : ENNReal.ofReal (1 - 2 * ((n : ℝ) ^ ((-D): ℝ))) ≤ μΩ E := by
    calc
      _ = 1 - ENNReal.ofReal (2 * ((n : ℝ) ^ ((-D): ℝ))) := by
        rw [ENNReal.ofReal_sub 1 (mul_nonneg (by norm_num) (Real.rpow_nonneg hnpos.le _)), ENNReal.ofReal_one]
      _ ≤ 1 - μΩ Eᶜ := tsub_le_tsub_left hEc 1
      _ = μΩ E := by
        have hcE : μΩ Eᶜ = 1 - μΩ E := by
          simpa only [measure_univ] using measure_compl hE (measure_ne_top μΩ E)
        rw [hcE]
        exact ENNReal.sub_sub_cancel (by simp) (by simpa only [measure_univ] using (measure_mono (μ := μΩ) (Set.subset_univ E)))
  exact hmeasure.trans (measure_mono hsub)


  /- @proof-region region.target-node.session.271bda966c17c4a2 end -/

end ResidualLoss20261106.Statlib.Imported

end

#print axioms ResidualLoss20261106.Statlib.Imported.reference_all_alpha

