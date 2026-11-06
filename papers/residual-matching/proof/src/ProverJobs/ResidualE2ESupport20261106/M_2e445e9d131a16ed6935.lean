import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.SingularValueProperties
import Statlib.HighDim.MatrixAnalysis.SoftThresholdDenoisingHelpers
import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Statlib.HighDim.Vocabulary.SVD
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_655541399eba6e711ce1
import ProverJobs.ResidualE2ESupport20261106.M_d580ac9e42f19ac4b981
import ProverJobs.ResidualE2ESupport20261106.M_464261436ec0013c34c8
import ProverJobs.ResidualE2ESupport20261106.M_a8791fa1d3e4fe57b534

namespace PaperProofTasks.ResidualE2ESupport20261106
open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported
open scoped Matrix.Norms.L2Operator

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_387310739_6591aef4 : ∀ (D0 : ℝ) (hD0 : 0 < D0)
    (rhoMinus : ℝ) (hrhoMinus_pos : 0 < rhoMinus) (hrhoMinus_le : rhoMinus ≤ 1)
    (Kt : ℝ) (hKt : 0 < Kt)
    (alpha0 : ℝ) (halpha0 : 15 < alpha0)
    (CD : ℝ) (hCD : Kt * (D0 + 12) ≤ CD),
    ∃ Ce : ℝ, 0 < Ce ∧ ∃ M1 : ℕ,
      ∀ (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hnm : n ≤ m) (hM1 : M1 ≤ m)
        (hrho_lo : rhoMinus ≤ (n : ℝ) / (m : ℝ))
        (hrho_hi : (n : ℝ) / (m : ℝ) ≤ 1)
        (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
        (hsparse : Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p)
        (L : ℝ)
        (hL : L = CD * Real.log ((m : ℝ) * (n : ℝ)) +
          10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4),
        ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (Xi Mask : Ω → Matrix (Fin m) (Fin n) ℝ),
          (∀ (i : Fin m) (j : Fin n), Measurable fun ω => Xi ω i j) →
          (∀ (i : Fin m) (j : Fin n), Integrable (fun ω => Xi ω i j) μ) →
          (∀ (i : Fin m) (j : Fin n), Integrable (fun ω => (Xi ω i j) ^ 2) μ) →
          iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Xi ω ij.1 ij.2) μ →
          (∀ (i : Fin m) (j : Fin n), ∫ ω, Xi ω i j ∂μ = 0) →
          (∀ (i : Fin m) (j : Fin n), ∫ ω, (Xi ω i j) ^ 2 ∂μ = 1) →
          (∀ (i : Fin m) (j : Fin n) (t : ℝ), 0 < t →
            μ {ω | t < |Xi ω i j|} ≤ ENNReal.ofReal (2 * Real.exp (-t / Kt))) →
          (∀ (i : Fin m) (j : Fin n), Measurable fun ω => Mask ω i j) →
          (∀ (i : Fin m) (j : Fin n) (ω : Ω), Mask ω i j = 0 ∨ Mask ω i j = 1) →
          (∀ (i : Fin m) (j : Fin n), μ {ω | Mask ω i j = 1} = ENNReal.ofReal p) →
          iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Mask ω ij.1 ij.2) μ →
          IndepFun (fun ω (ij : Fin m × Fin n) => Xi ω ij.1 ij.2)
            (fun ω (ij : Fin m × Fin n) => Mask ω ij.1 ij.2) μ →
          (b c : Fin m → Fin n → ℝ) →
          (hb : ∀ (i : Fin m) (j : Fin n),
            b i j = ∫ ω, Xi ω i j * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0) ∂μ) →
          (hc : ∀ (i : Fin m) (j : Fin n),
            c i j = Real.sqrt
              (∫ ω, (Xi ω i j * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0) - b i j) ^ 2 ∂μ)) →
          (hc_pos : ∀ (i : Fin m) (j : Fin n), 0 < c i j) →
          (XT : Ω → Matrix (Fin m) (Fin n) ℝ) →
          (hXT : ∀ (ω : Ω) (i : Fin m) (j : Fin n),
            XT ω i j = (Xi ω i j * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0) - b i j) /
              c i j) →
          (hXT_mean : ∀ (i : Fin m) (j : Fin n), ∫ ω, XT ω i j ∂μ = 0) →
          (hXT_var : ∀ (i : Fin m) (j : Fin n), ∫ ω, (XT ω i j) ^ 2 ∂μ = 1) →
          (hXT_bound : ∀ (ω : Ω) (i : Fin m) (j : Fin n), |XT ω i j| ≤ 3 * L) →
          (htail : μ {ω : Ω | ∃ (i : Fin m) (j : Fin n), L < |Xi ω i j|} ≤
            ENNReal.ofReal (Real.rpow (n : ℝ) (-(D0 + 10)))) →
          (htransfer : ∀ (ω : Ω), (∀ (i : Fin m) (j : Fin n), |Xi ω i j| ≤ L) →
            ‖maskedScaled p (Xi ω) (Mask ω) - maskedScaled p (XT ω) (Mask ω)‖ ≤
              Real.rpow (n : ℝ) (-(D0 + 5))) →
          ∃ G : Set Ω, MeasurableSet G ∧
            μ Gᶜ ≤ ENNReal.ofReal (Real.rpow (n : ℝ) (-(D0 + 2))) ∧
            ∀ ω ∈ G,
              svals (maskedScaled p (Xi ω) (Mask ω)) ⟨0, by omega⟩ ≤
                1 + Real.sqrt ((n : ℝ) / (m : ℝ)) + Ce * deltaM m ∧
              1 - Real.sqrt ((n : ℝ) / (m : ℝ)) - Ce * deltaM m ≤
                svals (maskedScaled p (Xi ω) (Mask ω)) ⟨n - 1, by omega⟩ ∧
              ‖maskedScaled p (Xi ω) (Mask ω)‖ ≤ 4 := by
  /- @proof-region region.target-node.session.fd258a7fd0fe52d3 begin -/
  intro D0 hD0 rhoMinus h_rhoMinus_pos h_rhoMinus_le Kt hKt alpha0 h_alpha0 CD hCD
  classical
  have hXnn : (0 : ℝ) ≤ rhoMinus ^ (-(D0 + 5)) := Real.rpow_nonneg (le_of_lt h_rhoMinus_pos) _
  have hΛ : max (Kt * (D0 + 12)) (D0 + 20) ≤ max CD (D0 + 20) :=
    max_le (le_trans hCD (le_max_left CD (D0 + 20))) (le_max_right CD (D0 + 20))
  obtain ⟨Ce0, hCe0pos, M10, hedgeFn⟩ :=
    statopia_math_node_784642610_04ca9caa D0 hD0 rhoMinus h_rhoMinus_pos h_rhoMinus_le
      Kt hKt alpha0 h_alpha0 (max CD (D0 + 20)) hΛ
  have hCePos : (0 : ℝ) < Ce0 + rhoMinus ^ (-(D0 + 5)) + 1 := by linarith
  refine ⟨Ce0 + rhoMinus ^ (-(D0 + 5)) + 1, hCePos,
    max M10 (max 2 (Nat.ceil (Real.exp (Ce0 + rhoMinus ^ (-(D0 + 5)) + 1)))), ?_⟩
  intro m n hm hn hnm hM1 hrho_lo hrho_hi p hp0 hp1 hsparse L hL
  intro Ω _ μ _ Xi Mask hXi_meas hXi_int hXi_sq_int hXi_indep hXi_mean hXi_var hXi_tail
    hMask_meas hMask_val hMask_law hMask_indep hIndep b c hb hc hc_pos XT hXT hXT_mean
    hXT_var hXT_bound htail htransfer
  by_cases hn1 : n = 1
  · subst n
    exact ⟨∅, MeasurableSet.empty, by simp, by rintro ω hω; simp at hω⟩
  · have hn2 : 2 ≤ n := by omega
    have hM10le : M10 ≤ m := le_trans (le_max_left _ _) hM1
    have hm2 : 2 ≤ m := le_trans (le_max_left 2 _) (le_trans (le_max_right M10 _) hM1)
    have hmone : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
    have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hlogmn_pos : 0 < Real.log ((m : ℝ) * (n : ℝ)) := by
      apply Real.log_pos
      have h1 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
      nlinarith [hn_ge1]
    have hKle : Nat.ceil (Real.exp (Ce0 + rhoMinus ^ (-(D0 + 5)) + 1)) ≤ m :=
      le_trans (le_max_right 2 _) (le_trans (le_max_right M10 _) hM1)
    have hlogK : Ce0 + rhoMinus ^ (-(D0 + 5)) + 1 ≤ Real.log (m : ℝ) := by
      have hexp_pos : 0 < Real.exp (Ce0 + rhoMinus ^ (-(D0 + 5)) + 1) := Real.exp_pos _
      have hexp_le : Real.exp (Ce0 + rhoMinus ^ (-(D0 + 5)) + 1) ≤ (m : ℝ) :=
        le_trans (Nat.le_ceil _) (by exact_mod_cast hKle)
      have h := Real.log_le_log hexp_pos hexp_le
      rwa [Real.log_exp] at h
    have hlog_pos : 0 < Real.log (m : ℝ) := by linarith
    have hδpos : 0 < deltaM m := by
      rw [deltaM]
      exact inv_pos.mpr hlog_pos
    have hδnn : (0 : ℝ) ≤ deltaM m := le_of_lt hδpos
    have hCeδ : (Ce0 + rhoMinus ^ (-(D0 + 5)) + 1) * deltaM m ≤ 1 := by
      rw [deltaM, ← one_div, ← div_eq_mul_one_div]
      exact (div_le_one hlog_pos).2 (by linarith)
    have hmeasset : ∀ (i : Fin m) (j : Fin n), MeasurableSet {ω : Ω | |Xi ω i j| ≤ L} := by
      intro i j
      exact measurableSet_le (by simpa only [Real.norm_eq_abs] using (hXi_meas i j).norm)
        measurable_const
    have hXT_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun ω => XT ω i j := by
      intro i j
      have hfun0 : (fun ω => Xi ω i j * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0))
          = {ω : Ω | |Xi ω i j| ≤ L}.indicator (fun ω => Xi ω i j) := by
        funext ω
        by_cases hc : (|Xi ω i j| ≤ L)
        · simp [hc]
        · simp [hc]
      have hprod : Measurable fun ω =>
          Xi ω i j * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0) := by
        rw [hfun0]
        exact (hXi_meas i j).indicator (hmeasset i j)
      have hbase : Measurable fun ω =>
          (Xi ω i j * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0) - b i j) / c i j :=
        (hprod.sub measurable_const).div_const (c i j)
      have hfun : (fun ω => XT ω i j) =
          fun ω => (Xi ω i j * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0) - b i j) / c i j := by
        funext ω
        exact hXT ω i j
      rw [hfun]
      exact hbase
    have hXT_indep : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => XT ω ij.1 ij.2) μ := by
      have hcomp := hXi_indep.comp
        (fun (ij : Fin m × Fin n) (x : ℝ) =>
          (x * (if |x| ≤ L then (1 : ℝ) else 0) - b ij.1 ij.2) / c ij.1 ij.2)
        (fun ij => by
          have hfun2 : (fun x : ℝ => x * (if |x| ≤ L then (1 : ℝ) else 0))
              = {x : ℝ | |x| ≤ L}.indicator (fun x : ℝ => x) := by
            funext x
            by_cases hx : (|x| ≤ L)
            · simp [hx]
            · simp [hx]
          have hm1 : Measurable fun x : ℝ => x * (if |x| ≤ L then (1 : ℝ) else 0) := by
            rw [hfun2]
            exact (measurable_id : Measurable fun x : ℝ => x).indicator
              (measurableSet_le (by simpa only [Real.norm_eq_abs] using
                (measurable_id : Measurable fun x : ℝ => x).norm) measurable_const)
          exact (hm1.sub measurable_const).div_const (c ij.1 ij.2))
      have hfun : (fun (ij : Fin m × Fin n) (ω : Ω) => XT ω ij.1 ij.2)
          = fun (ij : Fin m × Fin n) (ω : Ω) =>
              (fun (ij : Fin m × Fin n) (x : ℝ) =>
                (x * (if |x| ≤ L then (1 : ℝ) else 0) - b ij.1 ij.2) / c ij.1 ij.2) ij
                ((fun (ij : Fin m × Fin n) (ω : Ω) => Xi ω ij.1 ij.2) ij ω) := by
        funext ij ω
        exact hXT ω ij.1 ij.2
      rw [hfun]
      exact hcomp
    have hXT_mask_indep : IndepFun (fun (ω : Ω) (ij : Fin m × Fin n) => XT ω ij.1 ij.2)
        (fun (ω : Ω) (ij : Fin m × Fin n) => Mask ω ij.1 ij.2) μ := by
      have hφmeas : Measurable (fun x : Fin m × Fin n → ℝ => fun (ij : Fin m × Fin n) =>
          (x ij * (if |x ij| ≤ L then (1 : ℝ) else 0) - b ij.1 ij.2) / c ij.1 ij.2) := by
        refine measurable_pi_iff.mpr (fun ij => ?_)
        have hev : Measurable fun x : Fin m × Fin n → ℝ => x ij := measurable_pi_apply ij
        have hfun0 : (fun x : Fin m × Fin n → ℝ => x ij * (if |x ij| ≤ L then (1 : ℝ) else 0))
            = {x : Fin m × Fin n → ℝ | |x ij| ≤ L}.indicator (fun x => x ij) := by
          funext x
          by_cases hx : (|x ij| ≤ L)
          · simp [hx]
          · simp [hx]
        have hm1 : Measurable fun x : Fin m × Fin n → ℝ =>
            x ij * (if |x ij| ≤ L then (1 : ℝ) else 0) := by
          rw [hfun0]
          exact hev.indicator
            (measurableSet_le (by simpa only [Real.norm_eq_abs] using hev.norm) measurable_const)
        exact (hm1.sub measurable_const).div_const (c ij.1 ij.2)
      have hcomp := hIndep.comp hφmeas measurable_id
      have hfun1 : (fun (ω : Ω) (ij : Fin m × Fin n) => XT ω ij.1 ij.2)
          = (fun x : Fin m × Fin n → ℝ => fun (ij : Fin m × Fin n) =>
              (x ij * (if |x ij| ≤ L then (1 : ℝ) else 0) - b ij.1 ij.2) / c ij.1 ij.2) ∘
            (fun (ω : Ω) (ij : Fin m × Fin n) => Xi ω ij.1 ij.2) := by
        funext ω ij
        exact hXT ω ij.1 ij.2
      have hfun2 : (fun (ω : Ω) (ij : Fin m × Fin n) => Mask ω ij.1 ij.2)
          = (id : (Fin m × Fin n → ℝ) → (Fin m × Fin n → ℝ)) ∘
            (fun (ω : Ω) (ij : Fin m × Fin n) => Mask ω ij.1 ij.2) := rfl
      rw [hfun1, hfun2]
      exact hcomp
    have hXTbndL : ∀ (ω : Ω) (i : Fin m) (j : Fin n),
        |XT ω i j| ≤ 3 * (max CD (D0 + 20) * Real.log ((m : ℝ) * (n : ℝ)) +
          10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) := by
      intro ω i j
      have hle : CD * Real.log ((m : ℝ) * (n : ℝ)) ≤
          max CD (D0 + 20) * Real.log ((m : ℝ) * (n : ℝ)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (le_of_lt hlogmn_pos)
      have hLle : L ≤ max CD (D0 + 20) * Real.log ((m : ℝ) * (n : ℝ)) +
          10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 := by
        rw [hL]
        linarith
      linarith [hXT_bound ω i j]
    have hedgeG := hedgeFn m n hm2 hn hnm hM10le hrho_lo hrho_hi p hp0 hp1 hsparse
      μ XT Mask hXT_meas hMask_meas hMask_val hMask_law hXT_indep hMask_indep hXT_mask_indep
      hXT_mean hXT_var hXTbndL
    obtain ⟨G, hGmeas, hGmeasLe, hGbounds⟩ := hedgeG
    have hsvals_bridge : ∀ (A : Matrix (Fin m) (Fin n) ℝ) (k : Fin n),
        svals A k = Statlib.HighDim.MatrixAnalysis.singularValues A
          (Fin.cast (by omega : n = min m n) k) := by
      intro A k
      rw [Statlib.HighDim.MatrixAnalysis.singularValues_eq_vocabulary]
      first
        | rfl
        | simp only [svals, Statlib.HighDim.Vocabulary.singularValues]
    have hnorm_of_svals : ∀ (ω : Ω),
        svals (maskedScaled p (Xi ω) (Mask ω)) ⟨0, by omega⟩ ≤
          1 + Real.sqrt ((n : ℝ) / (m : ℝ)) + (Ce0 + rhoMinus ^ (-(D0 + 5)) + 1) * deltaM m →
        ‖maskedScaled p (Xi ω) (Mask ω)‖ ≤ 4 := by
      intro ω hω
      have hmin : 0 < min m n := Nat.lt_min.mpr ⟨by omega, by omega⟩
      have hprops := (Statlib.HighDim.MatrixAnalysis.singular_value_properties
        (maskedScaled p (Xi ω) (Mask ω))
        (Or.inl (⟨⟨0, by omega⟩⟩ : Nonempty (Fin m)))).1 hmin
      have hAeq : ‖maskedScaled p (Xi ω) (Mask ω)‖ =
          svals (maskedScaled p (Xi ω) (Mask ω)) ⟨0, by omega⟩ := by
        rw [hsvals_bridge (maskedScaled p (Xi ω) (Mask ω)) ⟨0, by omega⟩]
        exact hprops.symm
      rw [hAeq]
      have hsq : Real.sqrt ((n : ℝ) / (m : ℝ)) ≤ 1 := by
        rw [Real.sqrt_le_one]
        exact hrho_hi
      linarith
    have htrans_le : Real.rpow (n : ℝ) (-(D0 + 5)) ≤
        rhoMinus ^ (-(D0 + 5)) * deltaM m := by
      have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
      have hnlo : rhoMinus * (m : ℝ) ≤ (n : ℝ) := by
        have h1 := mul_le_mul_of_nonneg_right hrho_lo (le_of_lt hmpos)
        have h2 : ((n : ℝ) / (m : ℝ)) * (m : ℝ) = (n : ℝ) := div_mul_cancel₀ _ hmne
        linarith [h1, h2]
      have hbmR : 0 < rhoMinus * (m : ℝ) := mul_pos h_rhoMinus_pos hmpos
      have hbase : Real.rpow (n : ℝ) (-(D0 + 5)) ≤
          Real.rpow (rhoMinus * (m : ℝ)) (-(D0 + 5)) :=
        Real.rpow_le_rpow_of_nonpos hbmR hnlo (by linarith)
      have hmulr : Real.rpow (rhoMinus * (m : ℝ)) (-(D0 + 5)) =
          Real.rpow rhoMinus (-(D0 + 5)) * Real.rpow (m : ℝ) (-(D0 + 5)) :=
        Real.mul_rpow (le_of_lt h_rhoMinus_pos) (le_of_lt hmpos)
      have hmlog : Real.log (m : ℝ) ≤ Real.rpow (m : ℝ) (D0 + 5) := by
        have h2 : (m : ℝ) ≤ Real.rpow (m : ℝ) (D0 + 5) :=
          Real.self_le_rpow_of_one_le hmone (by linarith)
        linarith [Real.log_le_sub_one_of_pos hmpos]
      have hmloss : Real.rpow (m : ℝ) (-(D0 + 5)) ≤ deltaM m := by
        have hdiv : 1 / Real.rpow (m : ℝ) (D0 + 5) ≤ 1 / Real.log (m : ℝ) :=
          one_div_le_one_div_of_le hlog_pos hmlog
        have hleft : Real.rpow (m : ℝ) (-(D0 + 5)) = 1 / Real.rpow (m : ℝ) (D0 + 5) := by
          rw [one_div]
          exact Real.rpow_neg (le_of_lt hmpos) (D0 + 5)
        have hright : deltaM m = 1 / Real.log (m : ℝ) := by
          rw [deltaM, one_div]
        rw [hleft, hright]
        exact hdiv
      have hfin : Real.rpow rhoMinus (-(D0 + 5)) * Real.rpow (m : ℝ) (-(D0 + 5)) ≤
          Real.rpow rhoMinus (-(D0 + 5)) * deltaM m :=
        mul_le_mul_of_nonneg_left hmloss hXnn
      calc Real.rpow (n : ℝ) (-(D0 + 5))
          ≤ Real.rpow (rhoMinus * (m : ℝ)) (-(D0 + 5)) := hbase
        _ = Real.rpow rhoMinus (-(D0 + 5)) * Real.rpow (m : ℝ) (-(D0 + 5)) := hmulr
        _ ≤ Real.rpow rhoMinus (-(D0 + 5)) * deltaM m := hfin
    have hsum : Real.rpow (n : ℝ) (-(D0 + 4)) + Real.rpow (n : ℝ) (-(D0 + 10)) ≤
        Real.rpow (n : ℝ) (-(D0 + 2)) := by
      have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      have hsq : (2 : ℝ) ≤ Real.rpow (n : ℝ) 2 := by
        have h2 : (n : ℝ) ≤ Real.rpow (n : ℝ) 2 :=
          Real.self_le_rpow_of_one_le hn_ge1 (by norm_num : (1 : ℝ) ≤ 2)
        linarith
      have hnn : (0 : ℝ) ≤ Real.rpow (n : ℝ) (-(D0 + 4)) :=
        Real.rpow_nonneg (le_of_lt hnpos) _
      have hmulpow : Real.rpow (n : ℝ) (-(D0 + 4)) * Real.rpow (n : ℝ) 2 =
          Real.rpow (n : ℝ) (-(D0 + 2)) := by
        have h := Real.rpow_add hnpos (-(D0 + 4)) 2
        have h2 : (-(D0 + 4) + 2 : ℝ) = -(D0 + 2) := by ring
        rw [h2] at h
        exact h.symm
      have hstep : 2 * Real.rpow (n : ℝ) (-(D0 + 4)) ≤ Real.rpow (n : ℝ) (-(D0 + 2)) := by
        have hA : Real.rpow (n : ℝ) (-(D0 + 4)) * 2 ≤
            Real.rpow (n : ℝ) (-(D0 + 4)) * Real.rpow (n : ℝ) 2 :=
          mul_le_mul_of_nonneg_left hsq hnn
        have hC : Real.rpow (n : ℝ) (-(D0 + 4)) * 2 =
            2 * Real.rpow (n : ℝ) (-(D0 + 4)) := mul_comm _ _
        rw [hC] at hA
        rw [hmulpow] at hA
        exact hA
      have h1 : Real.rpow (n : ℝ) (-(D0 + 10)) ≤ Real.rpow (n : ℝ) (-(D0 + 4)) :=
        Real.rpow_le_rpow_of_exponent_le hn_ge1 (by linarith)
      linarith [h1, hstep]
    refine ⟨{ω : Ω | ∀ (i : Fin m) (j : Fin n), |Xi ω i j| ≤ L} ∩ G, ?_, ?_, ?_⟩
    · have hEq : {ω : Ω | ∀ (i : Fin m) (j : Fin n), |Xi ω i j| ≤ L}
          = ⋂ i : Fin m, ⋂ j : Fin n, {ω : Ω | |Xi ω i j| ≤ L} := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_iInter]
      rw [hEq]
      exact (MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j =>
        measurableSet_le (by simpa only [Real.norm_eq_abs] using (hXi_meas i j).norm)
          measurable_const))).inter hGmeas
    · have hEq : {ω : Ω | ∀ (i : Fin m) (j : Fin n), |Xi ω i j| ≤ L}ᶜ
          = {ω : Ω | ∃ (i : Fin m) (j : Fin n), L < |Xi ω i j|} := by
        ext ω
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_le]
      rw [Set.compl_inter, hEq]
      refine le_trans (measure_union_le _ _) ?_
      have hrp10 : (0 : ℝ) ≤ Real.rpow (n : ℝ) (-(D0 + 10)) :=
        Real.rpow_nonneg (le_of_lt hnpos) _
      have hrp4 : (0 : ℝ) ≤ Real.rpow (n : ℝ) (-(D0 + 4)) :=
        Real.rpow_nonneg (le_of_lt hnpos) _
      calc μ {ω : Ω | ∃ (i : Fin m) (j : Fin n), L < |Xi ω i j|} + μ Gᶜ
          ≤ ENNReal.ofReal (Real.rpow (n : ℝ) (-(D0 + 10))) +
              ENNReal.ofReal (Real.rpow (n : ℝ) (-(D0 + 4))) := add_le_add htail hGmeasLe
        _ = ENNReal.ofReal (Real.rpow (n : ℝ) (-(D0 + 10)) + Real.rpow (n : ℝ) (-(D0 + 4))) := by
            rw [ENNReal.ofReal_add hrp10 hrp4]
        _ ≤ ENNReal.ofReal (Real.rpow (n : ℝ) (-(D0 + 2))) :=
            ENNReal.ofReal_le_ofReal (by linarith [hsum])
    · rintro ω ⟨htr, hGω⟩
      have hgb := hGbounds ω hGω
      have hTrans : ‖maskedScaled p (Xi ω) (Mask ω) - maskedScaled p (XT ω) (Mask ω)‖ ≤
          Real.rpow (n : ℝ) (-(D0 + 5)) := htransfer ω htr

      have hcast : n = min m n := by omega
      have hupper : ∀ (k : Fin n),
          svals (maskedScaled p (Xi ω) (Mask ω)) k ≤
            svals (maskedScaled p (XT ω) (Mask ω)) k + Real.rpow (n : ℝ) (-(D0 + 5)) := by
        intro k
        have hw := Statlib.HighDim.MatrixAnalysis.rectangular_singularValues_weyl_upper
          (maskedScaled p (XT ω) (Mask ω))
          (maskedScaled p (Xi ω) (Mask ω) - maskedScaled p (XT ω) (Mask ω))
          (Fin.cast hcast k)
        have heq : maskedScaled p (XT ω) (Mask ω) +
            (maskedScaled p (Xi ω) (Mask ω) - maskedScaled p (XT ω) (Mask ω))
            = maskedScaled p (Xi ω) (Mask ω) := by abel
        rw [heq] at hw
        have hnorm : Statlib.HighDim.MatrixAnalysis.opNorm
            (maskedScaled p (Xi ω) (Mask ω) - maskedScaled p (XT ω) (Mask ω)) ≤
            Real.rpow (n : ℝ) (-(D0 + 5)) := by
          rw [Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2]
          exact hTrans
        have hw' : Statlib.HighDim.MatrixAnalysis.singularValues
            (maskedScaled p (Xi ω) (Mask ω)) (Fin.cast hcast k) ≤
            Statlib.HighDim.MatrixAnalysis.singularValues
              (maskedScaled p (XT ω) (Mask ω)) (Fin.cast hcast k) +
              Real.rpow (n : ℝ) (-(D0 + 5)) := by
          linarith [hw, hnorm]
        rw [hsvals_bridge (maskedScaled p (Xi ω) (Mask ω)) k,
          hsvals_bridge (maskedScaled p (XT ω) (Mask ω)) k]
        exact hw'
      have hlower : ∀ (k : Fin n),
          svals (maskedScaled p (XT ω) (Mask ω)) k ≤
            svals (maskedScaled p (Xi ω) (Mask ω)) k + Real.rpow (n : ℝ) (-(D0 + 5)) := by
        intro k
        have hw := Statlib.HighDim.MatrixAnalysis.rectangular_singularValues_weyl_upper
          (maskedScaled p (Xi ω) (Mask ω))
          (maskedScaled p (XT ω) (Mask ω) - maskedScaled p (Xi ω) (Mask ω))
          (Fin.cast hcast k)
        have heq : maskedScaled p (Xi ω) (Mask ω) +
            (maskedScaled p (XT ω) (Mask ω) - maskedScaled p (Xi ω) (Mask ω))
            = maskedScaled p (XT ω) (Mask ω) := by abel
        rw [heq] at hw
        have hnorm : Statlib.HighDim.MatrixAnalysis.opNorm
            (maskedScaled p (XT ω) (Mask ω) - maskedScaled p (Xi ω) (Mask ω)) ≤
            Real.rpow (n : ℝ) (-(D0 + 5)) := by
          rw [Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2, norm_sub_rev]
          exact hTrans
        have hw' : Statlib.HighDim.MatrixAnalysis.singularValues
            (maskedScaled p (XT ω) (Mask ω)) (Fin.cast hcast k) ≤
            Statlib.HighDim.MatrixAnalysis.singularValues
              (maskedScaled p (Xi ω) (Mask ω)) (Fin.cast hcast k) +
              Real.rpow (n : ℝ) (-(D0 + 5)) := by
          linarith [hw, hnorm]
        rw [hsvals_bridge (maskedScaled p (XT ω) (Mask ω)) k,
          hsvals_bridge (maskedScaled p (Xi ω) (Mask ω)) k]
        exact hw'
      have hkey : (Ce0 + rhoMinus ^ (-(D0 + 5)) + 1) * deltaM m =
          Ce0 * deltaM m + rhoMinus ^ (-(D0 + 5)) * deltaM m + deltaM m := by ring
      have htop : svals (maskedScaled p (Xi ω) (Mask ω)) ⟨0, by omega⟩ ≤
          1 + Real.sqrt ((n : ℝ) / (m : ℝ)) + (Ce0 + rhoMinus ^ (-(D0 + 5)) + 1) * deltaM m := by
        have h1 := hgb.1
        have hk0 := hupper (⟨0, by omega⟩ : Fin n)
        rw [hkey]
        linarith [h1, hk0, htrans_le, hδnn]
      have hbot : svals (maskedScaled p (Xi ω) (Mask ω)) ⟨n - 1, by omega⟩ ≥
          1 - Real.sqrt ((n : ℝ) / (m : ℝ)) - (Ce0 + rhoMinus ^ (-(D0 + 5)) + 1) * deltaM m := by
        have h1 := hgb.2
        have hkn := hlower ⟨n - 1, by omega⟩
        rw [hkey]
        linarith [h1, hkn, htrans_le, hδnn]
      exact ⟨htop, hbot, hnorm_of_svals ω htop⟩

  /- @proof-region region.target-node.session.fd258a7fd0fe52d3 end -/

#print axioms statopia_math_node_387310739_6591aef4
end Statlib.Imported

