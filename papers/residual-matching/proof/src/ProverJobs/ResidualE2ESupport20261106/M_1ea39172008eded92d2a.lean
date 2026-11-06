import Lean
import ProverJobs.ResidualE2ESupport20261106.M_02fc9694186f0fd2900a
import ProverJobs.ResidualE2ESupport20261106.M_50f208e14c5d915b72d3
import ProverJobs.ResidualE2ESupport20261106.M_a310036c0c54e1f04215

namespace PaperProofTasks.ResidualE2ESupport20261106

run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
noncomputable section
set_option maxHeartbeats 2000000
set_option autoImplicit false in
theorem statopia_math_node_1400306846_f9cab3da : ∀ (rho : ℝ) (hrho : 0 < rho)
    (alpha0 : ℝ) (halpha0 : 15 < alpha0),
    ∃ CL : ℝ, 0 < CL ∧ ∃ N1 : ℕ, 3 ≤ N1 ∧
      ∀ (m n : ℕ), 1 ≤ n → n ≤ m → N1 ≤ m → rho ≤ (n : ℝ) / (m : ℝ) →
        ∀ (p : ℝ), 0 ≤ p → p ≤ 1 →
          (m : ℝ) * p ≥ Real.rpow (Real.log (m : ℝ)) alpha0 →
          ∀ {Ωm : Type*} [MeasurableSpace Ωm] (P : Measure Ωm) [IsProbabilityMeasure P]
            (Om : Fin m → Fin n → Ωm → ℝ),
            (∀ (i : Fin m) (j : Fin n), Measurable (Om i j)) →
            iIndepFun (fun (ij : Fin m × Fin n) => Om ij.1 ij.2) P →
            (∀ (i : Fin m) (j : Fin n), ∀ᵐ ω ∂P, Om i j ω = 0 ∨ Om i j ω = 1) →
            (∀ (i : Fin m) (j : Fin n), Integrable (Om i j) P) →
            (∀ (i : Fin m) (j : Fin n), ∫ ω, Om i j ω ∂P = p) →
            1 - ENNReal.ofReal ((1 / 2 : ℝ) * (n : ℝ) ^ (-4 : ℤ)) ≤
              P {ω | specNorm
                    (Matrix.of (fun i j => (Om i j ω - p) / Real.sqrt ((m : ℝ) * p)))
                  ≤ CL} := by
  classical
  intro rho hrho alpha0 halpha0
  obtain ⟨Cbig, hCbigpos, hbridge⟩ := ResidualMaskRepair20261106.mask_norm_vs_gaussian_mean
  obtain ⟨N0, hN0⟩ := exists_nat_gt ((4 * (1 + 1 / rho)) / rho)
  refine ⟨2 + Cbig * 24, by positivity, max 3 N0, le_max_left _ _, ?_⟩
  intros m n h1le hnm hNm hrho' p hp0 hp1 hgrowth Ωm instΩm P instP Om hmeas hindep hbin hInt hint
  by_cases hp : p = 1
  · -- p = 1
    have hOm : ∀ (i : Fin m) (j : Fin n), ∀ᵐ ω ∂P, Om i j ω = 1 := by
      intro i j
      have hE := hbin i j
      have hInt : Integrable (Om i j) P := by
        refine Integrable.mono' (integrable_const (1:ℝ)) (hmeas i j).aestronglyMeasurable ?_
        filter_upwards [hE] with ω hω
        rcases hω with h | h <;> simp [h]
      have hgInt : Integrable (fun ω => (1:ℝ) - Om i j ω) P :=
        (integrable_const (1:ℝ)).sub hInt
      have hgnn : 0 ≤ᵐ[P] (fun ω => (1:ℝ) - Om i j ω) := by
        filter_upwards [hE] with ω hω
        rcases hω with h | h <;> simp [h]
      have hgint : ∫ ω, ((1:ℝ) - Om i j ω) ∂P = 0 := by
        rw [integral_sub (integrable_const (1:ℝ)) hInt]
        have h1 : ∫ _ : Ωm, (1:ℝ) ∂P = 1 := by rw [integral_const]; simp
        rw [h1, hint i j, hp]; ring
      have hz : (fun ω => (1:ℝ) - Om i j ω) =ᵐ[P] 0 :=
        (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hgnn hgInt).mp hgint
      filter_upwards [hz] with ω hω
      have hω' : (1:ℝ) - Om i j ω = 0 := by simpa using hω
      linarith
    have hall : ∀ᵐ ω ∂P, ∀ (i : Fin m) (j : Fin n), Om i j ω = 1 := by
      have key : ∀ (s : Finset (Fin m × Fin n)), ∀ᵐ ω ∂P, ∀ ij ∈ s, Om ij.1 ij.2 ω = 1 := by
        intro s
        induction s using Finset.induction with
        | empty => simp
        | insert a s ha ih =>
            filter_upwards [(hOm a.1 a.2).and ih] with ω hω
            intro ij hij
            rw [Finset.mem_insert] at hij
            rcases hij with rfl | hij
            · exact hω.1
            · exact hω.2 ij hij
      filter_upwards [key Finset.univ] with ω hω i j
      exact hω (i, j) (Finset.mem_univ _)
    have hgoal_ae : ∀ᵐ ω ∂P, specNorm (Matrix.of (fun i j => (Om i j ω - p) / Real.sqrt ((m:ℝ) * p))) ≤ 2 + Cbig * 24 := by
      filter_upwards [hall] with ω hω
      have hmat0 : Matrix.of (fun i j => (Om i j ω - p) / Real.sqrt ((m:ℝ) * p)) = (0 : Matrix (Fin m) (Fin n) ℝ) := by
        ext i j
        change (Om i j ω - p) / Real.sqrt ((m:ℝ) * p) = 0
        rw [hω i j, hp]; simp
      rw [hmat0]
      have hsn : specNorm (0 : Matrix (Fin m) (Fin n) ℝ) = 0 := by simp [specNorm]
      rw [hsn]
      have hb : (0:ℝ) ≤ Cbig * 24 := mul_nonneg (le_of_lt hCbigpos) (by norm_num)
      linarith [hb, hCbigpos]
    have hSc : P ({ω : Ωm | specNorm (Matrix.of (fun i j => (Om i j ω - p) / Real.sqrt ((m:ℝ) * p))) ≤ 2 + Cbig * 24})ᶜ = 0 :=
      (MeasureTheory.ae_iff).mp hgoal_ae
    have hcongr : ({ω : Ωm | specNorm (Matrix.of (fun i j => (Om i j ω - p) / Real.sqrt ((m:ℝ) * p))) ≤ 2 + Cbig * 24}) =ᵐ[P] Set.univ :=
      MeasureTheory.ae_eq_univ.mpr hSc
    show 1 - ENNReal.ofReal ((1 / 2 : ℝ) * ((n : ℝ)) ^ (-4 : ℤ)) ≤ P {ω : Ωm | specNorm (Matrix.of (fun i j => (Om i j ω - p) / Real.sqrt ((m:ℝ) * p))) ≤ 2 + Cbig * 24}
    rw [MeasureTheory.measure_congr hcongr, MeasureTheory.measure_univ]
    rw [tsub_le_iff_right]
    exact le_add_of_nonneg_right (zero_le _)
  · have hn_nat : 0 < n := by omega
    have hm3 : 3 ≤ m := le_trans (le_max_left 3 N0) hNm
    have hm_nat : 0 < m := by omega
    have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm_nat
    have hlogpos : 0 < Real.log (m:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
    have hmp_pos : 0 < (m:ℝ) * p := lt_of_lt_of_le (Real.rpow_pos_of_pos hlogpos alpha0) hgrowth
    have hp_pos : 0 < p := by nlinarith
    have hp_lt_one : p < 1 := lt_of_le_of_ne hp1 hp
    have nlarge : (4:ℝ) * (1 + 1/rho) ≤ (n:ℝ) := by
      have hN0m : N0 ≤ m := le_trans (le_max_right 3 N0) hNm
      have hN0mR : (N0:ℝ) ≤ (m:ℝ) := by exact_mod_cast hN0m
      have step1 : (4:ℝ) * (1 + 1/rho) < (N0:ℝ) * rho := (div_lt_iff₀ hrho).mp hN0
      have step2 : (N0:ℝ) * rho ≤ (n:ℝ) := by
        have ha : (N0:ℝ) * rho ≤ (m:ℝ) * rho := mul_le_mul_of_nonneg_right hN0mR (le_of_lt hrho)
        have hb : (m:ℝ) * rho ≤ (n:ℝ) := by
          have hh := mul_le_mul_of_nonneg_right hrho' (le_of_lt hmpos)
          rw [div_mul_cancel₀ (n:ℝ) (ne_of_gt hmpos)] at hh
          calc (m:ℝ) * rho = rho * (m:ℝ) := by ring
            _ ≤ (n:ℝ) := hh
        linarith [ha, hb]
      linarith [step1, step2]
    have hm_le : (m:ℝ) ≤ (n:ℝ)/rho := by
      rw [le_div_iff₀ hrho]
      have hh := mul_le_mul_of_nonneg_right hrho' (le_of_lt hmpos)
      rw [div_mul_cancel₀ (n:ℝ) (ne_of_gt hmpos)] at hh
      calc (m:ℝ) * rho = rho * (m:ℝ) := by ring
        _ ≤ (n:ℝ) := hh
    have hmn_bound : (m:ℝ) + (n:ℝ) ≤ (n:ℝ)^2/4 := by
      have hfac : (n:ℝ)/rho + (n:ℝ) = (n:ℝ) * (1/rho + 1) := by ring
      have hstep : (1:ℝ)/rho + 1 ≤ (n:ℝ)/4 := by linarith [nlarge]
      have hnn : (0:ℝ) ≤ (n:ℝ) := by positivity
      have h2 : (n:ℝ) * (1/rho + 1) ≤ (n:ℝ) * ((n:ℝ)/4) :=
        mul_le_mul_of_nonneg_left hstep hnn
      have h3 : (n:ℝ) * ((n:ℝ)/4) = (n:ℝ)^2/4 := by ring
      have h1 : (n:ℝ)/rho + (n:ℝ) ≤ (n:ℝ)^2/4 := by
        rw [hfac, ← h3]; exact h2
      linarith [hm_le, h1]
    have hn6 : (n:ℝ)^(-6:ℤ) * ((m:ℝ) + (n:ℝ)) ≤ (1/4) * (n:ℝ)^(-4:ℤ) := by
      have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn_nat
      have hne : (n:ℝ) ≠ 0 := ne_of_gt hnR
      have hpos6 : (0:ℝ) < (n:ℝ)^(-6:ℤ) := zpow_pos hnR (-6)
      have hstep : (n:ℝ)^(-6:ℤ) * ((m:ℝ) + (n:ℝ)) ≤ (n:ℝ)^(-6:ℤ) * ((n:ℝ)^2/4) :=
        mul_le_mul_of_nonneg_left hmn_bound (le_of_lt hpos6)
      have h1 : (n:ℝ)^(-6:ℤ) * (n:ℝ)^2 = (n:ℝ)^(-4:ℤ) := by
        rw [← zpow_natCast, ← zpow_add₀ hne]; norm_num
      have hprod : (n:ℝ)^(-6:ℤ) * ((n:ℝ)^2/4) = (1/4) * (n:ℝ)^(-4:ℤ) := by
        rw [← h1]; ring
      linarith [hstep, hprod]

    let Om' : Fin m → Fin n → Ωm → ℝ := fun i j ω => ResidualMaskRepair20261106.binaryVersion (Om i j ω)
    have hae (i : Fin m) (j : Fin n) : Om' i j =ᵐ[P] Om i j :=
      ResidualMaskRepair20261106.binaryVersion_ae P (Om i j) (hbin i j)
    have hmeas' (i : Fin m) (j : Fin n) : Measurable (Om' i j) :=
      ResidualMaskRepair20261106.binaryVersion_measurable.comp (hmeas i j)
    have hindep' : iIndepFun (fun ij : Fin m × Fin n => Om' ij.1 ij.2) P :=
      ResidualMaskRepair20261106.binaryVersion_independent P _ hindep
    have hpoint' (i : Fin m) (j : Fin n) (ω : Ωm) : Om' i j ω = 0 ∨ Om' i j ω = 1 :=
      ResidualMaskRepair20261106.binaryVersion_binary _
    have hbin' (i : Fin m) (j : Fin n) : ∀ᵐ ω ∂P, Om' i j ω = 0 ∨ Om' i j ω = 1 :=
      ae_of_all _ (hpoint' i j)
    have hint' (i : Fin m) (j : Fin n) : ∫ ω, Om' i j ω ∂P = p :=
      (integral_congr_ae (hae i j)).trans (hint i j)
    have hInt' (i : Fin m) (j : Fin n) : Integrable (Om' i j) P := (hInt i j).congr (hae i j).symm
    let γ := Measure.pi (fun _ : Fin m × Fin n => gaussianReal 0 ((1-p)/(m:ℝ)).toNNReal)
    haveI : IsProbabilityMeasure γ := inferInstance
    let t : ℝ := 6 * Real.log (n:ℝ)
    have ht : 0 ≤ t := mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast h1le))
    let eps : ℝ := Real.sqrt ((1-p)/(m:ℝ)) * Real.sqrt t +
      (1 / Real.sqrt ((m:ℝ)*p)) ^ ((1:ℝ)/3) * (Real.sqrt (1-p)) ^ ((2:ℝ)/3) * t ^ ((2:ℝ)/3) +
      (1 / Real.sqrt ((m:ℝ)*p)) * t
    let mean : ℝ := ∫ y : Ωm × ((Fin m × Fin n) → ℝ), specNorm (fun i j => y.2 (i,j)) ∂(P.prod γ)
    have hmean : mean ≤ 2 :=
      ResidualMaskRepair20261106.Assembly.product_gaussian_specNorm_mean_le_two m n hm_nat hnm p hp0 hp_lt_one P
    have heps : eps ≤ 24 :=
      ResidualMaskRepair20261106.Assembly.mask_bridge_error_le_twenty_four alpha0 p m n halpha0 hm3 h1le hnm hp0 hp1 hgrowth
    have htail := hbridge m n hm_nat hn_nat hnm p hp_pos hp1 hp_lt_one P Om' hmeas' hindep' hbin' hInt' hint' hpoint' t ht
    change (P.prod γ) {x | Cbig * eps < |specNorm (fun i j => (Om' i j x.1-p)/Real.sqrt ((m:ℝ)*p)) - mean|}
      ≤ ENNReal.ofReal (((m+n:ℕ):ℝ) * Real.exp (-t)) at htail
    have hsubset : {x : Ωm × ((Fin m × Fin n) → ℝ) | 2+Cbig*24 < specNorm (fun i j => (Om' i j x.1-p)/Real.sqrt ((m:ℝ)*p))} ⊆
        {x | Cbig * eps < |specNorm (fun i j => (Om' i j x.1-p)/Real.sqrt ((m:ℝ)*p)) - mean|} := by
      intro x hx
      have hab := le_abs_self (specNorm (fun i j => (Om' i j x.1-p)/Real.sqrt ((m:ℝ)*p)) - mean)
      have hh := mul_le_mul_of_nonneg_left heps hCbigpos.le
      change 2+Cbig*24 < _ at hx
      change Cbig * eps < |specNorm (fun i j => (Om' i j x.1-p)/Real.sqrt ((m:ℝ)*p)) - mean|
      linarith
    have hexp : Real.exp (-t) = (n:ℝ)^(-6:ℤ) := by
      dsimp [t]
      rw [Real.exp_neg]
      have hnR : (0:ℝ) < n := by exact_mod_cast hn_nat
      have h6 : Real.exp (6 * Real.log (n:ℝ)) = (n:ℝ)^6 := by
        rw [show (6:ℝ) = (6:ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log hnR]
      rw [h6]
      change ((n:ℝ)^6)⁻¹ = ((n:ℝ)^6)⁻¹
      rfl
    have htail' : (P.prod γ) {x : Ωm × ((Fin m × Fin n) → ℝ) | 2+Cbig*24 < specNorm (fun i j => (Om' i j x.1-p)/Real.sqrt ((m:ℝ)*p))} ≤
        ENNReal.ofReal ((1/2:ℝ)*(n:ℝ)^(-4:ℤ)) := by
      refine le_trans (measure_mono hsubset) (le_trans htail ?_)
      apply ENNReal.ofReal_le_ofReal
      rw [hexp, Nat.cast_add]
      have hz : (0:ℝ) ≤ (n:ℝ)^(-4:ℤ) := by positivity
      nlinarith [hn6]
    have hreduce : (P.prod γ) {x : Ωm × ((Fin m × Fin n) → ℝ) | 2+Cbig*24 < specNorm (fun i j => (Om' i j x.1-p)/Real.sqrt ((m:ℝ)*p))} =
        P {ω | 2+Cbig*24 < specNorm (fun i j => (Om' i j ω-p)/Real.sqrt ((m:ℝ)*p))} := by
      have heq : {x : Ωm × ((Fin m × Fin n) → ℝ) | 2+Cbig*24 < specNorm (fun i j => (Om' i j x.1-p)/Real.sqrt ((m:ℝ)*p))} =
          {ω | 2+Cbig*24 < specNorm (fun i j => (Om' i j ω-p)/Real.sqrt ((m:ℝ)*p))} ×ˢ Set.univ := by ext x; simp
      rw [heq, Measure.prod_prod, measure_univ, mul_one]
    rw [hreduce] at htail'
    have hall : ∀ᵐ ω ∂P, ∀ i j, Om' i j ω = Om i j ω := by
      simpa only [ae_all_iff] using (fun i j => hae i j)
    have hcongr : {ω | 2+Cbig*24 < specNorm (fun i j => (Om' i j ω-p)/Real.sqrt ((m:ℝ)*p))} =ᵐ[P]
        {ω | 2+Cbig*24 < specNorm (fun i j => (Om i j ω-p)/Real.sqrt ((m:ℝ)*p))} := by
      filter_upwards [hall] with ω hω
      have heq : (fun i j => (Om' i j ω-p)/Real.sqrt ((m:ℝ)*p)) = (fun i j => (Om i j ω-p)/Real.sqrt ((m:ℝ)*p)) := by
        ext i j; rw [hω i j]
      change (2+Cbig*24 < specNorm (fun i j => (Om' i j ω-p)/Real.sqrt ((m:ℝ)*p))) =
        (2+Cbig*24 < specNorm (fun i j => (Om i j ω-p)/Real.sqrt ((m:ℝ)*p)))
      rw [heq]
    rw [measure_congr hcongr] at htail'
    have hcover : (Set.univ : Set Ωm) ⊆
        {ω | 2+Cbig*24 < specNorm (fun i j => (Om i j ω-p)/Real.sqrt ((m:ℝ)*p))} ∪
        {ω | specNorm (fun i j => (Om i j ω-p)/Real.sqrt ((m:ℝ)*p)) ≤ 2+Cbig*24} := by
      intro ω _; simp only [Set.mem_union, Set.mem_setOf_eq]; exact lt_or_ge _ _
    have hone : 1 ≤ ENNReal.ofReal ((1/2:ℝ)*(n:ℝ)^(-4:ℤ)) +
        P {ω | specNorm (fun i j => (Om i j ω-p)/Real.sqrt ((m:ℝ)*p)) ≤ 2+Cbig*24} := by
      calc
        1 = P Set.univ := measure_univ.symm
        _ ≤ P (_ ∪ _) := measure_mono hcover
        _ ≤ _ := measure_union_le _ _
        _ ≤ _ := add_le_add htail' le_rfl
    rw [tsub_le_iff_right]
    simpa only [Matrix.of_apply, add_comm] using hone

end
end Statlib.Imported
#print axioms Statlib.Imported.statopia_math_node_1400306846_f9cab3da

