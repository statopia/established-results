import ProverJobs.jobea4701a9720de21f681f2da3.Vocabulary
import ProverJobs.jobea4701a9720de21f681f2da3.Base
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_315826285_30cc4431_c46d0e4c

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
open Statlib.Imported
open Statlib.Imported.T24
open T24

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
namespace Statlib.Imported
noncomputable section
open T24

set_option autoImplicit false in
theorem statopia_math_node_980129684_7aca482a : ∀ {U : Type*} [MeasurableSpace U] (n : ℕ)
    (kap lam : Fin n → Measure U)
    (hkap : ∀ i : Fin n, IsProbabilityMeasure (kap i))
    (hlam : ∀ i : Fin n, IsProbabilityMeasure (lam i))
    (hac : ∀ i : Fin n, kap i ≪ lam i)
    (hprod : (Measure.pi lam).withDensity
      (fun u : Fin n → U => ∏ i : Fin n, (kap i).rnDeriv (lam i) (u i)) = Measure.pi kap)
    (hllr : MeasureTheory.llr (Measure.pi kap) (Measure.pi lam) =ᵐ[Measure.pi kap]
      (fun u : Fin n → U => ∑ i : Fin n, MeasureTheory.llr (kap i) (lam i) (u i))),
    Integrable (MeasureTheory.llr (Measure.pi kap) (Measure.pi lam)) (Measure.pi kap) →
      ∀ i : Fin n, Integrable (MeasureTheory.llr (kap i) (lam i)) (kap i) := by
  /- @proof-region region.target-node.session.3a1fbbed76cd2c25 begin -/
  refine fun {U} [MeasurableSpace U] n kap lam hkap hlam hac hprod hllr h i => ?_
  haveI hkp : ∀ j, IsProbabilityMeasure (kap j) := hkap
  haveI hlp : ∀ j, IsProbabilityMeasure (lam j) := hlam
  haveI hdec : ∀ j, (kap j).HaveLebesgueDecomposition (lam j) :=
    fun j => Measure.haveLebesgueDecomposition_of_finiteMeasure
  have hlog_bound : ∀ y : ℝ, 0 ≤ y → max (-(Real.log y)) 0 ≤ y⁻¹ := by
    intro y hy
    rcases hy.eq_or_lt with h0 | hpos
    · rw [← h0]
      simp
    · have hyinv : 0 ≤ y⁻¹ := le_of_lt (inv_pos.mpr hpos)
      by_cases h1 : y ≤ 1
      · have hb : Real.log y⁻¹ ≤ y⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
        rw [Real.log_inv] at hb
        exact max_le (by linarith) hyinv
      · have hb : 0 ≤ Real.log y := Real.log_nonneg (le_of_lt (not_le.mp h1))
        exact max_le (by linarith) hyinv
  have hmul_bound : ∀ d : ℝ≥0∞, d * ENNReal.ofReal ((d.toReal)⁻¹) ≤ 1 := by
    intro d
    by_cases hd : d = ⊤
    · simp [hd]
    · by_cases hz : d.toReal = 0
      · have hdz : d = 0 := by
          rw [← ENNReal.ofReal_toReal hd, hz]
          simp
        rw [hdz]
        simp
      · have hy : 0 < d.toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hz)
        have h1 : d.toReal * (d.toReal)⁻¹ = 1 := by field_simp
        have h2 : ENNReal.ofReal d.toReal * ENNReal.ofReal ((d.toReal)⁻¹) = 1 := by
          rw [← ENNReal.ofReal_mul (le_of_lt hy), h1, ENNReal.ofReal_one]
        calc d * ENNReal.ofReal ((d.toReal)⁻¹)
            = ENNReal.ofReal d.toReal * ENNReal.ofReal ((d.toReal)⁻¹) := by
                rw [ENNReal.ofReal_toReal hd]
          _ ≤ 1 := le_of_eq h2
  have hkey : ∀ d : ℝ≥0∞, d * ENNReal.ofReal (max (-(Real.log d.toReal)) 0) ≤ 1 := by
    intro d
    have h1 : max (-(Real.log d.toReal)) 0 ≤ (d.toReal)⁻¹ :=
      hlog_bound d.toReal ENNReal.toReal_nonneg
    calc d * ENNReal.ofReal (max (-(Real.log d.toReal)) 0)
        ≤ d * ENNReal.ofReal ((d.toReal)⁻¹) := by gcongr
      _ ≤ 1 := hmul_bound d
  have hllr_meas : ∀ j, Measurable (llr (kap j) (lam j)) := by
    intro j
    have hdm : Measurable ((kap j).rnDeriv (lam j)) :=
      (Measure.haveLebesgueDecomposition_spec (kap j) (lam j)).1
    rw [llr_def]
    exact Real.measurable_log.comp (ENNReal.measurable_toReal.comp hdm)
  have hmeas_neg : ∀ j,
      Measurable (fun x => ENNReal.ofReal (max (-(llr (kap j) (lam j) x)) 0)) := by
    intro j
    have h1 : Measurable (fun x => max (-(llr (kap j) (lam j) x)) 0) :=
      ((continuous_id.neg.max continuous_const).measurable).comp (hllr_meas j)
    exact ENNReal.measurable_ofReal.comp h1
  have hA : ∀ j, ∫⁻ x, ENNReal.ofReal (max (-(llr (kap j) (lam j) x)) 0) ∂(kap j) ≤ 1 := by
    intro j
    have hdm : Measurable ((kap j).rnDeriv (lam j)) :=
      (Measure.haveLebesgueDecomposition_spec (kap j) (lam j)).1
    have hwd : (lam j).withDensity ((kap j).rnDeriv (lam j)) = kap j :=
      Measure.withDensity_rnDeriv_eq (μ := kap j) (ν := lam j) (hac j)
    calc ∫⁻ x, ENNReal.ofReal (max (-(llr (kap j) (lam j) x)) 0) ∂(kap j)
        = ∫⁻ x, ENNReal.ofReal (max (-(llr (kap j) (lam j) x)) 0)
            ∂((lam j).withDensity ((kap j).rnDeriv (lam j))) := by rw [hwd]
      _ = ∫⁻ x, (kap j).rnDeriv (lam j) x * ENNReal.ofReal (max (-(llr (kap j) (lam j) x)) 0)
            ∂(lam j) := by
          have hkey2 := MeasureTheory.setLIntegral_withDensity_eq_setLIntegral_mul (lam j)
            (f := (kap j).rnDeriv (lam j))
            (g := fun x => ENNReal.ofReal (max (-(llr (kap j) (lam j) x)) 0))
            hdm (hmeas_neg j) (s := Set.univ) MeasurableSet.univ
          simpa using hkey2
      _ ≤ ∫⁻ x, (1 : ℝ≥0∞) ∂(lam j) :=
          lintegral_mono (fun x => by
            have hx := hkey ((kap j).rnDeriv (lam j) x)
            simpa only [llr_def] using hx)
      _ = 1 := by simp
  have hmap : ∀ j : Fin n,
      Measure.map (Function.eval j) (Measure.pi (α := fun _ : Fin n => U) kap) = kap j := by
    intro j
    rw [Measure.pi_map_eval]
    simp
  have hev : ∀ j : Fin n, AEMeasurable (Function.eval j)
      (Measure.pi (α := fun _ : Fin n => U) kap) :=
    fun j => (measurable_pi_apply j).aemeasurable
  have htr : ∀ (j : Fin n) (G : U → ℝ≥0∞), Measurable G →
      ∫⁻ u, G (u j) ∂(Measure.pi (α := fun _ : Fin n => U) kap) = ∫⁻ x, G x ∂(kap j) := by
    intro j G hG
    rw [← hmap j]
    exact (MeasureTheory.lintegral_map' hG.aemeasurable (hev j)).symm
  have hB : ∀ j : Fin n,
      ∫⁻ u, ENNReal.ofReal (max (-(llr (kap j) (lam j) (u j))) 0)
        ∂(Measure.pi (α := fun _ : Fin n => U) kap) < ⊤ := by
    intro j
    rw [htr j (fun x => ENNReal.ofReal (max (-(llr (kap j) (lam j) x)) 0)) (hmeas_neg j)]
    exact lt_of_le_of_lt (hA j) (by simp)
  have hcoe : ∀ y : ℝ, ‖y‖ₑ = ENNReal.ofReal ‖y‖ := by
    intro y
    simp only [enorm]
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
  have hS : Integrable (fun u : Fin n → U => ∑ j, llr (kap j) (lam j) (u j))
      (Measure.pi (α := fun _ : Fin n => U) kap) := h.congr hllr
  have hNeg : ∀ j : Fin n,
      Integrable (fun u : Fin n → U => max (-(llr (kap j) (lam j) (u j))) 0)
        (Measure.pi (α := fun _ : Fin n => U) kap) := by
    intro j
    have hmeasj : Measurable (fun u : Fin n → U => max (-(llr (kap j) (lam j) (u j))) 0) :=
      ((continuous_id.neg.max continuous_const).measurable).comp
        ((hllr_meas j).comp (measurable_pi_apply j))
    refine ⟨hmeasj.aestronglyMeasurable, ?_⟩
    simp only [HasFiniteIntegral]
    rw [show (fun a : Fin n → U => ‖max (-(llr (kap j) (lam j) (a j))) 0‖ₑ)
        = (fun a : Fin n → U => ENNReal.ofReal (max (-(llr (kap j) (lam j) (a j))) 0)) from
      funext (fun a => by
        rw [hcoe (max (-(llr (kap j) (lam j) (a j))) 0), Real.norm_eq_abs,
          abs_of_nonneg (le_max_right _ 0)])]
    exact hB j
  have hAint : Integrable (fun u : Fin n → U => ∑ j, max (-(llr (kap j) (lam j) (u j))) 0)
      (Measure.pi (α := fun _ : Fin n => U) kap) := by
    have key : ∀ s : Finset (Fin n), Integrable
        (fun u : Fin n → U => ∑ j ∈ s, max (-(llr (kap j) (lam j) (u j))) 0)
        (Measure.pi (α := fun _ : Fin n => U) kap) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
          simp only [Finset.sum_insert ha]
          exact (hNeg a).add ih
    simpa using key Finset.univ
  have hGint : Integrable (fun u : Fin n → U => ‖∑ j, llr (kap j) (lam j) (u j)‖
      + ∑ j, max (-(llr (kap j) (lam j) (u j))) 0)
      (Measure.pi (α := fun _ : Fin n => U) kap) := hS.norm.add hAint
  have hbound : ∀ u : Fin n → U, ‖llr (kap i) (lam i) (u i)‖ ≤
      ‖∑ j, llr (kap j) (lam j) (u j)‖ + ∑ j, max (-(llr (kap j) (lam j) (u j))) 0 := by
    intro u
    have hsplit : (∑ j, llr (kap j) (lam j) (u j))
        = llr (kap i) (lam i) (u i) + ∑ j ∈ Finset.univ.erase i, llr (kap j) (lam j) (u j) := by
      conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ i)]
      rw [Finset.sum_insert (by simp)]
    have hAerase : -(∑ j ∈ Finset.univ.erase i, llr (kap j) (lam j) (u j))
        ≤ ∑ j, max (-(llr (kap j) (lam j) (u j))) 0 := by
      rw [← Finset.sum_neg_distrib]
      refine le_trans (Finset.sum_le_sum (fun j _ => le_max_left (-(llr (kap j) (lam j) (u j))) 0)) ?_
      have hsum := Finset.sum_insert (by simp : i ∉ Finset.univ.erase i)
        (f := fun j => max (-(llr (kap j) (lam j) (u j))) 0)
      rw [Finset.insert_erase (Finset.mem_univ i)] at hsum
      have hnn : 0 ≤ max (-(llr (kap i) (lam i) (u i))) 0 := le_max_right _ 0
      linarith
    have hle1 : llr (kap i) (lam i) (u i)
        ≤ ‖∑ j, llr (kap j) (lam j) (u j)‖ + ∑ j, max (-(llr (kap j) (lam j) (u j))) 0 := by
      have h2 : (∑ j, llr (kap j) (lam j) (u j)) ≤ ‖∑ j, llr (kap j) (lam j) (u j)‖ :=
        le_abs_self _
      linarith
    have hle2 : -(llr (kap i) (lam i) (u i))
        ≤ ‖∑ j, llr (kap j) (lam j) (u j)‖ + ∑ j, max (-(llr (kap j) (lam j) (u j))) 0 := by
      have h1 : -(llr (kap i) (lam i) (u i)) ≤ max (-(llr (kap i) (lam i) (u i))) 0 :=
        le_max_left _ 0
      have h2 : max (-(llr (kap i) (lam i) (u i))) 0
          ≤ ∑ j, max (-(llr (kap j) (lam j) (u j))) 0 :=
        Finset.single_le_sum (f := fun j => max (-(llr (kap j) (lam j) (u j))) 0)
          (fun j _ => le_max_right _ 0) (Finset.mem_univ i)
      have h3 : 0 ≤ ‖∑ j, llr (kap j) (lam j) (u j)‖ := norm_nonneg _
      linarith
    calc ‖llr (kap i) (lam i) (u i)‖ = |llr (kap i) (lam i) (u i)| := Real.norm_eq_abs _
      _ ≤ ‖∑ j, llr (kap j) (lam j) (u j)‖ + ∑ j, max (-(llr (kap j) (lam j) (u j))) 0 :=
          abs_le.mpr ⟨by linarith, hle1⟩
  have hIntP : Integrable (fun u : Fin n → U => llr (kap i) (lam i) (u i))
      (Measure.pi (α := fun _ : Fin n => U) kap) := by
    refine Integrable.mono' hGint ?_ (Filter.Eventually.of_forall hbound)
    exact ((hllr_meas i).comp (measurable_pi_apply i)).aestronglyMeasurable
  have hfin : HasFiniteIntegral (llr (kap i) (lam i)) (kap i) := by
    have hfunX : (fun x : U => ‖llr (kap i) (lam i) x‖ₑ)
        = (fun x : U => ENNReal.ofReal ‖llr (kap i) (lam i) x‖) :=
      funext (fun x => hcoe (llr (kap i) (lam i) x))
    have hfunP : (fun u : Fin n → U => ‖llr (kap i) (lam i) (u i)‖ₑ)
        = (fun u : Fin n → U => ENNReal.ofReal ‖llr (kap i) (lam i) (u i)‖) :=
      funext (fun u => hcoe (llr (kap i) (lam i) (u i)))
    have h1 : ∫⁻ u, ENNReal.ofReal ‖llr (kap i) (lam i) (u i)‖
        ∂(Measure.pi (α := fun _ : Fin n => U) kap) < ⊤ := by
      rw [← hfunP]
      exact hIntP.2
    rw [htr i (fun x => ENNReal.ofReal ‖llr (kap i) (lam i) x‖)
      (ENNReal.measurable_ofReal.comp (hllr_meas i).norm)] at h1
    simp only [HasFiniteIntegral]
    rw [hfunX]
    exact h1
  exact ⟨(hllr_meas i).aestronglyMeasurable, hfin⟩
  /- @proof-region region.target-node.session.3a1fbbed76cd2c25 end -/

end
end Statlib.Imported
