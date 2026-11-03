import Statlib.StatFoundation.Concentration.ExponentialType.bernstein_sum_meas_abs_ge_le_two_exp
import Statlib.StatFoundation.Vocabulary.RandomVariable
import Lean
import ProverJobs.job_paper_ebad183ded244602a77f3710a9957efa.Vocabulary
import ProverJobs.job_paper_ebad183ded244602a77f3710a9957efa.ProvedNodes
import ProverJobs.job_paper_ebad183ded244602a77f3710a9957efa.Base

namespace PaperProofTasks.job_paper_ebad183ded244602a77f3710a9957efa

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))

theorem paper_ebad183ded244602a77f3710a9957efa :
    ∃ b : ℝ, 0 < b ∧
      ∀ (N : ℕ), 1 ≤ N → ∀ (V : ℝ), 0 < V →
        ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (U : Fin N → Ω → ℝ),
          (∀ l, Measurable (U l)) → iIndepFun U μ → (∀ l, Integrable (U l) μ) →
          (∀ l, ∫ ω, U l ω ∂μ = 0) →
          (∀ l (r : ℕ), 2 ≤ r →
            ∫⁻ ω, ENNReal.ofReal (|U l ω| ^ r) ∂μ
              ≤ ENNReal.ofReal ((r.factorial : ℝ) * V ^ r)) →
          ∀ t : ℝ, 0 < t →
            μ.real {ω | t < |(N : ℝ)⁻¹ * ∑ l, U l ω|} ≤
              2 * Real.exp (-(b * (N : ℝ) * min (t ^ 2 / V ^ 2) (t / V)))
:= by
  /- @proof-region region.root.942265ae1aae begin -/
  refine ⟨1/8, by norm_num, ?_⟩
  intro N hN V hV Ω inst μ hprob U hmeas hindep hint hmean hmom t ht
  haveI : NeZero N := ⟨by omega⟩
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hNne : (N:ℝ) ≠ 0 := ne_of_gt hNpos
  have hVne : V ≠ 0 := ne_of_gt hV
  have hMGF : ∀ i : Fin N, Statlib.StatFoundation.Vocabulary.HasSubexponentialMGF (U i) (2*V) (2*V) μ := by
    intro i
    refine ⟨fun lam hlam => ?_, fun lam hlam => ?_⟩
    · exact (statopia_math_node_498541701_93d2db24 Ω μ V hV (U i) (hmeas i) (hint i) (hmean i) (hmom i) lam hlam).1
    · have h := (statopia_math_node_498541701_93d2db24 Ω μ V hV (U i) (hmeas i) (hint i) (hmean i) (hmom i) lam hlam).2
      convert h using 2
      ring
  have hbpos : ∀ i : Fin N, 0 < (2*V) := fun _ => by linarith
  have htE : 0 < (N:ℝ) * t := by positivity
  have hsum : (∑ i : Fin N, (2*V)^2) = 4 * (N:ℝ) * V^2 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hsumpos : 0 < ∑ i : Fin N, (2*V)^2 := by rw [hsum]; positivity
  have hne : (Finset.univ : Finset (Fin N)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hsupval : ∀ (h : (Finset.univ : Finset (Fin N)).Nonempty),
      (Finset.univ : Finset (Fin N)).sup' h (fun _ => 2*V) = 2*V := by
    intro h
    apply le_antisymm
    · apply Finset.sup'_le
      intro i _
      exact le_refl _
    · exact Finset.le_sup' (fun _ => (2:ℝ)*V) (Finset.mem_univ (0 : Fin N))
  
  
  have e4 := Statlib.StatFoundation.Concentration.ExponentialType.bernstein_sum_meas_abs_ge_le_two_exp
    μ U hmeas (fun _ => 2*V) (fun _ => 2*V) hbpos hindep hMGF (N*t) htE hsumpos
  have hmono : μ {ω | t < |(N:ℝ)⁻¹ * ∑ l, U l ω|} ≤ μ {ω | (N:ℝ)*t ≤ |∑ i, U i ω|} := by
    apply measure_mono
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have habs : |(N:ℝ)⁻¹ * ∑ l, U l ω| = (N:ℝ)⁻¹ * |∑ l, U l ω| := by
      rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hNpos.le)]
    rw [habs] at hω
    have h2 : (N:ℝ) * ((N:ℝ)⁻¹ * |∑ l, U l ω|) = |∑ l, U l ω| := by
      rw [← mul_assoc, mul_inv_cancel₀ hNne, one_mul]
    have h3 : (N:ℝ) * t < (N:ℝ) * ((N:ℝ)⁻¹ * |∑ l, U l ω|) :=
      mul_lt_mul_of_pos_left hω hNpos
    rw [h2] at h3
    exact le_of_lt h3
  have hclosed_ne_top : μ {ω | (N:ℝ)*t ≤ |∑ i, U i ω|} ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top e4
  have hstep1 : (μ {ω | t < |(N:ℝ)⁻¹ * ∑ l, U l ω|}).toReal
      ≤ (μ {ω | (N:ℝ)*t ≤ |∑ i, U i ω|}).toReal :=
    ENNReal.toReal_mono hclosed_ne_top hmono
  have hstep2 : (μ {ω | (N:ℝ)*t ≤ |∑ i, U i ω|}).toReal
      ≤ 2 * Real.exp (-(1/2) * min ((N*t)^2/(∑ i : Fin N, (2*V)^2)) ((N*t)/((Finset.univ : Finset (Fin N)).sup' hne (fun _ => 2*V)))) := by
  
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top e4
    rw [ENNReal.toReal_ofReal (by positivity)] at h
    exact h
  have hexp : -(1/2) * min ((N*t)^2/(4*(N:ℝ)*V^2)) ((N*t)/(2*V))
      ≤ -(1/8 * (N:ℝ) * min (t^2/V^2) (t/V)) := by
    rw [neg_mul, neg_le_neg_iff]
  
    have hX : 2 * ((1/8) * (N:ℝ) * min (t^2/V^2) (t/V)) ≤ (N*t)^2/(4*(N:ℝ)*V^2) := by
      have h1 : min (t^2/V^2) (t/V) ≤ t^2/V^2 := min_le_left _ _
      have h2 : 2 * ((1/8) * (N:ℝ) * min (t^2/V^2) (t/V)) ≤ 2 * ((1/8) * (N:ℝ) * (t^2/V^2)) := by
        have hnn : (0:ℝ) ≤ 2 * ((1/8) * (N:ℝ)) := by positivity
        have := mul_le_mul_of_nonneg_left h1 hnn
        linarith [this]
      have h3 : 2 * ((1/8) * (N:ℝ) * (t^2/V^2)) = (N*t)^2/(4*(N:ℝ)*V^2) := by
        rw [eq_div_iff (by positivity : (4*(N:ℝ)*V^2) ≠ 0)]
        field_simp
        ring
      rw [← h3]; exact h2
    have hY : 2 * ((1/8) * (N:ℝ) * min (t^2/V^2) (t/V)) ≤ (N*t)/(2*V) := by
      have h1 : min (t^2/V^2) (t/V) ≤ t/V := min_le_right _ _
      have h2 : 2 * ((1/8) * (N:ℝ) * min (t^2/V^2) (t/V)) ≤ 2 * ((1/8) * (N:ℝ) * (t/V)) := by
        have hnn : (0:ℝ) ≤ 2 * ((1/8) * (N:ℝ)) := by positivity
        have := mul_le_mul_of_nonneg_left h1 hnn
        linarith [this]
      have h3 : 2 * ((1/8) * (N:ℝ) * (t/V)) ≤ (N*t)/(2*V) := by
        field_simp
        nlinarith [hNpos, ht]
  
      linarith [h2, h3]
    have h2A : 2 * ((1/8) * (N:ℝ) * min (t^2/V^2) (t/V))
        ≤ min ((N*t)^2/(4*(N:ℝ)*V^2)) ((N*t)/(2*V)) := le_min hX hY
    linarith [h2A]
  calc μ.real {ω | t < |(N:ℝ)⁻¹ * ∑ l, U l ω|}
      = (μ {ω | t < |(N:ℝ)⁻¹ * ∑ l, U l ω|}).toReal := rfl
    _ ≤ (μ {ω | (N:ℝ)*t ≤ |∑ i, U i ω|}).toReal := hstep1
    _ ≤ 2 * Real.exp (-(1/2) * min ((N*t)^2/(∑ i : Fin N, (2*V)^2)) ((N*t)/((Finset.univ : Finset (Fin N)).sup' hne (fun _ => 2*V)))) := hstep2
  
    _ = 2 * Real.exp (-(1/2) * min ((N*t)^2/(4*(N:ℝ)*V^2)) ((N*t)/(2*V))) := by
          simp only [hsum, hsupval]
    _ ≤ 2 * Real.exp (-(1/8 * (N:ℝ) * min (t^2/V^2) (t/V))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
          exact Real.exp_le_exp.mpr hexp
  /- @proof-region region.root.942265ae1aae end -/

end Statlib.Imported

