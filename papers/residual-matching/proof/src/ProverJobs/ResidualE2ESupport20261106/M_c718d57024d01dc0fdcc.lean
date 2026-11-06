import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Vocabulary.MaxType
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_466340105_bd7fbf52 : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (hN : 1 ≤ N)
    (X Y : Ω → Fin N → ℝ)
    (hX_gauss : ∀ a : Fin N → ℝ,
      ∃ v : NNReal,
        Measure.map (fun ω => ∑ k : Fin N, a k * X ω k) μ = gaussianReal 0 v)
    (hY_gauss : ∀ a : Fin N → ℝ,
      ∃ v : NNReal,
        Measure.map (fun ω => ∑ k : Fin N, a k * Y ω k) μ = gaussianReal 0 v)
    (hkey : ∀ β : ℝ, 0 < β →
      ∫ ω, Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (X ω)) ∂μ ≤
        ∫ ω, Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (Y ω)) ∂μ),
    ∫ ω, (⨆ k : Fin N, X ω k) ∂μ ≤ ∫ ω, (⨆ k : Fin N, Y ω k) ∂μ := by
  /- @proof-region region.target-node.session.d0b1233567becfca begin -/
  intro Ω _ μ hμ N hN X Y hX_gauss hY_gauss hkey
  have coord_map : ∀ (Z : Ω → Fin N → ℝ),
      (∀ a : Fin N → ℝ, ∃ v : NNReal, Measure.map (fun ω => ∑ j : Fin N, a j * Z ω j) μ = gaussianReal 0 v) →
      ∀ k : Fin N, ∃ v : NNReal, Measure.map (fun ω => Z ω k) μ = gaussianReal 0 v := by
    intro Z hZ k
    obtain ⟨v, hv⟩ := hZ (fun j => if j = k then 1 else 0)
    refine ⟨v, ?_⟩
    have hfun : (fun ω => ∑ j : Fin N, (if j = k then 1 else 0) * Z ω j) = (fun ω => Z ω k) := by
      funext ω
      rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hj; simp [hj]
      · intro hk; exact absurd (Finset.mem_univ k) hk
    rw [hfun] at hv
    exact hv
  have hXmap : ∀ k : Fin N, ∃ v : NNReal, Measure.map (fun ω => X ω k) μ = gaussianReal 0 v :=
    coord_map X hX_gauss
  have hYmap : ∀ k : Fin N, ∃ v : NNReal, Measure.map (fun ω => Y ω k) μ = gaussianReal 0 v :=
    coord_map Y hY_gauss
  have hmaxbr : ∀ z : Fin N → ℝ,
      Statlib.StatFoundation.Vocabulary.maxCoord (WithLp.toLp 2 z) = ⨆ k : Fin N, z k := by
    intro z
    simp [Statlib.StatFoundation.Vocabulary.maxCoord]
  have sup_int : ∀ (Z : Ω → Fin N → ℝ),
      (∀ k : Fin N, ∃ v : NNReal, Measure.map (fun ω => Z ω k) μ = gaussianReal 0 v) →
      Integrable (fun ω => ⨆ k : Fin N, Z ω k) μ := by
    intro Z hZ
    have hmeas : ∀ k : Fin N, AEMeasurable (fun ω => Z ω k) μ := by
      intro k
      obtain ⟨v, hv⟩ := hZ k
      by_contra hcon
      rw [MeasureTheory.Measure.map_of_not_aemeasurable hcon] at hv
      have huniv : gaussianReal (0 : ℝ) v Set.univ = 1 := measure_univ
      rw [← hv] at huniv
      simp at huniv
    have hcoord_int : ∀ k : Fin N, Integrable (fun ω => Z ω k) μ := by
      intro k
      have hmlp : MemLp (fun ω => Z ω k) 1 μ := by
        obtain ⟨v, hv⟩ := hZ k
        have hg : MemLp (fun x : ℝ => x) 1 (gaussianReal (0 : ℝ) v) := by
          simpa using ProbabilityTheory.memLp_id_gaussianReal (1 : NNReal)
        rw [← hv] at hg
        simpa using (MeasureTheory.MemLp.comp_of_map hg (hmeas k))
      exact MeasureTheory.memLp_one_iff_integrable.mp hmlp
    have hsupmeas : AEStronglyMeasurable (fun ω => ⨆ k : Fin N, Z ω k) μ :=
      (AEMeasurable.iSup hmeas).aestronglyMeasurable
    have hsum_int : Integrable (fun ω => ∑ k : Fin N, ‖Z ω k‖) μ :=
      MeasureTheory.integrable_finset_sum Finset.univ (f := fun k => fun ω => ‖Z ω k‖) (fun k _ => (hcoord_int k).norm)
    refine hsum_int.mono' hsupmeas ?_
    filter_upwards with ω
    have hj : Fin N := ⟨0, by omega⟩
    rw [Real.norm_eq_abs]
    refine abs_le.mpr ⟨?_, ?_⟩
    · have h1 : -∑ k : Fin N, ‖Z ω k‖ ≤ Z ω hj := by
        have hle : ‖Z ω hj‖ ≤ ∑ k : Fin N, ‖Z ω k‖ :=
          Finset.single_le_sum (f := fun k => ‖Z ω k‖) (fun i _ => norm_nonneg _) (Finset.mem_univ hj)
        have h2 : -‖Z ω hj‖ ≤ Z ω hj := by
          rw [Real.norm_eq_abs]; exact neg_abs_le _
        linarith
      have hbd : BddAbove (Set.range (fun k : Fin N => Z ω k)) := by
        refine ⟨∑ k : Fin N, ‖Z ω k‖, ?_⟩
        rintro b ⟨k, hk⟩
        rw [← hk]
        calc Z ω k ≤ ‖Z ω k‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
          _ ≤ ∑ k' : Fin N, ‖Z ω k'‖ := Finset.single_le_sum (f := fun k' => ‖Z ω k'‖) (fun i _ => norm_nonneg _) (Finset.mem_univ k)
      exact le_trans h1 (le_ciSup hbd hj)
    · refine Real.iSup_le (fun k => ?_) (Finset.sum_nonneg (fun k _ => norm_nonneg _))
      have hle : ‖Z ω k‖ ≤ ∑ k' : Fin N, ‖Z ω k'‖ :=
        Finset.single_le_sum (f := fun k' => ‖Z ω k'‖) (fun i _ => norm_nonneg _) (Finset.mem_univ k)
      calc Z ω k ≤ ‖Z ω k‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
        _ ≤ ∑ k' : Fin N, ‖Z ω k'‖ := hle
  have sm_int : ∀ (Z : Ω → Fin N → ℝ),
      (∀ k : Fin N, ∃ v : NNReal, Measure.map (fun ω => Z ω k) μ = gaussianReal 0 v) →
      ∀ β : ℝ, 0 < β → Integrable (fun ω => Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (Z ω))) μ := by
    intro Z hZ β hβ
    have hmeas : ∀ k : Fin N, AEMeasurable (fun ω => Z ω k) μ := by
      intro k
      obtain ⟨v, hv⟩ := hZ k
      by_contra hcon
      rw [MeasureTheory.Measure.map_of_not_aemeasurable hcon] at hv
      have huniv : gaussianReal (0 : ℝ) v Set.univ = 1 := measure_univ
      rw [← hv] at huniv
      simp at huniv
    have hZint : Integrable (fun ω => ⨆ k : Fin N, Z ω k) μ := sup_int Z hZ
    have hsmax_meas : Measurable (Statlib.StatFoundation.Convergence.smoothMax (p := N) β) :=
      (Statlib.StatFoundation.Convergence.smoothMax_def_measurable_continuous (p := N) (β := β) (by omega) hβ).2
    have hcomp_meas : Measurable (fun z : Fin N → ℝ => Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z)) :=
      hsmax_meas.comp (WithLp.measurable_toLp 2 (Fin N → ℝ))
    have hvec : AEMeasurable (fun ω => (fun k => Z ω k)) μ := aemeasurable_pi_iff.mpr hmeas
    have hsm_aesm : AEStronglyMeasurable (fun ω => Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (Z ω))) μ := by
      have h := hcomp_meas.comp_aemeasurable' hvec
      simpa using h.aestronglyMeasurable
    have hg_int : Integrable (fun ω => ‖⨆ k : Fin N, Z ω k‖ + ‖Real.log (N : ℝ) / β‖) μ :=
      hZint.norm.add (integrable_const _)
    refine hg_int.mono' hsm_aesm ?_
    filter_upwards with ω
    have hbnd := Statlib.StatFoundation.Convergence.smoothMax_bounds_max_log_card N (by omega) β hβ (WithLp.toLp 2 (Z ω))
    obtain ⟨hb1, hb2⟩ := hbnd
    rw [hmaxbr (Z ω)] at hb1 hb2
    rw [Real.norm_eq_abs]
    refine abs_le.mpr ⟨?_, ?_⟩
    · have h1 : -(‖⨆ k : Fin N, Z ω k‖ + ‖Real.log (N : ℝ) / β‖) ≤ (⨆ k : Fin N, Z ω k) := by
        have hA : -(‖⨆ k : Fin N, Z ω k‖) ≤ (⨆ k : Fin N, Z ω k) := by
          rw [Real.norm_eq_abs]; exact neg_abs_le _
        have hC : (0:ℝ) ≤ ‖Real.log (N : ℝ) / β‖ := norm_nonneg _
        linarith
      exact le_trans h1 hb1
    · have hA : (⨆ k : Fin N, Z ω k) ≤ ‖⨆ k : Fin N, Z ω k‖ := by
        rw [Real.norm_eq_abs]; exact le_abs_self _
      have hC : Real.log (N : ℝ) / β ≤ ‖Real.log (N : ℝ) / β‖ := by
        rw [Real.norm_eq_abs]; exact le_abs_self _
      linarith
  have hXint : Integrable (fun ω => ⨆ k : Fin N, X ω k) μ := sup_int X hXmap
  have hYint : Integrable (fun ω => ⨆ k : Fin N, Y ω k) μ := sup_int Y hYmap
  have hlogNnn : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  apply le_of_forall_pos_le_add
  intro ε hε
  have hβpos : 0 < Real.log (N : ℝ) / ε + 1 := by
    have h1 : 0 ≤ Real.log (N : ℝ) / ε := div_nonneg hlogNnn (le_of_lt hε)
    linarith
  have stepX : ∫ ω, (⨆ k : Fin N, X ω k) ∂μ ≤
      ∫ ω, Statlib.StatFoundation.Convergence.smoothMax (Real.log (N : ℝ) / ε + 1) (WithLp.toLp 2 (X ω)) ∂μ := by
    have hle : (fun ω => ⨆ k : Fin N, X ω k) ≤ᵐ[μ]
        (fun ω => Statlib.StatFoundation.Convergence.smoothMax (Real.log (N : ℝ) / ε + 1) (WithLp.toLp 2 (X ω))) := by
      filter_upwards with ω
      have hb := (Statlib.StatFoundation.Convergence.smoothMax_bounds_max_log_card N (by omega) (Real.log (N : ℝ) / ε + 1) hβpos (WithLp.toLp 2 (X ω))).1
      rwa [hmaxbr (X ω)] at hb
    refine MeasureTheory.integral_mono_ae ?_ ?_ ?_
    all_goals (first | exact hXint | exact hle | exact (sm_int X hXmap (Real.log (N : ℝ) / ε + 1) hβpos))
  have hkeyβ := hkey (Real.log (N : ℝ) / ε + 1) hβpos
  have stepY : ∫ ω, Statlib.StatFoundation.Convergence.smoothMax (Real.log (N : ℝ) / ε + 1) (WithLp.toLp 2 (Y ω)) ∂μ ≤
      ∫ ω, (⨆ k : Fin N, Y ω k) ∂μ + Real.log (N : ℝ) / (Real.log (N : ℝ) / ε + 1) := by
    have hle : (fun ω => Statlib.StatFoundation.Convergence.smoothMax (Real.log (N : ℝ) / ε + 1) (WithLp.toLp 2 (Y ω))) ≤ᵐ[μ]
        (fun ω => (⨆ k : Fin N, Y ω k) + Real.log (N : ℝ) / (Real.log (N : ℝ) / ε + 1)) := by
      filter_upwards with ω
      have hb := (Statlib.StatFoundation.Convergence.smoothMax_bounds_max_log_card N (by omega) (Real.log (N : ℝ) / ε + 1) hβpos (WithLp.toLp 2 (Y ω))).2
      rwa [hmaxbr (Y ω)] at hb
    have hInt : Integrable (fun ω => (⨆ k : Fin N, Y ω k) + Real.log (N : ℝ) / (Real.log (N : ℝ) / ε + 1)) μ :=
      hYint.add (integrable_const _)
    have key : ∫ ω, Statlib.StatFoundation.Convergence.smoothMax (Real.log (N : ℝ) / ε + 1) (WithLp.toLp 2 (Y ω)) ∂μ ≤
        ∫ ω, ((⨆ k : Fin N, Y ω k) + Real.log (N : ℝ) / (Real.log (N : ℝ) / ε + 1)) ∂μ := by
      refine MeasureTheory.integral_mono_ae ?_ ?_ ?_
      all_goals (first | exact (sm_int Y hYmap (Real.log (N : ℝ) / ε + 1) hβpos) | exact hle | exact hInt)
    rw [MeasureTheory.integral_add hYint (integrable_const (Real.log (N : ℝ) / (Real.log (N : ℝ) / ε + 1))),
      MeasureTheory.integral_const] at key
    simpa [Measure.real, hμ.measure_univ] using key
  have hlogβ : Real.log (N : ℝ) / (Real.log (N : ℝ) / ε + 1) < ε := by
    have hb : (0:ℝ) < Real.log (N : ℝ) / ε + 1 := hβpos
    have hmul : ε * (Real.log (N : ℝ) / ε + 1) = Real.log (N : ℝ) + ε := by
      rw [mul_add, mul_one, mul_comm ε (Real.log (N : ℝ) / ε),
        div_mul_cancel₀ (Real.log (N : ℝ)) (ne_of_gt hε)]
    rw [div_lt_iff₀ hb, hmul]
    linarith
  linarith
  /- @proof-region region.target-node.session.d0b1233567becfca end -/

end Statlib.Imported

