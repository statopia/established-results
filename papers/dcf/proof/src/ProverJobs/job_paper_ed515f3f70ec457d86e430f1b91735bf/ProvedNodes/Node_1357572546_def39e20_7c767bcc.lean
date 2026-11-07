import Statlib.HighDim.MatrixAnalysis.AndoVocabulary
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Statlib.StatFoundation.RandomVariable.Gaussian.Standard
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base

namespace PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Statlib.StatFoundation.RandomVariable.Gaussian
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Statlib.StatFoundation.RandomVariable.Gaussian
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_1357572546_def39e20 : ∀ (b : ℝ) (hb : 0 < b),
    ∃ Cb : ℝ, 0 < Cb ∧
      ∀ (p : ℕ), 1 ≤ p →
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (X : Ω → Fin p → ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ),
          Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector P X Sigma →
          (∀ j : Fin p, b ≤ Sigma j j) →
          ∀ (y : Fin p → ℝ) (w : ℝ), 0 ≤ w →
            (P {ω : Ω | -(w) < (⨆ j : Fin p, (X ω j - y j)) ∧
                      (⨆ j : Fin p, (X ω j - y j)) ≤ w}).toReal
              ≤ Cb * w * (Real.sqrt (Real.log (p : ℝ)) + 1) := by
  /- @proof-region region.target-node.session.eef59b858a2d8abb begin -/
  intro b hb
  refine ⟨4 / Real.sqrt b, by positivity, ?_⟩
  intro p hp Ω hΩ P hP X Sigma hX hSigma y w hw
  haveI : Nonempty (Fin p) := ⟨⟨0, by omega⟩⟩
  have hbpos : (0:ℝ) < Real.sqrt b := by positivity
  set σ : ℝ := Real.sqrt b with hσdef
  have hσpos : 0 < σ := by rw [hσdef]; exact hbpos
  have hσsq : σ ^ 2 = b := by rw [hσdef]; exact Real.sq_sqrt hb.le
  have hvar : ∀ j : Fin p, σ ^ 2 ≤ Sigma j j := by
    intro j; rw [hσsq]; exact hSigma j
  have h2w : (0:ℝ) ≤ 2*w := by linarith
  set y' : Fin p → ℝ := fun j => y j - w with hy'def
  set Aw : Set Ω := {ω | ∀ j : Fin p, X ω j ≤ y j + w} with hAw
  set Amw : Set Ω := {ω | ∀ j : Fin p, X ω j ≤ y j - w} with hAmw
  have hy' : ∀ j : Fin p, y' j = y j - w := fun j => by rw [hy'def]
  have hA1 : {ω : Ω | ∀ j : Fin p, X ω j ≤ y' j + 2*w} = Aw := by
    rw [hAw]; ext ω; constructor
    · intro h j; linarith [h j, hy' j]
    · intro h j; linarith [h j, hy' j]
  have hA2 : {ω : Ω | ∀ j : Fin p, X ω j ≤ y' j} = Amw := by rw [hAmw]
  have hrect := Statlib.StatFoundation.Convergence.gaussianVector_rectangle_increment_le
    p hp P Sigma X hX σ (2*w) hσpos h2w hvar y'
  rw [hA1, hA2] at hrect
  have hbdd : ∀ ω : Ω, BddAbove (Set.range (fun j : Fin p => X ω j - y j)) :=
    fun ω => (Set.toFinite _).bddAbove
  have hsup_le : ∀ (ω : Ω) (t : ℝ),
      (⨆ j : Fin p, (X ω j - y j)) ≤ t ↔ ∀ j : Fin p, X ω j ≤ y j + t := by
    intro ω t
    rw [ciSup_le_iff (hbdd ω)]
    constructor
    · intro h j; linarith [h j]
    · intro h j; linarith [h j]
  have hneg : ∀ ω : Ω, ((⨆ j : Fin p, (X ω j - y j)) ≤ -w) ↔ (∀ j : Fin p, X ω j ≤ y j - w) := by
    intro ω
    rw [hsup_le ω (-w)]
    constructor
    · intro h j; linarith [h j]
    · intro h j; linarith [h j]
  have hS_eq : {ω : Ω | -(w) < (⨆ j : Fin p, (X ω j - y j)) ∧ (⨆ j : Fin p, (X ω j - y j)) ≤ w}
      = Aw \ Amw := by
    ext ω
    rw [hAw, hAmw, Set.mem_diff]
    show (-w < (⨆ j : Fin p, (X ω j - y j)) ∧ (⨆ j : Fin p, (X ω j - y j)) ≤ w) ↔
      ((∀ j : Fin p, X ω j ≤ y j + w) ∧ ¬ (∀ j : Fin p, X ω j ≤ y j - w))
    exact ⟨fun h => ⟨(hsup_le ω w).mp h.2, fun hc => (not_le.mpr h.1) ((hneg ω).mpr hc)⟩,
      fun h => ⟨not_le.mp (fun hc => h.2 ((hneg ω).mp hc)), (hsup_le ω w).mpr h.1⟩⟩
  have hsub : Amw ⊆ Aw := by
    intro ω hω
    exact fun j => by linarith [hω j]
  have hfin : ∀ s : Set Ω, P s ≠ ⊤ := by
    haveI : IsProbabilityMeasure P := hP
    intro s
    have h1 : P s ≤ 1 := by
      calc P s ≤ P (Set.univ : Set Ω) := measure_mono (Set.subset_univ s)
        _ = 1 := by simp
    exact ne_of_lt (lt_of_le_of_lt h1 (by simp))
  have hnull : NullMeasurableSet Amw P := by
    let S2 : Matrix (Fin p) (Fin p) ℝ := (2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)
    have hS2 : S2.PosSemidef := hX.posSemidef_symmetrizedCovariance hp
    have hcoord : ∀ j : Fin p,
        Measurable fun z : Fin p → ℝ => Slepian.canonicalGaussianVector S2 z j := by
      intro j
      have hsum : ∀ (g : Fin p → ℝ),
          (∑ i : Fin p, (if i = j then (1:ℝ) else 0) * g i) = g j := by
        intro g
        have h := Finset.sum_eq_single (s := (Finset.univ : Finset (Fin p)))
          (f := fun i : Fin p => (if i = j then (1:ℝ) else 0) * g i) j
          (fun b _ hb => by simp [hb])
          (fun hj => absurd (Finset.mem_univ j) hj)
        simpa using h
      have key : (fun z : Fin p → ℝ => Slepian.canonicalGaussianVector S2 z j)
          = fun z => ∑ k : Fin p,
              (CFC.sqrt S2).mulVec (fun i : Fin p => if i = j then (1:ℝ) else 0) k * z k := by
        funext z
        rw [← Slepian.canonicalGaussianVector_linearCombination S2 hS2
          (fun i : Fin p => if i = j then (1:ℝ) else 0) z]
        exact (hsum (fun i => Slepian.canonicalGaussianVector S2 z i)).symm
      rw [key]
      exact Finset.measurable_sum Finset.univ fun k _ => measurable_const.mul (measurable_pi_apply k)
    have hmeas : Measurable (Slepian.canonicalGaussianVector S2) := measurable_pi_iff.mpr hcoord
    have hsp : standardPi p ≠ 0 := by
      haveI : IsProbabilityMeasure (standardPi p) := Slepian.standardPi_probability p
      have h1 : standardPi p (Set.univ) = 1 := by simp
      intro h0
      rw [h0] at h1
      simp at h1
    have hne : Measure.map (Slepian.canonicalGaussianVector S2) (standardPi p) ≠ 0 :=
      (MeasureTheory.Measure.map_ne_zero_iff hmeas.aemeasurable).mpr hsp
    have hneX : Measure.map X P ≠ 0 := by
      rw [hX.map_eq_canonicalGaussianVector hp]
      exact hne
    have hXae : AEMeasurable X P := AEMeasurable.of_map_ne_zero hneX
    have hT : MeasurableSet {z : Fin p → ℝ | ∀ j : Fin p, z j ≤ y j - w} := by
      have hT' : {z : Fin p → ℝ | ∀ j : Fin p, z j ≤ y j - w}
          = ⋂ j : Fin p, {z : Fin p → ℝ | z j ≤ y j - w} := by
        ext z
        simp
      rw [hT']
      exact MeasurableSet.iInter fun j => measurableSet_le (measurable_pi_apply j) measurable_const
    have hpre : Amw = X ⁻¹' {z : Fin p → ℝ | ∀ j : Fin p, z j ≤ y j - w} := rfl
    rw [hpre]
    exact hXae.nullMeasurableSet_preimage hT
  have hd : P (Aw \ Amw) = P Aw - P Amw := measure_diff hsub hnull (hfin Amw)
  have ht : (P Aw - P Amw).toReal = (P Aw).toReal - (P Amw).toReal :=
    ENNReal.toReal_sub_of_le (measure_mono hsub) (hfin Aw)
  have hbridge : (P {ω : Ω | -(w) < (⨆ j : Fin p, (X ω j - y j)) ∧
      (⨆ j : Fin p, (X ω j - y j)) ≤ w}).toReal ≤ (P Aw).toReal - (P Amw).toReal :=
    le_of_eq (by rw [hS_eq, hd, ht])
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp)
  have hsqrt2 : Real.sqrt (2 * Real.log (p:ℝ)) ≤ 2 * Real.sqrt (Real.log (p:ℝ)) := by
    have h4 : Real.sqrt (4 * Real.log (p:ℝ)) = 2 * Real.sqrt (Real.log (p:ℝ)) := by
      rw [show (4:ℝ) = 2^2 by norm_num,
        Real.sqrt_mul (by positivity : (0:ℝ) ≤ (2:ℝ)^2), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    calc Real.sqrt (2 * Real.log (p:ℝ)) ≤ Real.sqrt (4 * Real.log (p:ℝ)) := Real.sqrt_le_sqrt (by linarith)
      _ = 2 * Real.sqrt (Real.log (p:ℝ)) := h4
  have hbne : Real.sqrt b ≠ 0 := ne_of_gt hbpos
  have harith : (2*w)/σ * (Real.sqrt (2 * Real.log (p:ℝ)) + 2)
      ≤ (4 / Real.sqrt b) * w * (Real.sqrt (Real.log (p:ℝ)) + 1) := by
    rw [hσdef]
    have hstep1 : (2*w)/Real.sqrt b * (Real.sqrt (2*Real.log (p:ℝ)) + 2)
        ≤ (2*w)/Real.sqrt b * (2*(Real.sqrt (Real.log (p:ℝ)) + 1)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hstep2 : (2*w)/Real.sqrt b * (2*(Real.sqrt (Real.log (p:ℝ)) + 1))
        = (4 / Real.sqrt b) * w * (Real.sqrt (Real.log (p:ℝ)) + 1) := by
      field_simp
      ring
    calc (2*w)/Real.sqrt b * (Real.sqrt (2*Real.log (p:ℝ)) + 2)
        ≤ (2*w)/Real.sqrt b * (2*(Real.sqrt (Real.log (p:ℝ)) + 1)) := hstep1
      _ = (4 / Real.sqrt b) * w * (Real.sqrt (Real.log (p:ℝ)) + 1) := hstep2
  calc (P {ω : Ω | -(w) < (⨆ j : Fin p, (X ω j - y j)) ∧ (⨆ j : Fin p, (X ω j - y j)) ≤ w}).toReal
      ≤ (P Aw).toReal - (P Amw).toReal := hbridge
    _ ≤ (2*w)/σ * (Real.sqrt (2 * Real.log (p:ℝ)) + 2) := hrect
    _ ≤ (4 / Real.sqrt b) * w * (Real.sqrt (Real.log (p:ℝ)) + 1) := harith
  /- @proof-region region.target-node.session.eef59b858a2d8abb end -/

end

end Statlib.Imported

