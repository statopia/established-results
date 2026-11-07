import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_2194576110_d2ad0cef_60d45604

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
theorem statopia_math_node_2755391374_6e6ed0b4 : ∀ (p : ℕ) (hp : 2 ≤ p)
    (phi : ℝ) (hphi : 1 ≤ phi)
    (phi0 : ℝ → ℝ)
    (hphi0_cont : ContDiff ℝ 3 phi0)
    (hphi0_left : ∀ z : ℝ, z ≤ 0 → phi0 z = 1)
    (hphi0_right : ∀ z : ℝ, 1 ≤ z → phi0 z = 0)
    (hphi0_range : ∀ z : ℝ, phi0 z ∈ Set.Icc (0 : ℝ) 1)
    (Ω : Type*) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (Z1 Z0 : Ω → Fin p → ℝ) (hZ1 : Measurable Z1) (hZ0 : Measurable Z0),
    (let kappa : (Fin p → ℝ) → (Fin p → ℝ) → ℝ :=
        fun u w => phi0 (phi * ((phi * Real.log (p : ℝ))⁻¹ *
          Real.log (∑ j : Fin p, Real.exp ((phi * Real.log (p : ℝ)) * (w j - u j)))));
      (∀ y : Fin p → ℝ,
        (Pr {ω | ∀ j : Fin p, Z1 ω j ≤ y j - phi⁻¹}).toReal ≤
            ∫ ω, kappa y (Z1 ω) ∂Pr ∧
          ∫ ω, kappa y (Z1 ω) ∂Pr ≤
            (Pr {ω | ∀ j : Fin p, Z1 ω j ≤ y j + phi⁻¹}).toReal) ∧
      (∀ y : Fin p → ℝ,
        (Pr {ω | ∀ j : Fin p, Z0 ω j ≤ y j - phi⁻¹}).toReal ≤
            ∫ ω, kappa y (Z0 ω) ∂Pr ∧
          ∫ ω, kappa y (Z0 ω) ∂Pr ≤
            (Pr {ω | ∀ j : Fin p, Z0 ω j ≤ y j + phi⁻¹}).toReal) ∧
      (∀ y : Fin p → ℝ,
        |(Pr {ω | ∀ j : Fin p, Z1 ω j ≤ y j}).toReal -
            (Pr {ω | ∀ j : Fin p, Z0 ω j ≤ y j}).toReal| ≤
          |∫ ω, (kappa (fun j : Fin p => y j + phi⁻¹) (Z1 ω) -
              kappa (fun j : Fin p => y j + phi⁻¹) (Z0 ω)) ∂Pr| +
            |∫ ω, (kappa (fun j : Fin p => y j - phi⁻¹) (Z1 ω) -
              kappa (fun j : Fin p => y j - phi⁻¹) (Z0 ω)) ∂Pr| +
            ((Pr {ω | ∀ j : Fin p, Z0 ω j ≤ y j + 2 * phi⁻¹}).toReal -
              (Pr {ω | ∀ j : Fin p, Z0 ω j ≤ y j - 2 * phi⁻¹}).toReal))) := by
  /- @proof-region region.target-node.session.a7e5b55113f203ad begin -/
  intro p hp phi hphi phi0 hphi0_smooth hphi0_left hphi0_right hphi0_range Ω _ P _ Z1 Z0 hZ1 hZ0
  intro kappa
  have hκrange : ∀ (y : Fin p → ℝ) (w : Fin p → ℝ), 0 ≤ kappa y w ∧ kappa y w ≤ 1 := by
    intro y w
    have h := (statopia_math_node_2194576110_d2ad0cef p hp phi hphi phi0 hphi0_smooth
      hphi0_left hphi0_right hphi0_range y).2.1 w
    dsimp only [kappa] at h ⊢
    exact h
  have hsand : ∀ (y : Fin p → ℝ) (w : Fin p → ℝ),
      Set.indicator {w : Fin p → ℝ | ∀ j : Fin p, w j ≤ y j - phi⁻¹} (fun _ => (1 : ℝ)) w ≤ kappa y w ∧
      kappa y w ≤ Set.indicator {w : Fin p → ℝ | ∀ j : Fin p, w j ≤ y j + phi⁻¹} (fun _ => (1 : ℝ)) w := by
    intro y w
    have h := (statopia_math_node_2194576110_d2ad0cef p hp phi hphi phi0 hphi0_smooth
      hphi0_left hphi0_right hphi0_range y).2.2.2.2.2.2.2 w
    dsimp only [kappa] at h ⊢
    exact h
  have hκmeas : ∀ (y : Fin p → ℝ) (Z : Ω → Fin p → ℝ), Measurable Z →
      Measurable (fun ω => kappa y (Z ω)) := by
    intro y Z hZ
    have hp0 : Measurable phi0 := hphi0_smooth.continuous.measurable
    dsimp only [kappa]
    measurability
  have hκint : ∀ (y : Fin p → ℝ) (Z : Ω → Fin p → ℝ), Measurable Z →
      Integrable (fun ω => kappa y (Z ω)) P := by
    intro y Z hZ
    refine Integrable.of_bound (hκmeas y Z hZ).aestronglyMeasurable 1 ?_
    filter_upwards with ω
    have h1 := (hκrange y (Z ω)).1
    have h2 := (hκrange y (Z ω)).2
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, h2⟩
  have hind : ∀ (S : Set Ω), MeasurableSet S →
      (∫ ω, S.indicator (fun _ => (1 : ℝ)) ω ∂P) = (P S).toReal := by
    intro S hS
    rw [MeasureTheory.integral_indicator hS]
    simp
    rfl
  have hA : ∀ (y : Fin p → ℝ) (Z : Ω → Fin p → ℝ), Measurable Z →
      (P {ω | ∀ k : Fin p, Z ω k ≤ y k - phi⁻¹}).toReal ≤ ∫ ω, kappa y (Z ω) ∂P ∧
      (∫ ω, kappa y (Z ω) ∂P) ≤ (P {ω | ∀ k : Fin p, Z ω k ≤ y k + phi⁻¹}).toReal := by
    intro y Z hZ
    have hmeas : ∀ (c : Fin p → ℝ), MeasurableSet {ω : Ω | ∀ k : Fin p, Z ω k ≤ c k} := by
      intro c
      rw [show {ω : Ω | ∀ k : Fin p, Z ω k ≤ c k} = ⋂ k, {ω | Z ω k ≤ c k} from by
        ext ω
        simp]
      exact MeasurableSet.iInter
        (fun k => measurableSet_le ((measurable_pi_apply k).comp hZ)
          (measurable_const : Measurable fun _ : Ω => c k))
    have hFrewrite : ∀ (c : Fin p → ℝ),
        (fun ω => Set.indicator {z : Fin p → ℝ | ∀ k : Fin p, z k ≤ c k} (fun _ => (1 : ℝ)) (Z ω))
          = ({ω | ∀ k : Fin p, Z ω k ≤ c k}).indicator (fun _ => (1 : ℝ)) := by
      intro c
      funext ω
      by_cases hc : ∀ k : Fin p, Z ω k ≤ c k <;> simp [Set.indicator, hc]
    have hFval : ∀ (c : Fin p → ℝ),
        (∫ ω, Set.indicator {z : Fin p → ℝ | ∀ k : Fin p, z k ≤ c k} (fun _ => (1 : ℝ)) (Z ω) ∂P)
          = (P {ω | ∀ k : Fin p, Z ω k ≤ c k}).toReal := by
      intro c
      rw [hFrewrite c]
      exact hind _ (hmeas c)
    have hFint : ∀ (c : Fin p → ℝ),
        Integrable (fun ω => Set.indicator {z : Fin p → ℝ | ∀ k : Fin p, z k ≤ c k} (fun _ => (1 : ℝ)) (Z ω)) P := by
      intro c
      rw [hFrewrite c]
      exact (MeasureTheory.integrable_const (1 : ℝ)).indicator (hmeas c)
    constructor
    · have hle : (fun ω => Set.indicator {z : Fin p → ℝ | ∀ k : Fin p, z k ≤ (fun k => y k - phi⁻¹) k} (fun _ => (1 : ℝ)) (Z ω))
          ≤ (fun ω => kappa y (Z ω)) := by
        intro ω
        exact (hsand y (Z ω)).1
      have hmono := integral_mono (hFint (fun k => y k - phi⁻¹)) (hκint y Z hZ) hle
      rw [hFval (fun k => y k - phi⁻¹)] at hmono
      exact hmono
    · have hle : (fun ω => kappa y (Z ω))
          ≤ (fun ω => Set.indicator {z : Fin p → ℝ | ∀ k : Fin p, z k ≤ (fun k => y k + phi⁻¹) k} (fun _ => (1 : ℝ)) (Z ω)) := by
        intro ω
        exact (hsand y (Z ω)).2
      have hmono := integral_mono (hκint y Z hZ) (hFint (fun k => y k + phi⁻¹)) hle
      rw [hFval (fun k => y k + phi⁻¹)] at hmono
      exact hmono
  refine ⟨fun y => hA y Z1 hZ1, fun y => hA y Z0 hZ0, ?_⟩
  intro y
  have hpos : (0 : ℝ) < phi⁻¹ := inv_pos.mpr (by linarith)
  have hmono : ∀ {s t : Set Ω}, s ⊆ t → (P s).toReal ≤ (P t).toReal := by
    intro s t hst
    exact ENNReal.toReal_mono (measure_ne_top P t) (measure_mono hst)
  have h1 : (P {ω : Ω | ∀ k : Fin p, Z1 ω k ≤ y k}).toReal ≤
      ∫ ω, kappa (fun k => y k + phi⁻¹) (Z1 ω) ∂P := by
    have hbase := (hA (fun k => y k + phi⁻¹) Z1 hZ1).1
    have hset : {ω : Ω | ∀ k : Fin p, Z1 ω k ≤ (fun k => y k + phi⁻¹) k - phi⁻¹}
        = {ω : Ω | ∀ k : Fin p, Z1 ω k ≤ y k} := by
      ext ω; simp only [Set.mem_setOf_eq]
      constructor <;> intro h k
      · have := h k; linarith
      · have := h k; linarith
    rw [hset] at hbase; exact hbase
  have h2 : (∫ ω, kappa (fun k => y k + phi⁻¹) (Z0 ω) ∂P) ≤
      (P {ω : Ω | ∀ k : Fin p, Z0 ω k ≤ y k + 2 * phi⁻¹}).toReal := by
    have hbase := (hA (fun k => y k + phi⁻¹) Z0 hZ0).2
    have hset : {ω : Ω | ∀ k : Fin p, Z0 ω k ≤ (fun k => y k + phi⁻¹) k + phi⁻¹}
        = {ω : Ω | ∀ k : Fin p, Z0 ω k ≤ y k + 2 * phi⁻¹} := by
      ext ω; simp only [Set.mem_setOf_eq]
      constructor <;> intro h k
      · have := h k; linarith
      · have := h k; linarith
    rw [hset] at hbase; exact hbase
  have h3 : (∫ ω, kappa (fun k => y k - phi⁻¹) (Z1 ω) ∂P) ≤
      (P {ω : Ω | ∀ k : Fin p, Z1 ω k ≤ y k}).toReal := by
    have hbase := (hA (fun k => y k - phi⁻¹) Z1 hZ1).2
    have hset : {ω : Ω | ∀ k : Fin p, Z1 ω k ≤ (fun k => y k - phi⁻¹) k + phi⁻¹}
        = {ω : Ω | ∀ k : Fin p, Z1 ω k ≤ y k} := by
      ext ω; simp only [Set.mem_setOf_eq]
      constructor <;> intro h k
      · have := h k; linarith
      · have := h k; linarith
    rw [hset] at hbase; exact hbase
  have h4 : (P {ω : Ω | ∀ k : Fin p, Z0 ω k ≤ y k - 2 * phi⁻¹}).toReal ≤
      ∫ ω, kappa (fun k => y k - phi⁻¹) (Z0 ω) ∂P := by
    have hbase := (hA (fun k => y k - phi⁻¹) Z0 hZ0).1
    have hset : {ω : Ω | ∀ k : Fin p, Z0 ω k ≤ (fun k => y k - phi⁻¹) k - phi⁻¹}
        = {ω : Ω | ∀ k : Fin p, Z0 ω k ≤ y k - 2 * phi⁻¹} := by
      ext ω; simp only [Set.mem_setOf_eq]
      constructor <;> intro h k
      · have := h k; linarith
      · have := h k; linarith
    rw [hset] at hbase; exact hbase
  have h5 : (P {ω : Ω | ∀ k : Fin p, Z0 ω k ≤ y k - 2 * phi⁻¹}).toReal ≤
      (P {ω : Ω | ∀ k : Fin p, Z0 ω k ≤ y k}).toReal := by
    apply hmono
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    intro k
    have := hω k
    linarith
  have h6 : (P {ω : Ω | ∀ k : Fin p, Z0 ω k ≤ y k}).toReal ≤
      (P {ω : Ω | ∀ k : Fin p, Z0 ω k ≤ y k + 2 * phi⁻¹}).toReal := by
    apply hmono
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    intro k
    have := hω k
    linarith
  have hE1 : (∫ ω, (kappa (fun k => y k + phi⁻¹) (Z1 ω) - kappa (fun k => y k + phi⁻¹) (Z0 ω)) ∂P)
      = (∫ ω, kappa (fun k => y k + phi⁻¹) (Z1 ω) ∂P) -
        (∫ ω, kappa (fun k => y k + phi⁻¹) (Z0 ω) ∂P) :=
    MeasureTheory.integral_sub (hκint (fun k => y k + phi⁻¹) Z1 hZ1)
      (hκint (fun k => y k + phi⁻¹) Z0 hZ0)
  have hE2 : (∫ ω, (kappa (fun k => y k - phi⁻¹) (Z1 ω) - kappa (fun k => y k - phi⁻¹) (Z0 ω)) ∂P)
      = (∫ ω, kappa (fun k => y k - phi⁻¹) (Z1 ω) ∂P) -
        (∫ ω, kappa (fun k => y k - phi⁻¹) (Z0 ω) ∂P) :=
    MeasureTheory.integral_sub (hκint (fun k => y k - phi⁻¹) Z1 hZ1)
      (hκint (fun k => y k - phi⁻¹) Z0 hZ0)
  have hEp : (∫ ω, (kappa (fun k => y k + phi⁻¹) (Z1 ω) - kappa (fun k => y k + phi⁻¹) (Z0 ω)) ∂P)
      ≤ |∫ ω, (kappa (fun k => y k + phi⁻¹) (Z1 ω) - kappa (fun k => y k + phi⁻¹) (Z0 ω)) ∂P| :=
    le_abs_self _
  have hEm : -(∫ ω, (kappa (fun k => y k - phi⁻¹) (Z1 ω) - kappa (fun k => y k - phi⁻¹) (Z0 ω)) ∂P)
      ≤ |∫ ω, (kappa (fun k => y k - phi⁻¹) (Z1 ω) - kappa (fun k => y k - phi⁻¹) (Z0 ω)) ∂P| :=
    neg_le_abs _
  have hnn1 : (0 : ℝ) ≤
      |∫ ω, (kappa (fun k => y k + phi⁻¹) (Z1 ω) - kappa (fun k => y k + phi⁻¹) (Z0 ω)) ∂P| :=
    abs_nonneg _
  have hnn2 : (0 : ℝ) ≤
      |∫ ω, (kappa (fun k => y k - phi⁻¹) (Z1 ω) - kappa (fun k => y k - phi⁻¹) (Z0 ω)) ∂P| :=
    abs_nonneg _
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
  /- @proof-region region.target-node.session.a7e5b55113f203ad end -/

end

end Statlib.Imported

