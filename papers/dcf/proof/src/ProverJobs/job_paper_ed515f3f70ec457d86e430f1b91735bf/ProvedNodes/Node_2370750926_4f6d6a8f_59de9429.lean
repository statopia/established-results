import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_384110174_b4277f3b_558afef4

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
theorem statopia_math_node_2370750926_4f6d6a8f : ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n m p : ℕ) (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
    (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
    (hn : 0 < n) (hm : 0 < m) (hp : 0 < p)
    (hX : ∀ i : Fin n, Measurable (X i)) (hY : ∀ i : Fin m, Measurable (Y i))
    (hF : ∀ i : Fin n, Measurable (F i)) (hG : ∀ i : Fin m, Measurable (G i))
    (hindep : iIndepFun (β := fun _ => Fin p → ℝ) (jointFam X Y F G) P)
    (hFcov : ∀ i : Fin n,
      IsCenteredGaussianVector P (fun ω j => F i ω j - muX j) (covX P muX X i))
    (hGcov : ∀ i : Fin m,
      IsCenteredGaussianVector P (fun ω j => G i ω j - muY j) (covY P muY Y i))
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (y : Fin p → ℝ) (w : ℝ) (hw : 0 ≤ w),
    let Z : ℝ → Ω × Ω → Fin p → ℝ := fun t x j =>
      (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ *
          (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)) +
            Real.sqrt (1 - t) * (F i x.2 j - muX j)))
        + (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m *
          (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j)) +
            Real.sqrt (1 - t) * (G i x.2 j - muY j)))
    ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      (∫ x : Ω × Ω,
        Set.indicator
          {x : Ω × Ω |
            -(w) < (⨆ j : Fin p, (Z t x j - y j)) ∧
            (⨆ j : Fin p, (Z t x j - y j)) ≤ w}
          (fun _ => (1 : ℝ)) x ∂(P.prod P))
      ≤ (P {ω : Ω |
          -(w) < (⨆ j : Fin p, (combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j - y j)) ∧
          (⨆ j : Fin p, (combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j - y j)) ≤ w}).toReal
        + 2 * rho P n m p (delta n m) muX muY X Y F G := by
  /- @proof-region region.target-node.session.33cbf9e32ecfa114 begin -/
  intro Ω _inst P _instP n m p delta muX muY X Y F G hn hm hp hX hY hF hG hindep hFcov hGcov v
    hv0 hv1 y w hw
  intro Z t ht
  obtain ⟨ht0, ht1⟩ := ht
  set SZ : Ω × Ω → ℝ := fun x => ⨆ j : Fin p, (Z t x j - y j) with hSZ
  set B : Ω → Fin p → ℝ := fun ω => combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) with hB
  set SB : Ω → ℝ := fun ω => ⨆ j : Fin p, (B ω j - y j) with hSB
  haveI hne : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  have hZmeas : ∀ j : Fin p, Measurable fun x : Ω × Ω => Z t x j := by
    intro j
    have mX1 : ∀ i : Fin n, Measurable fun x : Ω × Ω => X i x.1 j := fun i =>
      ((measurable_pi_apply j).comp (hX i)).comp measurable_fst
    have mY1 : ∀ i : Fin m, Measurable fun x : Ω × Ω => Y i x.1 j := fun i =>
      ((measurable_pi_apply j).comp (hY i)).comp measurable_fst
    have mF1 : ∀ i : Fin n, Measurable fun x : Ω × Ω => F i x.1 j := fun i =>
      ((measurable_pi_apply j).comp (hF i)).comp measurable_fst
    have mF2 : ∀ i : Fin n, Measurable fun x : Ω × Ω => F i x.2 j := fun i =>
      ((measurable_pi_apply j).comp (hF i)).comp measurable_snd
    have mG1 : ∀ i : Fin m, Measurable fun x : Ω × Ω => G i x.1 j := fun i =>
      ((measurable_pi_apply j).comp (hG i)).comp measurable_fst
    have mG2 : ∀ i : Fin m, Measurable fun x : Ω × Ω => G i x.2 j := fun i =>
      ((measurable_pi_apply j).comp (hG i)).comp measurable_snd
    have hterm1 : ∀ i : Fin n, Measurable fun x : Ω × Ω =>
        (Real.sqrt (n : ℝ))⁻¹ *
          (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)) +
            Real.sqrt (1 - t) * (F i x.2 j - muX j)) := by
      intro i
      have hA : Measurable fun x : Ω × Ω => Real.sqrt v * (X i x.1 j - muX j) :=
        ((mX1 i).sub measurable_const).const_mul (Real.sqrt v)
      have hB : Measurable fun x : Ω × Ω => Real.sqrt (1 - v) * (F i x.1 j - muX j) :=
        ((mF1 i).sub measurable_const).const_mul (Real.sqrt (1 - v))
      have hC : Measurable fun x : Ω × Ω => Real.sqrt (1 - t) * (F i x.2 j - muX j) :=
        ((mF2 i).sub measurable_const).const_mul (Real.sqrt (1 - t))
      have hAB : Measurable fun x : Ω × Ω =>
          Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)) :=
        (hA.add hB).const_mul (Real.sqrt t)
      exact (hAB.add hC).const_mul ((Real.sqrt (n : ℝ))⁻¹)
    have hterm2 : ∀ i : Fin m, Measurable fun x : Ω × Ω =>
        (Real.sqrt (m : ℝ))⁻¹ * delta n m *
          (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j)) +
            Real.sqrt (1 - t) * (G i x.2 j - muY j)) := by
      intro i
      have hA : Measurable fun x : Ω × Ω => Real.sqrt v * (Y i x.1 j - muY j) :=
        ((mY1 i).sub measurable_const).const_mul (Real.sqrt v)
      have hB : Measurable fun x : Ω × Ω => Real.sqrt (1 - v) * (G i x.1 j - muY j) :=
        ((mG1 i).sub measurable_const).const_mul (Real.sqrt (1 - v))
      have hC : Measurable fun x : Ω × Ω => Real.sqrt (1 - t) * (G i x.2 j - muY j) :=
        ((mG2 i).sub measurable_const).const_mul (Real.sqrt (1 - t))
      have hAB : Measurable fun x : Ω × Ω =>
          Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j)) :=
        (hA.add hB).const_mul (Real.sqrt t)
      exact (hAB.add hC).const_mul ((Real.sqrt (m : ℝ))⁻¹ * delta n m)
    have hs1 : Measurable fun x : Ω × Ω => ∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ *
          (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)) +
            Real.sqrt (1 - t) * (F i x.2 j - muX j)) :=
      Finset.measurable_sum Finset.univ (fun i _ => hterm1 i)
    have hs2 : Measurable fun x : Ω × Ω => ∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m *
          (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j)) +
            Real.sqrt (1 - t) * (G i x.2 j - muY j)) :=
      Finset.measurable_sum Finset.univ (fun i _ => hterm2 i)
    exact hs1.add hs2
  have hZw : MeasurableSet {x : Ω × Ω | SZ x ≤ w} := by
    have hiff : ∀ x : Ω × Ω, SZ x ≤ w ↔ ∀ j : Fin p, Z t x j - y j ≤ w := fun x =>
      ciSup_le_iff (Set.Finite.bddAbove (Set.finite_range (fun j : Fin p => Z t x j - y j)))
    have hset : {x : Ω × Ω | SZ x ≤ w} = ⋂ j : Fin p, {x : Ω × Ω | Z t x j - y j ≤ w} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      exact hiff x
    rw [hset]
    exact MeasurableSet.iInter (fun j => measurableSet_le ((hZmeas j).sub measurable_const) measurable_const)
  have hZnw : MeasurableSet {x : Ω × Ω | SZ x ≤ -w} := by
    have hiff : ∀ x : Ω × Ω, SZ x ≤ -w ↔ ∀ j : Fin p, Z t x j - y j ≤ -w := fun x =>
      ciSup_le_iff (Set.Finite.bddAbove (Set.finite_range (fun j : Fin p => Z t x j - y j)))
    have hset : {x : Ω × Ω | SZ x ≤ -w} = ⋂ j : Fin p, {x : Ω × Ω | Z t x j - y j ≤ -w} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      exact hiff x
    rw [hset]
    exact MeasurableSet.iInter (fun j => measurableSet_le ((hZmeas j).sub measurable_const) measurable_const)
  have hBmeas : ∀ j : Fin p, Measurable fun ω : Ω => B ω j := by
    intro j
    have mF : ∀ i : Fin n, Measurable fun ω : Ω => F i ω j := fun i =>
      (measurable_pi_apply j).comp (hF i)
    have mG : ∀ i : Fin m, Measurable fun ω : Ω => G i ω j := fun i =>
      (measurable_pi_apply j).comp (hG i)
    have sF : Measurable fun ω : Ω => ∑ i : Fin n, F i ω j :=
      Finset.measurable_sum Finset.univ (fun i _ => mF i)
    have sG : Measurable fun ω : Ω => ∑ i : Fin m, G i ω j :=
      Finset.measurable_sum Finset.univ (fun i _ => mG i)
    have hcomb : Measurable fun ω : Ω =>
        (Real.sqrt (n : ℝ))⁻¹ * (∑ i : Fin n, F i ω j) - Real.sqrt (n : ℝ) * muX j
          + delta n m * ((Real.sqrt (m : ℝ))⁻¹ * (∑ i : Fin m, G i ω j))
            - delta n m * Real.sqrt (m : ℝ) * muY j :=
      (((sF.const_mul ((Real.sqrt (n : ℝ))⁻¹)).sub measurable_const).add
        ((sG.const_mul ((Real.sqrt (m : ℝ))⁻¹)).const_mul (delta n m))).sub measurable_const
    simpa only [hB, combVec, normSum] using hcomb
  have hBw : MeasurableSet {ω : Ω | SB ω ≤ w} := by
    have hiff : ∀ ω : Ω, SB ω ≤ w ↔ ∀ j : Fin p, B ω j - y j ≤ w := fun ω =>
      ciSup_le_iff (Set.Finite.bddAbove (Set.finite_range (fun j : Fin p => B ω j - y j)))
    have hset : {ω : Ω | SB ω ≤ w} = ⋂ j : Fin p, {ω : Ω | B ω j - y j ≤ w} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      exact hiff ω
    rw [hset]
    exact MeasurableSet.iInter (fun j => measurableSet_le ((hBmeas j).sub measurable_const) measurable_const)
  have hBnw : MeasurableSet {ω : Ω | SB ω ≤ -w} := by
    have hiff : ∀ ω : Ω, SB ω ≤ -w ↔ ∀ j : Fin p, B ω j - y j ≤ -w := fun ω =>
      ciSup_le_iff (Set.Finite.bddAbove (Set.finite_range (fun j : Fin p => B ω j - y j)))
    have hset : {ω : Ω | SB ω ≤ -w} = ⋂ j : Fin p, {ω : Ω | B ω j - y j ≤ -w} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      exact hiff ω
    rw [hset]
    exact MeasurableSet.iInter (fun j => measurableSet_le ((hBmeas j).sub measurable_const) measurable_const)
  have key : ∀ c : ℝ,
      |((P.prod P) {x : Ω × Ω | SZ x ≤ c}).toReal - (P {ω : Ω | SB ω ≤ c}).toReal|
        ≤ rho P n m p (delta n m) muX muY X Y F G := by
    intro c
    exact statopia_math_node_384110174_b4277f3b Ω P n m p delta muX muY X Y F G
      hn hm hp hX hY hF hG hindep hFcov hGcov v hv0 hv1 y t ht0 ht1 c


  have hZsub : ((P.prod P) {x : Ω × Ω | -w < SZ x ∧ SZ x ≤ w}).toReal
      = ((P.prod P) {x : Ω × Ω | SZ x ≤ w}).toReal
        - ((P.prod P) {x : Ω × Ω | SZ x ≤ -w}).toReal := by
    have hset : {x : Ω × Ω | -w < SZ x ∧ SZ x ≤ w}
        = {x : Ω × Ω | SZ x ≤ w} \ {x : Ω × Ω | SZ x ≤ -w} := by
      ext x
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h2, not_le.mpr h1⟩
      · rintro ⟨h2, h3⟩
        exact ⟨not_le.mp h3, h2⟩
    have hsub : {x : Ω × Ω | SZ x ≤ -w} ⊆ {x : Ω × Ω | SZ x ≤ w} := by
      intro x hx
      have hx' : SZ x ≤ -w := hx
      have h2 : -w ≤ w := by linarith [hw]
      exact le_trans hx' h2
    rw [hset, MeasureTheory.measure_diff hsub hZnw.nullMeasurableSet (by simp),
      ENNReal.toReal_sub_of_le (measure_mono hsub) (by simp)]
  have hBsub : (P {ω : Ω | -w < SB ω ∧ SB ω ≤ w}).toReal
      = (P {ω : Ω | SB ω ≤ w}).toReal - (P {ω : Ω | SB ω ≤ -w}).toReal := by
    have hset : {ω : Ω | -w < SB ω ∧ SB ω ≤ w}
        = {ω : Ω | SB ω ≤ w} \ {ω : Ω | SB ω ≤ -w} := by
      ext ω
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h2, not_le.mpr h1⟩
      · rintro ⟨h2, h3⟩
        exact ⟨not_le.mp h3, h2⟩
    have hsub : {ω : Ω | SB ω ≤ -w} ⊆ {ω : Ω | SB ω ≤ w} := by
      intro ω hω
      have hω' : SB ω ≤ -w := hω
      have h2 : -w ≤ w := by linarith [hw]
      exact le_trans hω' h2
    rw [hset, MeasureTheory.measure_diff hsub hBnw.nullMeasurableSet (by simp),
      ENNReal.toReal_sub_of_le (measure_mono hsub) (by simp)]
  have h1 : ((P.prod P) {x : Ω × Ω | SZ x ≤ w}).toReal
      ≤ (P {ω : Ω | SB ω ≤ w}).toReal + rho P n m p (delta n m) muX muY X Y F G := by
    have h := (abs_le.mp (key w)).2
    linarith
  have h2 : (P {ω : Ω | SB ω ≤ -w}).toReal
      ≤ ((P.prod P) {x : Ω × Ω | SZ x ≤ -w}).toReal
        + rho P n m p (delta n m) muX muY X Y F G := by
    have h := (abs_le.mp (key (-w))).1
    linarith
  have hmeas : MeasurableSet {x : Ω × Ω | -w < SZ x ∧ SZ x ≤ w} := by
    have hset : {x : Ω × Ω | -w < SZ x ∧ SZ x ≤ w}
        = {x : Ω × Ω | SZ x ≤ -w}ᶜ ∩ {x : Ω × Ω | SZ x ≤ w} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff, not_le]
    rw [hset]
    exact hZnw.compl.inter hZw
  have hint : (∫ x : Ω × Ω,
        Set.indicator {x : Ω × Ω | -w < SZ x ∧ SZ x ≤ w} (fun _ => (1 : ℝ)) x ∂(P.prod P))
      = ((P.prod P) {x : Ω × Ω | -w < SZ x ∧ SZ x ≤ w}).toReal := by
    have h1' : (∫ x : Ω × Ω,
          Set.indicator {x : Ω × Ω | -w < SZ x ∧ SZ x ≤ w} (fun _ => (1 : ℝ)) x ∂(P.prod P))
        = ∫ x : Ω × Ω,
          Set.indicator {x : Ω × Ω | -w < SZ x ∧ SZ x ≤ w} (1 : Ω × Ω → ℝ) x ∂(P.prod P) := rfl
    rw [h1']
    exact integral_indicator_one hmeas
  have hmain : (∫ x : Ω × Ω,
        Set.indicator {x : Ω × Ω | -w < SZ x ∧ SZ x ≤ w} (fun _ => (1 : ℝ)) x ∂(P.prod P))
      ≤ (P {ω : Ω | -w < SB ω ∧ SB ω ≤ w}).toReal
        + 2 * rho P n m p (delta n m) muX muY X Y F G := by
    rw [hint, hZsub, hBsub]
    linarith
  exact hmain



  /- @proof-region region.target-node.session.33cbf9e32ecfa114 end -/

end

end Statlib.Imported

