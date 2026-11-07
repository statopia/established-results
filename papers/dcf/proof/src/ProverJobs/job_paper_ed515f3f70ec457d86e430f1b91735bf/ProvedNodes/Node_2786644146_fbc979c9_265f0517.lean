import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_1224548605_c698de4a_4a2fc4da
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_1332223818_b5c088a2_0ab99bd5
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ExternalNodes.Node_4e38c0b212aeaf238af1

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
theorem statopia_math_node_2786644146_fbc979c9 : ∀ (b : ℝ) (hb : 0 < b),
    ∃ Cb : ℝ, 0 < Cb ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (n m p : ℕ), 0 < n → 0 < m → 0 < p → 0 < Real.log (p : ℝ) →
        ∀ (delta : ℕ → ℕ → ℝ), delta n m = 0 →
        ∀ (muX muY : Fin p → ℝ)
          (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
          (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ),
          (∀ i : Fin n, Measurable (F i)) →
          (∀ i : Fin m, Measurable (G i)) →
          iIndepFun (β := fun _ => Fin p → ℝ) (jointFam X Y F G) P →
          (∀ (i : Fin n) (j : Fin p), MemLp (fun ω => X i ω j) 2 P) →
          (∀ (i : Fin m) (j : Fin p), MemLp (fun ω => Y i ω j) 2 P) →
          (∀ (i : Fin n) (j : Fin p), ∫ ω, X i ω j ∂P = muX j) →
          (∀ (i : Fin m) (j : Fin p), ∫ ω, Y i ω j ∂P = muY j) →
          (∀ i : Fin n,
            IsCenteredGaussianVector P (fun ω j => F i ω j - muX j) (covX P muX X i)) →
          (∀ i : Fin m,
            IsCenteredGaussianVector P (fun ω j => G i ω j - muY j) (covY P muY Y i)) →
          (∀ j : Fin p, Integrable (fun ω =>
            (combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j) ^ 2) P) →
          (∀ j : Fin p, b ≤ ∫ ω,
            (combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j) ^ 2 ∂P) →
            ((∀ j : Fin p,
                (∫ ω, (combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j) ^ 2 ∂P)
                  = (∫ ω, (combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j) ^ 2 ∂P))
              ∧ (∀ j : Fin p, b ≤ ∫ ω,
                  (combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j) ^ 2 ∂P))
              ∧ (∀ (y : Fin p → ℝ) (a : ℝ), 0 < a →
                  (P {ω | ∀ j : Fin p,
                      combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤ y j + a}).toReal -
                    (P {ω | ∀ j : Fin p,
                      combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤ y j}).toReal
                    ≤ Cb * a * Real.sqrt (Real.log (p : ℝ))) := by
  /- @proof-region region.target-node.session.40d16c476f6a373f begin -/
  intro b hb
  obtain ⟨C, hC, hCbound⟩ := ext_model_2 b hb
  refine ⟨C * 4 + 1, by linarith, ?_⟩
  intro Ω _ P _ n m p hn hm hp hlog delta hdelta muX muY X Y F G hFm hGm hind hMemX hMemY
    hMeanX hMeanY hGaussF hGaussG hInt hb2
  have hp2 : 2 ≤ p := by
    by_contra hcon
    have h2 : p = 1 := by omega
    subst h2
    simp at hlog
  obtain ⟨hGauss, hmean⟩ :=
    statopia_math_node_1224548605_c698de4a P hn hm hp delta muX muY X Y F G hFm hGm hind
      hMemX hMemY hMeanX hMeanY hGaussF hGaussG
  have hvar :=
    statopia_math_node_1332223818_b5c088a2 P hn hm hp delta muX muY X Y F G hFm hGm hind
      hMemX hMemY hMeanX hMeanY hGaussF hGaussG
  refine ⟨⟨hvar, ?_⟩, ?_⟩
  · intro j
    rw [hvar j]
    exact hb2 j
  · intro y a ha
    set U' : Ω → Fin p → ℝ :=
      fun ω j => combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j with hU'
    have hU'meas : Measurable U' := by
      rw [hU']
      refine measurable_pi_iff.mpr (fun j => ?_)
      have hsum : Measurable fun ω => ∑ i : Fin n, F i ω j := by
        apply Finset.measurable_sum
        intro i _
        exact (measurable_pi_apply j).comp (hFm i)
      have h1 : Measurable fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i : Fin n, F i ω j :=
        measurable_const.mul hsum
      have h2 : Measurable fun _ : Ω => Real.sqrt (n : ℝ) * muX j := measurable_const
      simpa only [combVec, normSum, hdelta, mul_zero, zero_mul, sub_zero, add_zero] using h1.sub h2
    haveI hprobU : IsProbabilityMeasure (Measure.map U' P) :=
      Measure.isProbabilityMeasure_map hU'meas.aemeasurable
    have hvar' : ∀ j : Fin p, b ≤ ∫ z : Fin p → ℝ, (z j) ^ 2 ∂(Measure.map U' P) := by
      intro j
      have hpow : Measurable fun z : Fin p → ℝ => (z j) ^ 2 := by
        simpa only [pow_two] using (measurable_pi_apply j).mul (measurable_pi_apply j)
      rw [integral_map hU'meas.aemeasurable (f := fun z : Fin p → ℝ => (z j) ^ 2)
        hpow.aestronglyMeasurable]
      show b ≤ ∫ ω, (combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j) ^ 2 ∂P
      rw [hvar j]
      exact hb2 j
    have hvarc : ∀ k : Fin p, b ≤ ∫ ω, (U' ω k) ^ 2 ∂P := by
      intro k
      have h := hvar' k
      have hposk : Measurable fun z : Fin p → ℝ => (z k) ^ 2 := by
        simpa only [pow_two] using (measurable_pi_apply k).mul (measurable_pi_apply k)
      rw [integral_map hU'meas.aemeasurable (f := fun z : Fin p → ℝ => (z k) ^ 2)
        hposk.aestronglyMeasurable] at h
      simpa using h
    have hmean' : ∫ z : Fin p → ℝ, z ∂(Measure.map U' P) = fun _ => 0 := hmean
    have hGauss' : IsGaussian (Measure.map U' P) := hGauss
    have hTgen : ∀ (q : ℕ) (c : Fin q → ℝ),
        MeasurableSet {z : Fin q → ℝ | ∀ j : Fin q, z j ≤ c j} := by
      intro q c
      have h : {z : Fin q → ℝ | ∀ j : Fin q, z j ≤ c j}
          = ⋂ j : Fin q, {z : Fin q → ℝ | z j ≤ c j} := by
        ext z
        simp
      rw [h]
      exact MeasurableSet.iInter
        (fun j => measurableSet_le (measurable_pi_apply j) measurable_const)
    have key : (P {ω | ∀ j : Fin p, U' ω j ≤ y j + a}).toReal -
          (P {ω | ∀ j : Fin p, U' ω j ≤ y j}).toReal
          ≤ (C * 4 + 1) * a * Real.sqrt (Real.log (p : ℝ)) := by
      by_cases hp3 : 3 ≤ p
      · have hkey := hCbound p hp3 (Measure.map U' P) hGauss' hmean' hvar' y a ha
        have hT1 := hTgen p (fun j : Fin p => y j + a)
        have hT2 := hTgen p (fun j : Fin p => y j)
        have e1 : (Measure.map U' P) {z : Fin p → ℝ | ∀ j : Fin p, z j ≤ (fun j : Fin p => y j + a) j}
            = P {ω | ∀ j : Fin p, U' ω j ≤ y j + a} := by
          rw [Measure.map_apply hU'meas hT1]
          rfl
        have e2 : (Measure.map U' P) {z : Fin p → ℝ | ∀ j : Fin p, z j ≤ (fun j : Fin p => y j) j}
            = P {ω | ∀ j : Fin p, U' ω j ≤ y j} := by
          rw [Measure.map_apply hU'meas hT2]
          rfl
        calc (P {ω | ∀ j : Fin p, U' ω j ≤ y j + a}).toReal -
              (P {ω | ∀ j : Fin p, U' ω j ≤ y j}).toReal
            = ((Measure.map U' P) {z : Fin p → ℝ | ∀ j : Fin p,
                  z j ≤ (fun j : Fin p => y j + a) j}).toReal -
                ((Measure.map U' P) {z : Fin p → ℝ | ∀ j : Fin p,
                  z j ≤ (fun j : Fin p => y j) j}).toReal := by
                rw [← e1, ← e2]
          _ ≤ C * a * Real.sqrt (Real.log (p : ℝ)) := hkey
          _ ≤ (C * 4 + 1) * a * Real.sqrt (Real.log (p : ℝ)) := by
              have hs : 0 ≤ Real.sqrt (Real.log (p : ℝ)) := Real.sqrt_nonneg _
              have h1 : C ≤ C * 4 + 1 := by linarith
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right h1 (le_of_lt ha)) hs
      · have hp_eq : p = 2 := by omega
        subst hp_eq
        let g : Fin 3 → Fin 2 := fun j => Fin.cases (0 : Fin 2) (fun i : Fin 2 => i) j
        let L : (Fin 2 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
          ContinuousLinearMap.pi (fun j : Fin 3 => ContinuousLinearMap.proj (g j))
        have hL : ∀ (z : Fin 2 → ℝ) (j : Fin 3), L z j = z (g j) := by
          intro z j
          simp only [L, ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply]
        haveI hprob3 : IsProbabilityMeasure (Measure.map (⇑L) (Measure.map U' P)) :=
          Measure.isProbabilityMeasure_map L.continuous.measurable.aemeasurable
        have hGauss3 : IsGaussian (Measure.map (⇑L) (Measure.map U' P)) := by
          haveI : IsGaussian (Measure.map U' P) := hGauss'
          exact isGaussian_map L
        have hint1 : ∫ z : Fin 3 → ℝ, z ∂(Measure.map (⇑L) (Measure.map U' P))
            = ∫ z : Fin 2 → ℝ, L z ∂(Measure.map U' P) :=
          integral_map L.continuous.measurable.aemeasurable
            (f := fun z : Fin 3 → ℝ => z) measurable_id.aestronglyMeasurable
        have hcomp : ∫ z : Fin 2 → ℝ, L z ∂(Measure.map U' P)
            = L (∫ z : Fin 2 → ℝ, z ∂(Measure.map U' P)) := by
          refine ContinuousLinearMap.integral_comp_comm L ?_
          haveI : IsGaussian (Measure.map U' P) := hGauss'
          exact (IsGaussian.memLp_id (Measure.map U' P) (2 : ENNReal) (by norm_num)).integrable
            (by norm_num)
        have hmean3 : ∫ z : Fin 3 → ℝ, z ∂(Measure.map (⇑L) (Measure.map U' P))
            = fun _ => 0 := by
          rw [hint1, hcomp, hmean']
          exact map_zero L
        have hvar3 : ∀ j : Fin 3, b ≤
            ∫ z : Fin 3 → ℝ, (z j) ^ 2 ∂(Measure.map (⇑L) (Measure.map U' P)) := by
          intro j
          have hLproj : Measurable fun z : Fin 2 → ℝ => L z j :=
            (measurable_pi_apply j).comp L.continuous.measurable
          have hpowj : Measurable fun z : Fin 3 → ℝ => (z j) ^ 2 := by
            simpa only [pow_two] using (measurable_pi_apply j).mul (measurable_pi_apply j)
          have hpowL : Measurable fun z : Fin 2 → ℝ => (L z j) ^ 2 := by
            simpa only [pow_two] using hLproj.mul hLproj
          rw [integral_map L.continuous.measurable.aemeasurable
            (f := fun z : Fin 3 → ℝ => (z j) ^ 2) hpowj.aestronglyMeasurable]
          rw [integral_map hU'meas.aemeasurable (f := fun z : Fin 2 → ℝ => (L z j) ^ 2)
            hpowL.aestronglyMeasurable]
          have hcongr : ∫ ω, (L (U' ω) j) ^ 2 ∂P = ∫ ω, (U' ω (g j)) ^ 2 ∂P := by
            refine integral_congr_ae ?_
            filter_upwards with ω
            rw [hL]
          rw [hcongr]
          exact hvarc (g j)
        have hiff : ∀ (c : Fin 2 → ℝ) (z : Fin 2 → ℝ),
            (∀ j : Fin 3, z (g j) ≤ c (g j)) ↔ (∀ k : Fin 2, z k ≤ c k) := by
          intro c z
          constructor
          · intro h k
            have hk := h k.succ
            rwa [show g k.succ = k from rfl] at hk
          · intro h j
            rw [show g j = Fin.cases (0 : Fin 2) (fun i : Fin 2 => i) j from rfl]
            revert h
            refine Fin.cases ?_ ?_ j
            · intro h
              simpa using h 0
            · intro i h
              simpa using h i
        have hset3a : {z : Fin 2 → ℝ | ∀ j : Fin 3, z (g j) ≤ (fun k : Fin 2 => y k + a) (g j)}
            = {z : Fin 2 → ℝ | ∀ k : Fin 2, z k ≤ (fun k : Fin 2 => y k + a) k} := by
          ext z
          simp only [Set.mem_setOf_eq]
          exact hiff (fun k : Fin 2 => y k + a) z
        have hset3b : {z : Fin 2 → ℝ | ∀ j : Fin 3, z (g j) ≤ (fun k : Fin 2 => y k) (g j)}
            = {z : Fin 2 → ℝ | ∀ k : Fin 2, z k ≤ (fun k : Fin 2 => y k) k} := by
          ext z
          simp only [Set.mem_setOf_eq]
          exact hiff (fun k : Fin 2 => y k) z
        have e3a : (Measure.map (⇑L) (Measure.map U' P)) {z : Fin 3 → ℝ | ∀ j : Fin 3,
              z j ≤ (fun j : Fin 3 => y (g j) + a) j}
            = (Measure.map U' P) {z : Fin 2 → ℝ | ∀ j : Fin 3, L z j ≤ (fun j : Fin 3 => y (g j) + a) j} := by
          rw [Measure.map_apply L.continuous.measurable (hTgen 3 (fun j : Fin 3 => y (g j) + a))]
          rfl
        have e3a' : (Measure.map (⇑L) (Measure.map U' P)) {z : Fin 3 → ℝ | ∀ j : Fin 3,
              z j ≤ (fun j : Fin 3 => y (g j)) j}
            = (Measure.map U' P) {z : Fin 2 → ℝ | ∀ j : Fin 3, L z j ≤ (fun j : Fin 3 => y (g j)) j} := by
          rw [Measure.map_apply L.continuous.measurable (hTgen 3 (fun j : Fin 3 => y (g j)))]
          rfl
        have hset3c : {z : Fin 2 → ℝ | ∀ j : Fin 3, L z j ≤ (fun j : Fin 3 => y (g j) + a) j}
            = {z : Fin 2 → ℝ | ∀ j : Fin 3, z (g j) ≤ (fun k : Fin 2 => y k + a) (g j)} := by
          ext z
          simp only [Set.mem_setOf_eq, hL]
        have hset3c' : {z : Fin 2 → ℝ | ∀ j : Fin 3, L z j ≤ (fun j : Fin 3 => y (g j)) j}
            = {z : Fin 2 → ℝ | ∀ j : Fin 3, z (g j) ≤ (fun k : Fin 2 => y k) (g j)} := by
          ext z
          simp only [Set.mem_setOf_eq, hL]
        have e3b : (Measure.map U' P) {z : Fin 2 → ℝ | ∀ j : Fin 3,
              L z j ≤ (fun j : Fin 3 => y (g j) + a) j}
            = (Measure.map U' P) {z : Fin 2 → ℝ | ∀ k : Fin 2, z k ≤ (fun k : Fin 2 => y k + a) k} := by
          rw [hset3c, hset3a]
        have e3b' : (Measure.map U' P) {z : Fin 2 → ℝ | ∀ j : Fin 3,
              L z j ≤ (fun j : Fin 3 => y (g j)) j}
            = (Measure.map U' P) {z : Fin 2 → ℝ | ∀ k : Fin 2, z k ≤ (fun k : Fin 2 => y k) k} := by
          rw [hset3c', hset3b]
        have e3c : (Measure.map U' P) {z : Fin 2 → ℝ | ∀ k : Fin 2, z k ≤ (fun k : Fin 2 => y k + a) k}
            = P {ω | ∀ k : Fin 2, U' ω k ≤ y k + a} := by
          rw [Measure.map_apply hU'meas (hTgen 2 (fun k : Fin 2 => y k + a))]
          rfl
        have e3c' : (Measure.map U' P) {z : Fin 2 → ℝ | ∀ k : Fin 2, z k ≤ (fun k : Fin 2 => y k) k}
            = P {ω | ∀ k : Fin 2, U' ω k ≤ y k} := by
          rw [Measure.map_apply hU'meas (hTgen 2 (fun k : Fin 2 => y k))]
          rfl
        have hkey3 := hCbound 3 (by norm_num) (Measure.map (⇑L) (Measure.map U' P)) hGauss3 hmean3
          hvar3 (fun j : Fin 3 => y (g j)) a ha
        have hsqrt3 : C * a * Real.sqrt (Real.log (3 : ℝ))
            ≤ (C * 4 + 1) * a * Real.sqrt (Real.log (2 : ℝ)) := by
          have hlog2p : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
          have hlog3p : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
          have hlog43 : Real.log (3 : ℝ) ≤ 4 * Real.log (2 : ℝ) := by
            have h34 : Real.log (3 : ℝ) ≤ Real.log 4 :=
              Real.log_le_log (by norm_num) (by norm_num)
            have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
              rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
              ring
            linarith
          have hA : Real.sqrt (Real.log (3 : ℝ)) ^ 2 = Real.log 3 :=
            Real.sq_sqrt (le_of_lt hlog3p)
          have hB : Real.sqrt (Real.log (2 : ℝ)) ^ 2 = Real.log 2 :=
            Real.sq_sqrt (le_of_lt hlog2p)
          have hle : Real.sqrt (Real.log (3 : ℝ)) ≤ 2 * Real.sqrt (Real.log 2) := by
            nlinarith [hA, hB, hlog43, Real.sqrt_nonneg (Real.log 3),
              Real.sqrt_nonneg (Real.log 2)]
          have hs1 : C * a * Real.sqrt (Real.log (3 : ℝ))
              ≤ C * a * (2 * Real.sqrt (Real.log 2)) :=
            mul_le_mul_of_nonneg_left hle (le_of_lt (mul_pos hC ha))
          have hs2 : C * a * (2 * Real.sqrt (Real.log 2))
              ≤ (C * 4 + 1) * a * Real.sqrt (Real.log 2) := by
            have h2 : 2 * C ≤ C * 4 + 1 := by linarith
            have h3 : (0:ℝ) ≤ a * Real.sqrt (Real.log 2) :=
              mul_nonneg (le_of_lt ha) (Real.sqrt_nonneg _)
            have h4 := mul_le_mul_of_nonneg_right h2 h3
            nlinarith [h4]
          linarith
        calc (P {ω | ∀ k : Fin 2, U' ω k ≤ y k + a}).toReal -
              (P {ω | ∀ k : Fin 2, U' ω k ≤ y k}).toReal
            = ((Measure.map (⇑L) (Measure.map U' P)) {z : Fin 3 → ℝ | ∀ j : Fin 3,
                  z j ≤ (fun j : Fin 3 => y (g j) + a) j}).toReal -
                ((Measure.map (⇑L) (Measure.map U' P)) {z : Fin 3 → ℝ | ∀ j : Fin 3,
                  z j ≤ (fun j : Fin 3 => y (g j)) j}).toReal := by
                rw [← e3c, ← e3b, ← e3a, ← e3c', ← e3b', ← e3a']
          _ ≤ C * a * Real.sqrt (Real.log (3 : ℝ)) := hkey3
          _ ≤ (C * 4 + 1) * a * Real.sqrt (Real.log (2 : ℝ)) := hsqrt3
    exact key
  /- @proof-region region.target-node.session.40d16c476f6a373f end -/

end

end Statlib.Imported

