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
theorem statopia_math_node_3412747228_aa4ab764 : ∀ (b : ℝ) (hb : 0 < b),
    ∃ Cb : ℝ, 0 < Cb ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (n m p : ℕ) (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
        (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
        (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ),
        0 < n → 0 < m → 0 < p → 0 < Real.log (p : ℝ) → delta n m ≠ 0 →
        (∀ i : Fin n, Measurable (F i)) → (∀ i : Fin m, Measurable (G i)) →
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
            (∫ ω, (combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j) ^ 2 ∂P
              = ∫ ω, (combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j) ^ 2 ∂P)
            ∧ b ≤ ∫ ω,
                (combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j) ^ 2 ∂P)
          ∧ (∀ (y : Fin p → ℝ) (a : ℝ), 0 < a →
              (P {ω | ∀ j : Fin p,
                  combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j
                    ≤ y j + a}).toReal
                - (P {ω | ∀ j : Fin p,
                  combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j
                    ≤ y j}).toReal
              ≤ Cb * a * Real.sqrt (Real.log (p : ℝ)))) := by
  /- @proof-region region.target-node.session.ac260241f860b4ed begin -/
  intro b hb
  obtain ⟨C, hCpos, hC⟩ := ext_model_2 b hb
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨4 * C, by positivity, ?_⟩
  intro Ω _ P _ n m p delta muX muY X Y F G hn hm hp hlogp hdelta hFm hGm hind hMemX hMemY
    hMeanX hMeanY hGaussF hGaussG hInt hb2
  let U' : Ω → Fin p → ℝ := fun ω j =>
    combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j
  let D : Ω → Fin p → ℝ := fun ω j =>
    combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j
  have hU'meas : Measurable U' := by
    show Measurable (fun ω : Ω => fun j : Fin p =>
      combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j)
    rw [measurable_pi_iff]
    intro j
    have hFn : Measurable (fun ω : Ω => ∑ i : Fin n, F i ω j) :=
      Finset.measurable_sum _ (fun i _ => (measurable_pi_apply j).comp (hFm i))
    have hGn : Measurable (fun ω : Ω => ∑ i : Fin m, G i ω j) :=
      Finset.measurable_sum _ (fun i _ => (measurable_pi_apply j).comp (hGm i))
    have step1 : Measurable (fun ω : Ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i : Fin n, F i ω j) :=
      hFn.const_mul _
    have step2 : Measurable (fun ω : Ω =>
        delta n m * ((Real.sqrt (m : ℝ))⁻¹ * ∑ i : Fin m, G i ω j)) :=
      (hGn.const_mul _).const_mul _
    have stepB : Measurable (fun _ : Ω => Real.sqrt (n : ℝ) * muX j) := measurable_const
    have stepD : Measurable (fun _ : Ω => delta n m * Real.sqrt (m : ℝ) * muY j) :=
      measurable_const
    have step3 : Measurable (fun ω : Ω =>
        ((Real.sqrt (n : ℝ))⁻¹ * ∑ i : Fin n, F i ω j - Real.sqrt (n : ℝ) * muX j
          + delta n m * ((Real.sqrt (m : ℝ))⁻¹ * ∑ i : Fin m, G i ω j))) :=
      (step1.sub stepB).add step2
    have step4 : Measurable (fun ω : Ω =>
        ((Real.sqrt (n : ℝ))⁻¹ * ∑ i : Fin n, F i ω j - Real.sqrt (n : ℝ) * muX j
            + delta n m * ((Real.sqrt (m : ℝ))⁻¹ * ∑ i : Fin m, G i ω j))
          - delta n m * Real.sqrt (m : ℝ) * muY j) :=
      step3.sub stepD
    simpa only [combVec, normSum] using step4
  have horth : ∀ c : Fin p → ℝ, MeasurableSet {z : Fin p → ℝ | ∀ j : Fin p, z j ≤ c j} := by
    intro c
    have h : {z : Fin p → ℝ | ∀ j : Fin p, z j ≤ c j}
        = ⋂ j : Fin p, {z : Fin p → ℝ | z j ≤ c j} := by
      ext z
      simp
    rw [h]
    exact MeasurableSet.iInter fun j => measurableSet_le (measurable_pi_apply j) measurable_const
  have hvar : ∀ j : Fin p, (∫ ω, (U' ω j) ^ 2 ∂P) = (∫ ω, (D ω j) ^ 2 ∂P) :=
    statopia_math_node_1332223818_b5c088a2 P hn hm hp delta muX muY X Y F G
      hFm hGm hind hMemX hMemY hMeanX hMeanY hGaussF hGaussG
  refine ⟨?_, ?_⟩
  · intro j
    refine ⟨?_, ?_⟩
    · show (∫ ω, (U' ω j) ^ 2 ∂P) = (∫ ω, (D ω j) ^ 2 ∂P)
      exact hvar j
    · show b ≤ ∫ ω, (U' ω j) ^ 2 ∂P
      rw [hvar j]
      exact hb2 j
  · intro y a ha
    have hU'2 : ∀ j : Fin p, b ≤ ∫ ω, (U' ω j) ^ 2 ∂P := by
      intro j
      rw [hvar j]
      exact hb2 j
    have hlawvar : ∀ j : Fin p, b ≤ ∫ z : Fin p → ℝ, (z j) ^ 2 ∂(Measure.map U' P) := by
      intro j
      have hb1 : (∫ z : Fin p → ℝ, (z j) ^ 2 ∂(Measure.map U' P))
          = ∫ ω, (U' ω j) ^ 2 ∂P :=
        integral_map hU'meas.aemeasurable
          ((measurable_pi_apply j).pow_const 2).aestronglyMeasurable
      rw [hb1]
      exact hU'2 j
    obtain ⟨hGauss, hmean⟩ :=
      statopia_math_node_1224548605_c698de4a P hn hm hp delta muX muY X Y F G
        hFm hGm hind hMemX hMemY hMeanX hMeanY hGaussF hGaussG
    by_cases h3 : 3 ≤ p
    · have hset : ∀ c : Fin p → ℝ,
          (Measure.map U' P) {z : Fin p → ℝ | ∀ j, z j ≤ c j}
            = P {ω | ∀ j : Fin p, U' ω j ≤ c j} := by
        intro c
        rw [Measure.map_apply hU'meas (horth c)]
        rfl
      haveI hprob : IsProbabilityMeasure (Measure.map U' P) :=
        ⟨by rw [Measure.map_apply hU'meas MeasurableSet.univ]; simp⟩
      have hmain := hC p h3 (Measure.map U' P) hGauss hmean hlawvar y a ha
      rw [hset (fun j => y j + a), hset y] at hmain
      refine le_trans hmain ?_
      have hprod : 0 ≤ C * a * Real.sqrt (Real.log (p : ℝ)) := by positivity
      linarith
    · have h2p : 2 ≤ p := by
        by_cases h1p : 1 < p
        · omega
        · exfalso
          push_neg at h1p
          have hp1 : p = 1 := by omega
          rw [hp1] at hlogp
          norm_num at hlogp
      have hB : Real.sqrt (Real.log 3) ≤ 4 * Real.sqrt (Real.log (p : ℝ)) := by
        have hlog2p : Real.log 2 ≤ Real.log (p : ℝ) :=
          Real.log_le_log (by norm_num) (by exact_mod_cast h2p)
        have h43 : Real.log 3 ≤ Real.log (4 : ℝ) :=
          Real.log_le_log (by norm_num) (by norm_num)
        have h44 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
          norm_num
        have h4 : Real.log 3 ≤ 4 * Real.log (p : ℝ) := by linarith
        have hsq : (2 * Real.sqrt (Real.log (p : ℝ))) ^ 2 = 4 * Real.log (p : ℝ) := by
          rw [mul_pow, Real.sq_sqrt (le_of_lt hlogp)]
          ring
        have h2 : Real.sqrt (Real.log 3) ≤
            Real.sqrt ((2 * Real.sqrt (Real.log (p : ℝ))) ^ 2) :=
          Real.sqrt_le_sqrt (hsq.symm ▸ h4)
        rw [Real.sqrt_sq (by positivity)] at h2
        have hs : 0 ≤ Real.sqrt (Real.log (p : ℝ)) := Real.sqrt_nonneg _
        linarith
      set σ : Fin 3 → Fin p := fun k => ⟨k.val % p, Nat.mod_lt k.val hp⟩ with hσdef
      set V : Ω → Fin 3 → ℝ := fun ω k => U' ω (σ k) with hVdef
      have hVmeas : Measurable V := by
        show Measurable (fun ω : Ω => fun k : Fin 3 => U' ω (σ k))
        rw [measurable_pi_iff]
        intro k
        exact (measurable_pi_apply (σ k)).comp hU'meas
      have hsurj : ∀ j : Fin p, ∃ k : Fin 3, σ k = j := by
        intro j
        refine ⟨⟨j.val, by omega⟩, ?_⟩
        apply Fin.ext
        show j.val % p = j.val
        exact Nat.mod_eq_of_lt j.isLt
      have hsetA : {ω : Ω | ∀ k : Fin 3, V ω k ≤ y (σ k) + a}
          = {ω : Ω | ∀ j : Fin p, U' ω j ≤ y j + a} := by
        have key : {ω : Ω | ∀ k : Fin 3, U' ω (σ k) ≤ y (σ k) + a}
            = {ω : Ω | ∀ j : Fin p, U' ω j ≤ y j + a} := by
          ext ω
          simp only [Set.mem_setOf_eq]
          constructor
          · intro h j
            obtain ⟨k, hk⟩ := hsurj j
            rw [← hk]
            exact h k
          · intro h k
            exact h (σ k)
        exact key
      have hsetB : {ω : Ω | ∀ k : Fin 3, V ω k ≤ y (σ k)}
          = {ω : Ω | ∀ j : Fin p, U' ω j ≤ y j} := by
        have key : {ω : Ω | ∀ k : Fin 3, U' ω (σ k) ≤ y (σ k)}
            = {ω : Ω | ∀ j : Fin p, U' ω j ≤ y j} := by
          ext ω
          simp only [Set.mem_setOf_eq]
          constructor
          · intro h j
            obtain ⟨k, hk⟩ := hsurj j
            rw [← hk]
            exact h k
          · intro h k
            exact h (σ k)
        exact key
      have horth3 : ∀ c : Fin 3 → ℝ, MeasurableSet {z : Fin 3 → ℝ | ∀ k, z k ≤ c k} := by
        intro c
        have h : {z : Fin 3 → ℝ | ∀ k, z k ≤ c k}
            = ⋂ k : Fin 3, {z : Fin 3 → ℝ | z k ≤ c k} := by
          ext z
          simp
        rw [h]
        exact MeasurableSet.iInter fun k => measurableSet_le (measurable_pi_apply k) measurable_const
      have hsetV : ∀ c : Fin 3 → ℝ,
          (Measure.map V P) {z : Fin 3 → ℝ | ∀ k, z k ≤ c k}
            = P {ω | ∀ k : Fin 3, V ω k ≤ c k} := by
        intro c
        rw [Measure.map_apply hVmeas (horth3 c)]
        rfl
      have hprobV : IsProbabilityMeasure (Measure.map V P) :=
        ⟨by rw [Measure.map_apply hVmeas MeasurableSet.univ]; simp⟩
      have hvarV : ∀ k : Fin 3, b ≤ ∫ z : Fin 3 → ℝ, (z k) ^ 2 ∂(Measure.map V P) := by
        intro k
        have h1 : (∫ z : Fin 3 → ℝ, (z k) ^ 2 ∂(Measure.map V P)) = ∫ ω, (V ω k) ^ 2 ∂P :=
          integral_map hVmeas.aemeasurable
            ((measurable_pi_apply k).pow_const 2).aestronglyMeasurable
        rw [h1]
        exact hU'2 (σ k)
      have hsV1 : (Measure.map V P) {z : Fin 3 → ℝ | ∀ k, z k ≤ y (σ k) + a}
          = P {ω | ∀ k : Fin 3, V ω k ≤ y (σ k) + a} := by
        simpa using hsetV (fun k => y (σ k) + a)
      have hsV2 : (Measure.map V P) {z : Fin 3 → ℝ | ∀ k, z k ≤ y (σ k)}
          = P {ω | ∀ k : Fin 3, V ω k ≤ y (σ k)} := by
        simpa using hsetV (fun k => y (σ k))
      let muX' : Fin 3 → ℝ := fun k => muX (σ k)
      let muY' : Fin 3 → ℝ := fun k => muY (σ k)
      let X' : Fin n → Ω → Fin 3 → ℝ := fun i ω k => X i ω (σ k)
      let Y' : Fin m → Ω → Fin 3 → ℝ := fun i ω k => Y i ω (σ k)
      let F' : Fin n → Ω → Fin 3 → ℝ := fun i ω k => F i ω (σ k)
      let G' : Fin m → Ω → Fin 3 → ℝ := fun i ω k => G i ω (σ k)
      have hgmeas : Measurable (fun z : Fin p → ℝ => fun k : Fin 3 => z (σ k)) := by
        rw [measurable_pi_iff]
        intro k
        exact measurable_pi_apply (σ k)
      have hfam : (fun a => (fun z : Fin p → ℝ => fun k : Fin 3 => z (σ k)) ∘ jointFam X Y F G a)
          = jointFam X' Y' F' G' := by
        funext a
        cases a with
        | inl i => rfl
        | inr a =>
          cases a with
          | inl i => rfl
          | inr a =>
            cases a with
            | inl i => rfl
            | inr i => rfl
      have hind' : iIndepFun (β := fun _ => Fin 3 → ℝ) (jointFam X' Y' F' G') P :=
        hfam ▸ hind.comp (fun _ => fun z : Fin p → ℝ => fun k : Fin 3 => z (σ k))
          (fun _ => hgmeas)
      have hFm' : ∀ i : Fin n, Measurable (F' i) := fun i => hgmeas.comp (hFm i)
      have hGm' : ∀ i : Fin m, Measurable (G' i) := fun i => hgmeas.comp (hGm i)
      set A : Matrix (Fin 3) (Fin p) ℝ := fun k j => if σ k = j then (1 : ℝ) else 0 with hAdef
      have hmulvec : ∀ (z : Fin p → ℝ) (k : Fin 3), A.mulVec z k = z (σ k) := by
        intro z k
        show (∑ j : Fin p, (if σ k = j then (1 : ℝ) else 0) * z j) = z (σ k)
        rw [Finset.sum_eq_single (σ k)
          (fun j _ hne => by rw [if_neg (Ne.symm hne), zero_mul])
          (fun h => absurd (Finset.mem_univ _) h)]
        rw [if_pos rfl, one_mul]
      have hmatentry : ∀ (M : Matrix (Fin p) (Fin p) ℝ) (k l : Fin 3),
          (A * M * A.transpose) k l = M (σ k) (σ l) := by
        intro M k l
        show (∑ b : Fin p, (∑ a : Fin p, (if σ k = a then (1 : ℝ) else 0) * M a b)
            * (if σ l = b then (1 : ℝ) else 0)) = M (σ k) (σ l)
        rw [Finset.sum_eq_single (σ l)
          (fun b _ hne => by rw [if_neg (Ne.symm hne), mul_zero])
          (fun h => absurd (Finset.mem_univ _) h)]
        rw [if_pos rfl, mul_one]
        rw [Finset.sum_eq_single (σ k)
          (fun a _ hne => by rw [if_neg (Ne.symm hne), zero_mul])
          (fun h => absurd (Finset.mem_univ _) h)]
        rw [if_pos rfl, one_mul]
      have hGaussF' : ∀ i : Fin n,
          IsCenteredGaussianVector P (fun ω k => F' i ω k - muX' k) (covX P muX' X' i) := by
        intro i
        have hlin := IsCenteredGaussianVector.linearImage P (fun ω j => F i ω j - muX j)
          (covX P muX X i) (hGaussF i) A
        have hfun : (fun ω => A.mulVec (fun j => F i ω j - muX j))
            = (fun ω k => F' i ω k - muX' k) := by
          funext ω k
          rw [hmulvec]
        have hmat : (A * covX P muX X i * A.transpose) = covX P muX' X' i := by
          ext k l
          rw [hmatentry]
          rfl
        rw [hfun, hmat] at hlin
        exact hlin
      have hGaussG' : ∀ i : Fin m,
          IsCenteredGaussianVector P (fun ω k => G' i ω k - muY' k) (covY P muY' Y' i) := by
        intro i
        have hlin := IsCenteredGaussianVector.linearImage P (fun ω j => G i ω j - muY j)
          (covY P muY Y i) (hGaussG i) A
        have hfun : (fun ω => A.mulVec (fun j => G i ω j - muY j))
            = (fun ω k => G' i ω k - muY' k) := by
          funext ω k
          rw [hmulvec]
        have hmat : (A * covY P muY Y i * A.transpose) = covY P muY' Y' i := by
          ext k l
          rw [hmatentry]
          rfl
        rw [hfun, hmat] at hlin
        exact hlin
      have hchild3 :=
        statopia_math_node_1224548605_c698de4a P hn hm (by norm_num : 0 < 3) delta muX' muY'
          X' Y' F' G' hFm' hGm' hind' (fun i k => hMemX i (σ k)) (fun i k => hMemY i (σ k))
          (fun i k => hMeanX i (σ k)) (fun i k => hMeanY i (σ k)) hGaussF' hGaussG'
      have hVeq : (fun ω => fun k : Fin 3 =>
          combVec n m (delta n m) muX' muY' (fun i => F' i ω) (fun i' => G' i' ω) k) = V := rfl
      have hGaussV : IsGaussian (Measure.map V P) := by
        rw [← hVeq]
        exact hchild3.1
      have hmeanV : (∫ z : Fin 3 → ℝ, z ∂(Measure.map V P)) = fun _ => 0 := by
        rw [← hVeq]
        exact hchild3.2
      have hmain3 := hC 3 (by norm_num) (Measure.map V P) hGaussV hmeanV hvarV
        (fun k => y (σ k)) a ha
      simp only [] at hmain3
      rw [hsV1, hsV2, hsetA, hsetB] at hmain3
      refine le_trans hmain3 ?_
      push_cast
      have hCs : (0 : ℝ) ≤ C * a := by positivity
      have hmul := mul_le_mul_of_nonneg_left hB hCs
      linarith
  /- @proof-region region.target-node.session.ac260241f860b4ed end -/

end

end Statlib.Imported

