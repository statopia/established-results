import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_2276987974_31808913_1237aaa0

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
theorem statopia_math_node_384110174_b4277f3b : ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
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
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (y : Fin p → ℝ) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1),
    (let Z : Ω × Ω → Fin p → ℝ := fun x j =>
        (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ *
            (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)) +
              Real.sqrt (1 - t) * (F i x.2 j - muX j)))
          + (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m *
            (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j)) +
              Real.sqrt (1 - t) * (G i x.2 j - muY j)))
     ∀ c : ℝ,
       |((P.prod P) {x : Ω × Ω | (⨆ j : Fin p, (Z x j - y j)) ≤ c}).toReal
         - (P {ω : Ω | (⨆ j : Fin p,
              (combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j - y j)) ≤ c}).toReal|
         ≤ rho P n m p (delta n m) muX muY X Y F G) := by
  /- @proof-region region.target-node.session.4b4a2f8572233fda begin -/
  intro Ω _ P _ n m p delta muX muY X Y F G hn hm hp hX hY hF hG hindep hFcov hGcov v hv0 hv1 y t ht0 ht1 Z c
  have hZdef : Z = fun x j =>
      (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ *
          (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)) +
            Real.sqrt (1 - t) * (F i x.2 j - muX j)))
        + (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m *
          (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j)) +
            Real.sqrt (1 - t) * (G i x.2 j - muY j))) := rfl
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hnsq : Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ) = (n:ℝ) := Real.mul_self_sqrt hnR.le
  have hmsq : Real.sqrt (m:ℝ) * Real.sqrt (m:ℝ) = (m:ℝ) := Real.mul_self_sqrt hmR.le
  have hsn0 : Real.sqrt (n:ℝ) ≠ 0 := by
    intro h0
    have h : Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ) = 0 := by rw [h0, mul_zero]
    rw [hnsq] at h
    linarith
  have hsm0 : Real.sqrt (m:ℝ) ≠ 0 := by
    intro h0
    have h : Real.sqrt (m:ℝ) * Real.sqrt (m:ℝ) = 0 := by rw [h0, mul_zero]
    rw [hmsq] at h
    linarith
  have hnsmul : (n:ℝ) * (Real.sqrt (n:ℝ))⁻¹ = Real.sqrt (n:ℝ) := by
    nth_rewrite 1 [← hnsq]
    rw [mul_assoc, mul_inv_cancel₀ hsn0, mul_one]
  have hmsmul : (m:ℝ) * (Real.sqrt (m:ℝ))⁻¹ = Real.sqrt (m:ℝ) := by
    nth_rewrite 1 [← hmsq]
    rw [mul_assoc, mul_inv_cancel₀ hsm0, mul_one]
  have hsum_n : ∀ (g : Fin n → ℝ) (c : ℝ),
      (∑ i : Fin n, (Real.sqrt (n:ℝ))⁻¹ * (g i - c))
        = (Real.sqrt (n:ℝ))⁻¹ * (∑ i : Fin n, g i) - Real.sqrt (n:ℝ) * c := by
    intro g c
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum, ← mul_assoc, hnsmul]
  have hsum_m : ∀ (g : Fin m → ℝ) (c : ℝ),
      (∑ i : Fin m, (Real.sqrt (m:ℝ))⁻¹ * (g i - c))
        = (Real.sqrt (m:ℝ))⁻¹ * (∑ i : Fin m, g i) - Real.sqrt (m:ℝ) * c := by
    intro g c
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum, ← mul_assoc, hmsmul]
  have hZeq : ∀ (x : Ω × Ω) (j : Fin p),
      Z x j = Real.sqrt (t * v) * combVec n m (delta n m) muX muY (fun i => X i x.1) (fun i => Y i x.1) j
        + Real.sqrt (t * (1 - v)) * combVec n m (delta n m) muX muY (fun i => F i x.1) (fun i => G i x.1) j
        + Real.sqrt (1 - t) * combVec n m (delta n m) muX muY (fun i => F i x.2) (fun i => G i x.2) j := by
    intro x j
    simp only [hZdef]
    have hX' : (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ * (X i x.1 j - muX j))
        = (Real.sqrt (n : ℝ))⁻¹ * (∑ i : Fin n, X i x.1 j) - Real.sqrt (n : ℝ) * muX j :=
      hsum_n (fun i => X i x.1 j) (muX j)
    have hF1 : (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ * (F i x.1 j - muX j))
        = (Real.sqrt (n : ℝ))⁻¹ * (∑ i : Fin n, F i x.1 j) - Real.sqrt (n : ℝ) * muX j :=
      hsum_n (fun i => F i x.1 j) (muX j)
    have hF2 : (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ * (F i x.2 j - muX j))
        = (Real.sqrt (n : ℝ))⁻¹ * (∑ i : Fin n, F i x.2 j) - Real.sqrt (n : ℝ) * muX j :=
      hsum_n (fun i => F i x.2 j) (muX j)
    have hp1 : (∑ i : Fin n, Real.sqrt t * Real.sqrt v * ((Real.sqrt (n : ℝ))⁻¹ * (X i x.1 j - muX j)))
        = Real.sqrt t * Real.sqrt v * (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ * (X i x.1 j - muX j)) := by
      rw [Finset.mul_sum]
    have hp2 : (∑ i : Fin n, Real.sqrt t * Real.sqrt (1 - v) * ((Real.sqrt (n : ℝ))⁻¹ * (F i x.1 j - muX j)))
        = Real.sqrt t * Real.sqrt (1 - v) * (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ * (F i x.1 j - muX j)) := by
      rw [Finset.mul_sum]
    have hp3 : (∑ i : Fin n, Real.sqrt (1 - t) * ((Real.sqrt (n : ℝ))⁻¹ * (F i x.2 j - muX j)))
        = Real.sqrt (1 - t) * (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ * (F i x.2 j - muX j)) := by
      rw [Finset.mul_sum]
    have hN : (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ *
          (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)) +
            Real.sqrt (1 - t) * (F i x.2 j - muX j)))
        = Real.sqrt t * Real.sqrt v *
              ((Real.sqrt (n : ℝ))⁻¹ * (∑ i : Fin n, X i x.1 j) - Real.sqrt (n : ℝ) * muX j)
          + Real.sqrt t * Real.sqrt (1 - v) *
              ((Real.sqrt (n : ℝ))⁻¹ * (∑ i : Fin n, F i x.1 j) - Real.sqrt (n : ℝ) * muX j)
          + Real.sqrt (1 - t) *
              ((Real.sqrt (n : ℝ))⁻¹ * (∑ i : Fin n, F i x.2 j) - Real.sqrt (n : ℝ) * muX j) := by
      have hdist : (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ *
            (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)) +
              Real.sqrt (1 - t) * (F i x.2 j - muX j)))
          = ∑ i : Fin n, (Real.sqrt t * Real.sqrt v * ((Real.sqrt (n : ℝ))⁻¹ * (X i x.1 j - muX j))
              + Real.sqrt t * Real.sqrt (1 - v) * ((Real.sqrt (n : ℝ))⁻¹ * (F i x.1 j - muX j))
              + Real.sqrt (1 - t) * ((Real.sqrt (n : ℝ))⁻¹ * (F i x.2 j - muX j))) :=
        Finset.sum_congr rfl (fun i _ => by ring)
      rw [hdist, Finset.sum_add_distrib, Finset.sum_add_distrib, hp1, hp2, hp3, hX', hF1, hF2]
    have hY' : (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * (Y i x.1 j - muY j))
        = (Real.sqrt (m : ℝ))⁻¹ * (∑ i : Fin m, Y i x.1 j) - Real.sqrt (m : ℝ) * muY j :=
      hsum_m (fun i => Y i x.1 j) (muY j)
    have hG1 : (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * (G i x.1 j - muY j))
        = (Real.sqrt (m : ℝ))⁻¹ * (∑ i : Fin m, G i x.1 j) - Real.sqrt (m : ℝ) * muY j :=
      hsum_m (fun i => G i x.1 j) (muY j)
    have hG2 : (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * (G i x.2 j - muY j))
        = (Real.sqrt (m : ℝ))⁻¹ * (∑ i : Fin m, G i x.2 j) - Real.sqrt (m : ℝ) * muY j :=
      hsum_m (fun i => G i x.2 j) (muY j)
    have hq1 : (∑ i : Fin m, Real.sqrt t * Real.sqrt v * delta n m *
          ((Real.sqrt (m : ℝ))⁻¹ * (Y i x.1 j - muY j)))
        = Real.sqrt t * Real.sqrt v * delta n m *
          (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * (Y i x.1 j - muY j)) := by
      rw [Finset.mul_sum]
    have hq2 : (∑ i : Fin m, Real.sqrt t * Real.sqrt (1 - v) * delta n m *
          ((Real.sqrt (m : ℝ))⁻¹ * (G i x.1 j - muY j)))
        = Real.sqrt t * Real.sqrt (1 - v) * delta n m *
          (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * (G i x.1 j - muY j)) := by
      rw [Finset.mul_sum]
    have hq3 : (∑ i : Fin m, Real.sqrt (1 - t) * delta n m *
          ((Real.sqrt (m : ℝ))⁻¹ * (G i x.2 j - muY j)))
        = Real.sqrt (1 - t) * delta n m *
          (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * (G i x.2 j - muY j)) := by
      rw [Finset.mul_sum]
    have hM : (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m *
          (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j)) +
            Real.sqrt (1 - t) * (G i x.2 j - muY j)))
        = Real.sqrt t * Real.sqrt v * delta n m *
              ((Real.sqrt (m : ℝ))⁻¹ * (∑ i : Fin m, Y i x.1 j) - Real.sqrt (m : ℝ) * muY j)
          + Real.sqrt t * Real.sqrt (1 - v) * delta n m *
              ((Real.sqrt (m : ℝ))⁻¹ * (∑ i : Fin m, G i x.1 j) - Real.sqrt (m : ℝ) * muY j)
          + Real.sqrt (1 - t) * delta n m *
              ((Real.sqrt (m : ℝ))⁻¹ * (∑ i : Fin m, G i x.2 j) - Real.sqrt (m : ℝ) * muY j) := by
      have hdist : (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m *
            (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j)) +
              Real.sqrt (1 - t) * (G i x.2 j - muY j)))
          = ∑ i : Fin m, (Real.sqrt t * Real.sqrt v * delta n m *
                ((Real.sqrt (m : ℝ))⁻¹ * (Y i x.1 j - muY j))
              + Real.sqrt t * Real.sqrt (1 - v) * delta n m *
                ((Real.sqrt (m : ℝ))⁻¹ * (G i x.1 j - muY j))
              + Real.sqrt (1 - t) * delta n m * ((Real.sqrt (m : ℝ))⁻¹ * (G i x.2 j - muY j))) :=
        Finset.sum_congr rfl (fun i _ => by ring)
      rw [hdist, Finset.sum_add_distrib, Finset.sum_add_distrib, hq1, hq2, hq3, hY', hG1, hG2]
    rw [hN, hM]
    simp only [combVec, normSum]
    rw [Real.sqrt_mul ht0.le v, Real.sqrt_mul ht0.le (1 - v)]
    ring
  have hlaw :=
    statopia_math_node_2276987974_31808913 Ω P n m p delta muX muY X Y F G hn hm hp
      hX hY hF hG hindep hFcov hGcov v hv0 hv1 t ht0 ht1
  have hSU : ∀ (u : Fin p → ℝ), ((⨆ j : Fin p, (u j - y j)) ≤ c) ↔ ∀ j : Fin p, u j ≤ y j + c := by
    haveI : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
    intro u
    have hb : BddAbove (Set.range (fun j : Fin p => u j - y j)) :=
      Set.Finite.bddAbove (Set.finite_range (fun j : Fin p => u j - y j))
    rw [ciSup_le_iff hb]
    exact ⟨fun h j => by linarith [h j], fun h j => by linarith [h j]⟩
  have hsum_meas_n : ∀ (g : Fin n → Ω → ℝ),
      (∀ i, Measurable (g i)) → Measurable (fun ω : Ω => ∑ i : Fin n, g i ω) := by
    intro g hg
    exact Finset.measurable_sum Finset.univ (fun i _ => hg i)
  have hsum_meas_m : ∀ (g : Fin m → Ω → ℝ),
      (∀ i, Measurable (g i)) → Measurable (fun ω : Ω => ∑ i : Fin m, g i ω) := by
    intro g hg
    exact Finset.measurable_sum Finset.univ (fun i _ => hg i)
  have hcomb_meas : ∀ (Z : Fin n → Ω → Fin p → ℝ) (W : Fin m → Ω → Fin p → ℝ),
      (∀ i, Measurable (Z i)) → (∀ i, Measurable (W i)) →
      Measurable (fun ω : Ω => fun j : Fin p =>
        combVec n m (delta n m) muX muY (fun i => Z i ω) (fun i => W i ω) j) := by
    intro Z W hZ hW
    rw [measurable_pi_iff]
    intro j
    have a : Measurable (fun ω : Ω => (Real.sqrt (n : ℝ))⁻¹ * (∑ i : Fin n, Z i ω j)) :=
      measurable_const.mul (hsum_meas_n (fun i ω => Z i ω j)
        (fun i => (measurable_pi_apply j).comp (hZ i)))
    have b : Measurable (fun ω : Ω =>
        delta n m * ((Real.sqrt (m : ℝ))⁻¹ * (∑ i : Fin m, W i ω j))) :=
      measurable_const.mul (measurable_const.mul (hsum_meas_m (fun i ω => W i ω j)
        (fun i => (measurable_pi_apply j).comp (hW i))))
    have c1 : Measurable (fun _ : Ω => Real.sqrt (n : ℝ) * muX j) := measurable_const
    have c2 : Measurable (fun _ : Ω => delta n m * Real.sqrt (m : ℝ) * muY j) := measurable_const
    have hfin : Measurable (fun ω : Ω => (Real.sqrt (n : ℝ))⁻¹ * (∑ i : Fin n, Z i ω j)
        - Real.sqrt (n : ℝ) * muX j + delta n m * ((Real.sqrt (m : ℝ))⁻¹ * (∑ i : Fin m, W i ω j))
        - delta n m * Real.sqrt (m : ℝ) * muY j) := ((a.sub c1).add b).sub c2
    simpa only [combVec, normSum] using hfin
  have hmeasA : Measurable (fun ω : Ω => fun j : Fin p =>
      combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j) :=
    hcomb_meas X Y hX hY
  have hmeasB : Measurable (fun ω : Ω => fun j : Fin p =>
      combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j) :=
    hcomb_meas F G hF hG
  have hmeasG : Measurable (fun ω : Ω => fun j : Fin p =>
      Real.sqrt (t * v) * combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j
        + Real.sqrt (1 - t * v) * combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j) := by
    rw [measurable_pi_iff]
    intro j
    have h1 := (measurable_pi_apply j).comp hmeasA
    have h2 := (measurable_pi_apply j).comp hmeasB
    exact (measurable_const.mul h1).add (measurable_const.mul h2)
  have hmeasF : Measurable (fun x : Ω × Ω => fun j : Fin p =>
      Real.sqrt (t * v) * combVec n m (delta n m) muX muY (fun i => X i x.1) (fun i => Y i x.1) j
        + Real.sqrt (t * (1 - v)) * combVec n m (delta n m) muX muY (fun i => F i x.1) (fun i => G i x.1) j
        + Real.sqrt (1 - t) * combVec n m (delta n m) muX muY (fun i => F i x.2) (fun i => G i x.2) j) := by
    rw [measurable_pi_iff]
    intro j
    have h1 : Measurable (fun x : Ω × Ω =>
        combVec n m (delta n m) muX muY (fun i => X i x.1) (fun i => Y i x.1) j) :=
      (measurable_pi_apply j).comp (hmeasA.comp measurable_fst)
    have h2 : Measurable (fun x : Ω × Ω =>
        combVec n m (delta n m) muX muY (fun i => F i x.1) (fun i => G i x.1) j) :=
      (measurable_pi_apply j).comp (hmeasB.comp measurable_fst)
    have h3 : Measurable (fun x : Ω × Ω =>
        combVec n m (delta n m) muX muY (fun i => F i x.2) (fun i => G i x.2) j) :=
      (measurable_pi_apply j).comp (hmeasB.comp measurable_snd)
    exact ((measurable_const.mul h1).add (measurable_const.mul h2)).add (measurable_const.mul h3)
  have hsetU : MeasurableSet {u : Fin p → ℝ | ∀ j : Fin p, u j ≤ y j + c} := by
    have hme : ∀ j : Fin p, MeasurableSet {u : Fin p → ℝ | u j ≤ y j + c} :=
      fun j => measurableSet_le (measurable_pi_apply j) measurable_const
    have h : {u : Fin p → ℝ | ∀ j : Fin p, u j ≤ y j + c}
        = ⋂ j : Fin p, {u : Fin p → ℝ | u j ≤ y j + c} := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [h]
    exact MeasurableSet.iInter hme
  have hSetA : {x : Ω × Ω | (⨆ j : Fin p, (Z x j - y j)) ≤ c}
      = {x : Ω × Ω | ∀ j : Fin p,
          Real.sqrt (t * v) * combVec n m (delta n m) muX muY (fun i => X i x.1) (fun i => Y i x.1) j
            + Real.sqrt (t * (1 - v)) * combVec n m (delta n m) muX muY (fun i => F i x.1) (fun i => G i x.1) j
            + Real.sqrt (1 - t) * combVec n m (delta n m) muX muY (fun i => F i x.2) (fun i => G i x.2) j ≤ y j + c} := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h j
      have h' : ∀ j : Fin p, Z x j ≤ y j + c := (hSU (fun j => Z x j)).1 h
      simpa only [hZeq x j] using h' j
    · intro h
      refine (hSU (fun j => Z x j)).2 (fun j => ?_)
      simpa only [hZeq x j] using h j
  have hSetB : {ω : Ω | (⨆ j : Fin p,
        (combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j - y j)) ≤ c}
      = {ω : Ω | ∀ j : Fin p,
          combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤ y j + c} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    exact hSU (fun j => combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j)
  have hmapF : (P.prod P) {x : Ω × Ω | ∀ j : Fin p,
          Real.sqrt (t * v) * combVec n m (delta n m) muX muY (fun i => X i x.1) (fun i => Y i x.1) j
            + Real.sqrt (t * (1 - v)) * combVec n m (delta n m) muX muY (fun i => F i x.1) (fun i => G i x.1) j
            + Real.sqrt (1 - t) * combVec n m (delta n m) muX muY (fun i => F i x.2) (fun i => G i x.2) j ≤ y j + c}
      = (Measure.map (fun x : Ω × Ω => fun j : Fin p =>
          Real.sqrt (t * v) * combVec n m (delta n m) muX muY (fun i => X i x.1) (fun i => Y i x.1) j
            + Real.sqrt (t * (1 - v)) * combVec n m (delta n m) muX muY (fun i => F i x.1) (fun i => G i x.1) j
            + Real.sqrt (1 - t) * combVec n m (delta n m) muX muY (fun i => F i x.2) (fun i => G i x.2) j) (P.prod P))
        {u : Fin p → ℝ | ∀ j : Fin p, u j ≤ y j + c} := by
    rw [Measure.map_apply hmeasF hsetU]
    rfl
  have hmapG : (Measure.map (fun ω : Ω => fun j : Fin p =>
        Real.sqrt (t * v) * combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j
          + Real.sqrt (1 - t * v) * combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j) P)
        {u : Fin p → ℝ | ∀ j : Fin p, u j ≤ y j + c}
      = P {ω : Ω | ∀ j : Fin p,
          Real.sqrt (t * v) * combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j
            + Real.sqrt (1 - t * v) * combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤ y j + c} := by
    rw [Measure.map_apply hmeasG hsetU]
    rfl
  have hstep : (P.prod P) {x : Ω × Ω | ∀ j : Fin p,
          Real.sqrt (t * v) * combVec n m (delta n m) muX muY (fun i => X i x.1) (fun i => Y i x.1) j
            + Real.sqrt (t * (1 - v)) * combVec n m (delta n m) muX muY (fun i => F i x.1) (fun i => G i x.1) j
            + Real.sqrt (1 - t) * combVec n m (delta n m) muX muY (fun i => F i x.2) (fun i => G i x.2) j ≤ y j + c}
      = P {ω : Ω | ∀ j : Fin p,
          Real.sqrt (t * v) * combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j
            + Real.sqrt (1 - t * v) * combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤ y j + c} := by
    rw [hmapF, hlaw, hmapG]
  rw [hSetA, hSetB, hstep]
  haveI : Nonempty (Set.Icc (0:ℝ) 1) := ⟨⟨0, by constructor <;> norm_num⟩⟩
  have hPle1 : ∀ (S : Set Ω), (P S).toReal ≤ 1 := by
    intro S
    have h2 : P S ≤ 1 := by
      have h3 : P S ≤ P Set.univ := measure_mono (Set.subset_univ S)
      simpa using h3
    calc (P S).toReal ≤ (1 : ℝ≥0∞).toReal := ENNReal.toReal_mono ENNReal.one_ne_top h2
      _ = 1 := ENNReal.toReal_one
  have hbound2 : ∀ (S1 S2 : Set Ω), |(P S1).toReal - (P S2).toReal| ≤ 1 := by
    intro S1 S2
    have h1 := hPle1 S1
    have h2 := hPle1 S2
    have h3 : (0:ℝ) ≤ (P S1).toReal := ENNReal.toReal_nonneg
    have h4 : (0:ℝ) ≤ (P S2).toReal := ENNReal.toReal_nonneg
    rw [abs_sub_le_iff]
    constructor <;> linarith
  have hbddInner : ∀ v' : Set.Icc (0:ℝ) 1, BddAbove (Set.range (fun y' : Fin p → ℝ =>
      |(P {ω : Ω | ∀ j : Fin p,
            Real.sqrt (v' : ℝ) * combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j
          + Real.sqrt (1 - (v' : ℝ)) * combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤ y' j}).toReal
        - (P {ω : Ω | ∀ j : Fin p,
            combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤ y' j}).toReal|)) :=
    fun v' => ⟨1, by rintro _ ⟨y', rfl⟩; exact hbound2 _ _⟩
  have hbddOuter : BddAbove (Set.range (fun v' : Set.Icc (0:ℝ) 1 => ⨆ y' : Fin p → ℝ,
      |(P {ω : Ω | ∀ j : Fin p,
            Real.sqrt (v' : ℝ) * combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j
          + Real.sqrt (1 - (v' : ℝ)) * combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤ y' j}).toReal
        - (P {ω : Ω | ∀ j : Fin p,
            combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤ y' j}).toReal|)) :=
    ⟨1, by rintro _ ⟨v', rfl⟩; exact (ciSup_le_iff (hbddInner v')).2 (fun y' => hbound2 _ _)⟩
  have hv' : t * v ∈ Set.Icc (0:ℝ) 1 :=
    ⟨mul_nonneg ht0.le hv0,
      by nlinarith [mul_nonneg ht0.le (sub_nonneg.2 hv1), sub_nonneg.2 ht1.le]⟩
  refine le_trans (le_ciSup (hbddInner ⟨t * v, hv'⟩) (fun j => y j + c)) ?_
  exact le_ciSup hbddOuter ⟨t * v, hv'⟩
  /- @proof-region region.target-node.session.4b4a2f8572233fda end -/

end

end Statlib.Imported

