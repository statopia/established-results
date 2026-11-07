import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_2515832765_1170112b_b9303f12

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
theorem statopia_math_node_955888345_2e654e22 : ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n m p : ℕ) (hn : 0 < n) (hm : 0 < m) (hp : 0 < p)
    (hlogp : 0 < Real.log (p : ℝ))
    (delta : ℕ → ℕ → ℝ) (hdelta : delta n m ≠ 0)
    (muX muY : Fin p → ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
    (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
    (hXm : ∀ i : Fin n, Measurable (X i)) (hYm : ∀ i : Fin m, Measurable (Y i))
    (hFm : ∀ i : Fin n, Measurable (F i)) (hGm : ∀ i : Fin m, Measurable (G i))
    (hindep : iIndepFun (β := fun _ => Fin p → ℝ) (jointFam X Y F G) P)
    (hX2 : ∀ (i : Fin n) (j : Fin p), MemLp (fun ω => X i ω j) 2 P)
    (hY2 : ∀ (i : Fin m) (j : Fin p), MemLp (fun ω => Y i ω j) 2 P)
    (hXint : ∀ (i : Fin n) (j : Fin p), ∫ ω, X i ω j ∂P = muX j)
    (hYint : ∀ (i : Fin m) (j : Fin p), ∫ ω, Y i ω j ∂P = muY j)
    (hFgauss : ∀ i : Fin n,
      IsCenteredGaussianVector P (fun ω j => F i ω j - muX j) (covX P muX X i))
    (hGgauss : ∀ i : Fin m,
      IsCenteredGaussianVector P (fun ω j => G i ω j - muY j) (covY P muY Y i))
    (phi1 phi2 : ℝ) (hphi1 : 1 ≤ phi1) (hphi2 : 1 ≤ phi2)
    (y : Fin p → ℝ) (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (z : Fin p → ℝ),
    |((P.prod P) {x : Ω × Ω | ∀ j : Fin p,
        (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ *
            (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j)
              + Real.sqrt (1 - v) * (F i x.1 j - muX j))
              + Real.sqrt (1 - t) * (F i x.2 j - muX j)))
        + (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m *
            (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j)
              + Real.sqrt (1 - v) * (G i x.1 j - muY j))
              + Real.sqrt (1 - t) * (G i x.2 j - muY j)))
          ≤ z j}).toReal
      - (P {ω : Ω | ∀ j : Fin p,
          combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤ z j}).toReal|
      ≤ rho P n m p (delta n m) muX muY X Y F G := by
  /- @proof-region region.target-node.session.76dcf28129fd0edd begin -/
  intro Ω _ P _ n m p hn hm hp hlogp delta hdelta muX muY X Y F G
    hXm hYm hFm hGm hindep hX2 hY2 hXint hYint hFgauss hGgauss
    phi1 phi2 hphi1 hphi2 y v hv0 hv1 t ht0 ht1 z
  have hZsplit : ∀ (x : Ω × Ω) (j : Fin p),
      (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ *
          (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j)
            + Real.sqrt (1 - v) * (F i x.1 j - muX j))
            + Real.sqrt (1 - t) * (F i x.2 j - muX j)))
      + (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m *
          (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j)
            + Real.sqrt (1 - v) * (G i x.1 j - muY j))
            + Real.sqrt (1 - t) * (G i x.2 j - muY j)))
      = Real.sqrt (t * v) * combVec n m (delta n m) muX muY (fun i => X i x.1) (fun i => Y i x.1) j
        + Real.sqrt (t * (1 - v)) * combVec n m (delta n m) muX muY (fun i => F i x.1) (fun i => G i x.1) j
        + Real.sqrt (1 - t) * combVec n m (delta n m) muX muY (fun i => F i x.2) (fun i => G i x.2) j := by
    intro x j
    have hsqrtN : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := by
      have h := Real.sq_sqrt (Nat.cast_nonneg n)
      rw [sq] at h
      exact h
    have hsqrtN_ne : Real.sqrt (n : ℝ) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hsqrtN
      have hNpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      linarith
    have hkeyN : (Real.sqrt (n : ℝ))⁻¹ * (n : ℝ) = Real.sqrt (n : ℝ) := by
      calc (Real.sqrt (n : ℝ))⁻¹ * (n : ℝ)
          = (Real.sqrt (n : ℝ))⁻¹ * (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by rw [hsqrtN]
        _ = Real.sqrt (n : ℝ) := by rw [← mul_assoc, inv_mul_cancel₀ hsqrtN_ne, one_mul]
    have hsqrtM : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) := by
      have h := Real.sq_sqrt (Nat.cast_nonneg m)
      rw [sq] at h
      exact h
    have hsqrtM_ne : Real.sqrt (m : ℝ) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hsqrtM
      have hMpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      linarith
    have hkeyM : (Real.sqrt (m : ℝ))⁻¹ * (m : ℝ) = Real.sqrt (m : ℝ) := by
      calc (Real.sqrt (m : ℝ))⁻¹ * (m : ℝ)
          = (Real.sqrt (m : ℝ))⁻¹ * (Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ)) := by rw [hsqrtM]
        _ = Real.sqrt (m : ℝ) := by rw [← mul_assoc, inv_mul_cancel₀ hsqrtM_ne, one_mul]
    have hsN : ∀ (A : Fin n → ℝ),
        (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ * (A i - muX j))
          = (Real.sqrt (n : ℝ))⁻¹ * (∑ i : Fin n, A i) - Real.sqrt (n : ℝ) * muX j := by
      intro A
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_sub]
      have h2 : (Real.sqrt (n : ℝ))⁻¹ * ((n : ℝ) * muX j) = Real.sqrt (n : ℝ) * muX j := by
        rw [← mul_assoc, hkeyN]
      rw [h2]
    have hsM : ∀ (B : Fin m → ℝ),
        (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m * (B i - muY j))
          = delta n m * ((Real.sqrt (m : ℝ))⁻¹ * (∑ i : Fin m, B i))
            - delta n m * Real.sqrt (m : ℝ) * muY j := by
      intro B
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_sub]
      have h2 : ((Real.sqrt (m : ℝ))⁻¹ * delta n m) * ((m : ℝ) * muY j)
          = delta n m * Real.sqrt (m : ℝ) * muY j := by
        calc ((Real.sqrt (m : ℝ))⁻¹ * delta n m) * ((m : ℝ) * muY j)
            = delta n m * muY j * ((Real.sqrt (m : ℝ))⁻¹ * (m : ℝ)) := by ring
          _ = delta n m * muY j * Real.sqrt (m : ℝ) := by rw [hkeyM]
          _ = delta n m * Real.sqrt (m : ℝ) * muY j := by ring
      rw [h2]
      ring
    have hX1 : (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ * (X i x.1 j - muX j))
        = (Real.sqrt (n : ℝ))⁻¹ * (∑ i : Fin n, X i x.1 j) - Real.sqrt (n : ℝ) * muX j := by
      simpa using hsN (fun i => X i x.1 j)
    have hF1 : (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ * (F i x.1 j - muX j))
        = (Real.sqrt (n : ℝ))⁻¹ * (∑ i : Fin n, F i x.1 j) - Real.sqrt (n : ℝ) * muX j := by
      simpa using hsN (fun i => F i x.1 j)
    have hF2 : (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ * (F i x.2 j - muX j))
        = (Real.sqrt (n : ℝ))⁻¹ * (∑ i : Fin n, F i x.2 j) - Real.sqrt (n : ℝ) * muX j := by
      simpa using hsN (fun i => F i x.2 j)
    have hY1 : (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m * (Y i x.1 j - muY j))
        = delta n m * ((Real.sqrt (m : ℝ))⁻¹ * (∑ i : Fin m, Y i x.1 j))
          - delta n m * Real.sqrt (m : ℝ) * muY j := by
      simpa using hsM (fun i => Y i x.1 j)
    have hG1 : (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m * (G i x.1 j - muY j))
        = delta n m * ((Real.sqrt (m : ℝ))⁻¹ * (∑ i : Fin m, G i x.1 j))
          - delta n m * Real.sqrt (m : ℝ) * muY j := by
      simpa using hsM (fun i => G i x.1 j)
    have hG2 : (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m * (G i x.2 j - muY j))
        = delta n m * ((Real.sqrt (m : ℝ))⁻¹ * (∑ i : Fin m, G i x.2 j))
          - delta n m * Real.sqrt (m : ℝ) * muY j := by
      simpa using hsM (fun i => G i x.2 j)
    have cX : (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ * (X i x.1 j - muX j))
        + (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m * (Y i x.1 j - muY j))
        = combVec n m (delta n m) muX muY (fun i => X i x.1) (fun i => Y i x.1) j := by
      simp only [combVec, normSum]
      rw [hX1, hY1]
      ring
    have cF : (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ * (F i x.1 j - muX j))
        + (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m * (G i x.1 j - muY j))
        = combVec n m (delta n m) muX muY (fun i => F i x.1) (fun i => G i x.1) j := by
      simp only [combVec, normSum]
      rw [hF1, hG1]
      ring
    have cF2 : (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ * (F i x.2 j - muX j))
        + (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m * (G i x.2 j - muY j))
        = combVec n m (delta n m) muX muY (fun i => F i x.2) (fun i => G i x.2) j := by
      simp only [combVec, normSum]
      rw [hF2, hG2]
      ring
    have hfacA : (∑ i : Fin n, (Real.sqrt t * Real.sqrt v) * ((Real.sqrt (n : ℝ))⁻¹ * (X i x.1 j - muX j)))
        = (Real.sqrt t * Real.sqrt v) * (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ * (X i x.1 j - muX j)) := by
      simp only [Finset.mul_sum]
    have hfacB : (∑ i : Fin n, (Real.sqrt t * Real.sqrt (1 - v)) * ((Real.sqrt (n : ℝ))⁻¹ * (F i x.1 j - muX j)))
        = (Real.sqrt t * Real.sqrt (1 - v)) * (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ * (F i x.1 j - muX j)) := by
      simp only [Finset.mul_sum]
    have hfacC : (∑ i : Fin n, Real.sqrt (1 - t) * ((Real.sqrt (n : ℝ))⁻¹ * (F i x.2 j - muX j)))
        = Real.sqrt (1 - t) * (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ * (F i x.2 j - muX j)) := by
      simp only [Finset.mul_sum]
    have e1 : (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ *
          (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j)
            + Real.sqrt (1 - v) * (F i x.1 j - muX j))
            + Real.sqrt (1 - t) * (F i x.2 j - muX j)))
        = Real.sqrt t * (Real.sqrt v * (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ * (X i x.1 j - muX j))
            + Real.sqrt (1 - v) * (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ * (F i x.1 j - muX j)))
          + Real.sqrt (1 - t) * (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ * (F i x.2 j - muX j)) := by
      rw [show (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ *
          (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j)
            + Real.sqrt (1 - v) * (F i x.1 j - muX j))
            + Real.sqrt (1 - t) * (F i x.2 j - muX j)))
          = ∑ i : Fin n, ((Real.sqrt t * Real.sqrt v) * ((Real.sqrt (n : ℝ))⁻¹ * (X i x.1 j - muX j))
            + (Real.sqrt t * Real.sqrt (1 - v)) * ((Real.sqrt (n : ℝ))⁻¹ * (F i x.1 j - muX j))
            + Real.sqrt (1 - t) * ((Real.sqrt (n : ℝ))⁻¹ * (F i x.2 j - muX j)))
          from Finset.sum_congr rfl (fun i _ => by ring)]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hfacA, hfacB, hfacC]
      ring
    have hfacD : (∑ i : Fin m, (Real.sqrt t * Real.sqrt v) * ((Real.sqrt (m : ℝ))⁻¹ * delta n m * (Y i x.1 j - muY j)))
        = (Real.sqrt t * Real.sqrt v) * (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m * (Y i x.1 j - muY j)) := by
      simp only [Finset.mul_sum]
    have hfacE : (∑ i : Fin m, (Real.sqrt t * Real.sqrt (1 - v)) * ((Real.sqrt (m : ℝ))⁻¹ * delta n m * (G i x.1 j - muY j)))
        = (Real.sqrt t * Real.sqrt (1 - v)) * (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m * (G i x.1 j - muY j)) := by
      simp only [Finset.mul_sum]
    have hfacF : (∑ i : Fin m, Real.sqrt (1 - t) * ((Real.sqrt (m : ℝ))⁻¹ * delta n m * (G i x.2 j - muY j)))
        = Real.sqrt (1 - t) * (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m * (G i x.2 j - muY j)) := by
      simp only [Finset.mul_sum]
    have e2 : (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m *
          (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j)
            + Real.sqrt (1 - v) * (G i x.1 j - muY j))
            + Real.sqrt (1 - t) * (G i x.2 j - muY j)))
        = Real.sqrt t * (Real.sqrt v * (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m * (Y i x.1 j - muY j))
            + Real.sqrt (1 - v) * (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m * (G i x.1 j - muY j)))
          + Real.sqrt (1 - t) * (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m * (G i x.2 j - muY j)) := by
      rw [show (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m *
          (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j)
            + Real.sqrt (1 - v) * (G i x.1 j - muY j))
            + Real.sqrt (1 - t) * (G i x.2 j - muY j)))
          = ∑ i : Fin m, ((Real.sqrt t * Real.sqrt v) * ((Real.sqrt (m : ℝ))⁻¹ * delta n m * (Y i x.1 j - muY j))
            + (Real.sqrt t * Real.sqrt (1 - v)) * ((Real.sqrt (m : ℝ))⁻¹ * delta n m * (G i x.1 j - muY j))
            + Real.sqrt (1 - t) * ((Real.sqrt (m : ℝ))⁻¹ * delta n m * (G i x.2 j - muY j)))
          from Finset.sum_congr rfl (fun i _ => by ring)]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hfacD, hfacE, hfacF]
      ring
    rw [Real.sqrt_mul ht0 v, Real.sqrt_mul ht0 (1 - v)]
    rw [e1, e2, ← cX, ← cF, ← cF2]
    ring
  have hset : {x : Ω × Ω | ∀ j : Fin p,
        (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ *
            (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j)
              + Real.sqrt (1 - v) * (F i x.1 j - muX j))
              + Real.sqrt (1 - t) * (F i x.2 j - muX j)))
        + (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m *
            (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j)
              + Real.sqrt (1 - v) * (G i x.1 j - muY j))
              + Real.sqrt (1 - t) * (G i x.2 j - muY j)))
          ≤ z j}
      = {x : Ω × Ω | ∀ j : Fin p,
        Real.sqrt (t * v) * combVec n m (delta n m) muX muY (fun i => X i x.1) (fun i => Y i x.1) j
      + Real.sqrt (t * (1 - v)) * combVec n m (delta n m) muX muY (fun i => F i x.1) (fun i => G i x.1) j
      + Real.sqrt (1 - t) * combVec n m (delta n m) muX muY (fun i => F i x.2) (fun i => G i x.2) j
        ≤ z j} := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h j
      rw [← hZsplit x j]
      exact h j
    · intro h j
      rw [hZsplit x j]
      exact h j
  rw [hset]
  have hlaw := statopia_math_node_2515832765_1170112b Ω P n m p delta muX muY X Y F G
    hn hm hp hXm hYm hFm hGm hindep hX2 hY2 hXint hYint hFgauss hGgauss v t hv0 hv1 ht0 ht1 z
  rw [hlaw]
  let A2 : Set.Icc (0 : ℝ) 1 → (Fin p → ℝ) → Set Ω := fun v' y' => {ω : Ω | ∀ j : Fin p,
      Real.sqrt (v' : ℝ) * combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j
    + Real.sqrt (1 - (v' : ℝ)) * combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j
      ≤ y' j}
  let B : (Fin p → ℝ) → Set Ω := fun y' => {ω : Ω | ∀ j : Fin p,
      combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤ y' j}
  let v0 : Set.Icc (0 : ℝ) 1 := ⟨t * v, by nlinarith, by nlinarith⟩
  let A : (Fin p → ℝ) → Set Ω := A2 v0
  have habs1 : ∀ (s s' : Set Ω), |(P s).toReal - (P s').toReal| ≤ 1 := by
    have hb : ∀ t' : Set Ω, (P t').toReal ≤ 1 := by
      intro t'
      have hle : P t' ≤ (1 : ℝ≥0∞) := by
        have h := measure_mono (Set.subset_univ t') (μ := P)
        simpa using h
      simpa using ENNReal.toReal_le_of_le_ofReal (by norm_num : (0 : ℝ) ≤ 1) (by simpa using hle)
    intro s s'
    have h1 := hb s
    have h1' := hb s'
    have h2 : (0 : ℝ) ≤ (P s).toReal := ENNReal.toReal_nonneg
    have h2' : (0 : ℝ) ≤ (P s').toReal := ENNReal.toReal_nonneg
    rw [abs_le]
    constructor <;> linarith
  have hb1 : ∀ (S T : (Fin p → ℝ) → Set Ω),
      BddAbove (Set.range fun y' : Fin p → ℝ =>
        |(P (S y')).toReal - (P (T y')).toReal|) := by
    intro S T
    refine ⟨1, ?_⟩
    rintro _ ⟨y', rfl⟩
    exact habs1 (S y') (T y')
  have hb2 : ∀ (S : Set.Icc (0 : ℝ) 1 → (Fin p → ℝ) → Set Ω) (T : (Fin p → ℝ) → Set Ω),
      BddAbove (Set.range fun v' : Set.Icc (0 : ℝ) 1 =>
        ⨆ y' : Fin p → ℝ, |(P (S v' y')).toReal - (P (T y')).toReal|) := by
    intro S T
    refine ⟨1, ?_⟩
    rintro _ ⟨v', rfl⟩
    exact ciSup_le (fun y' => habs1 (S v' y') (T y'))
  have key : |(P (A z)).toReal - (P (B z)).toReal|
      ≤ rho P n m p (delta n m) muX muY X Y F G := by
    show |(P (A z)).toReal - (P (B z)).toReal|
      ≤ ⨆ v' : Set.Icc (0 : ℝ) 1, ⨆ y' : Fin p → ℝ,
        |(P (A2 v' y')).toReal - (P (B y')).toReal|
    refine le_trans (le_ciSup
      (f := fun y' : Fin p → ℝ => |(P (A y')).toReal - (P (B y')).toReal|) (hb1 A B) z) ?_
    exact le_ciSup
      (f := fun v' : Set.Icc (0 : ℝ) 1 =>
        ⨆ y' : Fin p → ℝ, |(P (A2 v' y')).toReal - (P (B y')).toReal|) (hb2 A2 B) v0
  exact key
  /- @proof-region region.target-node.session.76dcf28129fd0edd end -/

end

end Statlib.Imported

