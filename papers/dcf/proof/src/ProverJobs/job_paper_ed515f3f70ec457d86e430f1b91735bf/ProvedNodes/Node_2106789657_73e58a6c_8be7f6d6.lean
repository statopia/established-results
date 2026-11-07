import Statlib.HypothesisTesting.Nonparametric.MannWhitney
import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_2194576110_d2ad0cef_60d45604
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_2515832765_1170112b_b9303f12
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_2786644146_fbc979c9_265f0517
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_4002104850_4380db1f_47e2833e

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
theorem statopia_math_node_2106789657_73e58a6c : ∀ (b : ℝ) (hb : 0 < b),
    ∃ Cb : ℝ, 0 < Cb ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (n m p : ℕ) (delta : ℕ → ℕ → ℝ), delta n m = 0 →
        ∀ (muX muY : Fin p → ℝ)
          (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
          (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
          (phi1 phi2 : ℝ),
          0 < n → 0 < m → 0 < p → 0 < Real.log (p : ℝ) →
          (∀ i : Fin n, Measurable (X i)) → (∀ i : Fin m, Measurable (Y i)) →
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
          1 ≤ phi1 → 1 ≤ phi2 →
          ∀ (v : ℝ), 0 ≤ v → v ≤ 1 → ∀ (y : Fin p → ℝ),
          (let phi : ℝ := min phi1 phi2
           let beta : ℝ := phi * Real.log (p : ℝ)
           let kappa0 : ℝ := phi⁻¹ + 2 * beta⁻¹
           let Zstar : ℝ → Ω × Ω → Fin n → Fin p → ℝ := fun t x i j =>
             (Real.sqrt (n : ℝ))⁻¹ *
               (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) +
                   Real.sqrt (1 - v) * (F i x.1 j - muX j)) +
                 Real.sqrt (1 - t) * (F i x.2 j - muX j))
           let Zstarstar : ℝ → Ω × Ω → Fin m → Fin p → ℝ := fun t x i j =>
             (Real.sqrt (m : ℝ))⁻¹ * delta n m *
               (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) +
                   Real.sqrt (1 - v) * (G i x.1 j - muY j)) +
                 Real.sqrt (1 - t) * (G i x.2 j - muY j))
           let Z : ℝ → Ω × Ω → Fin p → ℝ := fun t x j =>
             (∑ i : Fin n, Zstar t x i j) + (∑ i : Fin m, Zstarstar t x i j)
           let h : (Fin p → ℝ) → ℝ := fun w =>
             Set.indicator {w' : Fin p → ℝ |
                 -phi⁻¹ - 2 * beta⁻¹ < (⨆ j : Fin p, (w' j - y j)) ∧
                   (⨆ j : Fin p, (w' j - y j)) ≤ phi⁻¹ + 2 * beta⁻¹}
               (fun _ => (1 : ℝ)) w
           let U' : Ω → Fin p → ℝ := fun ω j =>
             combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j
           let PrPlus : ℝ := (P {ω | ∀ j : Fin p, U' ω j ≤ y j + kappa0}).toReal
           let PrMinus : ℝ := (P {ω | ∀ j : Fin p, U' ω j ≤ y j - kappa0}).toReal
           kappa0 ≤ (1 + 2 / Real.log 2) * phi⁻¹ ∧
             (∀ w : Fin p → ℝ,
               Set.indicator {w' : Fin p → ℝ |
                   -phi⁻¹ ≤ (⨆ j : Fin p, (w' j - y j)) ∧
                     (⨆ j : Fin p, (w' j - y j)) ≤ phi⁻¹}
                 (fun _ => (1 : ℝ)) w ≤ h w) ∧
             (∀ t ∈ Set.Icc (0 : ℝ) 1,
               (∫ x, h (Z t x) ∂(P.prod P)) ≤
                   2 * rho P n m p (delta n m) muX muY X Y F G + (PrPlus - PrMinus) ∧
                 2 * rho P n m p (delta n m) muX muY X Y F G + (PrPlus - PrMinus) ≤
                   2 * rho P n m p (delta n m) muX muY X Y F G +
                     Cb * kappa0 * Real.sqrt (Real.log (p : ℝ))) ∧
             (∀ t ∈ Set.Icc (0 : ℝ) 1,
               (∫ x, h (Z t x) ∂(P.prod P)) ≤
                 2 * rho P n m p (delta n m) muX muY X Y F G +
                   Cb * (1 + 2 / Real.log 2) * phi⁻¹ * Real.sqrt (Real.log (p : ℝ)))) := by
  /- @proof-region region.target-node.session.3e4b9508300980a2 begin -/
  intro b hb
  obtain ⟨Cb, hCbpos, hCb⟩ := statopia_math_node_2786644146_fbc979c9 b hb
  refine ⟨2 * Cb, by linarith, ?_⟩
  intro Ω _ P _ n m p delta hdelta muX muY X Y F G phi1 phi2
    hn hm hp hlogp hXm hYm hFm hGm hindep hMemX hMemY hmuX hmuY hGaussF hGaussG hInt hb_lb
    hphi1 hphi2 v hv0 hv1 y
  obtain ⟨-, hnode1⟩ := hCb Ω P n m p hn hm hp hlogp delta hdelta muX muY X Y F G
    hFm hGm hindep hMemX hMemY hmuX hmuY hGaussF hGaussG hInt hb_lb
  have hphi_ge : 1 ≤ min phi1 phi2 := le_min hphi1 hphi2
  have hphi_pos : 0 < min phi1 phi2 := lt_of_lt_of_le zero_lt_one hphi_ge
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp2 : 2 ≤ p := by
    rcases Nat.lt_or_ge p 2 with hlt | hge
    · have hp1 : p = 1 := by omega
      rw [hp1] at hlogp
      simp at hlogp
    · exact hge
  have hle_log : Real.log 2 ≤ Real.log (p : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hp2)
  have hinvbeta_pos : 0 < ((min phi1 phi2) * Real.log (p : ℝ))⁻¹ :=
    inv_pos.mpr (mul_pos hphi_pos hlogp)
  have hκ0 : (min phi1 phi2)⁻¹ + 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹ ≤
      (1 + 2 / Real.log 2) * (min phi1 phi2)⁻¹ := by
    have hb' : (Real.log (p : ℝ))⁻¹ ≤ (Real.log 2)⁻¹ := by
      have hc : (0 : ℝ) ≤ (Real.log (p : ℝ))⁻¹ * (Real.log 2)⁻¹ :=
        le_of_lt (mul_pos (inv_pos.mpr hlogp) (inv_pos.mpr hlog2))
      have h := mul_le_mul_of_nonneg_left hle_log hc
      have h1 : (Real.log (p : ℝ))⁻¹ * (Real.log 2)⁻¹ * Real.log 2 = (Real.log (p : ℝ))⁻¹ := by
        rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hlog2), mul_one]
      have h2 : (Real.log (p : ℝ))⁻¹ * (Real.log 2)⁻¹ * Real.log (p : ℝ) = (Real.log 2)⁻¹ := by
        rw [mul_assoc, mul_comm (Real.log 2)⁻¹ (Real.log (p : ℝ)), ← mul_assoc,
          inv_mul_cancel₀ (ne_of_gt hlogp), one_mul]
      rwa [h1, h2] at h
    have key : 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹ ≤
        (2 / Real.log 2) * (min phi1 phi2)⁻¹ := by
      rw [mul_inv]
      have hcoef : (0 : ℝ) ≤ 2 * (min phi1 phi2)⁻¹ :=
        mul_nonneg (by norm_num) (le_of_lt (inv_pos.mpr hphi_pos))
      have hmul := mul_le_mul_of_nonneg_left hb' hcoef
      calc 2 * ((min phi1 phi2)⁻¹ * (Real.log (p : ℝ))⁻¹)
          = (2 * (min phi1 phi2)⁻¹) * (Real.log (p : ℝ))⁻¹ := by ring
        _ ≤ (2 * (min phi1 phi2)⁻¹) * (Real.log 2)⁻¹ := hmul
        _ = (2 / Real.log 2) * (min phi1 phi2)⁻¹ := by ring
    have hexp : (1 + 2 / Real.log 2) * (min phi1 phi2)⁻¹
        = (min phi1 phi2)⁻¹ + (2 / Real.log 2) * (min phi1 phi2)⁻¹ := by ring
    rw [hexp]
    linarith [key]
  have hkappa_pos : 0 < (min phi1 phi2)⁻¹ + 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹ := by
    have h1 : 0 < (min phi1 phi2)⁻¹ := inv_pos.mpr hphi_pos
    linarith [hinvbeta_pos, h1]
  have hmain3b : ∀ _t ∈ Set.Icc (0 : ℝ) 1,
      2 * rho P n m p (delta n m) muX muY X Y F G +
          ((P {ω | ∀ j : Fin p, combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤
              y j + ((min phi1 phi2)⁻¹ + 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹)}).toReal -
            (P {ω | ∀ j : Fin p, combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤
              y j - ((min phi1 phi2)⁻¹ + 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹)}).toReal) ≤
        2 * rho P n m p (delta n m) muX muY X Y F G +
          (2 * Cb) * ((min phi1 phi2)⁻¹ + 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹) *
            Real.sqrt (Real.log (p : ℝ)) := by
    intro _ _
    have hplus := hnode1 y ((min phi1 phi2)⁻¹ + 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹)
      hkappa_pos
    have hminus := hnode1
      (fun j : Fin p => y j - ((min phi1 phi2)⁻¹ + 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹))
      ((min phi1 phi2)⁻¹ + 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹) hkappa_pos
    have hset : {ω : Ω | ∀ j : Fin p,
          combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤
            (y j - ((min phi1 phi2)⁻¹ + 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹)) +
              ((min phi1 phi2)⁻¹ + 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹)} =
        {ω : Ω | ∀ j : Fin p,
          combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤ y j} := by
      simp only [sub_add_cancel]
    rw [hset] at hminus
    linarith [hplus, hminus]
  have hmain3 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (∫ x, (fun w => Set.indicator {w' : Fin p → ℝ |
          -(min phi1 phi2)⁻¹ - 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹ <
              (⨆ j : Fin p, (w' j - y j)) ∧
            (⨆ j : Fin p, (w' j - y j)) ≤
              (min phi1 phi2)⁻¹ + 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹}
        (fun _ => (1 : ℝ)) w)

        ((fun (t : ℝ) (x : Ω × Ω) (j : Fin p) =>
            (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ *
              (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) +
                  Real.sqrt (1 - v) * (F i x.1 j - muX j)) +
                Real.sqrt (1 - t) * (F i x.2 j - muX j))) +
            (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m *
              (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) +
                  Real.sqrt (1 - v) * (G i x.1 j - muY j)) +
                Real.sqrt (1 - t) * (G i x.2 j - muY j)))) t x) ∂(P.prod P)) ≤
        2 * rho P n m p (delta n m) muX muY X Y F G +
          ((P {ω | ∀ j : Fin p, combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤
              y j + ((min phi1 phi2)⁻¹ + 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹)}).toReal -
            (P {ω | ∀ j : Fin p, combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤
              y j - ((min phi1 phi2)⁻¹ + 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹)}).toReal) := by
    intro t ht
    haveI hne : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
    set κ : ℝ := (min phi1 phi2)⁻¹ + 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹ with hκ
    set Zb : ℝ → Ω × Ω → Fin p → ℝ := fun t x j =>
      (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ *
        (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) +
            Real.sqrt (1 - v) * (F i x.1 j - muX j)) +
          Real.sqrt (1 - t) * (F i x.2 j - muX j))) +
      (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m *
        (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) +
            Real.sqrt (1 - v) * (G i x.1 j - muY j)) +
          Real.sqrt (1 - t) * (G i x.2 j - muY j))) with hZb
    have hsup : ∀ (w : Fin p → ℝ) (c : ℝ),
        (⨆ j : Fin p, (w j - y j)) ≤ c ↔ ∀ j : Fin p, w j ≤ y j + c := by
      intro w c
      rw [← Finset.sup'_univ_eq_ciSup, Finset.sup'_le_iff]
      constructor
      · intro h j
        have := h j (Finset.mem_univ j)
        linarith
      · intro h j _
        linarith [h j]
    have hZeq : ∀ (x : Ω × Ω) (j : Fin p),
        Zb t x j =
          Real.sqrt (t * v) * combVec n m (delta n m) muX muY (fun i => X i x.1) (fun i => Y i x.1) j +
            Real.sqrt (t * (1 - v)) *
                combVec n m (delta n m) muX muY (fun i => F i x.1) (fun i => G i x.1) j +
              Real.sqrt (1 - t) *
                combVec n m (delta n m) muX muY (fun i => F i x.2) (fun i => G i x.2) j := by
      intro x j
      have htv : Real.sqrt (t * v) = Real.sqrt t * Real.sqrt v := Real.sqrt_mul ht.1 v
      have ht1v : Real.sqrt (t * (1 - v)) = Real.sqrt t * Real.sqrt (1 - v) :=
        Real.sqrt_mul ht.1 (1 - v)
      have hmN : ∀ (c : ℝ) (f : Fin n → ℝ), (∑ i : Fin n, c * f i) = c * ∑ i : Fin n, f i := by
        intro c f
        rw [Finset.mul_sum]
      have hmM : ∀ (c : ℝ) (f : Fin m → ℝ), (∑ i : Fin m, c * f i) = c * ∑ i : Fin m, f i := by
        intro c f
        rw [Finset.mul_sum]
      have hsubN : ∀ (f g : Fin n → ℝ),
          (∑ i : Fin n, (f i - g i)) = (∑ i : Fin n, f i) - ∑ i : Fin n, g i := by
        intro f g
        rw [Finset.sum_sub_distrib]
      have hsubM : ∀ (f g : Fin m → ℝ),
          (∑ i : Fin m, (f i - g i)) = (∑ i : Fin m, f i) - ∑ i : Fin m, g i := by
        intro f g
        rw [Finset.sum_sub_distrib]
      have hconstN : ∀ c : ℝ, (∑ _i : Fin n, c) = (n : ℝ) * c := by
        intro c
        simp [Finset.sum_const, nsmul_eq_mul]
      have hconstM : ∀ c : ℝ, (∑ _i : Fin m, c) = (m : ℝ) * c := by
        intro c
        simp [Finset.sum_const, nsmul_eq_mul]
      rw [hZb, htv, ht1v]
      simp only [combVec, normSum, hmN, hmM, Finset.sum_add_distrib, hsubN, hsubM, hconstN,
        hconstM]
      set SX : ℝ := ∑ i : Fin n, X i x.1 j with hSX
      set SF : ℝ := ∑ i : Fin n, F i x.1 j with hSF
      set SF2 : ℝ := ∑ i : Fin n, F i x.2 j with hSF2
      set SY : ℝ := ∑ i : Fin m, Y i x.1 j with hSY
      set SG : ℝ := ∑ i : Fin m, G i x.1 j with hSG
      set SG2 : ℝ := ∑ i : Fin m, G i x.2 j with hSG2
      set s : ℝ := Real.sqrt (n : ℝ) with hs
      set r : ℝ := Real.sqrt (m : ℝ) with hr
      have hs2 : s * s = (n : ℝ) := by
        rw [hs]
        exact Real.mul_self_sqrt (by exact_mod_cast hn.le)
      have hr2 : r * r = (m : ℝ) := by
        rw [hr]
        exact Real.mul_self_sqrt (by exact_mod_cast hm.le)
      have hs0 : s ≠ 0 := by
        intro h0
        rw [h0] at hs2
        simp only [zero_mul] at hs2
        exact absurd hs2.symm (by exact_mod_cast (ne_of_gt hn))
      have hr0 : r ≠ 0 := by
        intro h0
        rw [h0] at hr2
        simp only [zero_mul] at hr2
        exact absurd hr2.symm (by exact_mod_cast (ne_of_gt hm))
      rw [← hs2, ← hr2]
      field_simp
      ring
    have hκneg : -(min phi1 phi2)⁻¹ - 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹ = -κ := by
      rw [hκ]
      ring
    have hZmeas : ∀ j : Fin p, Measurable (fun x : Ω × Ω => Zb t x j) := by
      intro j
      have hXq : ∀ i : Fin n, Measurable (fun x : Ω × Ω => X i x.1 j) := fun i =>
        (measurable_pi_apply j).comp ((hXm i).comp measurable_fst)
      have hFq : ∀ i : Fin n, Measurable (fun x : Ω × Ω => F i x.1 j) := fun i =>
        (measurable_pi_apply j).comp ((hFm i).comp measurable_fst)
      have hF2 : ∀ i : Fin n, Measurable (fun x : Ω × Ω => F i x.2 j) := fun i =>
        (measurable_pi_apply j).comp ((hFm i).comp measurable_snd)
      have hYq : ∀ i : Fin m, Measurable (fun x : Ω × Ω => Y i x.1 j) := fun i =>
        (measurable_pi_apply j).comp ((hYm i).comp measurable_fst)
      have hGq : ∀ i : Fin m, Measurable (fun x : Ω × Ω => G i x.1 j) := fun i =>
        (measurable_pi_apply j).comp ((hGm i).comp measurable_fst)
      have hG2 : ∀ i : Fin m, Measurable (fun x : Ω × Ω => G i x.2 j) := fun i =>
        (measurable_pi_apply j).comp ((hGm i).comp measurable_snd)
      rw [hZb]
      dsimp only
      refine Measurable.add ?_ ?_
      · refine Finset.measurable_sum (Finset.univ : Finset (Fin n))
          (f := fun (i : Fin n) (x : Ω × Ω) =>
            (Real.sqrt (n : ℝ))⁻¹ *
              (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) +
                  Real.sqrt (1 - v) * (F i x.1 j - muX j)) +
                Real.sqrt (1 - t) * (F i x.2 j - muX j))) ?_
        intro i _
        exact Measurable.mul measurable_const (Measurable.add
          (Measurable.mul measurable_const (Measurable.add
            (Measurable.mul measurable_const ((hXq i).sub measurable_const))
            (Measurable.mul measurable_const ((hFq i).sub measurable_const))))
          (Measurable.mul measurable_const ((hF2 i).sub measurable_const)))
      · refine Finset.measurable_sum (Finset.univ : Finset (Fin m))
          (f := fun (i : Fin m) (x : Ω × Ω) =>
            (Real.sqrt (m : ℝ))⁻¹ * delta n m *
              (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) +
                  Real.sqrt (1 - v) * (G i x.1 j - muY j)) +
                Real.sqrt (1 - t) * (G i x.2 j - muY j))) ?_
        intro i _
        exact Measurable.mul measurable_const (Measurable.add
          (Measurable.mul measurable_const (Measurable.add
            (Measurable.mul measurable_const ((hYq i).sub measurable_const))
            (Measurable.mul measurable_const ((hGq i).sub measurable_const))))
          (Measurable.mul measurable_const ((hG2 i).sub measurable_const)))
    have hmes : ∀ z : Fin p → ℝ, MeasurableSet {x : Ω × Ω | ∀ j : Fin p, Zb t x j ≤ z j} := by
      intro z
      have h : MeasurableSet (⋂ j : Fin p, {x : Ω × Ω | Zb t x j ≤ z j}) := by
        refine MeasurableSet.iInter (fun j => ?_)
        exact MeasurableSet.preimage (measurableSet_Iic (a := z j)) (hZmeas j)
      convert h using 1
      ext x
      simp
    have hA1meas : MeasurableSet {x' : Ω × Ω | (⨆ j : Fin p, (Zb t x' j - y j)) ≤ κ} := by
      have heq : {x' : Ω × Ω | (⨆ j : Fin p, (Zb t x' j - y j)) ≤ κ}
          = {x' : Ω × Ω | ∀ j : Fin p, Zb t x' j ≤ y j + κ} := by
        ext x'
        exact hsup (Zb t x') κ
      rw [heq]
      exact hmes (fun j => y j + κ)
    have hA2meas : MeasurableSet {x' : Ω × Ω | (⨆ j : Fin p, (Zb t x' j - y j)) ≤ -κ} := by
      have heq : {x' : Ω × Ω | (⨆ j : Fin p, (Zb t x' j - y j)) ≤ -κ}
          = {x' : Ω × Ω | ∀ j : Fin p, Zb t x' j ≤ y j - κ} := by
        ext x'
        simp only [Set.mem_setOf_eq]
        rw [hsup (Zb t x') (-κ)]
        simp only [sub_eq_add_neg]
      rw [heq]
      exact hmes (fun j => y j - κ)
    have hpt : ∀ x : Ω × Ω,
        Set.indicator {w' : Fin p → ℝ |
            -(min phi1 phi2)⁻¹ - 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹ <
                (⨆ j : Fin p, (w' j - y j)) ∧
              (⨆ j : Fin p, (w' j - y j)) ≤ κ} (fun _ => (1 : ℝ)) (Zb t x)
          = Set.indicator {x' : Ω × Ω | (⨆ j : Fin p, (Zb t x' j - y j)) ≤ κ}
              (fun _ => (1 : ℝ)) x
            - Set.indicator {x' : Ω × Ω | (⨆ j : Fin p, (Zb t x' j - y j)) ≤ -κ}
              (fun _ => (1 : ℝ)) x := by
      intro x
      set S : Set (Fin p → ℝ) := {w' : Fin p → ℝ |
          -(min phi1 phi2)⁻¹ - 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹ <
              (⨆ j : Fin p, (w' j - y j)) ∧
            (⨆ j : Fin p, (w' j - y j)) ≤ κ} with hS
      set A1 : Set (Ω × Ω) := {x' : Ω × Ω | (⨆ j : Fin p, (Zb t x' j - y j)) ≤ κ} with hA1
      set A2 : Set (Ω × Ω) := {x' : Ω × Ω | (⨆ j : Fin p, (Zb t x' j - y j)) ≤ -κ} with hA2
      set m : ℝ := (⨆ j : Fin p, (Zb t x j - y j)) with hm
      have hmS : Zb t x ∈ S ↔ (-κ < m ∧ m ≤ κ) := by
        rw [hS]
        simp only [Set.mem_setOf_eq, hκneg, ← hm]
      have hm1 : x ∈ A1 ↔ m ≤ κ := by
        rw [hA1]
        simp only [Set.mem_setOf_eq, ← hm]
      have hm2 : x ∈ A2 ↔ m ≤ -κ := by
        rw [hA2]
        simp only [Set.mem_setOf_eq, ← hm]
      by_cases hle : m ≤ -κ
      · rw [Set.indicator_of_notMem (show Zb t x ∉ S from by
            rw [hmS]; intro h; linarith [h.1]),
          Set.indicator_of_mem (show x ∈ A1 from by rw [hm1]; linarith),
          Set.indicator_of_mem (show x ∈ A2 from by rw [hm2]; exact hle)]
        norm_num
      · have hlt : -κ < m := by linarith
        by_cases hle2 : m ≤ κ
        · rw [Set.indicator_of_mem (show Zb t x ∈ S from by rw [hmS]; exact ⟨hlt, hle2⟩),
            Set.indicator_of_mem (show x ∈ A1 from by rw [hm1]; exact hle2),
            Set.indicator_of_notMem (show x ∉ A2 from by rw [hm2]; exact hle)]
          norm_num
        · rw [Set.indicator_of_notMem (show Zb t x ∉ S from by
              rw [hmS]; intro h; exact hle2 h.2),
            Set.indicator_of_notMem (show x ∉ A1 from by rw [hm1]; exact hle2),
            Set.indicator_of_notMem (show x ∉ A2 from by rw [hm2]; exact hle)]
          norm_num
    have hfun : (fun x : Ω × Ω =>
        (fun w : Fin p → ℝ => Set.indicator {w' : Fin p → ℝ |
            -(min phi1 phi2)⁻¹ - 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹ <
                (⨆ j : Fin p, (w' j - y j)) ∧
              (⨆ j : Fin p, (w' j - y j)) ≤ κ} (fun _ => (1 : ℝ)) w) (Zb t x))
        = fun x : Ω × Ω =>
          Set.indicator {x' : Ω × Ω | (⨆ j : Fin p, (Zb t x' j - y j)) ≤ κ}
              (fun _ => (1 : ℝ)) x
            - Set.indicator {x' : Ω × Ω | (⨆ j : Fin p, (Zb t x' j - y j)) ≤ -κ}
              (fun _ => (1 : ℝ)) x := by
      funext x
      exact hpt x
    rw [hfun]
    have hI1 : Integrable (Set.indicator {x' : Ω × Ω | (⨆ j : Fin p, (Zb t x' j - y j)) ≤ κ}
        (fun _ => (1 : ℝ))) (P.prod P) :=
      (MeasureTheory.integrable_const (1 : ℝ)).indicator hA1meas
    have hI2 : Integrable (Set.indicator {x' : Ω × Ω | (⨆ j : Fin p, (Zb t x' j - y j)) ≤ -κ}
        (fun _ => (1 : ℝ))) (P.prod P) :=
      (MeasureTheory.integrable_const (1 : ℝ)).indicator hA2meas
    rw [MeasureTheory.integral_sub hI1 hI2,
      ← Statlib.HypothesisTesting.measure_eq_integral_indicator hA1meas,
      ← Statlib.HypothesisTesting.measure_eq_integral_indicator hA2meas]
    have hchild1 := statopia_math_node_2515832765_1170112b Ω P n m p delta muX muY X Y F G
      hn hm hp hXm hYm hFm hGm hindep hMemX hMemY hmuX hmuY hGaussF hGaussG v t hv0 hv1
      ht.1 ht.2 (fun j : Fin p => y j + κ)
    have hchild2 := statopia_math_node_2515832765_1170112b Ω P n m p delta muX muY X Y F G
      hn hm hp hXm hYm hFm hGm hindep hMemX hMemY hmuX hmuY hGaussF hGaussG v t hv0 hv1
      ht.1 ht.2 (fun j : Fin p => y j - κ)
    have hchild1' : ((P.prod P) {x : Ω × Ω | ∀ j : Fin p,
          Real.sqrt (t * v) * combVec n m (delta n m) muX muY (fun i => X i x.1) (fun i => Y i x.1) j
        + Real.sqrt (t * (1 - v)) * combVec n m (delta n m) muX muY (fun i => F i x.1) (fun i => G i x.1) j
        + Real.sqrt (1 - t) * combVec n m (delta n m) muX muY (fun i => F i x.2) (fun i => G i x.2) j
          ≤ y j + κ})
      = P {ω : Ω | ∀ j : Fin p,
          Real.sqrt (t * v) * combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j
        + Real.sqrt (1 - t * v) * combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j
          ≤ y j + κ} := hchild1
    have hchild2' : ((P.prod P) {x : Ω × Ω | ∀ j : Fin p,
          Real.sqrt (t * v) * combVec n m (delta n m) muX muY (fun i => X i x.1) (fun i => Y i x.1) j
        + Real.sqrt (t * (1 - v)) * combVec n m (delta n m) muX muY (fun i => F i x.1) (fun i => G i x.1) j
        + Real.sqrt (1 - t) * combVec n m (delta n m) muX muY (fun i => F i x.2) (fun i => G i x.2) j
          ≤ y j - κ})
      = P {ω : Ω | ∀ j : Fin p,
          Real.sqrt (t * v) * combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j
        + Real.sqrt (1 - t * v) * combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j
          ≤ y j - κ} := hchild2
    have hM1 : ((P.prod P) {x' : Ω × Ω | (⨆ j : Fin p, (Zb t x' j - y j)) ≤ κ}).toReal
        = (P {ω : Ω | ∀ j : Fin p,
          Real.sqrt (t * v) * combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j
        + Real.sqrt (1 - t * v) * combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j
          ≤ y j + κ}).toReal := by
      have hL : {x' : Ω × Ω | (⨆ j : Fin p, (Zb t x' j - y j)) ≤ κ}
          = {x : Ω × Ω | ∀ j : Fin p,
              Real.sqrt (t * v) * combVec n m (delta n m) muX muY (fun i => X i x.1) (fun i => Y i x.1) j
            + Real.sqrt (t * (1 - v)) * combVec n m (delta n m) muX muY (fun i => F i x.1) (fun i => G i x.1) j
            + Real.sqrt (1 - t) * combVec n m (delta n m) muX muY (fun i => F i x.2) (fun i => G i x.2) j
              ≤ y j + κ} := by
        ext x'
        simp only [Set.mem_setOf_eq]
        rw [hsup (Zb t x') κ]
        constructor
        · intro h j
          rw [← hZeq x' j]
          exact h j
        · intro h j
          rw [hZeq x' j]
          exact h j
      rw [hL, hchild1']
    have hM2 : ((P.prod P) {x' : Ω × Ω | (⨆ j : Fin p, (Zb t x' j - y j)) ≤ -κ}).toReal
        = (P {ω : Ω | ∀ j : Fin p,
          Real.sqrt (t * v) * combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j
        + Real.sqrt (1 - t * v) * combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j
          ≤ y j - κ}).toReal := by
      have hL : {x' : Ω × Ω | (⨆ j : Fin p, (Zb t x' j - y j)) ≤ -κ}
          = {x : Ω × Ω | ∀ j : Fin p,
              Real.sqrt (t * v) * combVec n m (delta n m) muX muY (fun i => X i x.1) (fun i => Y i x.1) j
            + Real.sqrt (t * (1 - v)) * combVec n m (delta n m) muX muY (fun i => F i x.1) (fun i => G i x.1) j
            + Real.sqrt (1 - t) * combVec n m (delta n m) muX muY (fun i => F i x.2) (fun i => G i x.2) j
              ≤ y j - κ} := by
        ext x'
        simp only [Set.mem_setOf_eq]
        rw [hsup (Zb t x') (-κ)]
        constructor
        · intro h j
          rw [← hZeq x' j]
          linarith [h j]
        · intro h j
          rw [hZeq x' j]
          linarith [h j]
      rw [hL, hchild2']
    have hprob_le_one : ∀ s : Set Ω, (P s).toReal ≤ 1 := by
      intro s
      have h1 : P s ≤ 1 := MeasureTheory.prob_le_one (μ := P)
      have h2 := ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ⊤) h1
      simpa using h2
    let V : Set.Icc (0 : ℝ) 1 :=
      ⟨t * v, mul_nonneg ht.1 hv0, by nlinarith [ht.2, ht.1, hv1, hv0]⟩
    have hbnd : ∀ (v' : Set.Icc (0 : ℝ) 1) (z' : Fin p → ℝ),
        |(P {ω : Ω | ∀ j : Fin p,
              Real.sqrt ((v' : ℝ)) * combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j
            + Real.sqrt (1 - (v' : ℝ)) * combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j
              ≤ z' j}).toReal
          - (P {ω : Ω | ∀ j : Fin p,
              combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤ z' j}).toReal| ≤ 1 := by
      intro v' z'
      have ha0 : (0 : ℝ) ≤ (P {ω : Ω | ∀ j : Fin p,
          Real.sqrt ((v' : ℝ)) * combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j
        + Real.sqrt (1 - (v' : ℝ)) * combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j
          ≤ z' j}).toReal := ENNReal.toReal_nonneg
      have ha1 : (P {ω : Ω | ∀ j : Fin p,
          Real.sqrt ((v' : ℝ)) * combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j
        + Real.sqrt (1 - (v' : ℝ)) * combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j
          ≤ z' j}).toReal ≤ 1 := hprob_le_one _
      have hb0 : (0 : ℝ) ≤ (P {ω : Ω | ∀ j : Fin p,
          combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤ z' j}).toReal :=
        ENNReal.toReal_nonneg
      have hb1 : (P {ω : Ω | ∀ j : Fin p,
          combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤ z' j}).toReal ≤ 1 :=
        hprob_le_one _
      rw [abs_le]
      constructor <;> linarith
    have hby : BddAbove (Set.range fun z' : Fin p → ℝ =>
        |(P {ω : Ω | ∀ j : Fin p,
              Real.sqrt ((V : ℝ)) * combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j
            + Real.sqrt (1 - (V : ℝ)) * combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j
              ≤ z' j}).toReal
          - (P {ω : Ω | ∀ j : Fin p,
              combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤ z' j}).toReal|) :=
      ⟨1, by rintro _ ⟨z', rfl⟩; exact hbnd V z'⟩
    have hbv : BddAbove (Set.range fun v' : Set.Icc (0 : ℝ) 1 => ⨆ z' : Fin p → ℝ,
        |(P {ω : Ω | ∀ j : Fin p,
              Real.sqrt ((v' : ℝ)) * combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j
            + Real.sqrt (1 - (v' : ℝ)) * combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j
              ≤ z' j}).toReal
          - (P {ω : Ω | ∀ j : Fin p,
              combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤ z' j}).toReal|) :=
      ⟨1, by rintro _ ⟨v', rfl⟩; exact Real.iSup_le (fun z' => hbnd v' z') (by norm_num)⟩
    have hr1 : |(P {ω : Ω | ∀ j : Fin p,
          Real.sqrt (t * v) * combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j
        + Real.sqrt (1 - t * v) * combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j
          ≤ y j + κ}).toReal
        - (P {ω : Ω | ∀ j : Fin p,
            combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤ y j + κ}).toReal|
        ≤ rho P n m p (delta n m) muX muY X Y F G := by
      simp only [rho]
      exact le_trans (le_ciSup hby (fun j : Fin p => y j + κ)) (le_ciSup hbv V)
    have hr2 : |(P {ω : Ω | ∀ j : Fin p,
          Real.sqrt (t * v) * combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j
        + Real.sqrt (1 - t * v) * combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j
          ≤ y j - κ}).toReal
        - (P {ω : Ω | ∀ j : Fin p,
            combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤ y j - κ}).toReal|
        ≤ rho P n m p (delta n m) muX muY X Y F G := by
      simp only [rho]
      exact le_trans (le_ciSup hby (fun j : Fin p => y j - κ)) (le_ciSup hbv V)
    rw [hM1, hM2]
    have h1 := abs_le.mp hr1
    have h2 := abs_le.mp hr2
    linarith [h1.1, h1.2, h2.1, h2.2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hκ0
  · intro w
    change Set.indicator {w' : Fin p → ℝ |
        -(min phi1 phi2)⁻¹ ≤ (⨆ j : Fin p, (w' j - y j)) ∧
          (⨆ j : Fin p, (w' j - y j)) ≤ (min phi1 phi2)⁻¹} (fun _ => (1 : ℝ)) w ≤
      Set.indicator {w' : Fin p → ℝ |
          -(min phi1 phi2)⁻¹ - 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹ <
              (⨆ j : Fin p, (w' j - y j)) ∧
            (⨆ j : Fin p, (w' j - y j)) ≤
              (min phi1 phi2)⁻¹ + 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹}
        (fun _ => (1 : ℝ)) w
    by_cases hw : w ∈ {w' : Fin p → ℝ |
        -(min phi1 phi2)⁻¹ ≤ (⨆ j : Fin p, (w' j - y j)) ∧
          (⨆ j : Fin p, (w' j - y j)) ≤ (min phi1 phi2)⁻¹}
    · rw [Set.indicator_of_mem hw]
      have hmem : w ∈ {w' : Fin p → ℝ |
          -(min phi1 phi2)⁻¹ - 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹ <
              (⨆ j : Fin p, (w' j - y j)) ∧
            (⨆ j : Fin p, (w' j - y j)) ≤
              (min phi1 phi2)⁻¹ + 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹} := by
        obtain ⟨h1, h2⟩ := hw
        exact ⟨by linarith, by linarith⟩
      rw [Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem hw]
      by_cases h2 : w ∈ {w' : Fin p → ℝ |
          -(min phi1 phi2)⁻¹ - 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹ <
              (⨆ j : Fin p, (w' j - y j)) ∧
            (⨆ j : Fin p, (w' j - y j)) ≤
              (min phi1 phi2)⁻¹ + 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹}
      · rw [Set.indicator_of_mem h2]
        norm_num
      · rw [Set.indicator_of_notMem h2]
  · intro t ht
    exact ⟨hmain3 t ht, hmain3b t ht⟩
  · intro t ht
    have h1 := hmain3 t ht
    have h2 := hmain3b t ht
    have hCb0 : (0 : ℝ) ≤ 2 * Cb := by linarith
    have hs : (0 : ℝ) ≤ Real.sqrt (Real.log (p : ℝ)) := Real.sqrt_nonneg _
    have hmul : (2 * Cb) * ((min phi1 phi2)⁻¹ + 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹) *
        Real.sqrt (Real.log (p : ℝ)) ≤
        (2 * Cb) * ((1 + 2 / Real.log 2) * (min phi1 phi2)⁻¹) *
          Real.sqrt (Real.log (p : ℝ)) := by
      have hc : (0 : ℝ) ≤ 2 * Cb * Real.sqrt (Real.log (p : ℝ)) := mul_nonneg hCb0 hs
      have hm := mul_le_mul_of_nonneg_left hκ0 hc
      calc (2 * Cb) * ((min phi1 phi2)⁻¹ + 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹) *
            Real.sqrt (Real.log (p : ℝ))
          = (2 * Cb * Real.sqrt (Real.log (p : ℝ))) *
              ((min phi1 phi2)⁻¹ + 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹) := by ring
        _ ≤ (2 * Cb * Real.sqrt (Real.log (p : ℝ))) *
              ((1 + 2 / Real.log 2) * (min phi1 phi2)⁻¹) := hm
        _ = (2 * Cb) * ((1 + 2 / Real.log 2) * (min phi1 phi2)⁻¹) *
              Real.sqrt (Real.log (p : ℝ)) := by ring
    have hring : (2 * Cb) * ((1 + 2 / Real.log 2) * (min phi1 phi2)⁻¹) *
          Real.sqrt (Real.log (p : ℝ))
        = (2 * Cb) * (1 + 2 / Real.log 2) * (min phi1 phi2)⁻¹ *
            Real.sqrt (Real.log (p : ℝ)) := by ring
    linarith [h1, h2, hmul, hring]



  /- @proof-region region.target-node.session.3e4b9508300980a2 end -/

end

end Statlib.Imported

