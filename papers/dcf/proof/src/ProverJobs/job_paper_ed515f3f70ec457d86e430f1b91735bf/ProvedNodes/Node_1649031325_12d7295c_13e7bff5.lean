import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
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
theorem statopia_math_node_1649031325_12d7295c : ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n m p : ℕ) (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
    (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
    (hn : 0 < n) (hm : 0 < m) (hp : 0 < p)
    (hXm : ∀ i : Fin n, Measurable (X i))
    (hYm : ∀ i : Fin m, Measurable (Y i))
    (hFm : ∀ i : Fin n, Measurable (F i))
    (hGm : ∀ i : Fin m, Measurable (G i))
    (hindep : iIndepFun (β := fun _ => Fin p → ℝ) (jointFam X Y F G) P)
    (hXmean : ∀ (i : Fin n) (j : Fin p), ∫ ω, X i ω j ∂P = muX j)
    (hYmean : ∀ (i : Fin m) (j : Fin p), ∫ ω, Y i ω j ∂P = muY j)
    (hXL2 : ∀ (i : Fin n) (j : Fin p), MemLp (fun ω => X i ω j) 2 P)
    (hYL2 : ∀ (i : Fin m) (j : Fin p), MemLp (fun ω => Y i ω j) 2 P)
    (hX3 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |X i ω j - muX j| ^ 3) P)
    (hY3 : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => |Y i ω j - muY j| ^ 3) P)
    (hF3 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |F i ω j - muX j| ^ 3) P)
    (hG3 : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => |G i ω j - muY j| ^ 3) P)
    (hFcov : ∀ i : Fin n,
      IsCenteredGaussianVector P (fun ω j => F i ω j - muX j) (covX P muX X i))
    (hGcov : ∀ i : Fin m,
      IsCenteredGaussianVector P (fun ω j => G i ω j - muY j) (covY P muY Y i))
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1),
    ∀ t : ℝ, 0 < t → t < 1 → ∀ (i : Fin m) (j k : Fin p),
      let Zs : Ω × Ω → ℝ := fun x =>
        (Real.sqrt (m : ℝ))⁻¹ * delta n m *
          (Real.sqrt t *
              (Real.sqrt v * (Y i x.1 k - muY k) + Real.sqrt (1 - v) * (G i x.1 k - muY k))
            + Real.sqrt (1 - t) * (G i x.2 k - muY k))
      let Zd : Ω × Ω → ℝ := fun x =>
        (Real.sqrt (m : ℝ))⁻¹ * delta n m *
          ((2 * Real.sqrt t)⁻¹ *
              (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))
            - (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j))
      Integrable (fun x => Zs x * Zd x) (P.prod P) ∧
        ∫ x, Zs x * Zd x ∂(P.prod P) = 0 := by
  /- @proof-region region.target-node.session.e967d7a385dc882f begin -/
  intro Ω instΩ P instP n m p delta muX muY X Y F G hn hm hp hXm hYm hFm hGm hindep
    hXmean hYmean hXL2 hYL2 hX3 hY3 hF3 hG3 hFcov hGcov v hv0 hv1 t ht0 ht1 i j k
  dsimp only
  obtain ⟨hbmeas, hbExpInt, hbExpEq⟩ := hGcov i
  have hmoment : ∀ u : Fin p → ℝ,
      (∫ ω, (∑ a, u a * (G i ω a - muY a)) ∂P = 0) ∧
      (∫ ω, (∑ a, u a * (G i ω a - muY a)) ^ 2 ∂P =
        ∑ a, ∑ b, u a * covY P muY Y i a b * u b) := by
    intro u
    set Xf : Ω → ℝ := fun ω => ∑ a, u a * (G i ω a - muY a) with hXf
    set Qm : ℝ := ∑ a, ∑ b, u a * covY P muY Y i a b * u b with hQm
    have hmemp : ∀ t : ℝ, t ∈ integrableExpSet Xf P := by
      intro t
      have h := hbExpInt (fun a => t * u a)
      simpa only [integrableExpSet, hXf, Finset.mul_sum, mul_assoc] using h
    have huniv : integrableExpSet Xf P = Set.univ := Set.eq_univ_of_forall hmemp
    have hmemI : ∀ t : ℝ, t ∈ interior (integrableExpSet Xf P) := by
      intro t
      rw [huniv]
      simp
    have hfun : (fun t : ℝ => ∫ ω, Real.exp (t * Xf ω) ∂P) =
        fun t : ℝ => Real.exp (t ^ 2 * Qm / 2) := by
      funext t
      have hΦ := hbExpEq (fun a => t * u a)
      simp only [] at hΦ
      have hQ : (∑ a, ∑ b, (t * u a) * covY P muY Y i a b * (t * u b)) = t ^ 2 * Qm := by
        rw [hQm, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun b _ => by ring)
      rw [hQ] at hΦ
      have hleft : (fun ω => Real.exp (∑ a, (t * u a) * (G i ω a - muY a))) =
          fun ω => Real.exp (t * Xf ω) := by
        funext ω
        rw [hXf]
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun a _ => by ring)
      rw [hleft] at hΦ
      exact hΦ
    have hinner0 : HasDerivAt (fun s : ℝ => s ^ 2 * Qm / 2) 0 0 := by
      have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * (0:ℝ)) 0 := by
        simpa [pow_two] using (hasDerivAt_id (0:ℝ)).mul (hasDerivAt_id (0:ℝ))
      have h := (hsq.mul_const Qm).div_const 2
      simpa using h
    have hexp0 : HasDerivAt (fun s : ℝ => Real.exp (s ^ 2 * Qm / 2)) 0 0 := by
      have h := hinner0.exp
      simpa using h
    have hfirst : ∫ ω, Xf ω ∂P = 0 := by
      have hd : HasDerivAt (fun t : ℝ => ∫ ω, Real.exp (t * Xf ω) ∂P) (∫ ω, Xf ω ∂P) 0 := by
        have h := hasDerivAt_integral_pow_mul_exp_real (X := Xf) (μ := P) (hmemI 0) 0
        simpa using h
      have hd' : HasDerivAt (fun t : ℝ => ∫ ω, Real.exp (t * Xf ω) ∂P) 0 0 := by
        rw [hfun]
        exact hexp0
      exact hd.unique hd'
    have hd1 : HasDerivAt (fun t : ℝ => ∫ ω, Xf ω * Real.exp (t * Xf ω) ∂P) (∫ ω, Xf ω ^ 2 ∂P) 0 := by
      have h := hasDerivAt_integral_pow_mul_exp_real (X := Xf) (μ := P) (hmemI 0) 1
      simpa using h
    have hderiv_formula : ∀ t : ℝ,
        ∫ ω, Xf ω * Real.exp (t * Xf ω) ∂P = t * Qm * Real.exp (t ^ 2 * Qm / 2) := by
      intro t
      have hinner_t : HasDerivAt (fun s : ℝ => s ^ 2 * Qm / 2) (t * Qm) t := by
        have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
          have h := (hasDerivAt_id t).mul (hasDerivAt_id t)
          simpa [pow_two, two_mul] using h
        have h := (hsq.mul_const Qm).div_const 2
        have hval : (2 * t) * Qm / 2 = t * Qm := by ring
        rwa [hval] at h
      have hexp_t : HasDerivAt (fun s : ℝ => Real.exp (s ^ 2 * Qm / 2))
          (Real.exp (t ^ 2 * Qm / 2) * (t * Qm)) t := hinner_t.exp
      have hdA : HasDerivAt (fun s : ℝ => ∫ ω, Xf ω ^ 0 * Real.exp (s * Xf ω) ∂P)
          (∫ ω, Xf ω ^ (0 + 1) * Real.exp (t * Xf ω) ∂P) t :=
        hasDerivAt_integral_pow_mul_exp_real (X := Xf) (μ := P) (hmemI t) 0
      have hdA' : HasDerivAt (fun s : ℝ => ∫ ω, Real.exp (s * Xf ω) ∂P)
          (∫ ω, Xf ω * Real.exp (t * Xf ω) ∂P) t := by
        simpa using hdA
      have hdA'' : HasDerivAt (fun s : ℝ => Real.exp (s ^ 2 * Qm / 2))
          (∫ ω, Xf ω * Real.exp (t * Xf ω) ∂P) t := by
        rw [← hfun]
        exact hdA'
      have hres := hdA''.unique hexp_t
      rw [hres]
      ring
    have hsecond : ∫ ω, Xf ω ^ 2 ∂P = Qm := by
      have hd2 : HasDerivAt (fun t : ℝ => t * Qm * Real.exp (t ^ 2 * Qm / 2)) Qm 0 := by
        have h1 : HasDerivAt (fun t : ℝ => t * Qm) Qm 0 := by
          have h0 := (hasDerivAt_id (0:ℝ)).mul_const Qm
          have h1' : HasDerivAt (fun t : ℝ => t * Qm) (1 * Qm) 0 := h0
          simpa using h1'
        have h2 : HasDerivAt (fun t : ℝ => Real.exp (t ^ 2 * Qm / 2)) 0 0 := hexp0
        have hm := h1.mul h2
        simpa using hm
      have hd2' : HasDerivAt (fun t : ℝ => ∫ ω, Xf ω * Real.exp (t * Xf ω) ∂P) Qm 0 := by
        rw [show (fun t : ℝ => ∫ ω, Xf ω * Real.exp (t * Xf ω) ∂P) =
          fun t : ℝ => t * Qm * Real.exp (t ^ 2 * Qm / 2) from funext hderiv_formula]
        exact hd2
      exact hd1.unique hd2'
    exact ⟨hfirst, hsecond⟩
  have habs_cube : ∀ t : ℝ, |t| ≤ 1 + |t| ^ 3 := by
    intro t
    set s := |t| with hs
    have hs0 : (0:ℝ) ≤ s := by rw [hs]; exact abs_nonneg t
    rcases le_total s 1 with h | h
    · have h3 : (0:ℝ) ≤ s ^ 3 := pow_nonneg hs0 3
      linarith
    · have h2 : (1:ℝ) ≤ s * s := by nlinarith
      have h4 : s ^ 3 = s * (s * s) := by ring
      have h3 : s ≤ s * (s * s) := by
        calc s = s * 1 := by ring
          _ ≤ s * (s * s) := mul_le_mul_of_nonneg_left h2 hs0
      linarith
  have hsq_cube : ∀ t : ℝ, t ^ 2 ≤ 1 + |t| ^ 3 := by
    intro t
    set s := |t| with hs
    have hs0 : (0:ℝ) ≤ s := by rw [hs]; exact abs_nonneg t
    have hsq : t ^ 2 = s ^ 2 := by rw [hs]; exact (sq_abs t).symm
    rcases le_total s 1 with h | h
    · have h2 : s ^ 2 ≤ 1 := by nlinarith
      have h3 : (0:ℝ) ≤ s ^ 3 := pow_nonneg hs0 3
      linarith
    · have h3 : s ^ 2 ≤ s ^ 3 := by
        have h5 : s ^ 2 * 1 ≤ s ^ 2 * s := mul_le_mul_of_nonneg_left h (by positivity)
        calc s ^ 2 = s ^ 2 * 1 := by ring
          _ ≤ s ^ 2 * s := h5
          _ = s ^ 3 := by ring
      linarith
  have hbasic : ∀ (u : Ω → ℝ), Measurable u → Integrable (fun ω => |u ω| ^ 3) P →
      Integrable u P ∧ Integrable (fun ω => u ω ^ 2) P := by
    intro u hum hu3
    have hdom : Integrable (fun ω => 1 + |u ω| ^ 3) P := (integrable_const (1:ℝ)).add hu3
    constructor
    · refine Integrable.mono' hdom hum.aestronglyMeasurable ?_
      filter_upwards with ω
      rw [Real.norm_eq_abs]
      exact habs_cube (u ω)
    · refine Integrable.mono' hdom ?_ ?_
      · exact ((continuous_id.pow 2).measurable.comp hum).aestronglyMeasurable
      · filter_upwards with ω
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (u ω))]
        exact hsq_cube (u ω)
  have haKm : Measurable (fun ω => Y i ω k - muY k) :=
    ((measurable_pi_apply k).comp (hYm i)).sub measurable_const
  have haJm : Measurable (fun ω => Y i ω j - muY j) :=
    ((measurable_pi_apply j).comp (hYm i)).sub measurable_const
  have hbKm : Measurable (fun ω => G i ω k - muY k) :=
    ((measurable_pi_apply k).comp (hGm i)).sub measurable_const
  have hbJm : Measurable (fun ω => G i ω j - muY j) :=
    ((measurable_pi_apply j).comp (hGm i)).sub measurable_const
  have haK := hbasic (fun ω => Y i ω k - muY k) haKm (hY3 i k)
  have haJ := hbasic (fun ω => Y i ω j - muY j) haJm (hY3 i j)
  have hbKi := hbasic (fun ω => G i ω k - muY k) hbKm (hG3 i k)
  have hbJi := hbasic (fun ω => G i ω j - muY j) hbJm (hG3 i j)
  have hsum1 : ∀ (l : Fin p) (x : Fin p → ℝ),
      (∑ a, (if a = l then (1:ℝ) else 0) * x a) = x l := by
    intro l x
    rw [Finset.sum_eq_single l]
    · simp
    · intro b _ hb
      rw [if_neg hb, zero_mul]
    · intro hl
      exact absurd (Finset.mem_univ l) hl
  have hbKmean : ∫ ω, G i ω k - muY k ∂P = 0 := by
    have h := (hmoment (fun a => if a = k then (1:ℝ) else 0)).1
    have hfun : (fun ω => ∑ a, (if a = k then (1:ℝ) else 0) * (G i ω a - muY a))
        = fun ω => G i ω k - muY k := by
      funext ω
      exact hsum1 k (fun a => G i ω a - muY a)
    simpa only [hfun] using h
  have hbJmean : ∫ ω, G i ω j - muY j ∂P = 0 := by
    have h := (hmoment (fun a => if a = j then (1:ℝ) else 0)).1
    have hfun : (fun ω => ∑ a, (if a = j then (1:ℝ) else 0) * (G i ω a - muY a))
        = fun ω => G i ω j - muY j := by
      funext ω
      exact hsum1 j (fun a => G i ω a - muY a)
    simpa only [hfun] using h
  have hsymm : ∀ l m : Fin p, covY P muY Y i l m = covY P muY Y i m l := by
    intro l m
    simp only [covY]
    congr 1
    funext ω
    ring
  have hQ1 : ∀ (l m : Fin p),
      (∑ a, ∑ b, (if a = l then (1:ℝ) else 0) * covY P muY Y i a b * (if b = m then (1:ℝ) else 0))
        = covY P muY Y i l m := by
    intro l m
    rw [Finset.sum_eq_single l]
    · rw [Finset.sum_eq_single m]
      · simp
      · intro b _ hb
        rw [if_neg hb, mul_zero]
      · intro hm
        exact absurd (Finset.mem_univ m) hm
    · intro a _ ha
      simp [ha]
    · intro hl
      exact absurd (Finset.mem_univ l) hl
  set uP : Fin p → ℝ := fun a => (if a = k then (1:ℝ) else 0) + (if a = j then (1:ℝ) else 0) with huP
  set uM : Fin p → ℝ := fun a => (if a = k then (1:ℝ) else 0) - (if a = j then (1:ℝ) else 0) with huM
  have hsumP' : ∀ ω : Ω, (∑ a, uP a * (G i ω a - muY a))
      = (G i ω k - muY k) + (G i ω j - muY j) := by
    intro ω
    rw [huP]
    simp only [add_mul, Finset.sum_add_distrib]
    rw [hsum1 k (fun a => G i ω a - muY a), hsum1 j (fun a => G i ω a - muY a)]
  have hsumM' : ∀ ω : Ω, (∑ a, uM a * (G i ω a - muY a))
      = (G i ω k - muY k) - (G i ω j - muY j) := by
    intro ω
    rw [huM]
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [hsum1 k (fun a => G i ω a - muY a), hsum1 j (fun a => G i ω a - muY a)]
  have hbPlus : ∫ ω, ((G i ω k - muY k) + (G i ω j - muY j)) ^ 2 ∂P
      = ∑ a, ∑ b, uP a * covY P muY Y i a b * uP b := by
    simpa only [hsumP'] using (hmoment uP).2
  have hbMinus : ∫ ω, ((G i ω k - muY k) - (G i ω j - muY j)) ^ 2 ∂P
      = ∑ a, ∑ b, uM a * covY P muY Y i a b * uM b := by
    simpa only [hsumM'] using (hmoment uM).2
  have hQPu : (∑ a, ∑ b, uP a * covY P muY Y i a b * uP b)
      = covY P muY Y i k k + covY P muY Y i k j + covY P muY Y i j k + covY P muY Y i j j := by
    rw [huP]
    simp only [add_mul, mul_add, Finset.sum_add_distrib]
    rw [hQ1 k k, hQ1 k j, hQ1 j k, hQ1 j j]
    ring
  have hQMu : (∑ a, ∑ b, uM a * covY P muY Y i a b * uM b)
      = covY P muY Y i k k - covY P muY Y i k j - covY P muY Y i j k + covY P muY Y i j j := by
    rw [huM]
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
    rw [hQ1 k k, hQ1 k j, hQ1 j k, hQ1 j j]
    ring
  have hPlusInt : Integrable (fun ω => ((G i ω k - muY k) + (G i ω j - muY j)) ^ 2) P := by
    refine Integrable.mono'
      (g := fun ω => 2 * ((G i ω k - muY k) ^ 2) + 2 * ((G i ω j - muY j) ^ 2) + 1) ?_ ?_ ?_
    · exact (((hbKi.2.const_mul 2).add (hbJi.2.const_mul 2)).add (integrable_const 1))
    · exact ((continuous_id.pow 2).measurable.comp (hbKm.add hbJm)).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [sq_nonneg ((G i ω k - muY k) - (G i ω j - muY j))]
  have hMinusInt : Integrable (fun ω => ((G i ω k - muY k) - (G i ω j - muY j)) ^ 2) P := by
    refine Integrable.mono'
      (g := fun ω => 2 * ((G i ω k - muY k) ^ 2) + 2 * ((G i ω j - muY j) ^ 2) + 1) ?_ ?_ ?_
    · exact (((hbKi.2.const_mul 2).add (hbJi.2.const_mul 2)).add (integrable_const 1))
    · exact ((continuous_id.pow 2).measurable.comp (hbKm.sub hbJm)).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [sq_nonneg ((G i ω k - muY k) + (G i ω j - muY j))]
  have hdiff : ∫ ω, (((G i ω k - muY k) + (G i ω j - muY j)) ^ 2
      - ((G i ω k - muY k) - (G i ω j - muY j)) ^ 2) ∂P
      = 4 * ∫ ω, (G i ω k - muY k) * (G i ω j - muY j) ∂P := by
    have hpt : (fun ω => ((G i ω k - muY k) + (G i ω j - muY j)) ^ 2
        - ((G i ω k - muY k) - (G i ω j - muY j)) ^ 2)
        = fun ω => 4 * ((G i ω k - muY k) * (G i ω j - muY j)) := by
      funext ω
      ring
    rw [hpt, integral_const_mul]
  have hbKbJ : ∫ ω, (G i ω k - muY k) * (G i ω j - muY j) ∂P = covY P muY Y i k j := by
    have hsub : ∫ ω, (((G i ω k - muY k) + (G i ω j - muY j)) ^ 2
        - ((G i ω k - muY k) - (G i ω j - muY j)) ^ 2) ∂P
        = (∑ a, ∑ b, uP a * covY P muY Y i a b * uP b)
          - (∑ a, ∑ b, uM a * covY P muY Y i a b * uM b) := by
      rw [integral_sub hPlusInt hMinusInt, hbPlus, hbMinus]
    have h1 : 4 * ∫ ω, (G i ω k - muY k) * (G i ω j - muY j) ∂P
        = covY P muY Y i k k + covY P muY Y i k j + covY P muY Y i j k + covY P muY Y i j j
          - (covY P muY Y i k k - covY P muY Y i k j - covY P muY Y i j k
            + covY P muY Y i j j) := by
      rw [← hdiff, hsub, hQPu, hQMu]
    have hsym2 := hsymm k j
    linarith
  have hint_const : ∀ c : ℝ, ∫ x : Ω, c ∂P = c := by
    intro c
    rw [integral_const]
    simp [Measure.real]
  have hYintk : Integrable (fun ω => Y i ω k) P := by
    have h := haK.1.add (integrable_const (muY k))
    have h3 : Integrable (fun ω => Y i ω k - muY k + muY k) P := h
    rw [show (fun ω => Y i ω k - muY k + muY k) = fun ω => Y i ω k from
      funext (fun ω => by ring)] at h3
    exact h3
  have hYintj : Integrable (fun ω => Y i ω j) P := by
    have h := haJ.1.add (integrable_const (muY j))
    have h3 : Integrable (fun ω => Y i ω j - muY j + muY j) P := h
    rw [show (fun ω => Y i ω j - muY j + muY j) = fun ω => Y i ω j from
      funext (fun ω => by ring)] at h3
    exact h3
  have haKmean : ∫ ω, Y i ω k - muY k ∂P = 0 := by
    rw [integral_sub hYintk (integrable_const (muY k))]
    simp only [hYmean i k, hint_const]
    ring
  have haJmean : ∫ ω, Y i ω j - muY j ∂P = 0 := by
    rw [integral_sub hYintj (integrable_const (muY j))]
    simp only [hYmean i j, hint_const]
    ring
  have hcross1 : ∫ ω, (Y i ω k - muY k) * (G i ω j - muY j) ∂P = 0 := by
    have hne : (Sum.inr (Sum.inl i) : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) ≠
        Sum.inr (Sum.inr (Sum.inr i)) := by simp
    have hind : jointFam X Y F G (Sum.inr (Sum.inl i)) ⟂ᵢ[P]
        jointFam X Y F G (Sum.inr (Sum.inr (Sum.inr i))) := hindep.indepFun hne
    have hind' : Y i ⟂ᵢ[P] G i := hind
    have hkey := IndepFun.integral_fun_comp_mul_comp (μ := P) (X := Y i) (Y := G i)
      (f := fun v : Fin p → ℝ => v k - muY k) (g := fun v : Fin p → ℝ => v j - muY j) hind'
      (hYm i).aemeasurable (hGm i).aemeasurable
      ((measurable_pi_apply k).sub measurable_const).aestronglyMeasurable
      ((measurable_pi_apply j).sub measurable_const).aestronglyMeasurable
    simpa [haKmean, hbJmean] using hkey
  have hcross2 : ∫ ω, (G i ω k - muY k) * (Y i ω j - muY j) ∂P = 0 := by
    have hne : (Sum.inr (Sum.inl i) : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) ≠
        Sum.inr (Sum.inr (Sum.inr i)) := by simp
    have hind : jointFam X Y F G (Sum.inr (Sum.inr (Sum.inr i))) ⟂ᵢ[P]
        jointFam X Y F G (Sum.inr (Sum.inl i)) := hindep.indepFun (Ne.symm hne)
    have hind' : G i ⟂ᵢ[P] Y i := hind
    have hkey := IndepFun.integral_fun_comp_mul_comp (μ := P) (X := G i) (Y := Y i)
      (f := fun v : Fin p → ℝ => v k - muY k) (g := fun v : Fin p → ℝ => v j - muY j) hind'
      (hGm i).aemeasurable (hYm i).aemeasurable
      ((measurable_pi_apply k).sub measurable_const).aestronglyMeasurable
      ((measurable_pi_apply j).sub measurable_const).aestronglyMeasurable
    simpa [hbKmean, haJmean] using hkey
  have hmulint : ∀ u v : Ω → ℝ, Measurable u → Measurable v →
      Integrable (fun ω => u ω ^ 2) P → Integrable (fun ω => v ω ^ 2) P →
      Integrable (fun ω => u ω * v ω) P := by
    intro u v hum hvm hu2 hv2
    refine Integrable.mono' (g := fun ω => u ω ^ 2 + v ω ^ 2 + 1) ?_ ?_ ?_
    · exact (hu2.add hv2).add (integrable_const 1)
    · exact (hum.mul hvm).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_eq_abs, abs_mul]
      nlinarith [sq_abs (u ω), sq_abs (v ω), sq_nonneg (|u ω| - |v ω|)]
  have haKaJint : Integrable (fun ω => (Y i ω k - muY k) * (Y i ω j - muY j)) P :=
    hmulint _ _ haKm haJm haK.2 haJ.2
  have haKbJint : Integrable (fun ω => (Y i ω k - muY k) * (G i ω j - muY j)) P :=
    hmulint _ _ haKm hbJm haK.2 hbJi.2
  have hbKaJint : Integrable (fun ω => (G i ω k - muY k) * (Y i ω j - muY j)) P :=
    hmulint _ _ hbKm haJm hbKi.2 haJ.2
  have hbKbJint : Integrable (fun ω => (G i ω k - muY k) * (G i ω j - muY j)) P :=
    hmulint _ _ hbKm hbJm hbKi.2 hbJi.2
  set φk : Ω → ℝ := fun ω => Real.sqrt v * (Y i ω k - muY k) + Real.sqrt (1 - v) * (G i ω k - muY k) with hφk
  set φj : Ω → ℝ := fun ω => Real.sqrt v * (Y i ω j - muY j) + Real.sqrt (1 - v) * (G i ω j - muY j) with hφj
  set g1 : Ω → ℝ := fun ω => v * ((Y i ω k - muY k) * (Y i ω j - muY j)) with hg1
  set g2 : Ω → ℝ := fun ω => (Real.sqrt v * Real.sqrt (1 - v)) *
    ((Y i ω k - muY k) * (G i ω j - muY j)) with hg2
  set g3 : Ω → ℝ := fun ω => (Real.sqrt (1 - v) * Real.sqrt v) *
    ((G i ω k - muY k) * (Y i ω j - muY j)) with hg3
  set g4 : Ω → ℝ := fun ω => (1 - v) * ((G i ω k - muY k) * (G i ω j - muY j)) with hg4
  have hφkint : Integrable φk P := by
    rw [hφk]
    exact (haK.1.const_mul (Real.sqrt v)).add (hbKi.1.const_mul (Real.sqrt (1 - v)))
  have hφjint : Integrable φj P := by
    rw [hφj]
    exact (haJ.1.const_mul (Real.sqrt v)).add (hbJi.1.const_mul (Real.sqrt (1 - v)))
  have hT1 : Integrable g1 P := haKaJint.const_mul v
  have hT2 : Integrable g2 P := haKbJint.const_mul _
  have hT3 : Integrable g3 P := hbKaJint.const_mul _
  have hT4 : Integrable g4 P := hbKbJint.const_mul _
  have hptφ : ∀ ω : Ω, φk ω * φj ω = g1 ω + g2 ω + g3 ω + g4 ω := by
    have key : ∀ (a b c d sv sw : ℝ), (sv * a + sw * b) * (sv * c + sw * d)
        = sv * sv * (a * c) + sv * sw * (a * d) + sw * sv * (b * c) + sw * sw * (b * d) := by
      intro a b c d sv sw
      ring
    have hv' : Real.sqrt v * Real.sqrt v = v := by
      rw [← sq, Real.sq_sqrt hv0]
    have hw' : Real.sqrt (1 - v) * Real.sqrt (1 - v) = 1 - v := by
      rw [← sq, Real.sq_sqrt (show (0:ℝ) ≤ 1 - v by linarith)]
    intro ω
    rw [hφk, hφj]
    simp only []
    rw [key (Y i ω k - muY k) (G i ω k - muY k) (Y i ω j - muY j) (G i ω j - muY j)]
    rw [hv', hw']
  have hφφI : Integrable (fun ω => φk ω * φj ω) P := by
    rw [show (fun ω => φk ω * φj ω) = fun ω => g1 ω + g2 ω + g3 ω + g4 ω from funext hptφ]
    exact ((hT1.add hT2).add hT3).add hT4
  have c1 : ∫ ω, g1 ω ∂P = v * covY P muY Y i k j := by
    rw [show (∫ ω, g1 ω ∂P) = ∫ ω, v * ((Y i ω k - muY k) * (Y i ω j - muY j)) ∂P from by
      rw [hg1]]
    rw [integral_const_mul]
    rfl
  have c2 : ∫ ω, g2 ω ∂P = 0 := by
    rw [show (∫ ω, g2 ω ∂P) = ∫ ω, (Real.sqrt v * Real.sqrt (1 - v)) *
      ((Y i ω k - muY k) * (G i ω j - muY j)) ∂P from by rw [hg2]]
    rw [integral_const_mul, hcross1, mul_zero]
  have c3 : ∫ ω, g3 ω ∂P = 0 := by
    rw [show (∫ ω, g3 ω ∂P) = ∫ ω, (Real.sqrt (1 - v) * Real.sqrt v) *
      ((G i ω k - muY k) * (Y i ω j - muY j)) ∂P from by rw [hg3]]
    rw [integral_const_mul, hcross2, mul_zero]
  have c4 : ∫ ω, g4 ω ∂P = (1 - v) * covY P muY Y i k j := by
    rw [show (∫ ω, g4 ω ∂P) = ∫ ω, (1 - v) *
      ((G i ω k - muY k) * (G i ω j - muY j)) ∂P from by rw [hg4]]
    rw [integral_const_mul, hbKbJ]
  have hφφ : ∫ ω, φk ω * φj ω ∂P = covY P muY Y i k j := by
    rw [show (fun ω => φk ω * φj ω) = fun ω => g1 ω + g2 ω + g3 ω + g4 ω from funext hptφ]
    have e1 : ∫ ω, g1 ω + g2 ω + g3 ω + g4 ω ∂P
        = ∫ ω, g1 ω + g2 ω + g3 ω ∂P + ∫ ω, g4 ω ∂P :=
      integral_add ((hT1.add hT2).add hT3) hT4
    have e2 : ∫ ω, g1 ω + g2 ω + g3 ω ∂P = ∫ ω, g1 ω + g2 ω ∂P + ∫ ω, g3 ω ∂P :=
      integral_add (hT1.add hT2) hT3
    have e3 : ∫ ω, g1 ω + g2 ω ∂P = ∫ ω, g1 ω ∂P + ∫ ω, g2 ω ∂P := integral_add hT1 hT2
    rw [e1, e2, e3, c1, c2, c3, c4]
    ring
  set cc : ℝ := (Real.sqrt (m : ℝ))⁻¹ * delta n m with hcc
  have hPu : P.real Set.univ = 1 := by simp [Measure.real]
  have hkk : Real.sqrt t * (2 * Real.sqrt t)⁻¹ = 2⁻¹ := by
    have h : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht0).ne'
    field_simp
  have hll : Real.sqrt (1 - t) * (2 * Real.sqrt (1 - t))⁻¹ = 2⁻¹ := by
    have h : Real.sqrt (1 - t) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
    field_simp
  set K1 : ℝ := cc * cc * (Real.sqrt t * (2 * Real.sqrt t)⁻¹) with hK1
  set K2 : ℝ := cc * cc * (Real.sqrt t * (2 * Real.sqrt (1 - t))⁻¹) with hK2
  set K3 : ℝ := cc * cc * (Real.sqrt (1 - t) * (2 * Real.sqrt t)⁻¹) with hK3
  set K4 : ℝ := cc * cc * (Real.sqrt (1 - t) * (2 * Real.sqrt (1 - t))⁻¹) with hK4
  set F1 : Ω × Ω → ℝ := fun x => K1 * (φk x.1 * φj x.1) with hF1
  set F2 : Ω × Ω → ℝ := fun x => (K2 * φk x.1) * (G i x.2 j - muY j) with hF2
  set F3 : Ω × Ω → ℝ := fun x => (K3 * φj x.1) * (G i x.2 k - muY k) with hF3
  set F4 : Ω × Ω → ℝ := fun x => K4 * ((G i x.2 k - muY k) * (G i x.2 j - muY j)) with hF4
  have hdec : ∀ x : Ω × Ω,
      (cc * (Real.sqrt t * φk x.1 + Real.sqrt (1 - t) * (G i x.2 k - muY k))) *
        (cc * ((2 * Real.sqrt t)⁻¹ * φj x.1 - (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j)))
      = F1 x - F2 x + F3 x - F4 x := by
    intro x
    simp only [hF1, hF2, hF3, hF4, hK1, hK2, hK3, hK4]
    ring
  have hi1 : Integrable F1 (P.prod P) := by
    rw [hF1]
    have h := Integrable.mul_prod (μ := P) (ν := P)
      (f := fun y : Ω => K1 * (φk y * φj y)) (g := fun _ : Ω => (1:ℝ))
      (hφφI.const_mul K1) (integrable_const (1:ℝ))
    simpa only [mul_one] using h
  have hi2 : Integrable F2 (P.prod P) := by
    rw [hF2]
    exact Integrable.mul_prod (μ := P) (ν := P)
      (f := fun y : Ω => K2 * φk y) (g := fun y : Ω => G i y j - muY j)
      (hφkint.const_mul K2) hbJi.1
  have hi3 : Integrable F3 (P.prod P) := by
    rw [hF3]
    exact Integrable.mul_prod (μ := P) (ν := P)
      (f := fun y : Ω => K3 * φj y) (g := fun y : Ω => G i y k - muY k)
      (hφjint.const_mul K3) hbKi.1
  have hi4 : Integrable F4 (P.prod P) := by
    rw [hF4]
    have h := Integrable.mul_prod (μ := P) (ν := P)
      (f := fun _ : Ω => (1:ℝ)) (g := fun y : Ω => K4 * ((G i y k - muY k) * (G i y j - muY j)))
      (integrable_const (1:ℝ)) (hbKbJint.const_mul K4)
    simpa only [one_mul] using h
  have hI1 : ∫ x : Ω × Ω, F1 x ∂(P.prod P) = K1 * covY P muY Y i k j := by
    rw [hF1]
    rw [show (∫ x : Ω × Ω, K1 * (φk x.1 * φj x.1) ∂(P.prod P))
        = P.real Set.univ • ∫ y : Ω, K1 * (φk y * φj y) ∂P from
      integral_fun_fst (μ := P) (ν := P) (f := fun y : Ω => K1 * (φk y * φj y))]
    rw [hPu, one_smul, integral_const_mul, hφφ]
  have hI2 : ∫ x : Ω × Ω, F2 x ∂(P.prod P) = 0 := by
    rw [hF2]
    rw [show (∫ x : Ω × Ω, (K2 * φk x.1) * (G i x.2 j - muY j) ∂(P.prod P))
        = (∫ y : Ω, K2 * φk y ∂P) * (∫ y : Ω, G i y j - muY j ∂P) from
      integral_prod_mul (μ := P) (ν := P) (f := fun y : Ω => K2 * φk y)
        (g := fun y : Ω => G i y j - muY j)]
    rw [hbJmean, mul_zero]
  have hI3 : ∫ x : Ω × Ω, F3 x ∂(P.prod P) = 0 := by
    rw [hF3]
    rw [show (∫ x : Ω × Ω, (K3 * φj x.1) * (G i x.2 k - muY k) ∂(P.prod P))
        = (∫ y : Ω, K3 * φj y ∂P) * (∫ y : Ω, G i y k - muY k ∂P) from
      integral_prod_mul (μ := P) (ν := P) (f := fun y : Ω => K3 * φj y)
        (g := fun y : Ω => G i y k - muY k)]
    rw [hbKmean, mul_zero]
  have hI4 : ∫ x : Ω × Ω, F4 x ∂(P.prod P) = K4 * covY P muY Y i k j := by
    rw [hF4]
    rw [show (∫ x : Ω × Ω, K4 * ((G i x.2 k - muY k) * (G i x.2 j - muY j)) ∂(P.prod P))
        = P.real Set.univ •
          ∫ y : Ω, K4 * ((G i y k - muY k) * (G i y j - muY j)) ∂P from
      integral_fun_snd (μ := P) (ν := P)
        (f := fun y : Ω => K4 * ((G i y k - muY k) * (G i y j - muY j)))]
    rw [hPu, one_smul, integral_const_mul, hbKbJ]
  have hiAll : Integrable (fun x : Ω × Ω =>
      (cc * (Real.sqrt t * φk x.1 + Real.sqrt (1 - t) * (G i x.2 k - muY k))) *
        (cc * ((2 * Real.sqrt t)⁻¹ * φj x.1 - (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j))))
      (P.prod P) := by
    rw [show (fun x : Ω × Ω =>
        (cc * (Real.sqrt t * φk x.1 + Real.sqrt (1 - t) * (G i x.2 k - muY k))) *
          (cc * ((2 * Real.sqrt t)⁻¹ * φj x.1 - (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j))))
        = fun x : Ω × Ω => F1 x - F2 x + F3 x - F4 x from funext hdec]
    exact ((hi1.sub hi2).add hi3).sub hi4
  have htotal : ∫ x : Ω × Ω,
      (cc * (Real.sqrt t * φk x.1 + Real.sqrt (1 - t) * (G i x.2 k - muY k))) *
        (cc * ((2 * Real.sqrt t)⁻¹ * φj x.1 - (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j)))
      ∂(P.prod P) = 0 := by
    rw [show (fun x : Ω × Ω =>
        (cc * (Real.sqrt t * φk x.1 + Real.sqrt (1 - t) * (G i x.2 k - muY k))) *
          (cc * ((2 * Real.sqrt t)⁻¹ * φj x.1 - (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j))))
        = fun x : Ω × Ω => F1 x - F2 x + F3 x - F4 x from funext hdec]
    have s1 : ∫ x : Ω × Ω, F1 x - F2 x + F3 x - F4 x ∂(P.prod P)
        = ∫ x : Ω × Ω, F1 x - F2 x + F3 x ∂(P.prod P) - ∫ x : Ω × Ω, F4 x ∂(P.prod P) :=
      integral_sub ((hi1.sub hi2).add hi3) hi4
    have s2 : ∫ x : Ω × Ω, F1 x - F2 x + F3 x ∂(P.prod P)
        = ∫ x : Ω × Ω, (F1 x - F2 x) ∂(P.prod P) + ∫ x : Ω × Ω, F3 x ∂(P.prod P) :=
      integral_add (hi1.sub hi2) hi3
    have s3 : ∫ x : Ω × Ω, (F1 x - F2 x) ∂(P.prod P)
        = ∫ x : Ω × Ω, F1 x ∂(P.prod P) - ∫ x : Ω × Ω, F2 x ∂(P.prod P) :=
      integral_sub hi1 hi2
    rw [s1, s2, s3, hI1, hI2, hI3, hI4]
    have hK : K1 = K4 := by
      rw [hK1, hK4, hkk, hll]
    rw [hK]
    ring
  exact ⟨hiAll, htotal⟩
  /- @proof-region region.target-node.session.e967d7a385dc882f end -/

end

end Statlib.Imported

