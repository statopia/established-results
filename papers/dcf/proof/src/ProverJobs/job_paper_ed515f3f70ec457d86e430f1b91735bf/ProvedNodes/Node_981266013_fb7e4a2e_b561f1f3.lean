import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_478009398_9cbe8093_66d7da48

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
theorem statopia_math_node_981266013_fb7e4a2e : ∀ (phi0 : ℝ → ℝ) (hphi0_cont : ContDiff ℝ 3 phi0)
    (hphi0_left : ∀ z : ℝ, z ≤ 0 → phi0 z = 1)
    (hphi0_right : ∀ z : ℝ, 1 ≤ z → phi0 z = 0)
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n m p : ℕ) (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
    (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
    (phi1 phi2 : ℝ) (y : Fin p → ℝ) (v : ℝ)
    (hp : 0 < p) (hphi1 : 1 ≤ phi1) (hphi2 : 1 ≤ phi2) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hXm : ∀ i : Fin n, Measurable (X i)) (hYm : ∀ i : Fin m, Measurable (Y i))
    (hFm : ∀ i : Fin n, Measurable (F i)) (hGm : ∀ i : Fin m, Measurable (G i))
    (hX2 : ∀ (i : Fin n) (j : Fin p), MemLp (fun ω => X i ω j) 2 P)
    (hY2 : ∀ (i : Fin m) (j : Fin p), MemLp (fun ω => Y i ω j) 2 P)
    (hX3 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |X i ω j - muX j| ^ 3) P)
    (hY3 : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => |Y i ω j - muY j| ^ 3) P)
    (hF3 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |F i ω j - muX j| ^ 3) P)
    (hG3 : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => |G i ω j - muY j| ^ 3) P),
    (let phi : ℝ := min phi1 phi2
     let beta : ℝ := phi * Real.log (p : ℝ)
     let Zstar : ℝ → Ω × Ω → Fin n → Fin p → ℝ := fun t x i j =>
       (Real.sqrt (n : ℝ))⁻¹ *
         (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))
           + Real.sqrt (1 - t) * (F i x.2 j - muX j))
     let Zstarstar : ℝ → Ω × Ω → Fin m → Fin p → ℝ := fun t x i j =>
       (Real.sqrt (m : ℝ))⁻¹ * delta n m *
         (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))
           + Real.sqrt (1 - t) * (G i x.2 j - muY j))
     let Z : ℝ → Ω × Ω → Fin p → ℝ := fun t x j =>
       (∑ i : Fin n, Zstar t x i j) + (∑ i : Fin m, Zstarstar t x i j)
     let Zdotstar : ℝ → Ω × Ω → Fin n → Fin p → ℝ := fun t x i j =>
       (Real.sqrt (n : ℝ))⁻¹ *
         ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))
           - (2 * Real.sqrt (1 - t))⁻¹ * (F i x.2 j - muX j))
     let Zdot : ℝ → Ω × Ω → Fin m → Fin p → ℝ := fun t x i j =>
       (Real.sqrt (m : ℝ))⁻¹ * delta n m *
         ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))
           - (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j))
     let kappa : (Fin p → ℝ) → ℝ := fun w =>
       phi0 (phi * (beta⁻¹ * Real.log (∑ j : Fin p, Real.exp (beta * (w j - y j)))))
     let Istar : Ω × Ω → ℝ := fun x =>
       ∫ t in (0 : ℝ)..1,
         ∑ j : Fin p, ∑ i : Fin n,
           (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdotstar t x i j
     let Istarstar : Ω × Ω → ℝ := fun x =>
       ∫ t in (0 : ℝ)..1,
         ∑ j : Fin p, ∑ i : Fin m,
           (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdot t x i j
     Integrable Istar (P.prod P) ∧ Integrable Istarstar (P.prod P)) := by
  /- @proof-region region.target-node.session.ee65da1bf2281645 begin -/
  classical
  intro phi0 hphi0_cont hphi0_left hphi0_right Ω instΩ P instP n m p delta muX muY X Y F G phi1 phi2 y v hp hphi1 hphi2 hv0 hv1 hXm hYm hFm hGm hX2 hY2 hX3 hY3 hF3 hG3
  dsimp only
  set phi : ℝ := min phi1 phi2 with hphi
  set beta : ℝ := phi * Real.log (p : ℝ) with hbeta
  set kappa : (Fin p → ℝ) → ℝ :=
    fun w => phi0 (phi * (beta⁻¹ * Real.log (∑ j : Fin p, Real.exp (beta * (w j - y j))))) with hkappa
  have hboundPhi0 : ∃ M0 : ℝ, 0 ≤ M0 ∧ ∀ z : ℝ, |(fderiv ℝ phi0 z) (1 : ℝ)| ≤ M0 := by
    have hcont_eval : Continuous fun q : ℝ × ℝ => (fderiv ℝ phi0 q.1) q.2 :=
      (hphi0_cont.contDiff_fderiv_apply (m := 0) (n := 3) (by norm_num)).continuous
    set g : ℝ → ℝ := fun z => (fderiv ℝ phi0 z) (1 : ℝ) with hg
    have hgcont : Continuous g :=
      hcont_eval.comp (by fun_prop : Continuous fun z : ℝ => (z, (1 : ℝ)))
    have hgneg : ∀ z : ℝ, z < 0 → g z = 0 := by
      intro z hz
      have hmem : Set.Iio (0 : ℝ) ∈ nhds z := isOpen_Iio.mem_nhds hz
      have hev : phi0 =ᶠ[nhds z] fun _ : ℝ => (1 : ℝ) := by
        filter_upwards [hmem] with w hw
        exact hphi0_left w hw.le
      have h2 : HasFDerivAt (fun _ : ℝ => (1 : ℝ)) (0 : ℝ →L[ℝ] ℝ) z := hasFDerivAt_const 1 z
      have h1 : HasFDerivAt phi0 (0 : ℝ →L[ℝ] ℝ) z := h2.congr_of_eventuallyEq hev
      have h3 : fderiv ℝ phi0 z = 0 := h1.fderiv
      show (fderiv ℝ phi0 z) (1 : ℝ) = 0
      rw [h3]
      simp
    have hgpos : ∀ z : ℝ, 1 < z → g z = 0 := by
      intro z hz
      have hmem : Set.Ioi (1 : ℝ) ∈ nhds z := isOpen_Ioi.mem_nhds hz
      have hev : phi0 =ᶠ[nhds z] fun _ : ℝ => (0 : ℝ) := by
        filter_upwards [hmem] with w hw
        exact hphi0_right w hw.le
      have h2 : HasFDerivAt (fun _ : ℝ => (0 : ℝ)) (0 : ℝ →L[ℝ] ℝ) z := hasFDerivAt_const 0 z
      have h1 : HasFDerivAt phi0 (0 : ℝ →L[ℝ] ℝ) z := h2.congr_of_eventuallyEq hev
      have h3 : fderiv ℝ phi0 z = 0 := h1.fderiv
      show (fderiv ℝ phi0 z) (1 : ℝ) = 0
      rw [h3]
      simp
    have hgCO : ContinuousOn (fun z => |g z|) (Set.Icc (0 : ℝ) 1) :=
      fun z _ => (continuous_abs.comp hgcont).continuousAt.continuousWithinAt
    obtain ⟨z0, hz0, hmax⟩ := isCompact_Icc.exists_isMaxOn (⟨(0 : ℝ), by norm_num⟩ : (Set.Icc (0 : ℝ) 1).Nonempty) hgCO
    refine ⟨max (|g z0|) 0, le_max_right _ _, ?_⟩
    intro z
    change |g z| ≤ max (|g z0|) 0
    by_cases h0 : z < 0
    · rw [hgneg z h0]
      simp
    · have hz0' : 0 ≤ z := not_lt.mp h0
      by_cases h1 : z < 1
      · exact (hmax ⟨hz0', h1.le⟩).trans (le_max_left _ _)
      · have h2 : 1 ≤ z := not_lt.mp h1
        by_cases h3 : z = 1
        · subst h3
          exact (hmax ⟨by norm_num, le_rfl⟩).trans (le_max_left _ _)
        · rw [hgpos z (lt_of_le_of_ne h2 (Ne.symm h3))]
          simp
  obtain ⟨Mκ, hMκ0, hMκ, hcontκ⟩ :=
    statopia_math_node_478009398_9cbe8093 p hp phi0 hphi0_cont hphi0_left hphi0_right phi beta
      (by
        rw [hphi]
        first
          | exact le_min hphi1 hphi2
          | exact le_min.mpr ⟨hphi1, hphi2⟩)
      (by
        rw [hbeta]
        have h1 : (1 : ℝ) ≤ phi := by
          rw [hphi]
          first
            | exact le_min hphi1 hphi2
            | exact le_min.mpr ⟨hphi1, hphi2⟩
        have hpos : (0 : ℝ) ≤ phi := by linarith
        have hlog : (0 : ℝ) ≤ Real.log (p : ℝ) := by
          first
            | exact Real.log_natCast_nonneg p
            | exact Real.log_nonneg (by
                have hp1 : (1 : ℕ) ≤ p := hp
                exact_mod_cast hp1)
        exact mul_nonneg hpos hlog)
      y
  have hderiv : ∃ M : ℝ, 0 ≤ M ∧ ∀ w : Fin p → ℝ, ‖fderiv ℝ kappa w‖ ≤ M :=
    ⟨Mκ, hMκ0, hMκ⟩
  have hPne : P ≠ 0 := by
    intro h
    have h1 : P Set.univ = 1 := measure_univ
    rw [h] at h1
    simp at h1
  have hcube : ∀ a : ℝ, 0 ≤ a → a ≤ 1 + a ^ 3 := by
    intro a ha
    by_cases h : a ≤ 1
    · nlinarith [pow_nonneg ha 3]
    · have h1 : 1 < a := not_le.mp h
      nlinarith [mul_nonneg (mul_nonneg ha (by linarith : (0 : ℝ) ≤ a - 1)) (by linarith : (0 : ℝ) ≤ a + 1)]
  have hL1 : ∀ (f : Ω → ℝ), Integrable (fun ω => |f ω| ^ 3) P → Measurable f →
      Integrable (fun ω => |f ω|) P := by
    intro f h3 hm
    have hm' : AEStronglyMeasurable (fun ω => |f ω|) P :=
      (continuous_abs.measurable.comp hm).aestronglyMeasurable
    have hi : Integrable (fun ω => 1 + |f ω| ^ 3) P := (integrable_const (1 : ℝ)).add h3
    have hb : ∀ᵐ ω ∂P, ‖(|f ω| : ℝ)‖ ≤ 1 + |f ω| ^ 3 := by
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg (f ω))]
      exact hcube _ (abs_nonneg _)
    exact Integrable.mono' hi hm' hb
  have hmX : ∀ (i : Fin n) (j : Fin p), Measurable (fun ω => X i ω j) :=
    fun i j => (continuous_apply j).measurable.comp (hXm i)
  have hmY : ∀ (i : Fin m) (j : Fin p), Measurable (fun ω => Y i ω j) :=
    fun i j => (continuous_apply j).measurable.comp (hYm i)
  have hmF : ∀ (i : Fin n) (j : Fin p), Measurable (fun ω => F i ω j) :=
    fun i j => (continuous_apply j).measurable.comp (hFm i)
  have hmG : ∀ (i : Fin m) (j : Fin p), Measurable (fun ω => G i ω j) :=
    fun i j => (continuous_apply j).measurable.comp (hGm i)
  have hXL1 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |X i ω j - muX j|) P :=
    fun i j => hL1 _ (hX3 i j) ((hmX i j).sub measurable_const)
  have hYL1 : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => |Y i ω j - muY j|) P :=
    fun i j => hL1 _ (hY3 i j) ((hmY i j).sub measurable_const)
  have hFL1 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |F i ω j - muX j|) P :=
    fun i j => hL1 _ (hF3 i j) ((hmF i j).sub measurable_const)
  have hGL1 : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => |G i ω j - muY j|) P :=
    fun i j => hL1 _ (hG3 i j) ((hmG i j).sub measurable_const)
  have hPXL1 : ∀ (i : Fin n) (j : Fin p), Integrable (fun x : Ω × Ω => |X i x.1 j - muX j|) (P.prod P) :=
    fun i j => (hXL1 i j).comp_fst P
  have hPYL1 : ∀ (i : Fin m) (j : Fin p), Integrable (fun x : Ω × Ω => |Y i x.1 j - muY j|) (P.prod P) :=
    fun i j => (hYL1 i j).comp_fst P
  have hPFL1 : ∀ (i : Fin n) (j : Fin p), Integrable (fun x : Ω × Ω => |F i x.1 j - muX j|) (P.prod P) :=
    fun i j => (hFL1 i j).comp_fst P
  have hPGL1 : ∀ (i : Fin m) (j : Fin p), Integrable (fun x : Ω × Ω => |G i x.1 j - muY j|) (P.prod P) :=
    fun i j => (hGL1 i j).comp_fst P
  have hPF2L1 : ∀ (i : Fin n) (j : Fin p), Integrable (fun x : Ω × Ω => |F i x.2 j - muX j|) (P.prod P) :=
    fun i j => (hFL1 i j).comp_snd P
  have hPG2L1 : ∀ (i : Fin m) (j : Fin p), Integrable (fun x : Ω × Ω => |G i x.2 j - muY j|) (P.prod P) :=
    fun i j => (hGL1 i j).comp_snd P
  have hdom1 : Integrable (fun x : Ω × Ω => ∑ j : Fin p, ∑ i : Fin n,
      (|X i x.1 j - muX j| + |F i x.1 j - muX j|)) (P.prod P) := by
    have hj : ∀ j : Fin p, Integrable (fun x : Ω × Ω => ∑ i : Fin n,
        (|X i x.1 j - muX j| + |F i x.1 j - muX j|)) (P.prod P) := by
      intro j
      have hi : ∀ i : Fin n, Integrable (fun x : Ω × Ω =>
          (|X i x.1 j - muX j| + |F i x.1 j - muX j|)) (P.prod P) :=
        fun i => (hPXL1 i j).add (hPFL1 i j)
      simpa using integrable_finset_sum (Finset.univ : Finset (Fin n)) (fun i _ => hi i)
    simpa using integrable_finset_sum (Finset.univ : Finset (Fin p)) (fun j _ => hj j)
  have hdom2 : Integrable (fun x : Ω × Ω => ∑ j : Fin p, ∑ i : Fin n, |F i x.2 j - muX j|) (P.prod P) := by
    have hj : ∀ j : Fin p, Integrable (fun x : Ω × Ω => ∑ i : Fin n, |F i x.2 j - muX j|) (P.prod P) := by
      intro j
      simpa using integrable_finset_sum (Finset.univ : Finset (Fin n)) (fun i _ => hPF2L1 i j)
    simpa using integrable_finset_sum (Finset.univ : Finset (Fin p)) (fun j _ => hj j)
  have hdom3 : Integrable (fun x : Ω × Ω => ∑ j : Fin p, ∑ i : Fin m,
      (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)) (P.prod P) := by
    have hj : ∀ j : Fin p, Integrable (fun x : Ω × Ω => ∑ i : Fin m,
        (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)) (P.prod P) := by
      intro j
      have hi : ∀ i : Fin m, Integrable (fun x : Ω × Ω =>
          (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)) (P.prod P) :=
        fun i => (hPYL1 i j).add (hPGL1 i j)
      simpa using integrable_finset_sum (Finset.univ : Finset (Fin m)) (fun i _ => hi i)
    simpa using integrable_finset_sum (Finset.univ : Finset (Fin p)) (fun j _ => hj j)
  have hdom4 : Integrable (fun x : Ω × Ω => ∑ j : Fin p, ∑ i : Fin m, |G i x.2 j - muY j|) (P.prod P) := by
    have hj : ∀ j : Fin p, Integrable (fun x : Ω × Ω => ∑ i : Fin m, |G i x.2 j - muY j|) (P.prod P) := by
      intro j
      simpa using integrable_finset_sum (Finset.univ : Finset (Fin m)) (fun i _ => hPG2L1 i j)
    simpa using integrable_finset_sum (Finset.univ : Finset (Fin p)) (fun j _ => hj j)
  have hsqrteq : ∀ t : ℝ, 0 < t → (2 * Real.sqrt t)⁻¹ = (1 / 2) * t ^ (-(1 / 2) : ℝ) := by
    intro t ht
    have hpos : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht
    have hsqrt : Real.sqrt t = t ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow t
    have hneg : t ^ (-(1 / 2) : ℝ) = (Real.sqrt t)⁻¹ := by
      rw [hsqrt, Real.rpow_neg ht.le (1 / 2)]
    rw [hneg]
    field_simp
  have hInt1 : IntervalIntegrable (fun t : ℝ => (2 * Real.sqrt t)⁻¹) volume (0 : ℝ) 1 := by
    have hrpow : IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 2) : ℝ)) volume (0 : ℝ) 1 :=
      intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1) (r := -(1 / 2 : ℝ)) (by norm_num)
    have hconst : IntervalIntegrable (fun t : ℝ => (1 / 2) * t ^ (-(1 / 2) : ℝ)) volume (0 : ℝ) 1 :=
      hrpow.const_mul (1 / 2)
    refine IntervalIntegrable.congr ?_ hconst
    intro t ht
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact (hsqrteq t ht.1).symm
  have hInt2 : IntervalIntegrable (fun t : ℝ => (2 * Real.sqrt (1 - t))⁻¹) volume (0 : ℝ) 1 := by
    have h1 := hInt1.comp_sub_left (1 : ℝ)
    rw [show (1 : ℝ) - 0 = 1 by norm_num, show (1 : ℝ) - 1 = 0 by norm_num] at h1
    exact h1.symm
  set Cint : ℝ := ∫ t in (0 : ℝ)..1, ((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹) with hCint
  have hM1 : Integrable (fun t : ℝ => (2 * Real.sqrt t)⁻¹) (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).1 hInt1
  have hM2 : Integrable (fun t : ℝ => (2 * Real.sqrt (1 - t))⁻¹) (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).1 hInt2
  have hMsum : Integrable (fun t : ℝ => (2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    hM1.add hM2
  have hDint : Integrable (fun x : Ω × Ω => |Cint| * (Mκ * (Real.sqrt (n : ℝ))⁻¹) *
      ((∑ j : Fin p, ∑ i : Fin n, (|X i x.1 j - muX j| + |F i x.1 j - muX j|)) +
        ∑ j : Fin p, ∑ i : Fin n, |F i x.2 j - muX j|)) (P.prod P) :=
    (hdom1.add hdom2).const_mul (|Cint| * (Mκ * (Real.sqrt (n : ℝ))⁻¹))
  have hcle : ∀ a b : ℝ, |Real.sqrt v * a + Real.sqrt (1 - v) * b| ≤ |a| + |b| := by
    intro a b
    have hv1' : Real.sqrt v ≤ 1 := by
      nlinarith [Real.sq_sqrt hv0, Real.sqrt_nonneg v]
    have hv2' : Real.sqrt (1 - v) ≤ 1 := by
      nlinarith [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 - v), Real.sqrt_nonneg (1 - v)]
    have h1 : |Real.sqrt v| ≤ 1 := by
      rw [abs_of_nonneg (Real.sqrt_nonneg v)]
      exact hv1'
    have h2 : |Real.sqrt (1 - v)| ≤ 1 := by
      rw [abs_of_nonneg (Real.sqrt_nonneg (1 - v))]
      exact hv2'
    calc |Real.sqrt v * a + Real.sqrt (1 - v) * b|
        ≤ |Real.sqrt v * a| + |Real.sqrt (1 - v) * b| := abs_add_le _ _
      _ = |Real.sqrt v| * |a| + |Real.sqrt (1 - v)| * |b| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * |a| + 1 * |b| := by
          exact add_le_add (mul_le_mul_of_nonneg_right h1 (abs_nonneg a))
            (mul_le_mul_of_nonneg_right h2 (abs_nonneg b))
      _ = |a| + |b| := by ring
  let Zarg : ℝ → Ω × Ω → Fin p → ℝ := fun t x j =>
    (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ *
        (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))
          + Real.sqrt (1 - t) * (F i x.2 j - muX j)))
      + (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m *
        (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))
          + Real.sqrt (1 - t) * (G i x.2 j - muY j)))
  let Zd : ℝ → Ω × Ω → Fin n → Fin p → ℝ := fun t x i j =>
    (Real.sqrt (n : ℝ))⁻¹ *
      ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))
        - (2 * Real.sqrt (1 - t))⁻¹ * (F i x.2 j - muX j))
  let BigF : ℝ → Ω × Ω → ℝ := fun t x =>
    ∑ j : Fin p, ∑ i : Fin n, (fderiv ℝ kappa (Zarg t x)) (Pi.single j (1 : ℝ)) * Zd t x i j
  let DFun : Ω × Ω → ℝ := fun x =>
    |Cint| * (Mκ * (Real.sqrt (n : ℝ))⁻¹) *
      ((∑ j : Fin p, ∑ i : Fin n, (|X i x.1 j - muX j| + |F i x.1 j - muX j|)) +
        ∑ j : Fin p, ∑ i : Fin n, |F i x.2 j - muX j|)
  have hDint' : Integrable DFun (P.prod P) := hDint
  have habs_sum_le : ∀ (ι : Type) [Fintype ι] (g : ι → ℝ), |∑ i : ι, g i| ≤ ∑ i : ι, |g i| := by
    intro ι _ g
    simpa using Finset.abs_sum_le_sum_abs (s := (Finset.univ : Finset ι)) (f := g)
  have hsum_le : ∀ (ι : Type) [Fintype ι] (u v : ι → ℝ),
      (∀ i, u i ≤ v i) → ∑ i : ι, u i ≤ ∑ i : ι, v i := by
    intro ι _ u v h
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => h i)
  have hpull : ∀ (K : ℝ) (u : Fin p → Fin n → ℝ),
      ∑ j : Fin p, ∑ i : Fin n, K * u j i = K * ∑ j : Fin p, ∑ i : Fin n, u j i := by
    intro K u
    simp only [Finset.mul_sum]
  have hsplit : ∀ (u v : Fin p → Fin n → ℝ),
      ∑ j : Fin p, ∑ i : Fin n, (u j i + v j i)
        = (∑ j : Fin p, ∑ i : Fin n, u j i) + ∑ j : Fin p, ∑ i : Fin n, v j i := by
    intro u v
    simp only [Finset.sum_add_distrib]
  have hpt1 : ∀ x : Ω × Ω, ‖∫ t in (0 : ℝ)..1, BigF t x‖ ≤ DFun x := by
    intro x
    have hn0 : (0 : ℝ) ≤ (Real.sqrt (n : ℝ))⁻¹ := by
      rw [inv_nonneg]
      exact Real.sqrt_nonneg _
    have hS1nn : (0 : ℝ) ≤ ∑ j : Fin p, ∑ i : Fin n, (|X i x.1 j - muX j| + |F i x.1 j - muX j|) := by
      have hj : ∀ j : Fin p, (0 : ℝ) ≤ ∑ i : Fin n, (|X i x.1 j - muX j| + |F i x.1 j - muX j|) :=
        fun j => by positivity
      simpa using Finset.sum_nonneg (s := (Finset.univ : Finset (Fin p))) (fun j _ => hj j)
    have hS2nn : (0 : ℝ) ≤ ∑ j : Fin p, ∑ i : Fin n, |F i x.2 j - muX j| := by
      have hj : ∀ j : Fin p, (0 : ℝ) ≤ ∑ i : Fin n, |F i x.2 j - muX j| :=
        fun j => by positivity
      simpa using Finset.sum_nonneg (s := (Finset.univ : Finset (Fin p))) (fun j _ => hj j)
    have hpt : ∀ t : ℝ, ‖BigF t x‖ ≤ ((Mκ * (Real.sqrt (n : ℝ))⁻¹) *
        ((∑ j : Fin p, ∑ i : Fin n, (|X i x.1 j - muX j| + |F i x.1 j - muX j|)) +
          ∑ j : Fin p, ∑ i : Fin n, |F i x.2 j - muX j|)) *
        ((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹) := by
      intro t
      have ht1 : (0 : ℝ) ≤ (2 * Real.sqrt t)⁻¹ := by
        rw [inv_nonneg]
        positivity
      have ht2 : (0 : ℝ) ≤ (2 * Real.sqrt (1 - t))⁻¹ := by
        rw [inv_nonneg]
        positivity
      have hK : (0 : ℝ) ≤ Mκ * (Real.sqrt (n : ℝ))⁻¹ := mul_nonneg hMκ0 hn0
      have hLb : ∀ j : Fin p, ‖(fderiv ℝ kappa (Zarg t x)) (Pi.single j (1 : ℝ))‖ ≤ Mκ := by
        intro j
        refine (ContinuousLinearMap.unit_le_opNorm (fderiv ℝ kappa (Zarg t x))
          (Pi.single j (1 : ℝ)) ?_).trans (hMκ (Zarg t x))
        rw [Pi.norm_single]
        simp
      have hZdb : ∀ (i : Fin n) (j : Fin p), ‖Zd t x i j‖ ≤ (Real.sqrt (n : ℝ))⁻¹ *
          ((2 * Real.sqrt t)⁻¹ * (|X i x.1 j - muX j| + |F i x.1 j - muX j|)
            + (2 * Real.sqrt (1 - t))⁻¹ * |F i x.2 j - muX j|) := by
        intro i j
        have hcl : |Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)|
            ≤ |X i x.1 j - muX j| + |F i x.1 j - muX j| := hcle _ _
        have e1 : |(2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))|
            = (2 * Real.sqrt t)⁻¹ * |Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)| := by
          rw [abs_mul, abs_of_nonneg ht1]
        have e2 : |(2 * Real.sqrt (1 - t))⁻¹ * (F i x.2 j - muX j)|
            = (2 * Real.sqrt (1 - t))⁻¹ * |F i x.2 j - muX j| := by
          rw [abs_mul, abs_of_nonneg ht2]
        have hAB : |(2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))
              - (2 * Real.sqrt (1 - t))⁻¹ * (F i x.2 j - muX j)|
            ≤ (2 * Real.sqrt t)⁻¹ * |Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)|
              + (2 * Real.sqrt (1 - t))⁻¹ * |F i x.2 j - muX j| := by
          calc |(2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))
                - (2 * Real.sqrt (1 - t))⁻¹ * (F i x.2 j - muX j)|
              = |(2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))
                  + -((2 * Real.sqrt (1 - t))⁻¹ * (F i x.2 j - muX j))| := by rw [sub_eq_add_neg]
            _ ≤ |(2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))|
                  + |(2 * Real.sqrt (1 - t))⁻¹ * (F i x.2 j - muX j)| := by
                simpa using abs_add_le
                  ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)))
                  (-((2 * Real.sqrt (1 - t))⁻¹ * (F i x.2 j - muX j)))
            _ = (2 * Real.sqrt t)⁻¹ * |Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)|
                  + (2 * Real.sqrt (1 - t))⁻¹ * |F i x.2 j - muX j| := by rw [e1, e2]
        simp only [Zd, Real.norm_eq_abs, abs_mul, abs_of_nonneg hn0]
        refine mul_le_mul_of_nonneg_left ?_ hn0
        calc |(2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))
              - (2 * Real.sqrt (1 - t))⁻¹ * (F i x.2 j - muX j)|
            ≤ (2 * Real.sqrt t)⁻¹ * |Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)|
              + (2 * Real.sqrt (1 - t))⁻¹ * |F i x.2 j - muX j| := hAB
          _ ≤ (2 * Real.sqrt t)⁻¹ * (|X i x.1 j - muX j| + |F i x.1 j - muX j|)
              + (2 * Real.sqrt (1 - t))⁻¹ * |F i x.2 j - muX j| := by
              exact add_le_add (mul_le_mul_of_nonneg_left hcl ht1) le_rfl
      have hsum : ‖BigF t x‖ ≤ ∑ j : Fin p, ∑ i : Fin n,
          Mκ * ((Real.sqrt (n : ℝ))⁻¹ * ((2 * Real.sqrt t)⁻¹ * (|X i x.1 j - muX j| + |F i x.1 j - muX j|)
            + (2 * Real.sqrt (1 - t))⁻¹ * |F i x.2 j - muX j|)) := by
        have hbf : BigF t x = ∑ j : Fin p, ∑ i : Fin n,
            (fderiv ℝ kappa (Zarg t x)) (Pi.single j (1 : ℝ)) * Zd t x i j := rfl
        rw [hbf, Real.norm_eq_abs]
        have h2 : ∀ (j : Fin p) (i : Fin n),
            |(fderiv ℝ kappa (Zarg t x)) (Pi.single j (1 : ℝ)) * Zd t x i j|
            ≤ Mκ * ((Real.sqrt (n : ℝ))⁻¹ * ((2 * Real.sqrt t)⁻¹ * (|X i x.1 j - muX j| + |F i x.1 j - muX j|)
              + (2 * Real.sqrt (1 - t))⁻¹ * |F i x.2 j - muX j|)) := by
          intro j i
          rw [abs_mul]
          exact mul_le_mul (by rw [← Real.norm_eq_abs]; exact hLb j)
            (by rw [← Real.norm_eq_abs]; exact hZdb i j) (abs_nonneg _) hMκ0
        calc |∑ j : Fin p, ∑ i : Fin n, (fderiv ℝ kappa (Zarg t x)) (Pi.single j (1 : ℝ)) * Zd t x i j|
            ≤ ∑ j : Fin p, |∑ i : Fin n, (fderiv ℝ kappa (Zarg t x)) (Pi.single j (1 : ℝ)) * Zd t x i j| :=
              habs_sum_le (Fin p) _
          _ ≤ ∑ j : Fin p, ∑ i : Fin n, |(fderiv ℝ kappa (Zarg t x)) (Pi.single j (1 : ℝ)) * Zd t x i j| :=
              hsum_le (Fin p) _ _ (fun j => habs_sum_le (Fin n) _)
          _ ≤ ∑ j : Fin p, ∑ i : Fin n, Mκ * ((Real.sqrt (n : ℝ))⁻¹ * ((2 * Real.sqrt t)⁻¹ * (|X i x.1 j - muX j| + |F i x.1 j - muX j|)
              + (2 * Real.sqrt (1 - t))⁻¹ * |F i x.2 j - muX j|)) :=
              hsum_le (Fin p) _ _ (fun j => hsum_le (Fin n) _ _ (fun i => h2 j i))
      refine hsum.trans ?_
      have hterm : ∀ (j : Fin p) (i : Fin n),
          Mκ * ((Real.sqrt (n : ℝ))⁻¹ * ((2 * Real.sqrt t)⁻¹ * (|X i x.1 j - muX j| + |F i x.1 j - muX j|)
            + (2 * Real.sqrt (1 - t))⁻¹ * |F i x.2 j - muX j|))
          ≤ (Mκ * (Real.sqrt (n : ℝ))⁻¹ * ((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹)) *
            ((|X i x.1 j - muX j| + |F i x.1 j - muX j|) + |F i x.2 j - muX j|) := by
        intro j i
        have hcross : (0 : ℝ) ≤ Mκ * (Real.sqrt (n : ℝ))⁻¹ *
            ((2 * Real.sqrt t)⁻¹ * |F i x.2 j - muX j| + (2 * Real.sqrt (1 - t))⁻¹ * (|X i x.1 j - muX j| + |F i x.1 j - muX j|)) :=
          mul_nonneg hK (add_nonneg (mul_nonneg ht1 (abs_nonneg _)) (mul_nonneg ht2 (by positivity)))
        calc Mκ * ((Real.sqrt (n : ℝ))⁻¹ * ((2 * Real.sqrt t)⁻¹ * (|X i x.1 j - muX j| + |F i x.1 j - muX j|)
              + (2 * Real.sqrt (1 - t))⁻¹ * |F i x.2 j - muX j|))
            = (Mκ * (Real.sqrt (n : ℝ))⁻¹) * ((2 * Real.sqrt t)⁻¹ * (|X i x.1 j - muX j| + |F i x.1 j - muX j|)
              + (2 * Real.sqrt (1 - t))⁻¹ * |F i x.2 j - muX j|) := by ring
          _ ≤ (Mκ * (Real.sqrt (n : ℝ))⁻¹) * ((2 * Real.sqrt t)⁻¹ * (|X i x.1 j - muX j| + |F i x.1 j - muX j|)
              + (2 * Real.sqrt (1 - t))⁻¹ * |F i x.2 j - muX j|) + Mκ * (Real.sqrt (n : ℝ))⁻¹ *
              ((2 * Real.sqrt t)⁻¹ * |F i x.2 j - muX j| + (2 * Real.sqrt (1 - t))⁻¹ * (|X i x.1 j - muX j| + |F i x.1 j - muX j|)) :=
              le_add_of_nonneg_right hcross
          _ = (Mκ * (Real.sqrt (n : ℝ))⁻¹ * ((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹)) *
              ((|X i x.1 j - muX j| + |F i x.1 j - muX j|) + |F i x.2 j - muX j|) := by ring
      have hstep2 : ∑ j : Fin p, ∑ i : Fin n,
          Mκ * ((Real.sqrt (n : ℝ))⁻¹ * ((2 * Real.sqrt t)⁻¹ * (|X i x.1 j - muX j| + |F i x.1 j - muX j|)
            + (2 * Real.sqrt (1 - t))⁻¹ * |F i x.2 j - muX j|))
          ≤ (Mκ * (Real.sqrt (n : ℝ))⁻¹ * ((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹)) *
            ((∑ j : Fin p, ∑ i : Fin n, (|X i x.1 j - muX j| + |F i x.1 j - muX j|)) +
              ∑ j : Fin p, ∑ i : Fin n, |F i x.2 j - muX j|) := by
        calc ∑ j : Fin p, ∑ i : Fin n,
              Mκ * ((Real.sqrt (n : ℝ))⁻¹ * ((2 * Real.sqrt t)⁻¹ * (|X i x.1 j - muX j| + |F i x.1 j - muX j|)
                + (2 * Real.sqrt (1 - t))⁻¹ * |F i x.2 j - muX j|))
            ≤ ∑ j : Fin p, ∑ i : Fin n,
              (Mκ * (Real.sqrt (n : ℝ))⁻¹ * ((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹)) *
                ((|X i x.1 j - muX j| + |F i x.1 j - muX j|) + |F i x.2 j - muX j|) :=
              Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun i _ => hterm j i))
          _ = (Mκ * (Real.sqrt (n : ℝ))⁻¹ * ((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹)) *
                (∑ j : Fin p, ∑ i : Fin n,
                  ((|X i x.1 j - muX j| + |F i x.1 j - muX j|) + |F i x.2 j - muX j|)) := hpull _ _
          _ = (Mκ * (Real.sqrt (n : ℝ))⁻¹ * ((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹)) *
                ((∑ j : Fin p, ∑ i : Fin n, (|X i x.1 j - muX j| + |F i x.1 j - muX j|)) +
                  ∑ j : Fin p, ∑ i : Fin n, |F i x.2 j - muX j|) := by rw [hsplit]
      refine hstep2.trans (le_of_eq ?_)
      ring
    have hmono : ∫ t in (0 : ℝ)..1, ‖BigF t x‖ ≤
        ∫ t in (0 : ℝ)..1, ((Mκ * (Real.sqrt (n : ℝ))⁻¹) *
          ((∑ j : Fin p, ∑ i : Fin n, (|X i x.1 j - muX j| + |F i x.1 j - muX j|)) +
            ∑ j : Fin p, ∑ i : Fin n, |F i x.2 j - muX j|)) *
          ((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹) := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
        (hMsum.const_mul _) (Filter.Eventually.of_forall fun t => hpt t)
    have hval : ∫ t in (0 : ℝ)..1, ((Mκ * (Real.sqrt (n : ℝ))⁻¹) *
          ((∑ j : Fin p, ∑ i : Fin n, (|X i x.1 j - muX j| + |F i x.1 j - muX j|)) +
            ∑ j : Fin p, ∑ i : Fin n, |F i x.2 j - muX j|)) *
          ((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹)
        = ((Mκ * (Real.sqrt (n : ℝ))⁻¹) *
          ((∑ j : Fin p, ∑ i : Fin n, (|X i x.1 j - muX j| + |F i x.1 j - muX j|)) +
            ∑ j : Fin p, ∑ i : Fin n, |F i x.2 j - muX j|)) * Cint := by
      rw [intervalIntegral.integral_const_mul, hCint]
    have hfin : ((Mκ * (Real.sqrt (n : ℝ))⁻¹) *
          ((∑ j : Fin p, ∑ i : Fin n, (|X i x.1 j - muX j| + |F i x.1 j - muX j|)) +
            ∑ j : Fin p, ∑ i : Fin n, |F i x.2 j - muX j|)) * Cint ≤ DFun x := by
      have hSnn : (0 : ℝ) ≤ (∑ j : Fin p, ∑ i : Fin n, (|X i x.1 j - muX j| + |F i x.1 j - muX j|)) +
          ∑ j : Fin p, ∑ i : Fin n, |F i x.2 j - muX j| := by linarith
      have hK' : (0 : ℝ) ≤ (Mκ * (Real.sqrt (n : ℝ))⁻¹) *
          ((∑ j : Fin p, ∑ i : Fin n, (|X i x.1 j - muX j| + |F i x.1 j - muX j|)) +
            ∑ j : Fin p, ∑ i : Fin n, |F i x.2 j - muX j|) := mul_nonneg (mul_nonneg hMκ0 hn0) hSnn
      refine (mul_le_mul_of_nonneg_left (le_abs_self Cint) hK').trans (le_of_eq ?_)
      simp only [DFun]
      ring
    calc ‖∫ t in (0 : ℝ)..1, BigF t x‖
        ≤ ∫ t in (0 : ℝ)..1, ‖BigF t x‖ :=
          intervalIntegral.norm_integral_le_integral_norm (f := fun t => BigF t x) (μ := volume) (by norm_num)
      _ ≤ ∫ t in (0 : ℝ)..1, ((Mκ * (Real.sqrt (n : ℝ))⁻¹) *
            ((∑ j : Fin p, ∑ i : Fin n, (|X i x.1 j - muX j| + |F i x.1 j - muX j|)) +
              ∑ j : Fin p, ∑ i : Fin n, |F i x.2 j - muX j|)) *
            ((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹) := hmono
      _ = ((Mκ * (Real.sqrt (n : ℝ))⁻¹) *
            ((∑ j : Fin p, ∑ i : Fin n, (|X i x.1 j - muX j| + |F i x.1 j - muX j|)) +
              ∑ j : Fin p, ∑ i : Fin n, |F i x.2 j - muX j|)) * Cint := hval
      _ ≤ DFun x := hfin
  have hmeasGen : ∀ (ι : Type) [Fintype ι] (c : ℝ) (A B : ι → Ω × Ω → Fin p → ℝ),
      (∀ i, Measurable (A i)) → (∀ i, Measurable (B i)) →
      AEStronglyMeasurable (fun q : (Ω × Ω) × ℝ =>
        ∑ j : Fin p, ∑ i : ι,
          (fderiv ℝ kappa (Zarg q.2 q.1)) (Pi.single j (1 : ℝ)) *
            (c * ((2 * Real.sqrt q.2)⁻¹ * A i q.1 j - (2 * Real.sqrt (1 - q.2))⁻¹ * B i q.1 j)))
        ((P.prod P).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
    intro ι hι c A B hA hB
    have hEv : ∀ j : Fin p, Measurable fun L : (Fin p → ℝ) →L[ℝ] ℝ => L (Pi.single j (1 : ℝ)) := by
      intro j
      exact (by fun_prop : Continuous fun L : (Fin p → ℝ) →L[ℝ] ℝ => L (Pi.single j (1 : ℝ))).measurable
    have hXp : ∀ (i : Fin n) (j : Fin p), Measurable fun q : (Ω × Ω) × ℝ => X i q.1.1 j :=
      fun i j => (hmX i j).comp (measurable_fst.comp measurable_fst)
    have hFp : ∀ (i : Fin n) (j : Fin p), Measurable fun q : (Ω × Ω) × ℝ => F i q.1.1 j :=
      fun i j => (hmF i j).comp (measurable_fst.comp measurable_fst)
    have hFp2 : ∀ (i : Fin n) (j : Fin p), Measurable fun q : (Ω × Ω) × ℝ => F i q.1.2 j :=
      fun i j => (hmF i j).comp (measurable_snd.comp measurable_fst)
    have hYp : ∀ (i : Fin m) (j : Fin p), Measurable fun q : (Ω × Ω) × ℝ => Y i q.1.1 j :=
      fun i j => (hmY i j).comp (measurable_fst.comp measurable_fst)
    have hGp : ∀ (i : Fin m) (j : Fin p), Measurable fun q : (Ω × Ω) × ℝ => G i q.1.1 j :=
      fun i j => (hmG i j).comp (measurable_fst.comp measurable_fst)
    have hGp2 : ∀ (i : Fin m) (j : Fin p), Measurable fun q : (Ω × Ω) × ℝ => G i q.1.2 j :=
      fun i j => (hmG i j).comp (measurable_snd.comp measurable_fst)
    have hsq : Measurable fun q : (Ω × Ω) × ℝ => Real.sqrt q.2 :=
      (by fun_prop : Continuous fun t : ℝ => Real.sqrt t).measurable.comp measurable_snd
    have hsq1 : Measurable fun q : (Ω × Ω) × ℝ => Real.sqrt (1 - q.2) :=
      (by fun_prop : Continuous fun t : ℝ => Real.sqrt t).measurable.comp (measurable_const.sub measurable_snd)
    have hsqinv : Measurable fun q : (Ω × Ω) × ℝ => (2 * Real.sqrt q.2)⁻¹ :=
      (measurable_const.mul hsq).inv
    have hsqinv1 : Measurable fun q : (Ω × Ω) × ℝ => (2 * Real.sqrt (1 - q.2))⁻¹ :=
      (measurable_const.mul hsq1).inv
    have hZc : ∀ j : Fin p, Measurable fun q : (Ω × Ω) × ℝ => Zarg q.2 q.1 j := by
      intro j
      have hAn : ∀ i : Fin n, Measurable fun q : (Ω × Ω) × ℝ =>
          Real.sqrt v * (X i q.1.1 j - muX j) + Real.sqrt (1 - v) * (F i q.1.1 j - muX j) := by
        intro i
        exact (measurable_const.mul ((hXp i j).sub measurable_const)).add
          (measurable_const.mul ((hFp i j).sub measurable_const))
      have hBn : ∀ i : Fin n, Measurable fun q : (Ω × Ω) × ℝ => F i q.1.2 j - muX j := by
        intro i
        exact (hFp2 i j).sub measurable_const
      have hAm : ∀ i : Fin m, Measurable fun q : (Ω × Ω) × ℝ =>
          Real.sqrt v * (Y i q.1.1 j - muY j) + Real.sqrt (1 - v) * (G i q.1.1 j - muY j) := by
        intro i
        exact (measurable_const.mul ((hYp i j).sub measurable_const)).add
          (measurable_const.mul ((hGp i j).sub measurable_const))
      have hBm : ∀ i : Fin m, Measurable fun q : (Ω × Ω) × ℝ => G i q.1.2 j - muY j := by
        intro i
        exact (hGp2 i j).sub measurable_const
      have hs1 : Measurable fun q : (Ω × Ω) × ℝ =>
          ∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ *
            (Real.sqrt q.2 * (Real.sqrt v * (X i q.1.1 j - muX j) + Real.sqrt (1 - v) * (F i q.1.1 j - muX j))
              + Real.sqrt (1 - q.2) * (F i q.1.2 j - muX j)) :=
        Finset.measurable_sum (Finset.univ : Finset (Fin n))
          (fun i _ => measurable_const.mul ((hsq.mul (hAn i)).add (hsq1.mul (hBn i))))
      have hs2 : Measurable fun q : (Ω × Ω) × ℝ =>
          ∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m *
            (Real.sqrt q.2 * (Real.sqrt v * (Y i q.1.1 j - muY j) + Real.sqrt (1 - v) * (G i q.1.1 j - muY j))
              + Real.sqrt (1 - q.2) * (G i q.1.2 j - muY j)) :=
        Finset.measurable_sum (Finset.univ : Finset (Fin m))
          (fun i _ => measurable_const.mul ((hsq.mul (hAm i)).add (hsq1.mul (hBm i))))
      exact hs1.add hs2
    have hZ : Measurable fun q : (Ω × Ω) × ℝ => Zarg q.2 q.1 :=
      measurable_pi_iff.2 hZc
    have hfZ : Measurable fun q : (Ω × Ω) × ℝ => fderiv ℝ kappa (Zarg q.2 q.1) :=
      hcontκ.measurable.comp hZ
    have hterm : ∀ (j : Fin p) (i : ι), Measurable fun q : (Ω × Ω) × ℝ =>
        (fderiv ℝ kappa (Zarg q.2 q.1)) (Pi.single j (1 : ℝ)) *
          (c * ((2 * Real.sqrt q.2)⁻¹ * A i q.1 j - (2 * Real.sqrt (1 - q.2))⁻¹ * B i q.1 j)) := by
      intro j i
      have hAj : Measurable fun q : (Ω × Ω) × ℝ => A i q.1 j :=
        (measurable_pi_apply j).comp ((hA i).comp measurable_fst)
      have hBj : Measurable fun q : (Ω × Ω) × ℝ => B i q.1 j :=
        (measurable_pi_apply j).comp ((hB i).comp measurable_fst)
      have h1 : Measurable fun q : (Ω × Ω) × ℝ =>
          (fderiv ℝ kappa (Zarg q.2 q.1)) (Pi.single j (1 : ℝ)) := (hEv j).comp hfZ
      have h2 : Measurable fun q : (Ω × Ω) × ℝ =>
          c * ((2 * Real.sqrt q.2)⁻¹ * A i q.1 j - (2 * Real.sqrt (1 - q.2))⁻¹ * B i q.1 j) :=
        measurable_const.mul ((hsqinv.mul hAj).sub (hsqinv1.mul hBj))
      exact h1.mul h2
    have hinner : ∀ j : Fin p, Measurable fun q : (Ω × Ω) × ℝ =>
        ∑ i : ι, (fderiv ℝ kappa (Zarg q.2 q.1)) (Pi.single j (1 : ℝ)) *
          (c * ((2 * Real.sqrt q.2)⁻¹ * A i q.1 j - (2 * Real.sqrt (1 - q.2))⁻¹ * B i q.1 j)) :=
      fun j => Finset.measurable_sum (Finset.univ : Finset ι) (fun i _ => hterm j i)
    have hsum : Measurable fun q : (Ω × Ω) × ℝ =>
        ∑ j : Fin p, ∑ i : ι,
          (fderiv ℝ kappa (Zarg q.2 q.1)) (Pi.single j (1 : ℝ)) *
            (c * ((2 * Real.sqrt q.2)⁻¹ * A i q.1 j - (2 * Real.sqrt (1 - q.2))⁻¹ * B i q.1 j)) :=
      Finset.measurable_sum (Finset.univ : Finset (Fin p)) (fun j _ => hinner j)
    exact hsum.aestronglyMeasurable
  have hmeas1 : AEStronglyMeasurable (fun x : Ω × Ω => ∫ t in (0 : ℝ)..1, BigF t x) (P.prod P) := by
    have hA1 : ∀ i : Fin n, Measurable fun x : Ω × Ω => fun j : Fin p =>
        Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j) := by
      intro i
      rw [measurable_pi_iff]
      intro j
      have h1 : Measurable fun x : Ω × Ω => X i x.1 j := (hmX i j).comp measurable_fst
      have h2 : Measurable fun x : Ω × Ω => F i x.1 j := (hmF i j).comp measurable_fst
      exact (measurable_const.mul (h1.sub measurable_const)).add (measurable_const.mul (h2.sub measurable_const))
    have hB1 : ∀ i : Fin n, Measurable fun x : Ω × Ω => fun j : Fin p => F i x.2 j - muX j := by
      intro i
      rw [measurable_pi_iff]
      intro j
      exact ((hmF i j).comp measurable_snd).sub measurable_const
    have hJ : AEStronglyMeasurable (fun p : (Ω × Ω) × ℝ => BigF p.2 p.1)
        ((P.prod P).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
      hmeasGen (Fin n) ((Real.sqrt (n : ℝ))⁻¹)
        (fun i x j => Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))
        (fun i x j => F i x.2 j - muX j) hA1 hB1
    have h1 := MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := P.prod P) (ν := volume.restrict (Set.Ioc (0 : ℝ) 1))
      (f := fun p : (Ω × Ω) × ℝ => BigF p.2 p.1) hJ
    exact h1.congr (Filter.Eventually.of_forall fun x =>
      (intervalIntegral.integral_of_le (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)).symm)
  have hI1 : Integrable (fun x : Ω × Ω => ∫ t in (0 : ℝ)..1, BigF t x) (P.prod P) := by
    refine Integrable.mono' hDint' hmeas1 ?_
    filter_upwards with x
    exact hpt1 x
  have hpull2 : ∀ (K : ℝ) (u : Fin p → Fin m → ℝ),
      ∑ j : Fin p, ∑ i : Fin m, K * u j i = K * ∑ j : Fin p, ∑ i : Fin m, u j i := by
    intro K u
    simp only [Finset.mul_sum]
  have hsplit2 : ∀ (u v : Fin p → Fin m → ℝ),
      ∑ j : Fin p, ∑ i : Fin m, (u j i + v j i)
        = (∑ j : Fin p, ∑ i : Fin m, u j i) + ∑ j : Fin p, ∑ i : Fin m, v j i := by
    intro u v
    simp only [Finset.sum_add_distrib]
  let Zd2 : ℝ → Ω × Ω → Fin m → Fin p → ℝ := fun t x i j =>
    (Real.sqrt (m : ℝ))⁻¹ * delta n m *
      ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))
        - (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j))
  let BigG : ℝ → Ω × Ω → ℝ := fun t x =>
    ∑ j : Fin p, ∑ i : Fin m, (fderiv ℝ kappa (Zarg t x)) (Pi.single j (1 : ℝ)) * Zd2 t x i j
  let DFun2 : Ω × Ω → ℝ := fun x =>
    |Cint| * (Mκ * |(Real.sqrt (m : ℝ))⁻¹ * delta n m|) *
      ((∑ j : Fin p, ∑ i : Fin m, (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)) +
        ∑ j : Fin p, ∑ i : Fin m, |G i x.2 j - muY j|)
  have hDint2 : Integrable DFun2 (P.prod P) :=
    (hdom3.add hdom4).const_mul (|Cint| * (Mκ * |(Real.sqrt (m : ℝ))⁻¹ * delta n m|))
  have hpt2 : ∀ x : Ω × Ω, ‖∫ t in (0 : ℝ)..1, BigG t x‖ ≤ DFun2 x := by
    intro x
    have hm0 : (0 : ℝ) ≤ |(Real.sqrt (m : ℝ))⁻¹ * delta n m| := abs_nonneg _
    have hS1nn : (0 : ℝ) ≤ ∑ j : Fin p, ∑ i : Fin m, (|Y i x.1 j - muY j| + |G i x.1 j - muY j|) := by
      have hj : ∀ j : Fin p, (0 : ℝ) ≤ ∑ i : Fin m, (|Y i x.1 j - muY j| + |G i x.1 j - muY j|) :=
        fun j => by positivity
      simpa using Finset.sum_nonneg (s := (Finset.univ : Finset (Fin p))) (fun j _ => hj j)
    have hS2nn : (0 : ℝ) ≤ ∑ j : Fin p, ∑ i : Fin m, |G i x.2 j - muY j| := by
      have hj : ∀ j : Fin p, (0 : ℝ) ≤ ∑ i : Fin m, |G i x.2 j - muY j| :=
        fun j => by positivity
      simpa using Finset.sum_nonneg (s := (Finset.univ : Finset (Fin p))) (fun j _ => hj j)
    have hpt : ∀ t : ℝ, ‖BigG t x‖ ≤ ((Mκ * |(Real.sqrt (m : ℝ))⁻¹ * delta n m|) *
        ((∑ j : Fin p, ∑ i : Fin m, (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)) +
          ∑ j : Fin p, ∑ i : Fin m, |G i x.2 j - muY j|)) *
        ((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹) := by
      intro t
      have ht1 : (0 : ℝ) ≤ (2 * Real.sqrt t)⁻¹ := by
        rw [inv_nonneg]
        positivity
      have ht2 : (0 : ℝ) ≤ (2 * Real.sqrt (1 - t))⁻¹ := by
        rw [inv_nonneg]
        positivity
      have hK : (0 : ℝ) ≤ Mκ * |(Real.sqrt (m : ℝ))⁻¹ * delta n m| := mul_nonneg hMκ0 hm0
      have hLb : ∀ j : Fin p, ‖(fderiv ℝ kappa (Zarg t x)) (Pi.single j (1 : ℝ))‖ ≤ Mκ := by
        intro j
        refine (ContinuousLinearMap.unit_le_opNorm (fderiv ℝ kappa (Zarg t x))
          (Pi.single j (1 : ℝ)) ?_).trans (hMκ (Zarg t x))
        rw [Pi.norm_single]
        simp
      have hZdb : ∀ (i : Fin m) (j : Fin p), ‖Zd2 t x i j‖ ≤ |(Real.sqrt (m : ℝ))⁻¹ * delta n m| *
          ((2 * Real.sqrt t)⁻¹ * (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)
            + (2 * Real.sqrt (1 - t))⁻¹ * |G i x.2 j - muY j|) := by
        intro i j
        have hcl : |Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j)|
            ≤ |Y i x.1 j - muY j| + |G i x.1 j - muY j| := hcle _ _
        have e1 : |(2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))|
            = (2 * Real.sqrt t)⁻¹ * |Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j)| := by
          rw [abs_mul, abs_of_nonneg ht1]
        have e2 : |(2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j)|
            = (2 * Real.sqrt (1 - t))⁻¹ * |G i x.2 j - muY j| := by
          rw [abs_mul, abs_of_nonneg ht2]
        have hAB : |(2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))
              - (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j)|
            ≤ (2 * Real.sqrt t)⁻¹ * |Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j)|
              + (2 * Real.sqrt (1 - t))⁻¹ * |G i x.2 j - muY j| := by
          calc |(2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))
                - (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j)|
              = |(2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))
                  + -((2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j))| := by rw [sub_eq_add_neg]
            _ ≤ |(2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))|
                  + |(2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j)| := by
                simpa using abs_add_le
                  ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j)))
                  (-((2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j)))
            _ = (2 * Real.sqrt t)⁻¹ * |Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j)|
                  + (2 * Real.sqrt (1 - t))⁻¹ * |G i x.2 j - muY j| := by rw [e1, e2]
        simp only [Zd2, Real.norm_eq_abs, abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0 : ℝ) ≤ |(Real.sqrt (m : ℝ))⁻¹| * |delta n m|)
        calc |(2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))
              - (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j)|
            ≤ (2 * Real.sqrt t)⁻¹ * |Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j)|
              + (2 * Real.sqrt (1 - t))⁻¹ * |G i x.2 j - muY j| := hAB
          _ ≤ (2 * Real.sqrt t)⁻¹ * (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)
              + (2 * Real.sqrt (1 - t))⁻¹ * |G i x.2 j - muY j| := by
              exact add_le_add (mul_le_mul_of_nonneg_left hcl ht1) le_rfl
      have hsum : ‖BigG t x‖ ≤ ∑ j : Fin p, ∑ i : Fin m,
          Mκ * (|(Real.sqrt (m : ℝ))⁻¹ * delta n m| * ((2 * Real.sqrt t)⁻¹ * (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)
            + (2 * Real.sqrt (1 - t))⁻¹ * |G i x.2 j - muY j|)) := by
        have hbf : BigG t x = ∑ j : Fin p, ∑ i : Fin m,
            (fderiv ℝ kappa (Zarg t x)) (Pi.single j (1 : ℝ)) * Zd2 t x i j := rfl
        rw [hbf, Real.norm_eq_abs]
        have h2 : ∀ (j : Fin p) (i : Fin m),
            |(fderiv ℝ kappa (Zarg t x)) (Pi.single j (1 : ℝ)) * Zd2 t x i j|
            ≤ Mκ * (|(Real.sqrt (m : ℝ))⁻¹ * delta n m| * ((2 * Real.sqrt t)⁻¹ * (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)
              + (2 * Real.sqrt (1 - t))⁻¹ * |G i x.2 j - muY j|)) := by
          intro j i
          rw [abs_mul]
          exact mul_le_mul (by rw [← Real.norm_eq_abs]; exact hLb j)
            (by rw [← Real.norm_eq_abs]; exact hZdb i j) (abs_nonneg _) hMκ0
        calc |∑ j : Fin p, ∑ i : Fin m, (fderiv ℝ kappa (Zarg t x)) (Pi.single j (1 : ℝ)) * Zd2 t x i j|
            ≤ ∑ j : Fin p, |∑ i : Fin m, (fderiv ℝ kappa (Zarg t x)) (Pi.single j (1 : ℝ)) * Zd2 t x i j| :=
              habs_sum_le (Fin p) _
          _ ≤ ∑ j : Fin p, ∑ i : Fin m, |(fderiv ℝ kappa (Zarg t x)) (Pi.single j (1 : ℝ)) * Zd2 t x i j| :=
              hsum_le (Fin p) _ _ (fun j => habs_sum_le (Fin m) _)
          _ ≤ ∑ j : Fin p, ∑ i : Fin m, Mκ * (|(Real.sqrt (m : ℝ))⁻¹ * delta n m| * ((2 * Real.sqrt t)⁻¹ * (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)
              + (2 * Real.sqrt (1 - t))⁻¹ * |G i x.2 j - muY j|)) :=
              hsum_le (Fin p) _ _ (fun j => hsum_le (Fin m) _ _ (fun i => h2 j i))
      refine hsum.trans ?_
      have hterm : ∀ (j : Fin p) (i : Fin m),
          Mκ * (|(Real.sqrt (m : ℝ))⁻¹ * delta n m| * ((2 * Real.sqrt t)⁻¹ * (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)
            + (2 * Real.sqrt (1 - t))⁻¹ * |G i x.2 j - muY j|))
          ≤ (Mκ * |(Real.sqrt (m : ℝ))⁻¹ * delta n m| * ((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹)) *
            ((|Y i x.1 j - muY j| + |G i x.1 j - muY j|) + |G i x.2 j - muY j|) := by
        intro j i
        have hcross : (0 : ℝ) ≤ Mκ * |(Real.sqrt (m : ℝ))⁻¹ * delta n m| *
            ((2 * Real.sqrt t)⁻¹ * |G i x.2 j - muY j| + (2 * Real.sqrt (1 - t))⁻¹ * (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)) :=
          mul_nonneg hK (add_nonneg (mul_nonneg ht1 (abs_nonneg _)) (mul_nonneg ht2 (by positivity)))
        calc Mκ * (|(Real.sqrt (m : ℝ))⁻¹ * delta n m| * ((2 * Real.sqrt t)⁻¹ * (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)
              + (2 * Real.sqrt (1 - t))⁻¹ * |G i x.2 j - muY j|))
            = (Mκ * |(Real.sqrt (m : ℝ))⁻¹ * delta n m|) * ((2 * Real.sqrt t)⁻¹ * (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)
              + (2 * Real.sqrt (1 - t))⁻¹ * |G i x.2 j - muY j|) := by ring
          _ ≤ (Mκ * |(Real.sqrt (m : ℝ))⁻¹ * delta n m|) * ((2 * Real.sqrt t)⁻¹ * (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)
              + (2 * Real.sqrt (1 - t))⁻¹ * |G i x.2 j - muY j|) + Mκ * |(Real.sqrt (m : ℝ))⁻¹ * delta n m| *
              ((2 * Real.sqrt t)⁻¹ * |G i x.2 j - muY j| + (2 * Real.sqrt (1 - t))⁻¹ * (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)) :=
              le_add_of_nonneg_right hcross
          _ = (Mκ * |(Real.sqrt (m : ℝ))⁻¹ * delta n m| * ((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹)) *
              ((|Y i x.1 j - muY j| + |G i x.1 j - muY j|) + |G i x.2 j - muY j|) := by ring
      have hstep2 : ∑ j : Fin p, ∑ i : Fin m,
          Mκ * (|(Real.sqrt (m : ℝ))⁻¹ * delta n m| * ((2 * Real.sqrt t)⁻¹ * (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)
            + (2 * Real.sqrt (1 - t))⁻¹ * |G i x.2 j - muY j|))
          ≤ (Mκ * |(Real.sqrt (m : ℝ))⁻¹ * delta n m| * ((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹)) *
            ((∑ j : Fin p, ∑ i : Fin m, (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)) +
              ∑ j : Fin p, ∑ i : Fin m, |G i x.2 j - muY j|) := by
        calc ∑ j : Fin p, ∑ i : Fin m,
              Mκ * (|(Real.sqrt (m : ℝ))⁻¹ * delta n m| * ((2 * Real.sqrt t)⁻¹ * (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)
                + (2 * Real.sqrt (1 - t))⁻¹ * |G i x.2 j - muY j|))
            ≤ ∑ j : Fin p, ∑ i : Fin m,
              (Mκ * |(Real.sqrt (m : ℝ))⁻¹ * delta n m| * ((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹)) *
                ((|Y i x.1 j - muY j| + |G i x.1 j - muY j|) + |G i x.2 j - muY j|) :=
              Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun i _ => hterm j i))
          _ = (Mκ * |(Real.sqrt (m : ℝ))⁻¹ * delta n m| * ((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹)) *
                (∑ j : Fin p, ∑ i : Fin m,
                  ((|Y i x.1 j - muY j| + |G i x.1 j - muY j|) + |G i x.2 j - muY j|)) := hpull2 _ _
          _ = (Mκ * |(Real.sqrt (m : ℝ))⁻¹ * delta n m| * ((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹)) *
                ((∑ j : Fin p, ∑ i : Fin m, (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)) +
                  ∑ j : Fin p, ∑ i : Fin m, |G i x.2 j - muY j|) := by rw [hsplit2]
      refine hstep2.trans (le_of_eq ?_)
      ring
    have hmono : ∫ t in (0 : ℝ)..1, ‖BigG t x‖ ≤
        ∫ t in (0 : ℝ)..1, ((Mκ * |(Real.sqrt (m : ℝ))⁻¹ * delta n m|) *
          ((∑ j : Fin p, ∑ i : Fin m, (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)) +
            ∑ j : Fin p, ∑ i : Fin m, |G i x.2 j - muY j|)) *
          ((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹) := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
        (hMsum.const_mul _) (Filter.Eventually.of_forall fun t => hpt t)
    have hval : ∫ t in (0 : ℝ)..1, ((Mκ * |(Real.sqrt (m : ℝ))⁻¹ * delta n m|) *
          ((∑ j : Fin p, ∑ i : Fin m, (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)) +
            ∑ j : Fin p, ∑ i : Fin m, |G i x.2 j - muY j|)) *
          ((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹)
        = ((Mκ * |(Real.sqrt (m : ℝ))⁻¹ * delta n m|) *
          ((∑ j : Fin p, ∑ i : Fin m, (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)) +
            ∑ j : Fin p, ∑ i : Fin m, |G i x.2 j - muY j|)) * Cint := by
      rw [intervalIntegral.integral_const_mul, hCint]
    have hfin : ((Mκ * |(Real.sqrt (m : ℝ))⁻¹ * delta n m|) *
          ((∑ j : Fin p, ∑ i : Fin m, (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)) +
            ∑ j : Fin p, ∑ i : Fin m, |G i x.2 j - muY j|)) * Cint ≤ DFun2 x := by
      have hSnn : (0 : ℝ) ≤ (∑ j : Fin p, ∑ i : Fin m, (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)) +
          ∑ j : Fin p, ∑ i : Fin m, |G i x.2 j - muY j| := by linarith
      have hK' : (0 : ℝ) ≤ (Mκ * |(Real.sqrt (m : ℝ))⁻¹ * delta n m|) *
          ((∑ j : Fin p, ∑ i : Fin m, (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)) +
            ∑ j : Fin p, ∑ i : Fin m, |G i x.2 j - muY j|) := mul_nonneg (mul_nonneg hMκ0 hm0) hSnn
      refine (mul_le_mul_of_nonneg_left (le_abs_self Cint) hK').trans (le_of_eq ?_)
      simp only [DFun2]
      ring
    calc ‖∫ t in (0 : ℝ)..1, BigG t x‖
        ≤ ∫ t in (0 : ℝ)..1, ‖BigG t x‖ :=
          intervalIntegral.norm_integral_le_integral_norm (f := fun t => BigG t x) (μ := volume) (by norm_num)
      _ ≤ ∫ t in (0 : ℝ)..1, ((Mκ * |(Real.sqrt (m : ℝ))⁻¹ * delta n m|) *
            ((∑ j : Fin p, ∑ i : Fin m, (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)) +
              ∑ j : Fin p, ∑ i : Fin m, |G i x.2 j - muY j|)) *
            ((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹) := hmono
      _ = ((Mκ * |(Real.sqrt (m : ℝ))⁻¹ * delta n m|) *
            ((∑ j : Fin p, ∑ i : Fin m, (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)) +
              ∑ j : Fin p, ∑ i : Fin m, |G i x.2 j - muY j|)) * Cint := hval
      _ ≤ DFun2 x := hfin
  have hmeas2 : AEStronglyMeasurable (fun x : Ω × Ω => ∫ t in (0 : ℝ)..1, BigG t x) (P.prod P) := by
    have hA2 : ∀ i : Fin m, Measurable fun x : Ω × Ω => fun j : Fin p =>
        Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j) := by
      intro i
      rw [measurable_pi_iff]
      intro j
      have h1 : Measurable fun x : Ω × Ω => Y i x.1 j := (hmY i j).comp measurable_fst
      have h2 : Measurable fun x : Ω × Ω => G i x.1 j := (hmG i j).comp measurable_fst
      exact (measurable_const.mul (h1.sub measurable_const)).add (measurable_const.mul (h2.sub measurable_const))
    have hB2 : ∀ i : Fin m, Measurable fun x : Ω × Ω => fun j : Fin p => G i x.2 j - muY j := by
      intro i
      rw [measurable_pi_iff]
      intro j
      exact ((hmG i j).comp measurable_snd).sub measurable_const
    have hJ2 : AEStronglyMeasurable (fun q : (Ω × Ω) × ℝ => BigG q.2 q.1)
        ((P.prod P).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
      hmeasGen (Fin m) ((Real.sqrt (m : ℝ))⁻¹ * delta n m)
        (fun i x j => Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))
        (fun i x j => G i x.2 j - muY j) hA2 hB2
    have h1 := MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := P.prod P) (ν := volume.restrict (Set.Ioc (0 : ℝ) 1))
      (f := fun q : (Ω × Ω) × ℝ => BigG q.2 q.1) hJ2
    exact h1.congr (Filter.Eventually.of_forall fun x =>
      (intervalIntegral.integral_of_le (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)).symm)
  have hI2 : Integrable (fun x : Ω × Ω => ∫ t in (0 : ℝ)..1, BigG t x) (P.prod P) := by
    refine Integrable.mono' hDint2 hmeas2 ?_
    filter_upwards with x
    exact hpt2 x
  refine ⟨?_, ?_⟩
  · exact hI1
  · exact hI2
  /- @proof-region region.target-node.session.ee65da1bf2281645 end -/

end

end Statlib.Imported

