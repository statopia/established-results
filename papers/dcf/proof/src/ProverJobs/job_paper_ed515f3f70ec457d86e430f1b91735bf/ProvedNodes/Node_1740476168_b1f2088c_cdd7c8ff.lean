import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
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
theorem statopia_math_node_1740476168_b1f2088c : ∀ (p : ℕ) (hp : 0 < p)
    (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : (Fin p → ℝ) → ℝ) (hf : ContDiff ℝ 3 f)
    (W U : Ω → (Fin p → ℝ)) (V : Ω → Fin p → ℝ)
    (R : ℝ) (hR : 0 ≤ R)
    (hU : ∀ l : Fin p, Measurable (fun x : Ω => U x l))
    (hV : ∀ j : Fin p, Measurable (fun x : Ω => V x j))
    (hmaj : ∀ (x : Ω) (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
      ∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p,
        |(iteratedFDeriv ℝ 3 f (W x + s • U x))
          (fun t : Fin 3 => Pi.single (![l, k, j] t) (1 : ℝ))| ≤ R)
    (hInt1 : Integrable (fun x : Ω =>
      ∑ j : Fin p, (fderiv ℝ f (W x + U x)) (Pi.single j (1 : ℝ)) * V x j) μ)
    (hInt0 : Integrable (fun x : Ω =>
      ∑ j : Fin p, (fderiv ℝ f (W x)) (Pi.single j (1 : ℝ)) * V x j) μ)
    (hIntD : Integrable (fun x : Ω =>
      ∑ j : Fin p, ∑ k : Fin p,
        (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) (W x))
          (Pi.single k (1 : ℝ)) * U x k * V x j) μ)
    (hIntB : Integrable (fun x : Ω => (maxAbs (U x)) ^ 2 * (maxAbs (V x))) μ)
    (hE0 : ∫ x, ∑ j : Fin p, (fderiv ℝ f (W x)) (Pi.single j (1 : ℝ)) * V x j ∂μ = 0)
    (hE1 : ∫ x, ∑ j : Fin p, ∑ k : Fin p,
        (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) (W x))
          (Pi.single k (1 : ℝ)) * U x k * V x j ∂μ = 0),
    |∫ x, ∑ j : Fin p, (fderiv ℝ f (W x + U x)) (Pi.single j (1 : ℝ)) * V x j ∂μ|
      ≤ (1 / 2) * R * ∫ x, (maxAbs (U x)) ^ 2 * (maxAbs (V x)) ∂μ := by
  /- @proof-region region.target-node.session.170fae3441855e51 begin -/
  intro p hp Ω _ μ _ f hf W U V R hR hU hV hmaj hInt1 hInt0 hIntD hIntB hE0 hE1
  have hle_max : ∀ (x : Fin p → ℝ) (j : Fin p), |x j| ≤ maxAbs x := by
    intro x j
    simpa [maxAbs] using le_ciSup (Set.finite_range (fun j : Fin p => |x j|)).bddAbove j
  have hmax_nonneg : ∀ (x : Fin p → ℝ), 0 ≤ maxAbs x := by
    intro x
    simpa [maxAbs] using Real.iSup_nonneg (fun j : Fin p => abs_nonneg (x j))
  have hlin : ∀ (L : (Fin p → ℝ) →L[ℝ] ℝ) (u : Fin p → ℝ),
      L u = ∑ k : Fin p, L (Pi.single k (1 : ℝ)) * u k := by
    intro L u
    have hu : u = ∑ k : Fin p, u k • (Pi.single k (1 : ℝ) : Fin p → ℝ) := by
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hk
        simp [hk]
      · intro hi
        simp at hi
    conv_lhs => rw [hu]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [map_smul, smul_eq_mul, mul_comm]
  have htriple : ∀ (x : Ω) (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
      |∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p,
        (iteratedFDeriv ℝ 3 f (W x + s • U x))
          (fun t : Fin 3 => Pi.single (![l, k, j] t) (1 : ℝ)) * U x k * U x l * V x j|
        ≤ R * ((maxAbs (U x)) ^ 2 * (maxAbs (V x))) := by
    intro x s hs
    have hmU0 : 0 ≤ maxAbs (U x) := hmax_nonneg (U x)
    have hmV0 : 0 ≤ maxAbs (V x) := hmax_nonneg (V x)
    have hterm : ∀ (j k l : Fin p),
        |(iteratedFDeriv ℝ 3 f (W x + s • U x))
            (fun t : Fin 3 => Pi.single (![l, k, j] t) (1 : ℝ)) * U x k * U x l * V x j|
          ≤ |(iteratedFDeriv ℝ 3 f (W x + s • U x))
              (fun t : Fin 3 => Pi.single (![l, k, j] t) (1 : ℝ))|
              * maxAbs (U x) * maxAbs (U x) * maxAbs (V x) := by
      intro j k l
      have h1 : |U x k| ≤ maxAbs (U x) := hle_max (U x) k
      have h2 : |U x l| ≤ maxAbs (U x) := hle_max (U x) l
      have h3 : |V x j| ≤ maxAbs (V x) := hle_max (V x) j
      have hD0 : 0 ≤ |(iteratedFDeriv ℝ 3 f (W x + s • U x))
          (fun t : Fin 3 => Pi.single (![l, k, j] t) (1 : ℝ))| := abs_nonneg _
      have s1 : |(iteratedFDeriv ℝ 3 f (W x + s • U x))
            (fun t : Fin 3 => Pi.single (![l, k, j] t) (1 : ℝ))| * |U x k|
          ≤ |(iteratedFDeriv ℝ 3 f (W x + s • U x))
            (fun t : Fin 3 => Pi.single (![l, k, j] t) (1 : ℝ))| * maxAbs (U x) :=
        mul_le_mul_of_nonneg_left h1 hD0
      have s2 : |(iteratedFDeriv ℝ 3 f (W x + s • U x))
            (fun t : Fin 3 => Pi.single (![l, k, j] t) (1 : ℝ))| * |U x k| * |U x l|
          ≤ |(iteratedFDeriv ℝ 3 f (W x + s • U x))
            (fun t : Fin 3 => Pi.single (![l, k, j] t) (1 : ℝ))| * maxAbs (U x) * maxAbs (U x) :=
        mul_le_mul s1 h2 (abs_nonneg _) (mul_nonneg hD0 hmU0)
      have s3 : |(iteratedFDeriv ℝ 3 f (W x + s • U x))
            (fun t : Fin 3 => Pi.single (![l, k, j] t) (1 : ℝ))| * |U x k| * |U x l| * |V x j|
          ≤ |(iteratedFDeriv ℝ 3 f (W x + s • U x))
            (fun t : Fin 3 => Pi.single (![l, k, j] t) (1 : ℝ))|
            * maxAbs (U x) * maxAbs (U x) * maxAbs (V x) :=
        mul_le_mul s2 h3 (abs_nonneg _) (mul_nonneg (mul_nonneg hD0 hmU0) hmU0)
      rw [abs_mul, abs_mul, abs_mul]
      exact s3
    have hAbs :
        |∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p,
          (iteratedFDeriv ℝ 3 f (W x + s • U x))
            (fun t : Fin 3 => Pi.single (![l, k, j] t) (1 : ℝ)) * U x k * U x l * V x j|
        ≤ ∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p,
          |(iteratedFDeriv ℝ 3 f (W x + s • U x))
            (fun t : Fin 3 => Pi.single (![l, k, j] t) (1 : ℝ))|
            * maxAbs (U x) * maxAbs (U x) * maxAbs (V x) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine Finset.sum_le_sum fun j _ => ?_
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine Finset.sum_le_sum fun k _ => ?_
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      exact Finset.sum_le_sum fun l _ => hterm j k l
    refine le_trans hAbs ?_
    have hfac : 0 ≤ maxAbs (U x) * (maxAbs (U x) * maxAbs (V x)) :=
      mul_nonneg hmU0 (mul_nonneg hmU0 hmV0)
    have hstep : (∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p,
          |(iteratedFDeriv ℝ 3 f (W x + s • U x))
            (fun t : Fin 3 => Pi.single (![l, k, j] t) (1 : ℝ))|
            * maxAbs (U x) * maxAbs (U x) * maxAbs (V x))
        = (∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p,
          |(iteratedFDeriv ℝ 3 f (W x + s • U x))
            (fun t : Fin 3 => Pi.single (![l, k, j] t) (1 : ℝ))|)
          * (maxAbs (U x) * (maxAbs (U x) * maxAbs (V x))) := by
      simp only [mul_assoc, Finset.sum_mul]
    rw [hstep]
    refine le_trans (mul_le_mul_of_nonneg_right (hmaj x s hs) hfac) ?_
    refine le_of_eq ?_
    ring
  set F : Ω → ℝ → ℝ := fun x s =>
    ∑ j : Fin p, (fderiv ℝ f (W x + s • U x)) (Pi.single j (1 : ℝ)) * V x j with hF
  set Fd : Ω → ℝ := fun x =>
    ∑ j : Fin p, ∑ k : Fin p,
      (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) (W x))
        (Pi.single k (1 : ℝ)) * U x k * V x j with hFd
  have hderiv1 : ∀ (x : Ω) (s : ℝ),
      HasDerivAt (F x)
        (∑ j : Fin p, ∑ k : Fin p,
          (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ)))
            (W x + s • U x)) (Pi.single k (1 : ℝ)) * U x k * V x j) s := by
    intro x s
    have hξ : HasDerivAt (fun t : ℝ => W x + t • U x) (U x) s := by
      simpa using ((hasDerivAt_id s).smul_const (U x)).const_add (W x)
    have hstep : ∀ j : Fin p,
        HasDerivAt (fun t : ℝ => (fderiv ℝ f (W x + t • U x)) (Pi.single j (1 : ℝ)))
          (∑ k : Fin p,
            (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ)))
              (W x + s • U x)) (Pi.single k (1 : ℝ)) * U x k) s := by
      intro j
      have hcd : ContDiff ℝ 1
          (fun p : (Fin p → ℝ) × (Fin p → ℝ) => (fderiv ℝ f p.1) p.2) := by
        have h := hf.contDiff_fderiv_apply (m := (1 : WithTop ℕ∞)) (by norm_num)
        simpa using h
      have hdiff : DifferentiableAt ℝ
          (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) (W x + s • U x) := by
        have hgd : Differentiable ℝ
            (fun p : (Fin p → ℝ) × (Fin p → ℝ) => (fderiv ℝ f p.1) p.2) :=
          hcd.differentiable (by norm_num)
        have hpair : DifferentiableAt ℝ
            (fun z : Fin p → ℝ => (z, (Pi.single j (1 : ℝ) : Fin p → ℝ))) (W x + s • U x) := by
          fun_prop
        exact DifferentiableAt.comp (W x + s • U x) hgd.differentiableAt hpair
      have hcomp := HasFDerivAt.comp_hasDerivAt s hdiff.hasFDerivAt hξ
      have hval : (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ)))
            (W x + s • U x)) (U x)
          = ∑ k : Fin p,
            (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ)))
              (W x + s • U x)) (Pi.single k (1 : ℝ)) * U x k :=
        hlin _ (U x)
      rw [hval] at hcomp
      simpa using hcomp
    have hgen : ∀ (T : Finset (Fin p)),
        HasDerivAt (fun t : ℝ => ∑ j ∈ T,
            (fderiv ℝ f (W x + t • U x)) (Pi.single j (1 : ℝ)) * V x j)
          (∑ j ∈ T, (∑ k : Fin p,
            (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ)))
              (W x + s • U x)) (Pi.single k (1 : ℝ)) * U x k) * V x j) s := by
      intro T
      induction T using Finset.induction_on with
      | empty => simpa using hasDerivAt_const (x := s) (c := (0 : ℝ))
      | insert a T ha ih =>
          have hfun : (fun t : ℝ => ∑ j ∈ insert a T,
                (fderiv ℝ f (W x + t • U x)) (Pi.single j (1 : ℝ)) * V x j)
              = (fun t : ℝ => (fderiv ℝ f (W x + t • U x)) (Pi.single a (1 : ℝ)) * V x a
                  + ∑ j ∈ T,
                    (fderiv ℝ f (W x + t • U x)) (Pi.single j (1 : ℝ)) * V x j) := by
            funext t
            rw [Finset.sum_insert ha]
          have hderiv : (∑ j ∈ insert a T, (∑ k : Fin p,
                (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ)))
                  (W x + s • U x)) (Pi.single k (1 : ℝ)) * U x k) * V x j)
              = ((∑ k : Fin p,
                  (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single a (1 : ℝ)))
                    (W x + s • U x)) (Pi.single k (1 : ℝ)) * U x k) * V x a
                  + ∑ j ∈ T, (∑ k : Fin p,
                    (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ)))
                      (W x + s • U x)) (Pi.single k (1 : ℝ)) * U x k) * V x j) := by
            rw [Finset.sum_insert ha]
          rw [hfun, hderiv]
          exact ((hstep a).mul_const (V x a)).add ih
    have hsum : HasDerivAt (fun t : ℝ => ∑ j : Fin p,
          (fderiv ℝ f (W x + t • U x)) (Pi.single j (1 : ℝ)) * V x j)
        (∑ j : Fin p, (∑ k : Fin p,
          (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ)))
            (W x + s • U x)) (Pi.single k (1 : ℝ)) * U x k) * V x j) s := by
      simpa using hgen Finset.univ
    have hfin : (∑ j : Fin p, (∑ k : Fin p,
            (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ)))
              (W x + s • U x)) (Pi.single k (1 : ℝ)) * U x k) * V x j)
        = ∑ j : Fin p, ∑ k : Fin p,
            (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ)))
              (W x + s • U x)) (Pi.single k (1 : ℝ)) * U x k * V x j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul]
    rw [hfin] at hsum
    simpa [hF] using hsum
  have hderiv1_zero : ∀ x : Ω, HasDerivAt (F x) (Fd x) 0 := by
    intro x
    have h := hderiv1 x 0
    have hval : (∑ j : Fin p, ∑ k : Fin p,
        (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ)))
          (W x + (0 : ℝ) • U x)) (Pi.single k (1 : ℝ)) * U x k * V x j) = Fd x := by
      simp [hFd]
    rw [hval] at h
    exact h
  have hcd2 : ContDiff ℝ 2
      (fun p : (Fin p → ℝ) × (Fin p → ℝ) => (fderiv ℝ f p.1) p.2) := by
    have h := hf.contDiff_fderiv_apply (m := (2 : WithTop ℕ∞)) (by norm_num)
    simpa using h
  have hF_pair : ∀ x : Ω, F x = fun s : ℝ => (fderiv ℝ f (W x + s • U x)) (V x) := by
    intro x
    funext s
    show (∑ j : Fin p, (fderiv ℝ f (W x + s • U x)) (Pi.single j (1 : ℝ)) * V x j)
      = (fderiv ℝ f (W x + s • U x)) (V x)
    exact (hlin _ (V x)).symm
  have hF_cont : ∀ x : Ω,
      ContDiff ℝ 2 (fun s : ℝ => (fderiv ℝ f (W x + s • U x)) (V x)) := by
    intro x
    have hA : ContDiff ℝ 2
        (fun s : ℝ => ((W x, V x) + s • ((U x), (0 : Fin p → ℝ)))) :=
      contDiff_const.add (contDiff_id.smul contDiff_const)
    have hcomp := hcd2.comp hA
    simpa using hcomp
  have hpairCD : ∀ v : Fin p → ℝ, ContDiff ℝ 2 (fun z : Fin p → ℝ => (z, v)) := by
    intro v
    fun_prop
  have hlj_cont : ∀ j : Fin p,
      ContDiff ℝ 2 (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) := by
    intro j
    have h := hcd2.comp (hpairCD (Pi.single j (1 : ℝ)))
    simpa using h
  have hlj_pair_cont : ∀ j : Fin p, ContDiff ℝ 1
      (fun q : (Fin p → ℝ) × (Fin p → ℝ) =>
        (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) q.1) q.2) := by
    intro j
    have h := (hlj_cont j).contDiff_fderiv_apply (m := (1 : WithTop ℕ∞)) (by norm_num)
    simpa using h
  have hdiff2 : ∀ (j k : Fin p) (z : Fin p → ℝ),
      DifferentiableAt ℝ (fun y : Fin p → ℝ =>
        (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) y)
          (Pi.single k (1 : ℝ))) z := by
    intro j k z
    have hgd : Differentiable ℝ
        (fun q : (Fin p → ℝ) × (Fin p → ℝ) =>
          (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) q.1) q.2) :=
      (hlj_pair_cont j).differentiable (by norm_num)
    have hpair : DifferentiableAt ℝ
        (fun y : Fin p → ℝ => (y, (Pi.single k (1 : ℝ) : Fin p → ℝ))) z := by
      fun_prop
    exact DifferentiableAt.comp z hgd.differentiableAt hpair
  have hstep2 : ∀ (x : Ω) (s : ℝ) (j k : Fin p),
      HasDerivAt (fun t : ℝ =>
          (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ)))
            (W x + t • U x)) (Pi.single k (1 : ℝ)))
        ((fderiv ℝ (fun y : Fin p → ℝ =>
            (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) y)
              (Pi.single k (1 : ℝ))) (W x + s • U x)) (U x)) s := by
    intro x s j k
    have hξ : HasDerivAt (fun t : ℝ => W x + t • U x) (U x) s := by
      simpa using ((hasDerivAt_id s).smul_const (U x)).const_add (W x)
    have hcomp := HasFDerivAt.comp_hasDerivAt s
      (hdiff2 j k (W x + s • U x)).hasFDerivAt hξ
    simpa using hcomp
  have hsumAt : ∀ (T : Finset (Fin p)) (g : Fin p → ℝ → ℝ) (g' : Fin p → ℝ) (t₀ : ℝ),
      (∀ i ∈ T, HasDerivAt (g i) (g' i) t₀) →
      HasDerivAt (fun t => ∑ i ∈ T, g i t) (∑ i ∈ T, g' i) t₀ := by
    intro T g g' t₀ h
    induction T using Finset.induction_on with
    | empty => simpa using hasDerivAt_const (x := t₀) (c := (0 : ℝ))
    | insert a T ha ih =>
        have hfun : (fun t : ℝ => ∑ i ∈ insert a T, g i t)
            = (fun t : ℝ => g a t + ∑ i ∈ T, g i t) := by
          funext t
          rw [Finset.sum_insert ha]
        have hder : (∑ i ∈ insert a T, g' i) = g' a + ∑ i ∈ T, g' i := by
          rw [Finset.sum_insert ha]
        rw [hfun, hder]
        exact (h a (by simp)).add (ih (fun i hi => h i (by simp [hi])))
  have hinner : ∀ (x : Ω) (s : ℝ) (j : Fin p),
      HasDerivAt (fun t : ℝ => ∑ k : Fin p,
          (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ)))
            (W x + t • U x)) (Pi.single k (1 : ℝ)) * U x k)
        (∑ k : Fin p,
          (fderiv ℝ (fun y : Fin p → ℝ =>
            (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) y)
              (Pi.single k (1 : ℝ))) (W x + s • U x)) (U x) * U x k) s := by
    intro x s j
    have h := hsumAt Finset.univ
      (fun k t => (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ)))
        (W x + t • U x)) (Pi.single k (1 : ℝ)) * U x k)
      (fun k => (fderiv ℝ (fun y : Fin p → ℝ =>
        (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) y)
          (Pi.single k (1 : ℝ))) (W x + s • U x)) (U x) * U x k)
      s (fun k _ => (hstep2 x s j k).mul_const (U x k))
    simpa using h
  have houter : ∀ (x : Ω) (s : ℝ),
      HasDerivAt (fun t : ℝ => ∑ j : Fin p,
          (∑ k : Fin p,
            (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ)))
              (W x + t • U x)) (Pi.single k (1 : ℝ)) * U x k) * V x j)
        (∑ j : Fin p,
          (∑ k : Fin p,
            (fderiv ℝ (fun y : Fin p → ℝ =>
              (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) y)
                (Pi.single k (1 : ℝ))) (W x + s • U x)) (U x) * U x k) * V x j) s := by
    intro x s
    have h := hsumAt Finset.univ
      (fun j t => (∑ k : Fin p,
        (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ)))
          (W x + t • U x)) (Pi.single k (1 : ℝ)) * U x k) * V x j)
      (fun j => (∑ k : Fin p,
        (fderiv ℝ (fun y : Fin p → ℝ =>
          (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) y)
            (Pi.single k (1 : ℝ))) (W x + s • U x)) (U x) * U x k) * V x j)
      s (fun j _ => (hinner x s j).mul_const (V x j))
    simpa using h
  have hsecond_nested : ∀ (x : Ω) (s : ℝ),
      HasDerivAt (fun t : ℝ => ∑ j : Fin p, ∑ k : Fin p,
          (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ)))
            (W x + t • U x)) (Pi.single k (1 : ℝ)) * U x k * V x j)
        (∑ j : Fin p, ∑ k : Fin p,
          (fderiv ℝ (fun y : Fin p → ℝ =>
            (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) y)
              (Pi.single k (1 : ℝ))) (W x + s • U x)) (U x) * U x k * V x j) s := by
    intro x s
    have h := houter x s
    have hf_eq : (fun t : ℝ => ∑ j : Fin p,
        (∑ k : Fin p,
          (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ)))
            (W x + t • U x)) (Pi.single k (1 : ℝ)) * U x k) * V x j)
        = (fun t : ℝ => ∑ j : Fin p, ∑ k : Fin p,
          (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ)))
            (W x + t • U x)) (Pi.single k (1 : ℝ)) * U x k * V x j) := by
      funext t
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul]
    have hd_eq : (∑ j : Fin p,
        (∑ k : Fin p,
          (fderiv ℝ (fun y : Fin p → ℝ =>
            (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) y)
              (Pi.single k (1 : ℝ))) (W x + s • U x)) (U x) * U x k) * V x j)
        = (∑ j : Fin p, ∑ k : Fin p,
          (fderiv ℝ (fun y : Fin p → ℝ =>
            (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) y)
              (Pi.single k (1 : ℝ))) (W x + s • U x)) (U x) * U x k * V x j) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul]
    rw [hf_eq, hd_eq] at h
    exact h
  have hident : ∀ (x : Ω) (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
      (∑ j : Fin p, ∑ k : Fin p,
        (fderiv ℝ (fun y : Fin p → ℝ =>
          (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) y)
            (Pi.single k (1 : ℝ))) (W x + s • U x)) (U x) * U x k * V x j)
        = (∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p,
          (iteratedFDeriv ℝ 3 f (W x + s • U x))
            (fun t : Fin 3 => Pi.single (![l, k, j] t) (1 : ℝ)) * U x k * U x l * V x j) := by
    intro x s hs
    have hentry : ∀ (j k l : Fin p) (z : Fin p → ℝ),
        (iteratedFDeriv ℝ 3 f z) (fun t : Fin 3 => Pi.single (![l, k, j] t) (1 : ℝ))
          = (fderiv ℝ (fun y : Fin p → ℝ =>
              (fderiv ℝ (fun z' : Fin p → ℝ => (fderiv ℝ f z') (Pi.single j (1 : ℝ))) y)
                (Pi.single k (1 : ℝ))) z) (Pi.single l (1 : ℝ)) := by
      intro j k l z
      have hclm : ContDiff ℝ 2 (fun y : Fin p → ℝ => fderiv ℝ f y) := by
        refine (contDiff_clm_apply_iff (𝕜 := ℝ)
          (f := fun y : Fin p → ℝ => fderiv ℝ f y)).mpr ?_
        intro y
        have h := hcd2.comp (hpairCD y)
        simpa using h
      have hclm' : ContDiff ℝ 1
          (fun y : Fin p → ℝ =>
            fderiv ℝ (fun z' : Fin p → ℝ => (fderiv ℝ f z') (Pi.single j (1 : ℝ))) y) := by
        refine (contDiff_clm_apply_iff (𝕜 := ℝ)
          (f := fun y : Fin p → ℝ =>
            fderiv ℝ (fun z' : Fin p → ℝ => (fderiv ℝ f z') (Pi.single j (1 : ℝ))) y)).mpr ?_
        intro y
        have hpair : ContDiff ℝ 1 (fun z : Fin p → ℝ => (z, y)) := by fun_prop
        have h := (hlj_pair_cont j).comp hpair
        simpa using h
      have hinst2 := iteratedFDerivWithin_clm_apply_const_apply (𝕜 := ℝ) (s := Set.univ)
        (c := fun y : Fin p → ℝ => fderiv ℝ f y) (n := (2 : WithTop ℕ∞))
        uniqueDiffOn_univ hclm.contDiffOn (by norm_num) (Set.mem_univ z)
        (u := Pi.single j (1 : ℝ)) (m := fun i : Fin 2 => Pi.single (![l, k] i) (1 : ℝ))
      have hmid : ((iteratedFDeriv ℝ 2
            (fun y : Fin p → ℝ => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) z)
            (fun i : Fin 2 => Pi.single (![l, k] i) (1 : ℝ)))
          = ((iteratedFDeriv ℝ 2 (fun y : Fin p → ℝ => fderiv ℝ f y) z)
            (fun i : Fin 2 => Pi.single (![l, k] i) (1 : ℝ))) (Pi.single j (1 : ℝ)) := by
        simpa [iteratedFDerivWithin_univ] using hinst2
      have hinst1 := iteratedFDerivWithin_clm_apply_const_apply (𝕜 := ℝ) (s := Set.univ)
        (c := fun y : Fin p → ℝ =>
          fderiv ℝ (fun z' : Fin p → ℝ => (fderiv ℝ f z') (Pi.single j (1 : ℝ))) y)
        (n := (1 : WithTop ℕ∞)) uniqueDiffOn_univ hclm'.contDiffOn (by norm_num)
        (Set.mem_univ z) (u := Pi.single k (1 : ℝ)) (m := fun _ : Fin 1 => Pi.single l (1 : ℝ))
      have h2 : (iteratedFDeriv ℝ 1 (fun y : Fin p → ℝ =>
            (fderiv ℝ (fun z' : Fin p → ℝ => (fderiv ℝ f z') (Pi.single j (1 : ℝ))) y)
              (Pi.single k (1 : ℝ))) z) (fun _ : Fin 1 => Pi.single l (1 : ℝ))
          = ((iteratedFDeriv ℝ 1 (fun y : Fin p → ℝ =>
              fderiv ℝ (fun z' : Fin p → ℝ => (fderiv ℝ f z') (Pi.single j (1 : ℝ))) y) z)
              (fun _ : Fin 1 => Pi.single l (1 : ℝ))) (Pi.single k (1 : ℝ)) := by
        simpa [iteratedFDerivWithin_univ] using hinst1
      have h3a : (iteratedFDeriv ℝ 3 f z)
            (fun t : Fin 3 => Pi.single (![l, k, j] t) (1 : ℝ))
          = ((iteratedFDeriv ℝ 2 (fun y : Fin p → ℝ => fderiv ℝ f y) z)
              (fun i : Fin 2 => Pi.single (![l, k] i) (1 : ℝ))) (Pi.single j (1 : ℝ)) := by
        rw [iteratedFDeriv_succ_apply_right (𝕜 := ℝ) (n := 2) (f := f) (x := z)
          (fun t : Fin 3 => Pi.single (![l, k, j] t) (1 : ℝ))]
        have hinit : (Fin.init (fun t : Fin 3 => (Pi.single (![l, k, j] t) (1 : ℝ) : Fin p → ℝ)))
            = (fun i : Fin 2 => (Pi.single (![l, k] i) (1 : ℝ) : Fin p → ℝ)) := by
          funext i
          fin_cases i <;> rfl
        have hlast : ((![l, k, j] : Fin 3 → Fin p) (Fin.last 2)) = j := rfl
        rw [hinit, hlast]
      have h3b : ((iteratedFDeriv ℝ 2 (fun y : Fin p → ℝ => fderiv ℝ f y) z)
              (fun i : Fin 2 => Pi.single (![l, k] i) (1 : ℝ))) (Pi.single j (1 : ℝ))
          = (iteratedFDeriv ℝ 2
              (fun y : Fin p → ℝ => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) z)
              (fun i : Fin 2 => Pi.single (![l, k] i) (1 : ℝ)) := hmid.symm
      have h3c : (iteratedFDeriv ℝ 2
              (fun y : Fin p → ℝ => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) z)
              (fun i : Fin 2 => Pi.single (![l, k] i) (1 : ℝ))
          = ((fderiv ℝ (fderiv ℝ (fun y : Fin p → ℝ =>
                (fderiv ℝ f y) (Pi.single j (1 : ℝ)))) z) (Pi.single l (1 : ℝ)))
              (Pi.single k (1 : ℝ)) := by
        rw [iteratedFDeriv_two_apply (𝕜 := ℝ)
          (fun y : Fin p → ℝ => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) z
          (fun i : Fin 2 => Pi.single (![l, k] i) (1 : ℝ))]
        have h0 : (![l, k] : Fin 2 → Fin p) 0 = l := rfl
        have h1 : (![l, k] : Fin 2 → Fin p) 1 = k := rfl
        rw [h0, h1]
      have h3d : ((fderiv ℝ (fderiv ℝ (fun y : Fin p → ℝ =>
                (fderiv ℝ f y) (Pi.single j (1 : ℝ)))) z) (Pi.single l (1 : ℝ)))
              (Pi.single k (1 : ℝ))
          = ((iteratedFDeriv ℝ 1 (fun y : Fin p → ℝ =>
                fderiv ℝ (fun z' : Fin p → ℝ => (fderiv ℝ f z') (Pi.single j (1 : ℝ))) y) z)
              (fun _ : Fin 1 => Pi.single l (1 : ℝ))) (Pi.single k (1 : ℝ)) := by
        rw [iteratedFDeriv_one_apply]
      have h3e : ((iteratedFDeriv ℝ 1 (fun y : Fin p → ℝ =>
                fderiv ℝ (fun z' : Fin p → ℝ => (fderiv ℝ f z') (Pi.single j (1 : ℝ))) y) z)
              (fun _ : Fin 1 => Pi.single l (1 : ℝ))) (Pi.single k (1 : ℝ))
          = (iteratedFDeriv ℝ 1 (fun y : Fin p → ℝ =>
              (fderiv ℝ (fun z' : Fin p → ℝ => (fderiv ℝ f z') (Pi.single j (1 : ℝ))) y)
                (Pi.single k (1 : ℝ))) z) (fun _ : Fin 1 => Pi.single l (1 : ℝ)) := h2.symm
      have h3f : (iteratedFDeriv ℝ 1 (fun y : Fin p → ℝ =>
              (fderiv ℝ (fun z' : Fin p → ℝ => (fderiv ℝ f z') (Pi.single j (1 : ℝ))) y)
                (Pi.single k (1 : ℝ))) z) (fun _ : Fin 1 => Pi.single l (1 : ℝ))
          = (fderiv ℝ (fun y : Fin p → ℝ =>
              (fderiv ℝ (fun z' : Fin p → ℝ => (fderiv ℝ f z') (Pi.single j (1 : ℝ))) y)
                (Pi.single k (1 : ℝ))) z) (Pi.single l (1 : ℝ)) := by
        rw [iteratedFDeriv_one_apply]
      exact h3a.trans (h3b.trans (h3c.trans (h3d.trans (h3e.trans h3f))))
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    have hL : (fderiv ℝ (fun y : Fin p → ℝ =>
        (fderiv ℝ (fun z' : Fin p → ℝ => (fderiv ℝ f z') (Pi.single j (1 : ℝ))) y)
          (Pi.single k (1 : ℝ))) (W x + s • U x)) (U x)
        = ∑ l : Fin p, (fderiv ℝ (fun y : Fin p → ℝ =>
            (fderiv ℝ (fun z' : Fin p → ℝ => (fderiv ℝ f z') (Pi.single j (1 : ℝ))) y)
              (Pi.single k (1 : ℝ))) (W x + s • U x)) (Pi.single l (1 : ℝ)) * U x l :=
      hlin _ (U x)
    rw [hL, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hentry j k l (W x + s • U x)]
    ring
  have hsecond : ∀ x : Ω, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => ∑ j : Fin p, ∑ k : Fin p,
          (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ)))
            (W x + t • U x)) (Pi.single k (1 : ℝ)) * U x k * V x j)
        (∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p,
          (iteratedFDeriv ℝ 3 f (W x + s • U x))
            (fun t : Fin 3 => Pi.single (![l, k, j] t) (1 : ℝ)) * U x k * U x l * V x j) s := by
    intro x s hs
    have h := hsecond_nested x s
    rw [hident x s hs] at h
    exact h
  have hPhi_lip : ∀ (x : Ω) (y : ℝ), y ∈ Set.Icc (0 : ℝ) 1 →
      |(∑ j : Fin p, ∑ k : Fin p,
          (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ)))
            (W x + y • U x)) (Pi.single k (1 : ℝ)) * U x k * V x j)
        - (∑ j : Fin p, ∑ k : Fin p,
          (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ)))
            (W x + (0 : ℝ) • U x)) (Pi.single k (1 : ℝ)) * U x k * V x j)|
        ≤ R * ((maxAbs (U x)) ^ 2 * (maxAbs (V x))) * y := by
    intro x y hy
    have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := fun t : ℝ => ∑ j : Fin p, ∑ k : Fin p,
        (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ)))
          (W x + t • U x)) (Pi.single k (1 : ℝ)) * U x k * V x j)
      (s := Set.Icc (0 : ℝ) 1) (C := R * ((maxAbs (U x)) ^ 2 * (maxAbs (V x))))
      (fun t ht => (hsecond x t ht).differentiableAt)
      (fun t ht => by
        rw [(hsecond x t ht).deriv, Real.norm_eq_abs]
        exact htriple x t ht)
      (convex_Icc 0 1) ⟨le_rfl, zero_le_one⟩ hy
    simp only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hy.1] at hmvt
    exact hmvt
  have hPhi_zero : ∀ x : Ω,
      (∑ j : Fin p, ∑ k : Fin p,
        (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ)))
          (W x + (0 : ℝ) • U x)) (Pi.single k (1 : ℝ)) * U x k * V x j) = Fd x := by
    intro x
    simp [hFd]
  have hC_nonneg : ∀ x : Ω, 0 ≤ R * ((maxAbs (U x)) ^ 2 * (maxAbs (V x))) := by
    intro x
    exact mul_nonneg hR (mul_nonneg (sq_nonneg _) (hmax_nonneg (V x)))
  have hTaylor : ∀ x : Ω,
      |F x 1 - F x 0 - Fd x| ≤ (1 / 2) * R * ((maxAbs (U x)) ^ 2 * maxAbs (V x)) := by
    intro x
    set Φ : ℝ → ℝ := (fun t : ℝ => ∑ j : Fin p, ∑ k : Fin p,
      (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ)))
        (W x + t • U x)) (Pi.single k (1 : ℝ)) * U x k * V x j) with hΦ
    set C : ℝ := R * ((maxAbs (U x)) ^ 2 * (maxAbs (V x))) with hCdef
    have hΦ0 : Φ 0 = Fd x := by rw [hΦ]; exact hPhi_zero x
    have h2Φ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Φ
        (∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p,
          (iteratedFDeriv ℝ 3 f (W x + t • U x))
            (fun s : Fin 3 => Pi.single (![l, k, j] s) (1 : ℝ)) * U x k * U x l * V x j) t := by
      intro t ht
      rw [hΦ]
      exact hsecond x t ht
    have hdu : ∀ t : ℝ, HasDerivAt (fun s : ℝ => F x s - F x 0 - s * Fd x) (Φ t - Φ 0) t := by
      intro t
      have h1 : HasDerivAt (fun s : ℝ => F x s - F x 0) (Φ t) t :=
        (hasDerivAt_sub_const_iff (F x 0)).mpr (by rw [hΦ]; exact hderiv1 x t)
      have h2 : HasDerivAt (fun s : ℝ => -(s * Fd x)) (-(Fd x)) t := by
        simpa using ((hasDerivAt_id t).mul_const (Fd x)).neg
      have h3 := h1.add h2
      have hv : Φ t + -(Fd x) = Φ t - Φ 0 := by
        rw [hΦ0, sub_eq_add_neg]
      rw [hv] at h3
      exact h3
    have hcontD : ContinuousOn (fun t : ℝ => Φ t - Φ 0) (Set.Icc (0 : ℝ) 1) := by
      intro t ht
      have h := (hasDerivAt_sub_const_iff (Φ 0)).mpr (h2Φ t ht)
      exact h.continuousAt.continuousWithinAt
    have hcont_lin : ContinuousOn (fun t : ℝ => C * t) (Set.Icc (0 : ℝ) 1) := by
      fun_prop
    have hIntD : IntervalIntegrable (fun t : ℝ => Φ t - Φ 0) volume 0 1 :=
      ContinuousOn.intervalIntegrable_of_Icc (show (0 : ℝ) ≤ 1 by norm_num) hcontD
    have hInt_lin : IntervalIntegrable (fun t : ℝ => C * t) volume 0 1 :=
      ContinuousOn.intervalIntegrable_of_Icc (show (0 : ℝ) ≤ 1 by norm_num) hcont_lin
    have hderiv_sq : ∀ t : ℝ, HasDerivAt (fun s : ℝ => s ^ 2 / 2) t t := by
      intro t
      have h1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
        simpa using hasDerivAt_pow 2 t
      simpa using h1.div_const 2
    have hcont_id : ContinuousOn (fun t : ℝ => t) (Set.uIcc (0 : ℝ) 1) := by
      intro t ht
      exact continuousAt_id.continuousWithinAt
    have hInt_id : IntervalIntegrable (fun t : ℝ => t) volume 0 1 :=
      hcont_id.intervalIntegrable
    have hint_id0 := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
      (f := fun s : ℝ => s ^ 2 / 2) (f' := fun t : ℝ => t)
      (fun t _ => hderiv_sq t) hInt_id
    have hnum : (1 : ℝ) ^ 2 / 2 - (0 : ℝ) ^ 2 / 2 = 1 / 2 := by norm_num
    have hint_id := hint_id0.trans hnum
    have hcl := intervalIntegral.integral_const_mul (a := (0 : ℝ)) (b := 1) (μ := volume)
      C (fun t : ℝ => t)
    have hint_lin := hcl.trans (by rw [hint_id])
    have hpt : ∀ t ∈ Set.Icc (0 : ℝ) 1, |Φ t - Φ 0| ≤ C * t := by
      intro t ht
      rw [hΦ, hCdef]
      exact hPhi_lip x t ht
    have hcont_abs : ContinuousOn (fun t : ℝ => |Φ t - Φ 0|) (Set.Icc (0 : ℝ) 1) := by
      fun_prop
    have hInt_abs : IntervalIntegrable (fun t : ℝ => |Φ t - Φ 0|) volume 0 1 :=
      ContinuousOn.intervalIntegrable_of_Icc (show (0 : ℝ) ≤ 1 by norm_num) hcont_abs
    have hstep1 := intervalIntegral.abs_integral_le_integral_abs
      (f := fun t : ℝ => Φ t - Φ 0) (a := (0 : ℝ)) (b := 1) (μ := volume)
      (show (0 : ℝ) ≤ 1 by norm_num)
    have hstep2 := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1) (μ := volume)
      (f := fun t : ℝ => |Φ t - Φ 0|) (g := fun t : ℝ => C * t)
      (show (0 : ℝ) ≤ 1 by norm_num) hInt_abs hInt_lin hpt
    have hFTC0 := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
      (f := fun s : ℝ => F x s - F x 0 - s * Fd x) (f' := fun t : ℝ => Φ t - Φ 0)
      (fun t _ => hdu t) hIntD
    have hval : (F x 1 - F x 0 - 1 * Fd x) - (F x 0 - F x 0 - 0 * Fd x)
        = F x 1 - F x 0 - Fd x := by ring
    have hFTC := hFTC0.trans hval
    have hchain := le_trans hstep1 (le_trans hstep2 (le_of_eq hint_lin))
    have hfin : |F x 1 - F x 0 - Fd x| ≤ C * (1 / 2) := by
      rw [← hFTC]
      exact hchain
    have hgoal : C * (1 / 2) = (1 / 2) * R * ((maxAbs (U x)) ^ 2 * maxAbs (V x)) := by
      rw [hCdef]; ring
    rw [hgoal] at hfin
    exact hfin
  have hIntF1 : Integrable (fun x => F x 1) μ := by
    simpa [hF, one_smul] using hInt1
  have hIntF0 : Integrable (fun x => F x 0) μ := by
    simpa [hF] using hInt0
  have hIntFd : Integrable Fd μ := by
    simpa [hFd] using hIntD
  have hIntR : Integrable (fun x => F x 1 - F x 0 - Fd x) μ :=
    (hIntF1.sub hIntF0).sub hIntFd
  have hIntAbs : Integrable (fun x => |F x 1 - F x 0 - Fd x|) μ := by
    simpa [Real.norm_eq_abs] using hIntR.norm
  have hIntM : Integrable (fun x => (1 / 2) * R * ((maxAbs (U x)) ^ 2 * maxAbs (V x))) μ :=
    hIntB.const_mul ((1 / 2) * R)
  have hE0' : ∫ x, F x 0 ∂μ = 0 := by simpa [hF] using hE0
  have hE1' : ∫ x, Fd x ∂μ = 0 := by simpa [hFd] using hE1
  have hsplit : ∫ x, F x 1 ∂μ = ∫ x, (F x 1 - F x 0 - Fd x) ∂μ := by
    have hA : ∫ x, (F x 1 - F x 0 - Fd x) ∂μ
        = ∫ x, (F x 1 - F x 0) ∂μ - ∫ x, Fd x ∂μ :=
      integral_sub (hIntF1.sub hIntF0) hIntFd
    have hB : ∫ x, (F x 1 - F x 0) ∂μ = ∫ x, F x 1 ∂μ - ∫ x, F x 0 ∂μ :=
      integral_sub hIntF1 hIntF0
    rw [hA, hB, hE0', hE1']
    ring
  have hmono : ∫ x, |F x 1 - F x 0 - Fd x| ∂μ
      ≤ ∫ x, (1 / 2) * R * ((maxAbs (U x)) ^ 2 * maxAbs (V x)) ∂μ := by
    have hpt : ∀ x : Ω, 0 ≤ (1 / 2) * R * ((maxAbs (U x)) ^ 2 * maxAbs (V x))
        - |F x 1 - F x 0 - Fd x| := by
      intro x
      linarith [hTaylor x]
    have h1 : ∫ x, ((1 / 2) * R * ((maxAbs (U x)) ^ 2 * maxAbs (V x))
        - |F x 1 - F x 0 - Fd x|) ∂μ
        = ∫ x, (1 / 2) * R * ((maxAbs (U x)) ^ 2 * maxAbs (V x)) ∂μ
          - ∫ x, |F x 1 - F x 0 - Fd x| ∂μ :=
      integral_sub hIntM hIntAbs
    have h2 : 0 ≤ ∫ x, ((1 / 2) * R * ((maxAbs (U x)) ^ 2 * maxAbs (V x))
        - |F x 1 - F x 0 - Fd x|) ∂μ :=
      integral_nonneg hpt
    linarith
  have hkey : |∫ x, F x 1 ∂μ|
      ≤ (1 / 2) * R * ∫ x, (maxAbs (U x)) ^ 2 * (maxAbs (V x)) ∂μ := by
    calc |∫ x, F x 1 ∂μ| = |∫ x, (F x 1 - F x 0 - Fd x) ∂μ| := by rw [hsplit]
      _ ≤ ∫ x, |F x 1 - F x 0 - Fd x| ∂μ := MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ x, (1 / 2) * R * ((maxAbs (U x)) ^ 2 * maxAbs (V x)) ∂μ := hmono
      _ = (1 / 2) * R * ∫ x, (maxAbs (U x)) ^ 2 * (maxAbs (V x)) ∂μ := by
          rw [integral_const_mul]
  simpa [hF, one_smul] using hkey
  /- @proof-region region.target-node.session.170fae3441855e51 end -/

end

end Statlib.Imported

