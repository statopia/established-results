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
theorem statopia_math_node_2945293653_548ae0bd : ∀ (p : ℕ) (f : (Fin p → ℝ) → ℝ) (hf : ContDiff ℝ 3 f)
    (x d : Fin p → ℝ) (j : Fin p) (Q : Fin p → Fin p → ℝ)
    (hQ : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ k l : Fin p,
      |(fderiv ℝ (fun y : Fin p → ℝ =>
          (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) y)
            (Pi.single k (1 : ℝ))) (x + s • d)) (Pi.single l (1 : ℝ))| ≤ Q k l),
    |(fderiv ℝ f (x + d)) (Pi.single j (1 : ℝ)) - (fderiv ℝ f x) (Pi.single j (1 : ℝ))
        - ∑ k : Fin p,
            (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) x)
              (Pi.single k (1 : ℝ)) * d k|
      ≤ (1 / 2) * ∑ k : Fin p, ∑ l : Fin p, Q k l * |d k| * |d l| := by
  /- @proof-region region.target-node.session.f3ac228d8893e804 begin -/
  intro p f hf x d j Q hQ
  let F : (Fin p → ℝ) → ℝ := fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))
  let G : Fin p → (Fin p → ℝ) → ℝ := fun k y => (fderiv ℝ F y) (Pi.single k (1 : ℝ))
  let H : Fin p → Fin p → (Fin p → ℝ) → ℝ :=
    fun k l y => (fderiv ℝ (G k) y) (Pi.single l (1 : ℝ))
  let g : ℝ → ℝ := fun s => F (x + s • d)
  let g' : ℝ → ℝ := fun s => ∑ k : Fin p, G k (x + s • d) * d k
  let g'' : ℝ → ℝ := fun s => ∑ k : Fin p, (∑ l : Fin p, H k l (x + s • d) * d l) * d k
  let C : ℝ := ∑ k : Fin p, ∑ l : Fin p, Q k l * |d k| * |d l|
  have hQ' : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ k l : Fin p, |H k l (x + s • d)| ≤ Q k l :=
    fun s hs k l => hQ s hs k l
  have hcoord : ∀ L : (Fin p → ℝ) →L[ℝ] ℝ,
      L d = ∑ k : Fin p, L (Pi.single k (1 : ℝ)) * d k := by
    intro L
    have hsum : (∑ k : Fin p, d k • (Pi.single k (1 : ℝ) : Fin p → ℝ)) = d := by
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single i]
      · rw [Pi.single_eq_same, mul_one]
      · intro b _ hb
        rw [Pi.single_eq_of_ne (Ne.symm hb), mul_zero]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    calc L d = L (∑ k : Fin p, d k • (Pi.single k (1 : ℝ) : Fin p → ℝ)) := by rw [hsum]
      _ = ∑ k : Fin p, L (d k • (Pi.single k (1 : ℝ) : Fin p → ℝ)) := map_sum L _ _
      _ = ∑ k : Fin p, d k • L (Pi.single k (1 : ℝ) : Fin p → ℝ) :=
            Finset.sum_congr rfl (fun k _ => map_smul L (d k) _)
      _ = ∑ k : Fin p, L (Pi.single k (1 : ℝ)) * d k :=
            Finset.sum_congr rfl (fun k _ => by rw [smul_eq_mul, mul_comm])
  have hF2 : ContDiff ℝ 2 F := by
    have hfd1 : ContDiff ℝ 2 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
    exact hfd1.clm_apply contDiff_const
  have hF_diff : Differentiable ℝ F := hF2.differentiable (by norm_num)
  have hfdF : ContDiff ℝ 1 (fderiv ℝ F) := hF2.fderiv_right (by norm_num)
  have hG_diff : ∀ k : Fin p, Differentiable ℝ (G k) := by
    intro k
    exact (hfdF.clm_apply contDiff_const).differentiable (by norm_num)
  have hcurve : ∀ s : ℝ, HasDerivAt (fun t : ℝ => x + t • d) d s := by
    intro s
    simpa using ((hasDerivAt_id s).smul_const d).const_add x
  have hg_deriv : ∀ s : ℝ, HasDerivAt g (g' s) s := by
    intro s
    have hFd : HasFDerivAt F (fderiv ℝ F (x + s • d)) (x + s • d) :=
      (hF_diff (x + s • d)).hasFDerivAt
    have h1 := hFd.comp_hasDerivAt s (hcurve s)
    have h2 := hcoord (fderiv ℝ F (x + s • d))
    rw [h2] at h1
    exact h1
  have hg'_deriv : ∀ s : ℝ, HasDerivAt g' (g'' s) s := by
    intro s
    have hterm : ∀ k : Fin p, HasDerivAt (fun t : ℝ => G k (x + t • d) * d k)
        ((fderiv ℝ (G k) (x + s • d)) d * d k) s := by
      intro k
      have hGd : HasFDerivAt (G k) (fderiv ℝ (G k) (x + s • d)) (x + s • d) :=
        (hG_diff k (x + s • d)).hasFDerivAt
      exact (hGd.comp_hasDerivAt s (hcurve s)).mul_const (d k)
    have hsum : HasDerivAt (fun t : ℝ => ∑ k : Fin p, G k (x + t • d) * d k)
        (∑ k : Fin p, (fderiv ℝ (G k) (x + s • d)) d * d k) s := by
      have key : ∀ u : Finset (Fin p),
          HasDerivAt (fun t : ℝ => ∑ k ∈ u, G k (x + t • d) * d k)
            (∑ k ∈ u, (fderiv ℝ (G k) (x + s • d)) d * d k) s := by
        intro u
        induction u using Finset.induction with
        | empty => simpa using hasDerivAt_const s (0 : ℝ)
        | insert a u ha ih =>
            simpa [Finset.sum_insert ha] using (hterm a).add ih
      simpa using key Finset.univ
    have hval : (∑ k : Fin p, (fderiv ℝ (G k) (x + s • d)) d * d k) = g'' s := by
      show (∑ k : Fin p, (fderiv ℝ (G k) (x + s • d)) d * d k)
        = ∑ k : Fin p, (∑ l : Fin p, H k l (x + s • d) * d l) * d k
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hcoord (fderiv ℝ (G k) (x + s • d))]
    rw [hval] at hsum
    exact hsum
  have hCbound : ∀ s ∈ Set.Icc (0 : ℝ) 1, |g'' s| ≤ C := by
    intro s hs
    have h1 : ∀ k l : Fin p, |H k l (x + s • d)| ≤ Q k l := fun k l => hQ' s hs k l
    show |∑ k : Fin p, (∑ l : Fin p, H k l (x + s • d) * d l) * d k|
      ≤ ∑ k : Fin p, ∑ l : Fin p, Q k l * |d k| * |d l|
    calc |∑ k : Fin p, (∑ l : Fin p, H k l (x + s • d) * d l) * d k|
        ≤ ∑ k : Fin p, |(∑ l : Fin p, H k l (x + s • d) * d l) * d k| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin p, |∑ l : Fin p, H k l (x + s • d) * d l| * |d k| := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [abs_mul]
      _ ≤ ∑ k : Fin p, (∑ l : Fin p, |H k l (x + s • d)| * |d l|) * |d k| := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          calc |∑ l : Fin p, H k l (x + s • d) * d l|
              ≤ ∑ l : Fin p, |H k l (x + s • d) * d l| := Finset.abs_sum_le_sum_abs _ _
            _ = ∑ l : Fin p, |H k l (x + s • d)| * |d l| := by
                refine Finset.sum_congr rfl (fun l _ => ?_)
                rw [abs_mul]
      _ ≤ ∑ k : Fin p, (∑ l : Fin p, Q k l * |d l|) * |d k| := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          exact Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_right (h1 k l) (abs_nonneg _))
      _ = ∑ k : Fin p, ∑ l : Fin p, Q k l * |d k| * |d l| := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun l _ => by ring)
  have hMVT : ∀ s ∈ Set.Icc (0 : ℝ) 1, |g' s - g' 0| ≤ C * s := by
    intro s hs
    have hdiff : ∀ t ∈ Set.Icc (0 : ℝ) s, DifferentiableAt ℝ g' t :=
      fun t _ => (hg'_deriv t).differentiableAt
    have hb : ∀ t ∈ Set.Icc (0 : ℝ) s, ‖deriv g' t‖ ≤ C := by
      intro t ht
      have ht1 : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1, le_trans ht.2 hs.2⟩
      rw [(hg'_deriv t).deriv]
      simpa [Real.norm_eq_abs] using hCbound t ht1
    have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hb (convex_Icc (0 : ℝ) s)
      ⟨le_rfl, hs.1⟩ ⟨hs.1, le_rfl⟩
    have h2 : |g' s - g' 0| ≤ C * s := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hs.1] using h
    exact h2
  let Phi : ℝ → ℝ := fun t => g t - g 0 - t * g' 0
  have hPhi : ∀ t : ℝ, HasDerivAt Phi (g' t - g' 0) t := by
    intro t
    have h1 : HasDerivAt (fun u : ℝ => g u - g 0 - u * g' 0) (g' t - g' 0) t := by
      have hbase := ((hg_deriv t).sub (hasDerivAt_const t (g 0))).sub
        ((hasDerivAt_id t).mul_const (g' 0))
      simpa using hbase
    exact h1
  have hgd : Differentiable ℝ g' := fun t => (hg'_deriv t).differentiableAt
  have hcont : Continuous (fun t : ℝ => g' t - g' 0) := hgd.continuous.sub continuous_const
  have hFTC : g 1 - g 0 - g' 0 = ∫ s in (0 : ℝ)..1, (g' s - g' 0) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := Phi) (a := (0 : ℝ)) (b := 1)
      (fun t _ => hPhi t) (hcont.intervalIntegrable 0 1)
    rw [h]
    show g 1 - g 0 - g' 0 = (g 1 - g 0 - 1 * g' 0) - (g 0 - g 0 - 0 * g' 0)
    ring
  have hbound : |∫ s in (0 : ℝ)..1, (g' s - g' 0)| ≤ C / 2 := by
    have h1 : |∫ s in (0 : ℝ)..1, (g' s - g' 0)| ≤ ∫ s in (0 : ℝ)..1, |g' s - g' 0| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    have h2 : (∫ s in (0 : ℝ)..1, |g' s - g' 0|) ≤ ∫ s in (0 : ℝ)..1, C * s := by
      refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ ?_
      · exact hcont.abs.intervalIntegrable 0 1
      · exact (continuous_const.mul continuous_id).intervalIntegrable 0 1
      · intro s hs
        exact hMVT s hs
    have h3 : (∫ s in (0 : ℝ)..1, C * s) = C / 2 := by
      rw [intervalIntegral.integral_const_mul]
      have hid : (∫ s in (0 : ℝ)..1, s) = 1 / 2 := by
        have hderiv : ∀ t : ℝ, HasDerivAt (fun u : ℝ => (1 / 2) * (u * u)) t t := by
          intro t
          have hbase : HasDerivAt (fun u : ℝ => (1 / 2) * (u * u)) ((1 / 2) * (t + t)) t := by
            simpa [smul_eq_mul] using
              ((hasDerivAt_id t).smul (hasDerivAt_id t)).const_mul ((1 : ℝ) / 2)
          convert hbase using 1
          ring
        have hinter : IntervalIntegrable (fun s : ℝ => s) volume 0 1 :=
          continuous_id.intervalIntegrable 0 1
        have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := fun u : ℝ => (1 / 2) * (u * u)) (f' := fun s : ℝ => s)
          (a := (0 : ℝ)) (b := 1) (fun t _ => hderiv t) hinter
        rw [h]
        simp only [mul_one, one_mul, mul_zero, sub_zero]
      rw [hid]
      ring
    linarith
  have hg1 : g 1 = (fderiv ℝ f (x + d)) (Pi.single j (1 : ℝ)) := by
    show (fderiv ℝ f (x + 1 • d)) (Pi.single j (1 : ℝ)) =
      (fderiv ℝ f (x + d)) (Pi.single j (1 : ℝ))
    rw [one_smul]
  have hg0 : g 0 = (fderiv ℝ f x) (Pi.single j (1 : ℝ)) := by
    show (fderiv ℝ f (x + (0 : ℝ) • d)) (Pi.single j (1 : ℝ)) =
      (fderiv ℝ f x) (Pi.single j (1 : ℝ))
    rw [zero_smul, add_zero]
  have hg'0 : g' 0 = ∑ k : Fin p,
      (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) x)
        (Pi.single k (1 : ℝ)) * d k := by
    show (∑ k : Fin p, (fderiv ℝ F (x + (0 : ℝ) • d)) (Pi.single k (1 : ℝ)) * d k) = _
    rw [zero_smul, add_zero]
  have hmain : |g 1 - g 0 - g' 0| ≤ C / 2 := by
    rw [hFTC]
    exact hbound
  have hrhs : (1 / 2 : ℝ) * ∑ k : Fin p, ∑ l : Fin p, Q k l * |d k| * |d l| = C / 2 := by
    show (1 / 2 : ℝ) * ∑ k : Fin p, ∑ l : Fin p, Q k l * |d k| * |d l|
      = (∑ k : Fin p, ∑ l : Fin p, Q k l * |d k| * |d l|) / 2
    ring
  rw [hrhs, ← hg1, ← hg0, ← hg'0]
  exact hmain
  /- @proof-region region.target-node.session.f3ac228d8893e804 end -/

end

end Statlib.Imported

