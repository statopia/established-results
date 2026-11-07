import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_3561563138_949e5db8_4e13e20e

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
theorem statopia_math_node_1332223818_b5c088a2 : ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n m p : ℕ} (hn : 0 < n) (hm : 0 < m) (hp : 0 < p)
    (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
    (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
    (hFm : ∀ i : Fin n, Measurable (F i))
    (hGm : ∀ i : Fin m, Measurable (G i))
    (hind : iIndepFun (β := fun _ => Fin p → ℝ) (jointFam X Y F G) P)
    (hMemX : ∀ (i : Fin n) (j : Fin p), MemLp (fun ω => X i ω j) 2 P)
    (hMemY : ∀ (i : Fin m) (j : Fin p), MemLp (fun ω => Y i ω j) 2 P)
    (hMeanX : ∀ (i : Fin n) (j : Fin p), ∫ ω, X i ω j ∂P = muX j)
    (hMeanY : ∀ (i : Fin m) (j : Fin p), ∫ ω, Y i ω j ∂P = muY j)
    (hGaussF : ∀ i : Fin n,
      IsCenteredGaussianVector P (fun ω j => F i ω j - muX j) (covX P muX X i))
    (hGaussG : ∀ i : Fin m,
      IsCenteredGaussianVector P (fun ω j => G i ω j - muY j) (covY P muY Y i)),
    ∀ j : Fin p,
      (∫ ω, (combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j) ^ 2 ∂P)
        = (∫ ω, (combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j) ^ 2 ∂P) := by
  /- @proof-region region.target-node.session.a85609cf2a7de307 begin -/
  intro Ω _ P _ n m p hn hm hp delta muX muY X Y F G hFm hGm hind hMemX hMemY hMeanX hMeanY
    hGaussF hGaussG j
  have hgen : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (wgt : ι → ℝ) (u : ι → Ω → ℝ),
      (∀ i, MemLp (u i) 2 P) →
      (∀ i k, i ≠ k → ∫ ω, u i ω * u k ω ∂P = 0) →
      ∫ ω, (∑ i, wgt i * u i ω) ^ 2 ∂P = ∑ i, wgt i ^ 2 * ∫ ω, u i ω * u i ω ∂P := by
    intro ι _ _ wgt u hM hX
    have hpt : (fun ω => (∑ i, wgt i * u i ω) ^ 2)
        = fun ω => ∑ i, ∑ k, (wgt i * wgt k) * (u i ω * u k ω) := by
      funext ω
      rw [sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => by ring))
    rw [hpt]
    rw [show ∫ ω, ∑ i, ∑ k, wgt i * wgt k * (u i ω * u k ω) ∂P
        = ∑ i, ∫ ω, ∑ k, wgt i * wgt k * (u i ω * u k ω) ∂P from
      integral_finset_sum Finset.univ (fun i _ =>
        integrable_finset_sum Finset.univ (fun k _ =>
          (MeasureTheory.MemLp.integrable_mul (hM i) (hM k)).const_mul (wgt i * wgt k)))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hval : ∀ k, ∫ ω, wgt i * wgt k * (u i ω * u k ω) ∂P
        = if i = k then wgt i ^ 2 * ∫ ω, u i ω * u i ω ∂P else 0 := by
      intro k
      by_cases hik : i = k
      · subst hik
        rw [integral_const_mul, if_pos rfl]
        ring
      · rw [integral_const_mul, hX i k hik, mul_zero, if_neg hik]
    rw [show ∫ ω, ∑ k, wgt i * wgt k * (u i ω * u k ω) ∂P
        = ∑ k, ∫ ω, wgt i * wgt k * (u i ω * u k ω) ∂P from
      integral_finset_sum Finset.univ (fun k _ =>
        (MeasureTheory.MemLp.integrable_mul (hM i) (hM k)).const_mul (wgt i * wgt k))]
    simp only [hval]
    simp
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hblock : ∀ (k : ℕ) (hk : 0 < k) (c : ℝ) (V : Fin k → ℝ) (mu : ℝ),
      ∑ i : Fin k, ((Real.sqrt (k:ℝ))⁻¹ * c) * (V i - mu)
        = c * ((Real.sqrt (k:ℝ))⁻¹ * (∑ i : Fin k, V i)) - c * Real.sqrt (k:ℝ) * mu := by
    intro k hk c V mu
    have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
    have hkroot : (Real.sqrt (k:ℝ))⁻¹ * (k:ℝ) = Real.sqrt (k:ℝ) := by
      have hsq : Real.sqrt (k:ℝ) * Real.sqrt (k:ℝ) = (k:ℝ) := Real.mul_self_sqrt hkpos.le
      have hne : Real.sqrt (k:ℝ) ≠ 0 := (Real.sqrt_pos.2 hkpos).ne'
      have h2 : (Real.sqrt (k:ℝ))⁻¹ * (Real.sqrt (k:ℝ) * Real.sqrt (k:ℝ)) = Real.sqrt (k:ℝ) := by
        rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
      rw [hsq] at h2
      exact h2
    have h1 : (Real.sqrt (k:ℝ))⁻¹ * ((k:ℝ) * mu) = Real.sqrt (k:ℝ) * mu := by
      rw [← mul_assoc, hkroot]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    linear_combination (-c) * h1
  have hred : ∀ (Z : Fin n → Ω → Fin p → ℝ) (W : Fin m → Ω → Fin p → ℝ) (ω : Ω),
      combVec n m (delta n m) muX muY (fun i => Z i ω) (fun i => W i ω) j
        = ∑ I : Fin n ⊕ Fin m,
            Sum.elim (fun _ => (Real.sqrt (n:ℝ))⁻¹) (fun _ => delta n m * (Real.sqrt (m:ℝ))⁻¹) I
              * Sum.elim (fun i ω => Z i ω j - muX j) (fun i ω => W i ω j - muY j) I ω := by
    intro Z W ω
    have hX := hblock n hn 1 (fun i => Z i ω j) (muX j)
    have hY := hblock m hm (delta n m) (fun i => W i ω j) (muY j)
    simp only [mul_one, one_mul] at hX hY
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    simp only [combVec, normSum]
    rw [show (∑ x : Fin m, delta n m * (Real.sqrt (m:ℝ))⁻¹ * (W x ω j - muY j))
        = ∑ x : Fin m, (Real.sqrt (m:ℝ))⁻¹ * delta n m * (W x ω j - muY j) from
      Finset.sum_congr rfl (fun x _ => by ring)]
    rw [hX, hY]
    ring
  have hconstInt : ∀ c : ℝ, Integrable (fun _ : Ω => c) P := fun c =>
    MeasureTheory.memLp_one_iff_integrable.mp (MeasureTheory.memLp_const c)
  have hcint : ∀ c : ℝ, ∫ _ : Ω, c ∂P = c := by
    intro c
    rw [integral_const]
    simp
  have hmeanAX : ∀ i : Fin n, ∫ ω, (X i ω j - muX j) ∂P = 0 := by
    intro i
    have hraw : ∫ ω, ((fun ω => X i ω j) * fun _ : Ω => (1:ℝ)) ω ∂P = muX j := by
      rw [show (fun ω => ((fun ω => X i ω j) * fun _ : Ω => (1:ℝ)) ω) = fun ω => X i ω j from
        funext (fun ω => mul_one _)]
      exact hMeanX i j
    have hsub : ∫ ω, (((fun ω => X i ω j) * fun _ : Ω => (1:ℝ)) ω - muX j) ∂P = 0 := by
      rw [show ∫ ω, (((fun ω => X i ω j) * fun _ : Ω => (1:ℝ)) ω - muX j) ∂P
          = (∫ ω, ((fun ω => X i ω j) * fun _ : Ω => (1:ℝ)) ω ∂P) - ∫ ω, muX j ∂P from
        integral_sub (MeasureTheory.MemLp.integrable_mul (hMemX i j)
          (MeasureTheory.memLp_const (1:ℝ) : MemLp (fun _ : Ω => (1:ℝ)) 2 P))
          (hconstInt (muX j)),
        hraw, hcint, sub_self]
    rwa [show (fun ω => (((fun ω => X i ω j) * fun _ : Ω => (1:ℝ)) ω - muX j))
      = fun ω => X i ω j - muX j from funext (fun ω => by simp)] at hsub
  have hmeanAY : ∀ i : Fin m, ∫ ω, (Y i ω j - muY j) ∂P = 0 := by
    intro i
    have hraw : ∫ ω, ((fun ω => Y i ω j) * fun _ : Ω => (1:ℝ)) ω ∂P = muY j := by
      rw [show (fun ω => ((fun ω => Y i ω j) * fun _ : Ω => (1:ℝ)) ω) = fun ω => Y i ω j from
        funext (fun ω => mul_one _)]
      exact hMeanY i j
    have hsub : ∫ ω, (((fun ω => Y i ω j) * fun _ : Ω => (1:ℝ)) ω - muY j) ∂P = 0 := by
      rw [show ∫ ω, (((fun ω => Y i ω j) * fun _ : Ω => (1:ℝ)) ω - muY j) ∂P
          = (∫ ω, ((fun ω => Y i ω j) * fun _ : Ω => (1:ℝ)) ω ∂P) - ∫ ω, muY j ∂P from
        integral_sub (MeasureTheory.MemLp.integrable_mul (hMemY i j)
          (MeasureTheory.memLp_const (1:ℝ) : MemLp (fun _ : Ω => (1:ℝ)) 2 P))
          (hconstInt (muY j)),
        hraw, hcint, sub_self]
    rwa [show (fun ω => (((fun ω => Y i ω j) * fun _ : Ω => (1:ℝ)) ω - muY j))
      = fun ω => Y i ω j - muY j from funext (fun ω => by simp)] at hsub
  have hzero : ∀ (f g : Ω → ℝ), f ⟂ᵢ[P] g → MemLp f 2 P → MemLp g 2 P →
      (∫ ω, f ω ∂P = 0) → (∫ ω, g ω ∂P = 0) → ∫ ω, f ω * g ω ∂P = 0 := by
    intro f g hfg hfm hgm hf0 hg0
    rw [show ∫ ω, f ω * g ω ∂P = (∫ ω, f ω ∂P) * ∫ ω, g ω ∂P from
      ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral hfg hfm.aestronglyMeasurable
        hgm.aestronglyMeasurable]
    rw [hf0, hg0, mul_zero]
  have hcoord : ∀ (I K : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))), I ≠ K → ∀ (c d : ℝ),
      (fun ω => jointFam X Y F G I ω j - c) ⟂ᵢ[P] (fun ω => jointFam X Y F G K ω j - d) := by
    intro I K hIK c d
    have h1 : jointFam X Y F G I ⟂ᵢ[P] jointFam X Y F G K := hind.indepFun hIK
    have hmc : Measurable (fun v : Fin p → ℝ => v j - c) :=
      (measurable_pi_apply j).sub measurable_const
    have hmd : Measurable (fun v : Fin p → ℝ => v j - d) :=
      (measurable_pi_apply j).sub measurable_const
    have h2 := h1.comp hmc hmd
    simpa using h2
  have hMemU : ∀ I : Fin n ⊕ Fin m,
      MemLp (Sum.elim (fun i ω => X i ω j - muX j) (fun i ω => Y i ω j - muY j) I) 2 P := by
    intro I
    cases I with
    | inl i => exact (hMemX i j).sub (MeasureTheory.memLp_const (muX j))
    | inr i => exact (hMemY i j).sub (MeasureTheory.memLp_const (muY j))
  have hMeanU : ∀ I : Fin n ⊕ Fin m,
      ∫ ω, Sum.elim (fun i ω => X i ω j - muX j) (fun i ω => Y i ω j - muY j) I ω ∂P = 0 := by
    intro I
    cases I with
    | inl i => exact hmeanAX i
    | inr i => exact hmeanAY i
  have hCrossU : ∀ I K : Fin n ⊕ Fin m, I ≠ K →
      ∫ ω, Sum.elim (fun i ω => X i ω j - muX j) (fun i ω => Y i ω j - muY j) I ω
        * Sum.elim (fun i ω => X i ω j - muX j) (fun i ω => Y i ω j - muY j) K ω ∂P = 0 := by
    intro I K hIK
    cases I with
    | inl i =>
      cases K with
      | inl k =>
        have hik : i ≠ k := fun h => hIK (by rw [h])
        exact hzero _ _ (hcoord (Sum.inl i) (Sum.inl k) (by simp [hik]) (muX j) (muX j))
          (hMemU _) (hMemU _) (hMeanU _) (hMeanU _)
      | inr k =>
        exact hzero _ _ (hcoord (Sum.inl i) (Sum.inr (Sum.inl k)) (by simp) (muX j) (muY j))
          (hMemU _) (hMemU _) (hMeanU _) (hMeanU _)
    | inr i =>
      cases K with
      | inl k =>
        exact hzero _ _ (hcoord (Sum.inr (Sum.inl i)) (Sum.inl k) (by simp) (muY j) (muX j))
          (hMemU _) (hMemU _) (hMeanU _) (hMeanU _)
      | inr k =>
        have hik : i ≠ k := fun h => hIK (by rw [h])
        exact hzero _ _ (hcoord (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl k)) (by simp [hik])
          (muY j) (muY j)) (hMemU _) (hMemU _) (hMeanU _) (hMeanU _)
  have hXY : ∫ ω, (combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j) ^ 2 ∂P
      = (Real.sqrt (n:ℝ))⁻¹ ^ 2 * (∑ i : Fin n, covX P muX X i j j)
        + (delta n m * (Real.sqrt (m:ℝ))⁻¹) ^ 2 * (∑ i : Fin m, covY P muY Y i j j) := by
    rw [show (fun ω => (combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j) ^ 2)
        = fun ω => (∑ I : Fin n ⊕ Fin m,
            Sum.elim (fun _ => (Real.sqrt (n:ℝ))⁻¹) (fun _ => delta n m * (Real.sqrt (m:ℝ))⁻¹) I
              * Sum.elim (fun i ω => X i ω j - muX j) (fun i ω => Y i ω j - muY j) I ω) ^ 2 from
      funext (fun ω => by rw [hred X Y ω])]
    rw [hgen _ _ hMemU hCrossU, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    simp only [covX, covY]
  have hp1 : 1 ≤ p := Nat.succ_le_of_lt hp
  have hmeasF : ∀ (i : Fin n) (jj : Fin p), AEMeasurable (fun ω => F i ω jj - muX jj) P := by
    intro i jj
    have hm : Measurable (fun ω => F i ω jj) := (measurable_pi_apply jj).comp (hFm i)
    exact (hm.sub measurable_const).aemeasurable
  have hmeasG : ∀ (i : Fin m) (jj : Fin p), AEMeasurable (fun ω => G i ω jj - muY jj) P := by
    intro i jj
    have hm : Measurable (fun ω => G i ω jj) := (measurable_pi_apply jj).comp (hGm i)
    exact (hm.sub measurable_const).aemeasurable
  have hGF := fun i : Fin n =>
    statopia_math_node_3561563138_949e5db8 P hp1 (fun ω jj => F i ω jj - muX jj) (covX P muX X i)
      (hmeasF i) (hGaussF i)
  have hGG := fun i : Fin m =>
    statopia_math_node_3561563138_949e5db8 P hp1 (fun ω jj => G i ω jj - muY jj) (covY P muY Y i)
      (hmeasG i) (hGaussG i)
  have hMemF : ∀ i : Fin n, MemLp (fun ω => F i ω j - muX j) 2 P := fun i => (hGF i).2.1 j
  have hMeanF : ∀ i : Fin n, ∫ ω, (F i ω j - muX j) ∂P = 0 := fun i => (hGF i).1 j
  have hDiagF : ∀ i : Fin n,
      ∫ ω, (F i ω j - muX j) * (F i ω j - muX j) ∂P = covX P muX X i j j :=
    fun i => (hGF i).2.2 j
  have hMemG : ∀ i : Fin m, MemLp (fun ω => G i ω j - muY j) 2 P := fun i => (hGG i).2.1 j
  have hMeanG : ∀ i : Fin m, ∫ ω, (G i ω j - muY j) ∂P = 0 := fun i => (hGG i).1 j
  have hDiagG : ∀ i : Fin m,
      ∫ ω, (G i ω j - muY j) * (G i ω j - muY j) ∂P = covY P muY Y i j j :=
    fun i => (hGG i).2.2 j
  have hMemV : ∀ I : Fin n ⊕ Fin m,
      MemLp (Sum.elim (fun i ω => F i ω j - muX j) (fun i ω => G i ω j - muY j) I) 2 P := by
    intro I
    cases I with
    | inl i => exact hMemF i
    | inr i => exact hMemG i
  have hMeanV : ∀ I : Fin n ⊕ Fin m,
      ∫ ω, Sum.elim (fun i ω => F i ω j - muX j) (fun i ω => G i ω j - muY j) I ω ∂P = 0 := by
    intro I
    cases I with
    | inl i => exact hMeanF i
    | inr i => exact hMeanG i
  have hCrossV : ∀ I K : Fin n ⊕ Fin m, I ≠ K →
      ∫ ω, Sum.elim (fun i ω => F i ω j - muX j) (fun i ω => G i ω j - muY j) I ω
        * Sum.elim (fun i ω => F i ω j - muX j) (fun i ω => G i ω j - muY j) K ω ∂P = 0 := by
    intro I K hIK
    cases I with
    | inl i =>
      cases K with
      | inl k =>
        have hik : i ≠ k := fun h => hIK (by rw [h])
        exact hzero _ _ (hcoord (Sum.inr (Sum.inr (Sum.inl i))) (Sum.inr (Sum.inr (Sum.inl k)))
          (by simp [hik]) (muX j) (muX j)) (hMemV _) (hMemV _) (hMeanV _) (hMeanV _)
      | inr k =>
        exact hzero _ _ (hcoord (Sum.inr (Sum.inr (Sum.inl i))) (Sum.inr (Sum.inr (Sum.inr k)))
          (by simp) (muX j) (muY j)) (hMemV _) (hMemV _) (hMeanV _) (hMeanV _)
    | inr i =>
      cases K with
      | inl k =>
        exact hzero _ _ (hcoord (Sum.inr (Sum.inr (Sum.inr i))) (Sum.inr (Sum.inr (Sum.inl k)))
          (by simp) (muY j) (muX j)) (hMemV _) (hMemV _) (hMeanV _) (hMeanV _)
      | inr k =>
        have hik : i ≠ k := fun h => hIK (by rw [h])
        exact hzero _ _ (hcoord (Sum.inr (Sum.inr (Sum.inr i))) (Sum.inr (Sum.inr (Sum.inr k)))
          (by simp [hik]) (muY j) (muY j)) (hMemV _) (hMemV _) (hMeanV _) (hMeanV _)
  have hFG : ∫ ω, (combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j) ^ 2 ∂P
      = (Real.sqrt (n:ℝ))⁻¹ ^ 2 * (∑ i : Fin n, covX P muX X i j j)
        + (delta n m * (Real.sqrt (m:ℝ))⁻¹) ^ 2 * (∑ i : Fin m, covY P muY Y i j j) := by
    rw [show (fun ω => (combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j) ^ 2)
        = fun ω => (∑ I : Fin n ⊕ Fin m,
            Sum.elim (fun _ => (Real.sqrt (n:ℝ))⁻¹) (fun _ => delta n m * (Real.sqrt (m:ℝ))⁻¹) I
              * Sum.elim (fun i ω => F i ω j - muX j) (fun i ω => G i ω j - muY j) I ω) ^ 2 from
      funext (fun ω => by rw [hred F G ω])]
    rw [hgen _ _ hMemV hCrossV, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    simp only [hDiagF, hDiagG]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
  exact hFG.trans hXY.symm

  /- @proof-region region.target-node.session.a85609cf2a7de307 end -/

end

end Statlib.Imported

