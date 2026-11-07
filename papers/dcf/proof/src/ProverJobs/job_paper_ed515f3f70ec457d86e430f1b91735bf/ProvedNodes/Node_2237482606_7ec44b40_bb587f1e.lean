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
theorem statopia_math_node_2237482606_7ec44b40 : ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n m p : ℕ) (hn : 0 < n) (hm : 0 < m) (hp : 0 < p)
    (delta : ℝ) (muX muY : Fin p → ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
    (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
    (hFm : ∀ i : Fin n, Measurable (F i))
    (hGm : ∀ i : Fin m, Measurable (G i))
    (hindep : iIndepFun (β := fun _ => Fin p → ℝ) (jointFam X Y F G) P)
    (hFgauss : ∀ i : Fin n,
      IsCenteredGaussianVector P (fun ω j => F i ω j - muX j) (covX P muX X i))
    (hGgauss : ∀ i : Fin m,
      IsCenteredGaussianVector P (fun ω j => G i ω j - muY j) (covY P muY Y i)),
    IsCenteredGaussianVector P
      (fun ω => combVec n m delta muX muY (fun i => F i ω) (fun i => G i ω))
      ((n : ℝ)⁻¹ • (∑ i : Fin n, covX P muX X i) +
        delta ^ 2 • ((m : ℝ)⁻¹ • (∑ i : Fin m, covY P muY Y i))) := by
  /- @proof-region region.target-node.session.9a789306fe42c6c7 begin -/
  intro Ω hΩ P hP n m p hn hm hp delta muX muY X Y F G hFm hGm hindep hFgauss hGgauss
  have hnpos : (0:ℝ) < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hmpos : (0:ℝ) < Real.sqrt (m:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  have hcXn : (Real.sqrt (n:ℝ))⁻¹ * (n:ℝ) = Real.sqrt (n:ℝ) := by
    have h2 : Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ) = (n:ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg n)
    have h3 : (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ)) = Real.sqrt (n:ℝ) := by
      rw [← mul_assoc, inv_mul_cancel₀ hnpos.ne', one_mul]
    rw [h2] at h3
    exact h3
  have hcYm : (Real.sqrt (m:ℝ))⁻¹ * (m:ℝ) = Real.sqrt (m:ℝ) := by
    have h2 : Real.sqrt (m:ℝ) * Real.sqrt (m:ℝ) = (m:ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg m)
    have h3 : (Real.sqrt (m:ℝ))⁻¹ * (Real.sqrt (m:ℝ) * Real.sqrt (m:ℝ)) = Real.sqrt (m:ℝ) := by
      rw [← mul_assoc, inv_mul_cancel₀ hmpos.ne', one_mul]
    rw [h2] at h3
    exact h3
  have hcomb : ∀ (ω : Ω) (j : Fin p),
      combVec n m delta muX muY (fun i => F i ω) (fun i => G i ω) j
        = (Real.sqrt (n:ℝ))⁻¹ * ∑ i : Fin n, (F i ω j - muX j)
          + delta * ((Real.sqrt (m:ℝ))⁻¹ * ∑ i : Fin m, (G i ω j - muY j)) := by
    intro ω j
    have hc : (∑ _i : Fin n, muX j) = (n:ℝ) * muX j := by simp
    have hcm : (∑ _i : Fin m, muY j) = (m:ℝ) * muY j := by simp
    have hF : (Real.sqrt (n:ℝ))⁻¹ * ∑ i : Fin n, (F i ω j - muX j)
        = (Real.sqrt (n:ℝ))⁻¹ * (∑ i : Fin n, F i ω j) - Real.sqrt (n:ℝ) * muX j := by
      rw [Finset.sum_sub_distrib, mul_sub, hc, ← mul_assoc, hcXn]
    have hG : (Real.sqrt (m:ℝ))⁻¹ * ∑ i : Fin m, (G i ω j - muY j)
        = (Real.sqrt (m:ℝ))⁻¹ * (∑ i : Fin m, G i ω j) - Real.sqrt (m:ℝ) * muY j := by
      rw [Finset.sum_sub_distrib, mul_sub, hcm, ← mul_assoc, hcYm]
    simp only [combVec, normSum]
    rw [hF, hG]
    ring
  have hmeas : Measurable (fun ω => combVec n m delta muX muY (fun i => F i ω) (fun i => G i ω)) := by
    rw [measurable_pi_iff]
    intro j
    have h1 : Measurable (fun ω => ∑ i : Fin n, (F i ω j - muX j)) :=
      Finset.measurable_sum _ (fun i _ => (Measurable.eval (a := j) (hFm i)).sub measurable_const)
    have h2 : Measurable (fun ω => ∑ i : Fin m, (G i ω j - muY j)) :=
      Finset.measurable_sum _ (fun i _ => (Measurable.eval (a := j) (hGm i)).sub measurable_const)
    have h3 : (fun ω => combVec n m delta muX muY (fun i => F i ω) (fun i => G i ω) j)
        = fun ω => (Real.sqrt (n:ℝ))⁻¹ * ∑ i : Fin n, (F i ω j - muX j)
            + delta * ((Real.sqrt (m:ℝ))⁻¹ * ∑ i : Fin m, (G i ω j - muY j)) :=
      funext fun ω => hcomb ω j
    rw [h3]
    exact (h1.const_mul _).add ((h2.const_mul _).const_mul _)
  have key : ∀ u : Fin p → ℝ,
      (Integrable (fun ω : Ω => Real.exp (∑ j, u j * combVec n m delta muX muY (fun i => F i ω) (fun i => G i ω) j)) P ∧
      (∫ ω, Real.exp (∑ j, u j * combVec n m delta muX muY (fun i => F i ω) (fun i => G i ω) j) ∂P
        = Real.exp ((∑ i, ∑ j, u i * ((n : ℝ)⁻¹ • (∑ i : Fin n, covX P muX X i) +
            delta ^ 2 • ((m : ℝ)⁻¹ • (∑ i : Fin m, covY P muY Y i))) i j * u j) / 2))) := by
    intro u
    classical
    have hproj : ∀ j : Fin p, Measurable (fun x : Fin p → ℝ => x j) := fun j => measurable_pi_apply j
    have hlinX : Measurable (fun x : Fin p → ℝ => (Real.sqrt (n:ℝ))⁻¹ * ∑ j, u j * (x j - muX j)) := by
      refine Measurable.const_mul ?_ _
      exact Finset.measurable_sum _ (fun j _ => Measurable.const_mul ((hproj j).sub measurable_const) (u j))
    have hlinY : Measurable (fun x : Fin p → ℝ => delta * (Real.sqrt (m:ℝ))⁻¹ * ∑ j, u j * (x j - muY j)) := by
      refine Measurable.const_mul ?_ _
      exact Finset.measurable_sum _ (fun j _ => Measurable.const_mul ((hproj j).sub measurable_const) (u j))
    have hgmeas : ∀ i : Fin n ⊕ Fin m, Measurable
        (Sum.elim (fun _ => fun x : Fin p → ℝ => (Real.sqrt (n:ℝ))⁻¹ * ∑ j, u j * (x j - muX j))
          (fun _ => fun x : Fin p → ℝ => delta * (Real.sqrt (m:ℝ))⁻¹ * ∑ j, u j * (x j - muY j)) i) := by
      intro i
      cases i with
      | inl a => exact hlinX
      | inr a => exact hlinY
    have hJindep : iIndepFun (fun i : Fin n ⊕ Fin m => jointFam X Y F G (Sum.inr (Sum.inr i))) P :=
      hindep.precomp (g := fun i : Fin n ⊕ Fin m => (Sum.inr (Sum.inr i) : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))))
        (by intro a b hab; simpa using hab)
    have hZindep : iIndepFun (fun i : Fin n ⊕ Fin m => fun ω : Ω =>
        Sum.elim (fun _ => fun x : Fin p → ℝ => (Real.sqrt (n:ℝ))⁻¹ * ∑ j, u j * (x j - muX j))
          (fun _ => fun x : Fin p → ℝ => delta * (Real.sqrt (m:ℝ))⁻¹ * ∑ j, u j * (x j - muY j))
          i (jointFam X Y F G (Sum.inr (Sum.inr i)) ω)) P :=
      hJindep.comp _ hgmeas
    have hEindep : iIndepFun (fun i : Fin n ⊕ Fin m => fun ω : Ω => Real.exp (
        Sum.elim (fun _ => fun x : Fin p → ℝ => (Real.sqrt (n:ℝ))⁻¹ * ∑ j, u j * (x j - muX j))
          (fun _ => fun x : Fin p → ℝ => delta * (Real.sqrt (m:ℝ))⁻¹ * ∑ j, u j * (x j - muY j))
          i (jointFam X Y F G (Sum.inr (Sum.inr i)) ω))) P :=
      hZindep.comp (fun _ => Real.exp) (fun _ => Real.measurable_exp)
    have hZmeas : ∀ i : Fin n ⊕ Fin m, Measurable (fun ω : Ω =>
        Sum.elim (fun _ => fun x : Fin p → ℝ => (Real.sqrt (n:ℝ))⁻¹ * ∑ j, u j * (x j - muX j))
          (fun _ => fun x : Fin p → ℝ => delta * (Real.sqrt (m:ℝ))⁻¹ * ∑ j, u j * (x j - muY j))
          i (jointFam X Y F G (Sum.inr (Sum.inr i)) ω)) := by
      intro i
      cases i with
      | inl a =>
        exact Measurable.const_mul (Finset.measurable_sum _
          (fun j _ => Measurable.const_mul ((Measurable.eval (a := j) (hFm a)).sub measurable_const) (u j))) _
      | inr a =>
        exact Measurable.const_mul (Finset.measurable_sum _
          (fun j _ => Measurable.const_mul ((Measurable.eval (a := j) (hGm a)).sub measurable_const) (u j))) _
    have hZaes : ∀ i : Fin n ⊕ Fin m, AEStronglyMeasurable (fun ω : Ω => Real.exp (
        Sum.elim (fun _ => fun x : Fin p → ℝ => (Real.sqrt (n:ℝ))⁻¹ * ∑ j, u j * (x j - muX j))
          (fun _ => fun x : Fin p → ℝ => delta * (Real.sqrt (m:ℝ))⁻¹ * ∑ j, u j * (x j - muY j))
          i (jointFam X Y F G (Sum.inr (Sum.inr i)) ω))) P :=
      fun i => (hZmeas i).exp.aestronglyMeasurable
    have hFW : ∀ (a : Fin n) (ω : Ω), (∑ j, (Real.sqrt (n:ℝ))⁻¹ * u j * (F a ω j - muX j))
        = (Real.sqrt (n:ℝ))⁻¹ * ∑ j, u j * (F a ω j - muX j) := by
      intro a ω
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have hGW : ∀ (a : Fin m) (ω : Ω), (∑ j, delta * (Real.sqrt (m:ℝ))⁻¹ * u j * (G a ω j - muY j))
        = delta * (Real.sqrt (m:ℝ))⁻¹ * ∑ j, u j * (G a ω j - muY j) := by
      intro a ω
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have hFmgf : ∀ a : Fin n, (∫ ω, Real.exp (∑ j, (Real.sqrt (n:ℝ))⁻¹ * u j * (F a ω j - muX j)) ∂P)
        = Real.exp ((∑ i, ∑ j, (Real.sqrt (n:ℝ))⁻¹ * u i * covX P muX X a i j * ((Real.sqrt (n:ℝ))⁻¹ * u j)) / 2) := by
      intro a
      obtain ⟨-, -, h3⟩ := hFgauss a
      exact h3 (fun j => (Real.sqrt (n:ℝ))⁻¹ * u j)
    have hGmgf : ∀ a : Fin m, (∫ ω, Real.exp (∑ j, delta * (Real.sqrt (m:ℝ))⁻¹ * u j * (G a ω j - muY j)) ∂P)
        = Real.exp ((∑ i, ∑ j, delta * (Real.sqrt (m:ℝ))⁻¹ * u i * covY P muY Y a i j * (delta * (Real.sqrt (m:ℝ))⁻¹ * u j)) / 2) := by
      intro a
      obtain ⟨-, -, h3⟩ := hGgauss a
      exact h3 (fun j => delta * (Real.sqrt (m:ℝ))⁻¹ * u j)
    have hFval : (∏ a : Fin n, ∫ ω, Real.exp ((Real.sqrt (n:ℝ))⁻¹ * ∑ j, u j * (F a ω j - muX j)) ∂P)
        = Real.exp ((∑ a : Fin n, ∑ i, ∑ j, (Real.sqrt (n:ℝ))⁻¹ * u i * covX P muX X a i j * ((Real.sqrt (n:ℝ))⁻¹ * u j)) / 2) := by
      rw [Finset.sum_div, Real.exp_sum]
      exact Finset.prod_congr rfl (fun a _ => by
        rw [← hFmgf a]
        simp only [hFW a])
    have hGval : (∏ a : Fin m, ∫ ω, Real.exp (delta * (Real.sqrt (m:ℝ))⁻¹ * ∑ j, u j * (G a ω j - muY j)) ∂P)
        = Real.exp ((∑ a : Fin m, ∑ i, ∑ j, delta * (Real.sqrt (m:ℝ))⁻¹ * u i * covY P muY Y a i j * (delta * (Real.sqrt (m:ℝ))⁻¹ * u j)) / 2) := by
      rw [Finset.sum_div, Real.exp_sum]
      exact Finset.prod_congr rfl (fun a _ => by
        rw [← hGmgf a]
        simp only [hGW a])
    have hprodval : (∏ i : Fin n ⊕ Fin m, ∫ ω, Real.exp (
        Sum.elim (fun _ => fun x : Fin p → ℝ => (Real.sqrt (n:ℝ))⁻¹ * ∑ j, u j * (x j - muX j))
          (fun _ => fun x : Fin p → ℝ => delta * (Real.sqrt (m:ℝ))⁻¹ * ∑ j, u j * (x j - muY j))
          i (jointFam X Y F G (Sum.inr (Sum.inr i)) ω)) ∂P)
        = Real.exp ((∑ a : Fin n, ∑ i, ∑ j, (Real.sqrt (n:ℝ))⁻¹ * u i * covX P muX X a i j * ((Real.sqrt (n:ℝ))⁻¹ * u j)) / 2)
          * Real.exp ((∑ a : Fin m, ∑ i, ∑ j, delta * (Real.sqrt (m:ℝ))⁻¹ * u i * covY P muY Y a i j * (delta * (Real.sqrt (m:ℝ))⁻¹ * u j)) / 2) := by
      rw [Fintype.prod_sum_type]
      show (∏ a : Fin n, ∫ ω, Real.exp ((Real.sqrt (n:ℝ))⁻¹ * ∑ j, u j * (F a ω j - muX j)) ∂P)
          * (∏ a : Fin m, ∫ ω, Real.exp (delta * (Real.sqrt (m:ℝ))⁻¹ * ∑ j, u j * (G a ω j - muY j)) ∂P)
        = Real.exp ((∑ a : Fin n, ∑ i, ∑ j, (Real.sqrt (n:ℝ))⁻¹ * u i * covX P muX X a i j * ((Real.sqrt (n:ℝ))⁻¹ * u j)) / 2)
          * Real.exp ((∑ a : Fin m, ∑ i, ∑ j, delta * (Real.sqrt (m:ℝ))⁻¹ * u i * covY P muY Y a i j * (delta * (Real.sqrt (m:ℝ))⁻¹ * u j)) / 2)
      rw [hFval, hGval]
    have hexpfact : Real.exp ((∑ a : Fin n, ∑ i, ∑ j, (Real.sqrt (n:ℝ))⁻¹ * u i * covX P muX X a i j * ((Real.sqrt (n:ℝ))⁻¹ * u j)) / 2)
          * Real.exp ((∑ a : Fin m, ∑ i, ∑ j, delta * (Real.sqrt (m:ℝ))⁻¹ * u i * covY P muY Y a i j * (delta * (Real.sqrt (m:ℝ))⁻¹ * u j)) / 2)
        = Real.exp (((∑ a : Fin n, ∑ i, ∑ j, (Real.sqrt (n:ℝ))⁻¹ * u i * covX P muX X a i j * ((Real.sqrt (n:ℝ))⁻¹ * u j))
            + ∑ a : Fin m, ∑ i, ∑ j, delta * (Real.sqrt (m:ℝ))⁻¹ * u i * covY P muY Y a i j * (delta * (Real.sqrt (m:ℝ))⁻¹ * u j)) / 2) := by
      rw [← Real.exp_add]
      congr 1
      rw [add_div]
    have hsumid : ∀ ω : Ω, (∑ j, u j * combVec n m delta muX muY (fun i => F i ω) (fun i => G i ω) j)
        = (∑ i : Fin n, (Real.sqrt (n:ℝ))⁻¹ * ∑ j, u j * (F i ω j - muX j))
          + ∑ i : Fin m, delta * (Real.sqrt (m:ℝ))⁻¹ * ∑ j, u j * (G i ω j - muY j) := by
      intro ω
      have hF : (∑ j, u j * ((Real.sqrt (n:ℝ))⁻¹ * ∑ i : Fin n, (F i ω j - muX j)))
          = ∑ i : Fin n, (Real.sqrt (n:ℝ))⁻¹ * ∑ j, u j * (F i ω j - muX j) := by
        have step : ∀ j : Fin p, u j * ((Real.sqrt (n:ℝ))⁻¹ * ∑ i : Fin n, (F i ω j - muX j))
            = (Real.sqrt (n:ℝ))⁻¹ * ∑ i : Fin n, u j * (F i ω j - muX j) := by
          intro j
          rw [← Finset.mul_sum]
          ring
        rw [Finset.sum_congr rfl (fun j _ => step j), ← Finset.mul_sum, Finset.sum_comm,
          Finset.mul_sum]
      have hG : (∑ j, u j * (delta * ((Real.sqrt (m:ℝ))⁻¹ * ∑ i : Fin m, (G i ω j - muY j))))
          = ∑ i : Fin m, delta * (Real.sqrt (m:ℝ))⁻¹ * ∑ j, u j * (G i ω j - muY j) := by
        have step : ∀ j : Fin p, u j * (delta * ((Real.sqrt (m:ℝ))⁻¹ * ∑ i : Fin m, (G i ω j - muY j)))
            = delta * (Real.sqrt (m:ℝ))⁻¹ * ∑ i : Fin m, u j * (G i ω j - muY j) := by
          intro j
          rw [← Finset.mul_sum]
          ring
        rw [Finset.sum_congr rfl (fun j _ => step j), ← Finset.mul_sum, Finset.sum_comm,
          Finset.mul_sum]
      have expand : ∀ j : Fin p, u j * combVec n m delta muX muY (fun i => F i ω) (fun i => G i ω) j
          = u j * ((Real.sqrt (n:ℝ))⁻¹ * ∑ i : Fin n, (F i ω j - muX j))
            + u j * (delta * ((Real.sqrt (m:ℝ))⁻¹ * ∑ i : Fin m, (G i ω j - muY j))) := by
        intro j
        rw [hcomb ω j, mul_add]
      rw [Finset.sum_congr rfl (fun j _ => expand j), Finset.sum_add_distrib, hF, hG]
    have hbracket : ((∑ a : Fin n, ∑ i, ∑ j, (Real.sqrt (n:ℝ))⁻¹ * u i * covX P muX X a i j * ((Real.sqrt (n:ℝ))⁻¹ * u j))
          + ∑ a : Fin m, ∑ i, ∑ j, delta * (Real.sqrt (m:ℝ))⁻¹ * u i * covY P muY Y a i j * (delta * (Real.sqrt (m:ℝ))⁻¹ * u j))
        = ∑ i, ∑ j, u i * ((n : ℝ)⁻¹ • (∑ i : Fin n, covX P muX X i) +
            delta ^ 2 • ((m : ℝ)⁻¹ • (∑ i : Fin m, covY P muY Y i))) i j * u j := by
      have hcXsq : (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ = (n:ℝ)⁻¹ := by
        rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg n)]
      have hcYsq : delta * (Real.sqrt (m:ℝ))⁻¹ * (delta * (Real.sqrt (m:ℝ))⁻¹) = delta ^ 2 * (m:ℝ)⁻¹ := by
        have h : (Real.sqrt (m:ℝ))⁻¹ * (Real.sqrt (m:ℝ))⁻¹ = (m:ℝ)⁻¹ := by
          rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg m)]
        rw [← h]
        ring
      have hSA : ∀ (i j : Fin p), (∑ a : Fin n, covX P muX X a) i j = ∑ a : Fin n, covX P muX X a i j := by
        intro i j
        first
          | rw [Finset.sum_apply, Finset.sum_apply]
          | simp only [Matrix.sum_apply]
          | simp
      have hSB : ∀ (i j : Fin p), (∑ a : Fin m, covY P muY Y a) i j = ∑ a : Fin m, covY P muY Y a i j := by
        intro i j
        first
          | rw [Finset.sum_apply, Finset.sum_apply]
          | simp only [Matrix.sum_apply]
          | simp
      have hA1 : (∑ a : Fin n, ∑ i : Fin p, ∑ j : Fin p, (Real.sqrt (n:ℝ))⁻¹ * u i * covX P muX X a i j * ((Real.sqrt (n:ℝ))⁻¹ * u j))
          = ∑ a : Fin n, ∑ i : Fin p, ∑ j : Fin p, ((Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹) * (u i * covX P muX X a i j * u j) := by
        refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_)))
        ring
      have hA2 : ((Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹) * (∑ a : Fin n, ∑ i : Fin p, ∑ j : Fin p, u i * covX P muX X a i j * u j)
          = ∑ a : Fin n, ∑ i : Fin p, ∑ j : Fin p, ((Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹) * (u i * covX P muX X a i j * u j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
      have hA : (∑ a : Fin n, ∑ i : Fin p, ∑ j : Fin p, (Real.sqrt (n:ℝ))⁻¹ * u i * covX P muX X a i j * ((Real.sqrt (n:ℝ))⁻¹ * u j))
          = ((Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹) * (∑ a : Fin n, ∑ i : Fin p, ∑ j : Fin p, u i * covX P muX X a i j * u j) :=
        hA1.trans hA2.symm
      have hB1 : (∑ a : Fin m, ∑ i : Fin p, ∑ j : Fin p, delta * (Real.sqrt (m:ℝ))⁻¹ * u i * covY P muY Y a i j * (delta * (Real.sqrt (m:ℝ))⁻¹ * u j))
          = ∑ a : Fin m, ∑ i : Fin p, ∑ j : Fin p, (delta * (Real.sqrt (m:ℝ))⁻¹ * (delta * (Real.sqrt (m:ℝ))⁻¹)) * (u i * covY P muY Y a i j * u j) := by
        refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_)))
        ring
      have hB2 : (delta * (Real.sqrt (m:ℝ))⁻¹ * (delta * (Real.sqrt (m:ℝ))⁻¹)) * (∑ a : Fin m, ∑ i : Fin p, ∑ j : Fin p, u i * covY P muY Y a i j * u j)
          = ∑ a : Fin m, ∑ i : Fin p, ∑ j : Fin p, (delta * (Real.sqrt (m:ℝ))⁻¹ * (delta * (Real.sqrt (m:ℝ))⁻¹)) * (u i * covY P muY Y a i j * u j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
      have hB : (∑ a : Fin m, ∑ i : Fin p, ∑ j : Fin p, delta * (Real.sqrt (m:ℝ))⁻¹ * u i * covY P muY Y a i j * (delta * (Real.sqrt (m:ℝ))⁻¹ * u j))
          = (delta * (Real.sqrt (m:ℝ))⁻¹ * (delta * (Real.sqrt (m:ℝ))⁻¹)) * (∑ a : Fin m, ∑ i : Fin p, ∑ j : Fin p, u i * covY P muY Y a i j * u j) :=
        hB1.trans hB2.symm
      have hC1 : (∑ a : Fin n, ∑ i : Fin p, ∑ j : Fin p, u i * covX P muX X a i j * u j)
          = ∑ i : Fin p, ∑ j : Fin p, ∑ a : Fin n, u i * covX P muX X a i j * u j := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_comm]
      have hC2 : (∑ i : Fin p, ∑ j : Fin p, ∑ a : Fin n, u i * covX P muX X a i j * u j)
          = ∑ i : Fin p, ∑ j : Fin p, u i * ((∑ a : Fin n, covX P muX X a) i j * u j) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        rw [show (∑ a : Fin n, u i * covX P muX X a i j * u j)
            = ∑ a : Fin n, u i * (covX P muX X a i j * u j) from
          Finset.sum_congr rfl (fun a _ => by ring)]
        rw [← Finset.mul_sum, ← Finset.sum_mul, ← hSA i j]
      have hD1 : (∑ a : Fin m, ∑ i : Fin p, ∑ j : Fin p, u i * covY P muY Y a i j * u j)
          = ∑ i : Fin p, ∑ j : Fin p, ∑ a : Fin m, u i * covY P muY Y a i j * u j := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_comm]
      have hD2 : (∑ i : Fin p, ∑ j : Fin p, ∑ a : Fin m, u i * covY P muY Y a i j * u j)
          = ∑ i : Fin p, ∑ j : Fin p, u i * ((∑ a : Fin m, covY P muY Y a) i j * u j) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        rw [show (∑ a : Fin m, u i * covY P muY Y a i j * u j)
            = ∑ a : Fin m, u i * (covY P muY Y a i j * u j) from
          Finset.sum_congr rfl (fun a _ => by ring)]
        rw [← Finset.mul_sum, ← Finset.sum_mul, ← hSB i j]
      have hR1 : (∑ i : Fin p, ∑ j : Fin p, u i * ((n : ℝ)⁻¹ • (∑ i : Fin n, covX P muX X i) + delta ^ 2 • ((m : ℝ)⁻¹ • (∑ i : Fin m, covY P muY Y i))) i j * u j)
          = ∑ i : Fin p, ∑ j : Fin p, u i * ((n:ℝ)⁻¹ * ((∑ a : Fin n, covX P muX X a) i j) + delta ^ 2 * ((m:ℝ)⁻¹ * ((∑ a : Fin m, covY P muY Y a) i j))) * u j := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      have hR2 : (∑ i : Fin p, ∑ j : Fin p, u i * ((n:ℝ)⁻¹ * ((∑ a : Fin n, covX P muX X a) i j) + delta ^ 2 * ((m:ℝ)⁻¹ * ((∑ a : Fin m, covY P muY Y a) i j))) * u j)
          = ∑ i : Fin p, ∑ j : Fin p, ((n:ℝ)⁻¹ * (u i * (((∑ a : Fin n, covX P muX X a) i j) * u j)) + delta ^ 2 * ((m:ℝ)⁻¹ * (u i * (((∑ a : Fin m, covY P muY Y a) i j) * u j)))) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        ring
      have hR4' : (n:ℝ)⁻¹ * (∑ i : Fin p, ∑ j : Fin p, u i * ((∑ a : Fin n, covX P muX X a) i j * u j))
          = ∑ i : Fin p, ∑ j : Fin p, (n:ℝ)⁻¹ * (u i * ((∑ a : Fin n, covX P muX X a) i j * u j)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
      have hR5' : (delta ^ 2 * (m:ℝ)⁻¹) * (∑ i : Fin p, ∑ j : Fin p, u i * ((∑ a : Fin m, covY P muY Y a) i j * u j))
          = ∑ i : Fin p, ∑ j : Fin p, delta ^ 2 * ((m:ℝ)⁻¹ * (u i * ((∑ a : Fin m, covY P muY Y a) i j * u j))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring
      rw [hA, hB, hcXsq, hcYsq, hC1, hC2, hD1, hD2]
      symm
      refine Eq.trans hR1 ?_
      refine Eq.trans hR2 ?_
      rw [hR4', hR5']
      refine Eq.trans ?_ Finset.sum_add_distrib
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact Finset.sum_add_distrib
    have hexp : ∀ ω : Ω, Real.exp (∑ j, u j * combVec n m delta muX muY (fun i => F i ω) (fun i => G i ω) j)
        = ∏ i : Fin n ⊕ Fin m, Real.exp (
            Sum.elim (fun _ => fun x : Fin p → ℝ => (Real.sqrt (n:ℝ))⁻¹ * ∑ j, u j * (x j - muX j))
              (fun _ => fun x : Fin p → ℝ => delta * (Real.sqrt (m:ℝ))⁻¹ * ∑ j, u j * (x j - muY j))
              i (jointFam X Y F G (Sum.inr (Sum.inr i)) ω)) := by
      intro ω
      rw [hsumid ω, Fintype.prod_sum_type, Real.exp_add, Real.exp_sum, Real.exp_sum]
      rfl
    constructor
    · have hFind : iIndepFun (fun i : Fin n => fun ω : Ω =>
          (Real.sqrt (n:ℝ))⁻¹ * ∑ j, u j * (F i ω j - muX j)) P :=
        hZindep.precomp (g := fun i : Fin n => (Sum.inl i : Fin n ⊕ Fin m))
          (by intro a b hab; simpa using hab)
      have hGind : iIndepFun (fun i : Fin m => fun ω : Ω =>
          delta * (Real.sqrt (m:ℝ))⁻¹ * ∑ j, u j * (G i ω j - muY j)) P :=
        hZindep.precomp (g := fun i : Fin m => (Sum.inr i : Fin n ⊕ Fin m))
          (by intro a b hab; simpa using hab)
      have hFmeas' : ∀ i : Fin n, Measurable (fun ω : Ω =>
          (Real.sqrt (n:ℝ))⁻¹ * ∑ j, u j * (F i ω j - muX j)) := fun i => hZmeas (Sum.inl i)
      have hGmeas' : ∀ i : Fin m, Measurable (fun ω : Ω =>
          delta * (Real.sqrt (m:ℝ))⁻¹ * ∑ j, u j * (G i ω j - muY j)) := fun i => hZmeas (Sum.inr i)
      have hFfac : ∀ i ∈ (Finset.univ : Finset (Fin n)), Integrable (fun ω : Ω =>
          Real.exp (1 * ((Real.sqrt (n:ℝ))⁻¹ * ∑ j, u j * (F i ω j - muX j)))) P := by
        intro i _
        obtain ⟨-, h2, -⟩ := hFgauss i
        rw [show (fun ω : Ω => Real.exp (1 * ((Real.sqrt (n:ℝ))⁻¹ * ∑ j, u j * (F i ω j - muX j))))
            = (fun ω : Ω => Real.exp (∑ j, (Real.sqrt (n:ℝ))⁻¹ * u j * (F i ω j - muX j))) from by
          funext ω
          simp only [hFW i, one_mul]]
        exact h2 (fun j => (Real.sqrt (n:ℝ))⁻¹ * u j)
      have hGfac : ∀ i ∈ (Finset.univ : Finset (Fin m)), Integrable (fun ω : Ω =>
          Real.exp (1 * (delta * (Real.sqrt (m:ℝ))⁻¹ * ∑ j, u j * (G i ω j - muY j)))) P := by
        intro i _
        obtain ⟨-, h2, -⟩ := hGgauss i
        rw [show (fun ω : Ω => Real.exp (1 * (delta * (Real.sqrt (m:ℝ))⁻¹ * ∑ j, u j * (G i ω j - muY j))))
            = (fun ω : Ω => Real.exp (∑ j, delta * (Real.sqrt (m:ℝ))⁻¹ * u j * (G i ω j - muY j))) from by
          funext ω
          simp only [hGW i, one_mul]]
        exact h2 (fun j => delta * (Real.sqrt (m:ℝ))⁻¹ * u j)
      have hZF : Integrable (fun ω : Ω =>
          Real.exp (∑ i : Fin n, (Real.sqrt (n:ℝ))⁻¹ * ∑ j, u j * (F i ω j - muX j))) P := by
        have hmain := ProbabilityTheory.iIndepFun.integrable_exp_mul_sum hFind hFmeas'
          (s := Finset.univ) (t := 1) hFfac
        convert hmain using 1
        funext ω
        simp only [one_mul, Finset.sum_apply]
      have hZG : Integrable (fun ω : Ω =>
          Real.exp (∑ i : Fin m, delta * (Real.sqrt (m:ℝ))⁻¹ * ∑ j, u j * (G i ω j - muY j))) P := by
        have hmain := ProbabilityTheory.iIndepFun.integrable_exp_mul_sum hGind hGmeas'
          (s := Finset.univ) (t := 1) hGfac
        convert hmain using 1
        funext ω
        simp only [one_mul, Finset.sum_apply]
      have hZfac : ∀ i ∈ (Finset.univ : Finset (Fin n ⊕ Fin m)), Integrable (fun ω : Ω => Real.exp (1 * (
          Sum.elim (fun _ => fun x : Fin p → ℝ => (Real.sqrt (n:ℝ))⁻¹ * ∑ j, u j * (x j - muX j))
            (fun _ => fun x : Fin p → ℝ => delta * (Real.sqrt (m:ℝ))⁻¹ * ∑ j, u j * (x j - muY j))
            i (jointFam X Y F G (Sum.inr (Sum.inr i)) ω)))) P := by
        intro i _
        cases i with
        | inl a => exact hFfac a (by simp)
        | inr a => exact hGfac a (by simp)
      have hmain : Integrable (fun ω : Ω => Real.exp (1 * (∑ i ∈ (Finset.univ : Finset (Fin n ⊕ Fin m)),
          fun ω => Sum.elim (fun _ => fun x : Fin p → ℝ => (Real.sqrt (n:ℝ))⁻¹ * ∑ j, u j * (x j - muX j))
            (fun _ => fun x : Fin p → ℝ => delta * (Real.sqrt (m:ℝ))⁻¹ * ∑ j, u j * (x j - muY j))
            i (jointFam X Y F G (Sum.inr (Sum.inr i)) ω)) ω)) P :=
        ProbabilityTheory.iIndepFun.integrable_exp_mul_sum hZindep hZmeas (s := Finset.univ) (t := 1) hZfac
      have hfun : (fun ω : Ω => Real.exp (∑ j, u j * combVec n m delta muX muY (fun i => F i ω) (fun i => G i ω) j))
          = (fun ω : Ω => Real.exp (1 * (∑ i ∈ (Finset.univ : Finset (Fin n ⊕ Fin m)),
              fun ω => Sum.elim (fun _ => fun x : Fin p → ℝ => (Real.sqrt (n:ℝ))⁻¹ * ∑ j, u j * (x j - muX j))
                (fun _ => fun x : Fin p → ℝ => delta * (Real.sqrt (m:ℝ))⁻¹ * ∑ j, u j * (x j - muY j))
                i (jointFam X Y F G (Sum.inr (Sum.inr i)) ω)) ω)) := by
        funext ω
        rw [hexp ω, one_mul, Finset.sum_apply, Real.exp_sum]
      rw [hfun]
      exact hmain
    · calc ∫ ω, Real.exp (∑ j, u j * combVec n m delta muX muY (fun i => F i ω) (fun i => G i ω) j) ∂P
          = ∫ ω, ∏ i : Fin n ⊕ Fin m, Real.exp (
              Sum.elim (fun _ => fun x : Fin p → ℝ => (Real.sqrt (n:ℝ))⁻¹ * ∑ j, u j * (x j - muX j))
                (fun _ => fun x : Fin p → ℝ => delta * (Real.sqrt (m:ℝ))⁻¹ * ∑ j, u j * (x j - muY j))
                i (jointFam X Y F G (Sum.inr (Sum.inr i)) ω)) ∂P := by
            simp only [hexp]
        _ = ∏ i : Fin n ⊕ Fin m, ∫ ω, Real.exp (
              Sum.elim (fun _ => fun x : Fin p → ℝ => (Real.sqrt (n:ℝ))⁻¹ * ∑ j, u j * (x j - muX j))
                (fun _ => fun x : Fin p → ℝ => delta * (Real.sqrt (m:ℝ))⁻¹ * ∑ j, u j * (x j - muY j))
                i (jointFam X Y F G (Sum.inr (Sum.inr i)) ω)) ∂P :=
            ProbabilityTheory.iIndepFun.integral_fun_prod_eq_prod_integral hEindep hZaes
        _ = Real.exp ((∑ a : Fin n, ∑ i, ∑ j, (Real.sqrt (n:ℝ))⁻¹ * u i * covX P muX X a i j * ((Real.sqrt (n:ℝ))⁻¹ * u j)) / 2)
              * Real.exp ((∑ a : Fin m, ∑ i, ∑ j, delta * (Real.sqrt (m:ℝ))⁻¹ * u i * covY P muY Y a i j * (delta * (Real.sqrt (m:ℝ))⁻¹ * u j)) / 2) := hprodval
        _ = Real.exp (((∑ a : Fin n, ∑ i, ∑ j, (Real.sqrt (n:ℝ))⁻¹ * u i * covX P muX X a i j * ((Real.sqrt (n:ℝ))⁻¹ * u j))
              + ∑ a : Fin m, ∑ i, ∑ j, delta * (Real.sqrt (m:ℝ))⁻¹ * u i * covY P muY Y a i j * (delta * (Real.sqrt (m:ℝ))⁻¹ * u j)) / 2) := hexpfact
        _ = Real.exp ((∑ i, ∑ j, u i * ((n : ℝ)⁻¹ • (∑ i : Fin n, covX P muX X i) +
              delta ^ 2 • ((m : ℝ)⁻¹ • (∑ i : Fin m, covY P muY Y i))) i j * u j) / 2) := by
            rw [hbracket]
  refine ⟨hmeas, fun u => (key u).1, fun u => (key u).2⟩
  /- @proof-region region.target-node.session.9a789306fe42c6c7 end -/

end

end Statlib.Imported

