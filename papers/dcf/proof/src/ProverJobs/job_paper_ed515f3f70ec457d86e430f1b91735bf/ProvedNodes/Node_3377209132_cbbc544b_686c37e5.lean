import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_3430447628_ae1e147f_4d81461a

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
theorem statopia_math_node_3377209132_cbbc544b : ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n m p : ℕ) (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
    (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
    (hXm : ∀ i : Fin n, Measurable (X i)) (hYm : ∀ i : Fin m, Measurable (Y i))
    (hFm : ∀ i : Fin n, Measurable (F i)) (hGm : ∀ i : Fin m, Measurable (G i))
    (hindep : iIndepFun (β := fun _ => Fin p → ℝ) (jointFam X Y F G) P)
    (kap : (Fin p → ℝ) → ℝ) (hkap : ContDiff ℝ 1 kap)
    (v t : ℝ) (i : Fin n) (j : Fin p),
    (let Zrest : Ω × Ω → Fin p → ℝ := fun x k =>
      (∑ i' : Fin n, if i' = i then 0 else
        (Real.sqrt (n : ℝ))⁻¹ *
          (Real.sqrt t * (Real.sqrt v * (X i' x.1 k - muX k) +
              Real.sqrt (1 - v) * (F i' x.1 k - muX k)) +
            Real.sqrt (1 - t) * (F i' x.2 k - muX k)))
      + (∑ i' : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m *
          (Real.sqrt t * (Real.sqrt v * (Y i' x.1 k - muY k) +
              Real.sqrt (1 - v) * (G i' x.1 k - muY k)) +
            Real.sqrt (1 - t) * (G i' x.2 k - muY k)))
     let Psi : Ω × Ω → ℝ := fun x => (fderiv ℝ kap (Zrest x)) (Pi.single j (1 : ℝ))
     IndepFun Psi (fun x : Ω × Ω => (X i x.1, (F i x.1, F i x.2))) (P.prod P)) := by
  /- @proof-region region.target-node.session.637bb06b74f5a5ad begin -/
  intro Ω _ P _ n m p delta muX muY X Y F G hXm hYm hFm hGm hindep kap hkap v t i j
  let S : (Fin m ⊕ (Fin n ⊕ (Fin m ⊕ Fin n))) → (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) :=
    fun a =>
      match a with
      | Sum.inl i' => Sum.inr (Sum.inl i')
      | Sum.inr (Sum.inl i') => Sum.inl i'
      | Sum.inr (Sum.inr (Sum.inl i')) => Sum.inr (Sum.inr (Sum.inr i'))
      | Sum.inr (Sum.inr (Sum.inr i')) => Sum.inr (Sum.inr (Sum.inl i'))
  let T : (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) → (Fin m ⊕ (Fin n ⊕ (Fin m ⊕ Fin n))) :=
    fun a =>
      match a with
      | Sum.inl i' => Sum.inr (Sum.inl i')
      | Sum.inr (Sum.inl i') => Sum.inl i'
      | Sum.inr (Sum.inr (Sum.inl i')) => Sum.inr (Sum.inr (Sum.inr i'))
      | Sum.inr (Sum.inr (Sum.inr i')) => Sum.inr (Sum.inr (Sum.inl i'))
  let Φ : (Fin m ⊕ (Fin n ⊕ (Fin m ⊕ Fin n))) → (Fin p → ℝ) → (Fin p → ℝ) :=
    fun a =>
      match a with
      | Sum.inl _ => fun z => delta n m • z
      | Sum.inr (Sum.inl _) => id
      | Sum.inr (Sum.inr (Sum.inl _)) => fun z => delta n m • z
      | Sum.inr (Sum.inr (Sum.inr _)) => id
  let A : Ω × Ω → Fin p → ℝ := fun x k => ∑ i' : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m *
      (Real.sqrt t * (Real.sqrt v * (Y i' x.1 k - muY k) +
          Real.sqrt (1 - v) * (G i' x.1 k - muY k)) +
        Real.sqrt (1 - t) * (G i' x.2 k - muY k))
  let Bs : Ω × Ω → Fin p → ℝ := fun x k => ∑ i' : Fin n, if i' = i then 0 else
      (Real.sqrt (n : ℝ))⁻¹ *
        (Real.sqrt t * (Real.sqrt v * (X i' x.1 k - muX k) +
            Real.sqrt (1 - v) * (F i' x.1 k - muX k)) +
          Real.sqrt (1 - t) * (F i' x.2 k - muX k))
  let As : Ω × Ω → Fin p → ℝ := fun x k => ∑ i' : Fin m, (Real.sqrt (m : ℝ))⁻¹ *
      (Real.sqrt t * (Real.sqrt v * (delta n m • Y i' x.1 k - delta n m * muY k) +
          Real.sqrt (1 - v) * (delta n m • G i' x.1 k - delta n m * muY k)) +
        Real.sqrt (1 - t) * (delta n m • G i' x.2 k - delta n m * muY k))
  let B1 : Ω × Ω → Fin p → ℝ := fun x k => ∑ i' : Fin n, if i' = i then 0 else
      (Real.sqrt (n : ℝ))⁻¹ * 1 *
        (Real.sqrt t * (Real.sqrt v * (X i' x.1 k - muX k) +
            Real.sqrt (1 - v) * (F i' x.1 k - muX k)) +
          Real.sqrt (1 - t) * (F i' x.2 k - muX k))
  show IndepFun (fun x : Ω × Ω => (fderiv ℝ kap (fun k : Fin p => Bs x k + A x k)) (Pi.single j (1 : ℝ)))
    (fun x : Ω × Ω => (X i x.1, (F i x.1, F i x.2))) (P.prod P)
  have hproj : ∀ k : Fin p, Measurable (fun z : Fin p → ℝ => z k) := fun k => measurable_pi_apply k
  have hsmul : Measurable (fun z : Fin p → ℝ => delta n m • z) := by
    rw [measurable_pi_iff]
    intro k
    simpa only [Pi.smul_apply, smul_eq_mul] using measurable_const.mul (hproj k)
  have hΦ : ∀ a, Measurable (Φ a) := by
    rintro (i' | (i' | (i' | i')))
    · show Measurable (fun z : Fin p → ℝ => delta n m • z); exact hsmul
    · show Measurable (fun z : Fin p → ℝ => z); exact measurable_id
    · show Measurable (fun z : Fin p → ℝ => delta n m • z); exact hsmul
    · show Measurable (fun z : Fin p → ℝ => z); exact measurable_id
  have hTS : ∀ a, T (S a) = a := by
    rintro (i' | (i' | (i' | i'))) <;> rfl
  have hinj : Function.Injective S := by
    intro a b h
    have h2 : T (S a) = T (S b) := congrArg T h
    simpa only [hTS] using h2

  have hbase : iIndepFun (β := fun _ => Fin p → ℝ) (fun a => jointFam X Y F G (S a)) P :=
    iIndepFun.precomp (g := S) hinj hindep
  have hscaled : iIndepFun (β := fun _ => Fin p → ℝ)
      (fun a => Φ a ∘ jointFam X Y F G (S a)) P :=
    hbase.comp Φ hΦ
  have hfam : (fun a => Φ a ∘ jointFam X Y F G (S a))
      = jointFam (fun i' => delta n m • Y i') X (fun i' => delta n m • G i') F := by
    funext a
    rcases a with i' | (i' | (i' | i')) <;> funext x <;> rfl
  have hsw : iIndepFun (β := fun _ => Fin p → ℝ)
      (jointFam (fun i' => delta n m • Y i') X (fun i' => delta n m • G i') F) P := by
    rw [← hfam]
    exact hscaled
  have hscale : ∀ (Z : Ω → Fin p → ℝ), Measurable Z → Measurable (fun x => delta n m • Z x) :=
    fun Z hZ => hsmul.comp hZ
  have hmain := statopia_math_node_3430447628_ae1e147f
    (Ω := Ω) (P := P) (n := m) (m := n) (p := p)
    (delta := fun _ _ => (1 : ℝ)) (muX := fun k => delta n m * muY k) (muY := muX)
    (X := fun i' => delta n m • Y i') (Y := X) (F := fun i' => delta n m • G i') (G := F)
    (hXm := fun i' => hscale (Y i') (hYm i')) (hYm := hXm)
    (hFm := fun i' => hscale (G i') (hGm i')) (hGm := hFm)
    (hindep := hsw) (kap := kap) (hkap := hkap) (v := v) (t := t) (i := i) (j := j)
  have hAfun : A = As := by
    funext x k
    show (∑ i' : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m *
        (Real.sqrt t * (Real.sqrt v * (Y i' x.1 k - muY k) +
            Real.sqrt (1 - v) * (G i' x.1 k - muY k)) +
          Real.sqrt (1 - t) * (G i' x.2 k - muY k)))
      = (∑ i' : Fin m, (Real.sqrt (m : ℝ))⁻¹ *
        (Real.sqrt t * (Real.sqrt v * (delta n m • Y i' x.1 k - delta n m * muY k) +
            Real.sqrt (1 - v) * (delta n m • G i' x.1 k - delta n m * muY k)) +
          Real.sqrt (1 - t) * (delta n m • G i' x.2 k - delta n m * muY k)))
    simp only [smul_eq_mul]
    exact Finset.sum_congr rfl (fun i' _ => by ring)
  have hBfun : Bs = B1 := by
    funext x k
    show (∑ i' : Fin n, if i' = i then 0 else
        (Real.sqrt (n : ℝ))⁻¹ *
          (Real.sqrt t * (Real.sqrt v * (X i' x.1 k - muX k) +
              Real.sqrt (1 - v) * (F i' x.1 k - muX k)) +
            Real.sqrt (1 - t) * (F i' x.2 k - muX k)))
      = (∑ i' : Fin n, if i' = i then 0 else
        (Real.sqrt (n : ℝ))⁻¹ * 1 *
          (Real.sqrt t * (Real.sqrt v * (X i' x.1 k - muX k) +
              Real.sqrt (1 - v) * (F i' x.1 k - muX k)) +
            Real.sqrt (1 - t) * (F i' x.2 k - muX k)))
    refine Finset.sum_congr rfl (fun i' _ => ?_)
    by_cases h : i' = i
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
      ring
  have hPsieq : (fun x : Ω × Ω => (fderiv ℝ kap (fun k : Fin p => Bs x k + A x k)) (Pi.single j (1 : ℝ)))
      = (fun x : Ω × Ω => (fderiv ℝ kap (fun k : Fin p => As x k + B1 x k)) (Pi.single j (1 : ℝ))) := by
    funext x
    have hZ : (fun k : Fin p => Bs x k + A x k) = (fun k : Fin p => As x k + B1 x k) := by
      rw [hBfun, hAfun]
      funext k
      rw [add_comm]
    rw [hZ]
  rw [hPsieq]
  exact hmain

  /- @proof-region region.target-node.session.637bb06b74f5a5ad end -/

end

end Statlib.Imported

