import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_2024687868_9ec8273d_4e9143f4

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
theorem statopia_math_node_3058610448_3f0d893f : ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℕ) (hp : 1 ≤ p) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (W U : Ω → Fin p → ℝ)
    (hWmeas : Measurable W) (hUmeas : Measurable U)
    (hU : IsCenteredGaussianVector P U Sigma)
    (hWU : IndepFun W U P)
    (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hbc : b ^ 2 + c ^ 2 = d ^ 2),
    Measure.map (fun x : Ω × Ω => fun j : Fin p => a * W x.1 j + b * U x.1 j + c * U x.2 j)
        (P.prod P)
      = Measure.map (fun ω : Ω => fun j : Fin p => a * W ω j + d * U ω j) P := by
  /- @proof-region region.target-node.session.c89d19122f39ada2 begin -/
  intro Ω _ P _ p hp Sigma W U hWmeas hUmeas hU hWU a b c d hb hc hd hbc
  let μ : Measure (Fin p → ℝ) := Measure.map W P
  let ν : Measure (Fin p → ℝ) := Measure.map U P
  let νd : Measure (Fin p → ℝ) := Measure.map (fun g : Fin p → ℝ => fun j => d * g j) ν
  let S : (Fin p → ℝ) × (Fin p → ℝ) → (Fin p → ℝ) := fun q => fun j => a * q.1 j + q.2 j
  let T2 : (Fin p → ℝ) × (Fin p → ℝ) → (Fin p → ℝ) := fun q => fun j => b * q.1 j + c * q.2 j
  have hS : Measurable S := by
    apply measurable_pi_iff.mpr
    intro j
    have h1 : Measurable fun q : (Fin p → ℝ) × (Fin p → ℝ) => q.1 j :=
      (measurable_pi_apply j).comp measurable_fst
    have h2 : Measurable fun q : (Fin p → ℝ) × (Fin p → ℝ) => q.2 j :=
      (measurable_pi_apply j).comp measurable_snd
    exact (measurable_const.mul h1).add h2
  have hdouble : Measurable (fun g : Fin p → ℝ => fun j => d * g j) := by
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_const.mul (measurable_pi_apply j)
  have hT2 : Measurable T2 := by
    apply measurable_pi_iff.mpr
    intro j
    have h1 : Measurable fun q : (Fin p → ℝ) × (Fin p → ℝ) => q.1 j :=
      (measurable_pi_apply j).comp measurable_fst
    have h2 : Measurable fun q : (Fin p → ℝ) × (Fin p → ℝ) => q.2 j :=
      (measurable_pi_apply j).comp measurable_snd
    exact (measurable_const.mul h1).add (measurable_const.mul h2)
  have hjoint : Measure.map (fun ω : Ω => (W ω, U ω)) P = μ.prod ν :=
    (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map hWmeas.aemeasurable hUmeas.aemeasurable).mp hWU
  have hconv : Measure.map T2 (ν.prod ν) = νd :=
    statopia_math_node_2024687868_9ec8273d (p := p) (hp := hp) (Sigma := Sigma) (U := U)
      (hUmeas := hUmeas) (hU := hU) (b := b) (c := c) (d := d)
      (hb := hb) (hc := hc) (hd := hd) (hbc := hbc)
  have hL : Measure.map (fun x : Ω × Ω => fun j : Fin p => a * W x.1 j + b * U x.1 j + c * U x.2 j) (P.prod P)
      = Measure.map S (μ.prod νd) := by
    let tripleMap : Ω × Ω → ((Fin p → ℝ) × (Fin p → ℝ)) × (Fin p → ℝ) :=
      fun x => ((W x.1, U x.1), U x.2)
    let Θ : Ω × Ω → (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) :=
      fun x => (W x.1, (U x.1, U x.2))
    let Λ : (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) → (Fin p → ℝ) × (Fin p → ℝ) :=
      fun r => (r.1, T2 r.2)
    have htriple_meas : Measurable tripleMap :=
      ((hWmeas.comp measurable_fst).prod (hUmeas.comp measurable_fst)).prod (hUmeas.comp measurable_snd)
    have hΘ_meas : Measurable Θ :=
      (hWmeas.comp measurable_fst).prod ((hUmeas.comp measurable_fst).prod (hUmeas.comp measurable_snd))
    have hΛ_meas : Measurable Λ := by
      change Measurable (fun r : (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) => (r.1, T2 r.2))
      fun_prop
    have htriple : Measure.map tripleMap (P.prod P) = (μ.prod ν).prod ν := by
      have h := Measure.map_prod_map (μa := P) (μc := P)
        (f := fun ω : Ω => (W ω, U ω)) (g := U) (hWmeas.prod hUmeas) hUmeas
      rw [hjoint] at h
      exact h.symm
    have hΘ : Measure.map Θ (P.prod P) = μ.prod (ν.prod ν) := by
      have e1 : Measure.map Θ (P.prod P)
          = Measure.map (⇑MeasurableEquiv.prodAssoc) (Measure.map tripleMap (P.prod P)) :=
        (Measure.map_map MeasurableEquiv.prodAssoc.measurable htriple_meas).symm
      rw [e1, htriple, Measure.prodAssoc_prod]
    have hΛ : Measure.map Λ (μ.prod (ν.prod ν)) = μ.prod νd := by
      have h := Measure.map_prod_map (μa := μ) (μc := ν.prod ν)
        (f := id) (g := T2) measurable_id hT2
      rw [Measure.map_id, hconv] at h
      exact h.symm
    have hFL : (fun x : Ω × Ω => fun j : Fin p => a * W x.1 j + b * U x.1 j + c * U x.2 j)
        = S ∘ Λ ∘ Θ := by
      funext x j
      change a * W x.1 j + b * U x.1 j + c * U x.2 j = a * W x.1 j + (b * U x.1 j + c * U x.2 j)
      ring
    calc Measure.map (fun x : Ω × Ω => fun j : Fin p => a * W x.1 j + b * U x.1 j + c * U x.2 j) (P.prod P)
        = Measure.map (S ∘ Λ ∘ Θ) (P.prod P) := by rw [hFL]
      _ = Measure.map S (Measure.map (Λ ∘ Θ) (P.prod P)) :=
            (Measure.map_map hS (hΛ_meas.comp hΘ_meas)).symm
      _ = Measure.map S (Measure.map Λ (Measure.map Θ (P.prod P))) := by
            rw [← Measure.map_map hΛ_meas hΘ_meas]
      _ = Measure.map S (Measure.map Λ (μ.prod (ν.prod ν))) := by rw [hΘ]
      _ = Measure.map S (μ.prod νd) := by rw [hΛ]
  have hR : Measure.map (fun ω : Ω => fun j : Fin p => a * W ω j + d * U ω j) P
      = Measure.map S (μ.prod νd) := by
    have hG_meas : Measurable (fun ω : Ω => (W ω, fun j => d * U ω j)) :=
      hWmeas.prod (hdouble.comp hUmeas)
    have hGmap : Measure.map (fun ω : Ω => (W ω, fun j => d * U ω j)) P = μ.prod νd := by
      have hWU' : W ⟂ᵢ[P] ((fun g : Fin p → ℝ => fun j => d * g j) ∘ U) :=
        hWU.comp measurable_id hdouble
      have h := (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map hWmeas.aemeasurable
        (hdouble.comp hUmeas).aemeasurable).mp hWU'
      have hdU : Measure.map ((fun g : Fin p → ℝ => fun j => d * g j) ∘ U) P = νd :=
        (Measure.map_map hdouble hUmeas).symm
      rw [hdU] at h
      exact h
    calc Measure.map (fun ω : Ω => fun j : Fin p => a * W ω j + d * U ω j) P
        = Measure.map S (Measure.map (fun ω : Ω => (W ω, fun j => d * U ω j)) P) :=
          (Measure.map_map hS hG_meas).symm
      _ = Measure.map S (μ.prod νd) := by rw [hGmap]
  exact hL.trans hR.symm
  /- @proof-region region.target-node.session.c89d19122f39ada2 end -/

end

end Statlib.Imported

