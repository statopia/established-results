import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base

namespace PaperProofTasks.paper_fresh_20261108t120211266248z_prior_learning33

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261108t120211266248z_prior_learning33.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_3039133055_9a199646 : ∀ (U : Type*) [MeasurableSpace U]
    (mu : Measure U) [IsProbabilityMeasure mu]
    (Phi : ℕ → U → ℝ) (nu : ℕ → Measure ℝ)
    (hnu : ∀ i : ℕ, IsProbabilityMeasure (nu i))
    (hPhi : ∀ i : ℕ, Measurable (Phi i))
    (hprod : ∀ n : ℕ,
      Measure.map (fun u : U => fun i : Fin n => Phi i u) mu
        = Measure.pi (fun i : Fin n => nu i)),
    iIndepFun Phi mu := by
  /- @proof-region region.target-node.session.724da48c25282c32 begin -/
  intro U instU mu instMu Phi nu hnu hPhi hprod
  have hmarg : ∀ i : ℕ, Measure.map (Phi i) mu = nu i := by
    intro i
    have hg : Measurable (fun v : (Fin (i + 1) → ℝ) => v ⟨i, Nat.lt_succ_self i⟩) :=
      measurable_pi_apply _
    have hf : Measurable (fun u : U => fun j : Fin (i + 1) => Phi j u) :=
      measurable_pi_iff.mpr (fun j => hPhi j)
    have hcomp : (fun v : (Fin (i + 1) → ℝ) => v ⟨i, Nat.lt_succ_self i⟩)
        ∘ (fun u : U => fun j : Fin (i + 1) => Phi j u) = Phi i := by
      funext u
      rfl
    haveI : ∀ j : Fin (i + 1), IsProbabilityMeasure ((fun j : Fin (i + 1) => nu j) j) :=
      fun j => hnu j
    calc Measure.map (Phi i) mu
        = Measure.map ((fun v : (Fin (i + 1) → ℝ) => v ⟨i, Nat.lt_succ_self i⟩)
            ∘ (fun u : U => fun j : Fin (i + 1) => Phi j u)) mu := by rw [hcomp]
      _ = Measure.map (fun v : (Fin (i + 1) → ℝ) => v ⟨i, Nat.lt_succ_self i⟩)
            (Measure.map (fun u : U => fun j : Fin (i + 1) => Phi j u) mu) :=
          (Measure.map_map hg hf).symm
      _ = Measure.map (fun v : (Fin (i + 1) → ℝ) => v ⟨i, Nat.lt_succ_self i⟩)
            (Measure.pi (fun j : Fin (i + 1) => nu j)) := by rw [hprod (i + 1)]
      _ = nu i := by
          have h := (measurePreserving_eval (fun j : Fin (i + 1) => nu j)
            (⟨i, Nat.lt_succ_self i⟩ : Fin (i + 1))).map_eq
          simpa using h
  have hmap : ∀ n : ℕ, Measure.map (fun u : U => fun i : Fin n => Phi i u) mu
      = Measure.pi (fun i : Fin n => Measure.map (Phi i) mu) := by
    intro n
    rw [hprod n]
    rw [show (fun i : Fin n => nu i) = (fun i : Fin n => Measure.map (Phi i) mu) from
      funext (fun i => (hmarg ↑i).symm)]
  have hindepn : ∀ n : ℕ, iIndepFun (fun i : Fin n => Phi i) mu := by
    intro n
    have h := iIndepFun_iff_map_fun_eq_pi_map (μ := mu) (f := fun i : Fin n => Phi i)
      (fun i => (hPhi i).aemeasurable)
    exact h.mpr (hmap n)
  refine iIndepFun_iff_finset.mpr (fun s => ?_)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ∀ i ∈ s, i < n :=
    ⟨s.sup id + 1, fun i hi => Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)⟩
  have hg : Function.Injective (fun i : s => (⟨↑i, hn ↑i i.2⟩ : Fin n)) := by
    intro a b hab
    exact Subtype.ext (congrArg (fun k : Fin n => (k : ℕ)) hab)
  have hsub : iIndepFun (fun i : s => Phi (i : ℕ)) mu :=
    iIndepFun.precomp (f := fun j : Fin n => Phi (j : ℕ))
      (g := fun i : s => (⟨(i : ℕ), hn (i : ℕ) i.2⟩ : Fin n)) hg (hindepn n)
  exact hsub
  /- @proof-region region.target-node.session.724da48c25282c32 end -/

end Statlib.Imported
end

