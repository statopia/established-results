import Lean
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.Vocabulary
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.Base
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.ProvedNodes.Node_436922874_8ad414b4_4d515167

namespace PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315

open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported

noncomputable section
universe u
open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_1799359223_1d14dae9 : ∀ (p : ℕ) (hp : 1 ≤ p) (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m)
    (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
    (μX μY : Fin p → ℝ) (d : ℝ)
    (X : Fin n → Ω → (Fin p → ℝ)) (Y : Fin m → Ω → (Fin p → ℝ)) (b : ℝ)
    (h_int : ∀ j : Fin p, Integrable (fun ω => (partXY X Y μX μY d ω j) ^ 2) μ)
    (h_lb : b ≤ ⨅ j : Fin p, ∫ ω, (partXY X Y μX μY d ω j) ^ 2 ∂μ),
    let T : (Fin p → ℝ) → (Fin (p + p) → ℝ) := fun z j =>
      if h : (j : ℕ) < p then z ⟨(j : ℕ), h⟩
      else -z ⟨(j : ℕ) - p, by have hj := j.isLt; omega⟩;
    (∀ j : Fin (p + p),
        Integrable (fun ω =>
          (partXY (fun i => T ∘ X i) (fun i => T ∘ Y i) (T μX) (T μY) d ω j) ^ 2) μ) ∧
      (b ≤ ⨅ j : Fin (p + p),
        ∫ ω, (partXY (fun i => T ∘ X i) (fun i => T ∘ Y i) (T μX) (T μY) d ω j) ^ 2 ∂μ) ∧
      ((⨅ j : Fin (p + p),
          ∫ ω, (partXY (fun i => T ∘ X i) (fun i => T ∘ Y i) (T μX) (T μY) d ω j) ^ 2 ∂μ)
        = (⨅ j : Fin p, ∫ ω, (partXY X Y μX μY d ω j) ^ 2 ∂μ)) := by
  /- @proof-region region.target-node.session.0efbbf8d6bb22fb1 begin -/
  intro p hp n hn m hm Ω instΩ μ μX μY d X Y b h_int h_lb
  dsimp only
  let T : (Fin p → ℝ) → (Fin (p + p) → ℝ) := fun z j =>
    if h : (j : ℕ) < p then z ⟨(j : ℕ), h⟩
    else -z ⟨(j : ℕ) - p, by have hj := j.isLt; omega⟩
  let FD : Fin (p + p) → ℝ := fun j =>
    ∫ ω, (partXY (fun i => T ∘ X i) (fun i => T ∘ Y i) (T μX) (T μY) d ω j) ^ 2 ∂μ
  let Fp : Fin p → ℝ := fun k => ∫ ω, (partXY X Y μX μY d ω k) ^ 2 ∂μ
  have H := statopia_math_node_436922874_8ad414b4 n m p hp PUnit
  dsimp only at H
  obtain ⟨-, -, -, -, -, -, hXY, -, -, -, hlt, hge, -, -⟩ := H
  have key_lt : ∀ (j : Fin (p + p)) (hj : (j : ℕ) < p) (ω : Ω),
      partXY (fun i => T ∘ X i) (fun i => T ∘ Y i) (T μX) (T μY) d ω j
        = partXY X Y μX μY d ω ⟨(j : ℕ), hj⟩ := by
    intro j hj ω
    exact (congrFun (hXY (fun i _ => X i ω) (fun i _ => Y i ω) (fun i _ => X i ω)
      (fun i _ => Y i ω) μX μY d PUnit.unit) j).trans (hlt (partXY X Y μX μY d ω) j hj)
  have key_ge : ∀ (j : Fin (p + p)) (hj : p ≤ (j : ℕ)) (ω : Ω),
      partXY (fun i => T ∘ X i) (fun i => T ∘ Y i) (T μX) (T μY) d ω j
        = -partXY X Y μX μY d ω ⟨(j : ℕ) - p, by have hk := j.isLt; omega⟩ := by
    intro j hj ω
    exact (congrFun (hXY (fun i _ => X i ω) (fun i _ => Y i ω) (fun i _ => X i ω)
      (fun i _ => Y i ω) μX μY d PUnit.unit) j).trans (hge (partXY X Y μX μY d ω) j hj)
  have hfun_lt : ∀ (j : Fin (p + p)) (hj : (j : ℕ) < p),
      (fun ω => (partXY (fun i => T ∘ X i) (fun i => T ∘ Y i) (T μX) (T μY) d ω j) ^ 2)
        = fun ω => (partXY X Y μX μY d ω ⟨(j : ℕ), hj⟩) ^ 2 := by
    intro j hj
    funext ω
    rw [key_lt j hj ω]
  have hfun_ge : ∀ (j : Fin (p + p)) (hj : p ≤ (j : ℕ)),
      (fun ω => (partXY (fun i => T ∘ X i) (fun i => T ∘ Y i) (T μX) (T μY) d ω j) ^ 2)
        = fun ω => (partXY X Y μX μY d ω ⟨(j : ℕ) - p, by have hk := j.isLt; omega⟩) ^ 2 := by
    intro j hj
    funext ω
    rw [key_ge j hj ω, neg_sq]
  have hint : ∀ j : Fin (p + p),
      Integrable (fun ω => (partXY (fun i => T ∘ X i) (fun i => T ∘ Y i) (T μX) (T μY) d ω j) ^ 2) μ := by
    intro j
    by_cases hj : (j : ℕ) < p
    · rw [hfun_lt j hj]
      exact h_int ⟨(j : ℕ), hj⟩
    · have hge' : p ≤ (j : ℕ) := by have hjlt := j.isLt; omega
      rw [hfun_ge j hge']
      exact h_int ⟨(j : ℕ) - p, by have hjlt := j.isLt; omega⟩
  have hFD_lt : ∀ (j : Fin (p + p)) (hj : (j : ℕ) < p), FD j = Fp ⟨(j : ℕ), hj⟩ := by
    intro j hj
    simp only [FD, Fp, hfun_lt j hj]
  have hFD_ge : ∀ (j : Fin (p + p)) (hj : p ≤ (j : ℕ)),
      FD j = Fp ⟨(j : ℕ) - p, by have hk := j.isLt; omega⟩ := by
    intro j hj
    simp only [FD, Fp, hfun_ge j hj]
  have hFD_first : ∀ k : Fin p, FD ⟨(k : ℕ), by have hk := k.isLt; omega⟩ = Fp k := by
    intro k
    exact hFD_lt ⟨(k : ℕ), by have hk := k.isLt; omega⟩ k.isLt
  haveI hneP : Nonempty (Fin p) := ⟨⟨0, by omega⟩⟩
  haveI hneD : Nonempty (Fin (p + p)) := ⟨⟨0, by omega⟩⟩
  have hbddD : BddBelow (Set.range FD) := (Set.finite_range FD).bddBelow
  have hbddP : BddBelow (Set.range Fp) := (Set.finite_range Fp).bddBelow
  have hinf : (⨅ j : Fin (p + p), FD j) = ⨅ k : Fin p, Fp k := by
    refine le_antisymm ?_ ?_
    · have hle : ∀ k : Fin p, (⨅ j : Fin (p + p), FD j) ≤ Fp k := by
        intro k
        rw [← hFD_first k]
        exact ciInf_le hbddD ⟨(k : ℕ), by have hk := k.isLt; omega⟩
      exact le_ciInf hle
    · have hle : ∀ j : Fin (p + p), (⨅ k : Fin p, Fp k) ≤ FD j := by
        intro j
        by_cases hj : (j : ℕ) < p
        · rw [hFD_lt j hj]
          exact ciInf_le hbddP ⟨(j : ℕ), hj⟩
        · have hge' : p ≤ (j : ℕ) := by have hjlt := j.isLt; omega
          rw [hFD_ge j hge']
          exact ciInf_le hbddP ⟨(j : ℕ) - p, by have hjlt := j.isLt; omega⟩
      exact le_ciInf hle
  refine ⟨hint, ?_, hinf⟩
  exact h_lb.trans (le_of_eq hinf.symm)
  /- @proof-region region.target-node.session.0efbbf8d6bb22fb1 end -/

end Statlib.Imported

end

