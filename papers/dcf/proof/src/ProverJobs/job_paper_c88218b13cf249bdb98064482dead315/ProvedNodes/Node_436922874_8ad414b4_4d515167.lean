import Lean
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.Vocabulary
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.Base

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
theorem statopia_math_node_436922874_8ad414b4 : ∀ (n m : ℕ) (p : ℕ) (hp : 1 ≤ p) (Ω : Type),
    let T : (Fin p → ℝ) → (Fin (p + p) → ℝ) := fun z j =>
      if h : (j : ℕ) < p then z ⟨(j : ℕ), h⟩
      else -z ⟨(j : ℕ) - p, by have hj := j.isLt; omega⟩;
    (∀ x y : Fin p → ℝ, T (x + y) = T x + T y) ∧
      (∀ (c : ℝ) (x : Fin p → ℝ), T (c • x) = c • T x) ∧
      Continuous T ∧
      Function.Injective T ∧
      Set.range T =
        {u : Fin (p + p) → ℝ |
          ∀ k : Fin p, u ⟨p + (k : ℕ), by have hk := k.isLt; omega⟩ =
            -u ⟨(k : ℕ), by have hk := k.isLt; omega⟩} ∧
      (∀ (k : ℕ) (Z : Fin k → Ω → (Fin p → ℝ)) (ω : Ω),
        normSum (fun i => T ∘ Z i) ω = T (normSum Z ω)) ∧
      (∀ (X : Fin n → Ω → (Fin p → ℝ)) (Y : Fin m → Ω → (Fin p → ℝ))
        (F : Fin n → Ω → (Fin p → ℝ)) (G : Fin m → Ω → (Fin p → ℝ))
        (μX μY : Fin p → ℝ) (d : ℝ) (ω : Ω),
        partXY (fun i => T ∘ X i) (fun i => T ∘ Y i) (T μX) (T μY) d ω =
          T (partXY X Y μX μY d ω)) ∧
      (∀ (X : Fin n → Ω → (Fin p → ℝ)) (Y : Fin m → Ω → (Fin p → ℝ))
        (F : Fin n → Ω → (Fin p → ℝ)) (G : Fin m → Ω → (Fin p → ℝ))
        (μX μY : Fin p → ℝ) (d : ℝ) (ω : Ω),
        partFG (fun i => T ∘ F i) (fun i => T ∘ G i) (T μX) (T μY) d ω =
          T (partFG F G μX μY d ω)) ∧
      (∀ (X : Fin n → Ω → (Fin p → ℝ)) (Y : Fin m → Ω → (Fin p → ℝ))
        (F : Fin n → Ω → (Fin p → ℝ)) (G : Fin m → Ω → (Fin p → ℝ))
        (μX μY : Fin p → ℝ) (d : ℝ) (v : ℝ) (ω : Ω),
        Real.sqrt v • partXY (fun i => T ∘ X i) (fun i => T ∘ Y i) (T μX) (T μY) d ω +
            Real.sqrt (1 - v) •
              partFG (fun i => T ∘ F i) (fun i => T ∘ G i) (T μX) (T μY) d ω =
          T (Real.sqrt v • partXY X Y μX μY d ω +
            Real.sqrt (1 - v) • partFG F G μX μY d ω)) ∧
      (∀ (X : Fin n → Ω → (Fin p → ℝ)) (Y : Fin m → Ω → (Fin p → ℝ))
        (F : Fin n → Ω → (Fin p → ℝ)) (G : Fin m → Ω → (Fin p → ℝ))
        (μX μY : Fin p → ℝ) (d : ℝ) (ω : Ω),
        partFG (fun i => T ∘ F i) (fun i => T ∘ G i) (T μX) (T μY) d ω =
          T (partFG F G μX μY d ω)) ∧
      (∀ (z : Fin p → ℝ) (j : Fin (p + p)) (hj : (j : ℕ) < p),
        T z j = z ⟨(j : ℕ), hj⟩) ∧
      (∀ (z : Fin p → ℝ) (j : Fin (p + p)) (hj : p ≤ (j : ℕ)),
        T z j = -z ⟨(j : ℕ) - p, by have hk := j.isLt; omega⟩) ∧
      (∀ (μX : Fin p → ℝ) (a : Fin p),
        T μX ⟨(a : ℕ), by have ha := a.isLt; omega⟩ = μX a) ∧
      (∀ (μX : Fin p → ℝ) (k : Fin p),
        T μX ⟨p + (k : ℕ), by have hk := k.isLt; omega⟩ = -μX k) := by
  /- @proof-region region.target-node.session.c51bc0e93738cb75 begin -/
  intro n m p hp Ω
  let T : (Fin p → ℝ) → (Fin (p + p) → ℝ) := fun z j =>
    if h : (j : ℕ) < p then z ⟨(j : ℕ), h⟩
    else -z ⟨(j : ℕ) - p, by have hj := j.isLt; omega⟩
  have hT : ∀ (z : Fin p → ℝ) (j : Fin (p + p)),
      T z j = if h : (j : ℕ) < p then z ⟨(j : ℕ), h⟩
        else -z ⟨(j : ℕ) - p, by have hj := j.isLt; omega⟩ := fun z j => rfl
  have hcoord1 : ∀ (z : Fin p → ℝ) (j : Fin (p + p)) (hj : (j : ℕ) < p),
      T z j = z ⟨(j : ℕ), hj⟩ := by
    intro z j hj
    simp only [hT, dif_pos hj]
  have hcoord2 : ∀ (z : Fin p → ℝ) (j : Fin (p + p)) (hj : p ≤ (j : ℕ)),
      T z j = -z ⟨(j : ℕ) - p, by have hk := j.isLt; omega⟩ := by
    intro z j hj
    simp only [hT, dif_neg (show ¬ ((j : ℕ) < p) from by omega)]
  have hleft : ∀ (μX : Fin p → ℝ) (a : Fin p),
      T μX ⟨(a : ℕ), by have ha := a.isLt; omega⟩ = μX a := by
    intro μX a
    exact hcoord1 μX ⟨(a : ℕ), by have ha := a.isLt; omega⟩ (by have ha := a.isLt; omega)
  have hsub : ∀ (k : Fin p), (⟨p + (k : ℕ) - p, by have hk := k.isLt; omega⟩ : Fin p) = k := by
    intro k
    ext
    show p + (k : ℕ) - p = (k : ℕ)
    omega
  have hright : ∀ (μX : Fin p → ℝ) (k : Fin p),
      T μX ⟨p + (k : ℕ), by have hk := k.isLt; omega⟩ = -μX k := by
    intro μX k
    rw [hcoord2 μX ⟨p + (k : ℕ), by have hk := k.isLt; omega⟩
        (by show p ≤ p + (k : ℕ); omega),
      hsub k]
  have hadd : ∀ x y : Fin p → ℝ, T (x + y) = T x + T y := by
    intro x y
    funext j
    rw [Pi.add_apply]
    by_cases hj : (j : ℕ) < p
    · rw [hcoord1 (x + y) j hj, hcoord1 x j hj, hcoord1 y j hj, Pi.add_apply]
    · have hj2 : p ≤ (j : ℕ) := by omega
      rw [hcoord2 (x + y) j hj2, hcoord2 x j hj2, hcoord2 y j hj2, Pi.add_apply, neg_add]
  have hsmul : ∀ (c : ℝ) (x : Fin p → ℝ), T (c • x) = c • T x := by
    intro c x
    funext j
    rw [Pi.smul_apply, smul_eq_mul]
    by_cases hj : (j : ℕ) < p
    · rw [hcoord1 (c • x) j hj, hcoord1 x j hj, Pi.smul_apply, smul_eq_mul]
    · have hj2 : p ≤ (j : ℕ) := by omega
      rw [hcoord2 (c • x) j hj2, hcoord2 x j hj2, Pi.smul_apply, smul_eq_mul]
      ring
  have hcont : Continuous T := by
    refine continuous_pi (fun j => ?_)
    by_cases hj : (j : ℕ) < p
    · have h1 : (fun z : Fin p → ℝ => T z j) = fun z => z ⟨(j : ℕ), hj⟩ := by
        funext z
        exact hcoord1 z j hj
      rw [h1]
      exact continuous_apply _
    · have hj2 : p ≤ (j : ℕ) := by omega
      have h1 : (fun z : Fin p → ℝ => T z j) =
          fun z => -z ⟨(j : ℕ) - p, by have hk := j.isLt; omega⟩ := by
        funext z
        exact hcoord2 z j hj2
      rw [h1]
      exact (continuous_apply _).neg
  have hinj : Function.Injective T := by
    intro x y hxy
    funext a
    have h := congrFun hxy ⟨(a : ℕ), by have ha := a.isLt; omega⟩
    exact (hleft x a).symm.trans (h.trans (hleft y a))
  have hrange : Set.range T = {u : Fin (p + p) → ℝ |
      ∀ k : Fin p, u ⟨p + (k : ℕ), by have hk := k.isLt; omega⟩ =
        -u ⟨(k : ℕ), by have hk := k.isLt; omega⟩} := by
    ext u
    constructor
    · rintro ⟨z, rfl⟩ k
      rw [hright z k, hleft z k]
    · intro hu
      refine ⟨fun a => u ⟨(a : ℕ), by have ha := a.isLt; omega⟩, ?_⟩
      funext j
      by_cases hj : (j : ℕ) < p
      · exact hcoord1 (fun a => u ⟨(a : ℕ), by have ha := a.isLt; omega⟩) j hj
      · have hj2 : p ≤ (j : ℕ) := by omega
        have hidx : (⟨p + ((j : ℕ) - p), by have hk := j.isLt; omega⟩ : Fin (p + p)) = j := by
          ext
          show p + ((j : ℕ) - p) = (j : ℕ)
          omega
        have hu' := hu ⟨(j : ℕ) - p, by have hk := j.isLt; omega⟩
        rw [hidx] at hu'
        exact (hcoord2 (fun a => u ⟨(a : ℕ), by have ha := a.isLt; omega⟩) j hj2).trans hu'.symm
  have hnormSum : ∀ (k : ℕ) (Z : Fin k → Ω → (Fin p → ℝ)) (ω : Ω),
      normSum (fun i => T ∘ Z i) ω = T (normSum Z ω) := by
    intro k Z ω
    funext j
    by_cases hj : (j : ℕ) < p
    · rw [hcoord1 (normSum Z ω) j hj]
      simp only [normSum, Function.comp_apply]
      exact congrArg (fun s => (Real.sqrt (k : ℝ))⁻¹ * s)
        (Finset.sum_congr rfl (fun i _ => hcoord1 (Z i ω) j hj))
    · have hj2 : p ≤ (j : ℕ) := by omega
      rw [hcoord2 (normSum Z ω) j hj2]
      simp only [normSum, Function.comp_apply]
      rw [Finset.sum_congr rfl (fun i _ => hcoord2 (Z i ω) j hj2), Finset.sum_neg_distrib,
        mul_neg]
  have hpartXY : ∀ (X : Fin n → Ω → (Fin p → ℝ)) (Y : Fin m → Ω → (Fin p → ℝ))
      (F : Fin n → Ω → (Fin p → ℝ)) (G : Fin m → Ω → (Fin p → ℝ))
      (μX μY : Fin p → ℝ) (d : ℝ) (ω : Ω),
      partXY (fun i => T ∘ X i) (fun i => T ∘ Y i) (T μX) (T μY) d ω =
        T (partXY X Y μX μY d ω) := by
    intro X Y F G μX μY d ω
    funext j
    by_cases hj : (j : ℕ) < p
    · rw [hcoord1 (partXY X Y μX μY d ω) j hj]
      simp only [partXY, hnormSum, hcoord1 _ j hj]
    · have hj2 : p ≤ (j : ℕ) := by omega
      rw [hcoord2 (partXY X Y μX μY d ω) j hj2]
      simp only [partXY, hnormSum, hcoord2 _ j hj2]
      ring
  have hpartFG : ∀ (X : Fin n → Ω → (Fin p → ℝ)) (Y : Fin m → Ω → (Fin p → ℝ))
      (F : Fin n → Ω → (Fin p → ℝ)) (G : Fin m → Ω → (Fin p → ℝ))
      (μX μY : Fin p → ℝ) (d : ℝ) (ω : Ω),
      partFG (fun i => T ∘ F i) (fun i => T ∘ G i) (T μX) (T μY) d ω =
        T (partFG F G μX μY d ω) := by
    intro X Y F G μX μY d ω
    funext j
    by_cases hj : (j : ℕ) < p
    · rw [hcoord1 (partFG F G μX μY d ω) j hj]
      simp only [partFG, hnormSum, hcoord1 _ j hj]
    · have hj2 : p ≤ (j : ℕ) := by omega
      rw [hcoord2 (partFG F G μX μY d ω) j hj2]
      simp only [partFG, hnormSum, hcoord2 _ j hj2]
      ring
  have hsqrt : ∀ (X : Fin n → Ω → (Fin p → ℝ)) (Y : Fin m → Ω → (Fin p → ℝ))
      (F : Fin n → Ω → (Fin p → ℝ)) (G : Fin m → Ω → (Fin p → ℝ))
      (μX μY : Fin p → ℝ) (d : ℝ) (v : ℝ) (ω : Ω),
      Real.sqrt v • partXY (fun i => T ∘ X i) (fun i => T ∘ Y i) (T μX) (T μY) d ω +
          Real.sqrt (1 - v) •
            partFG (fun i => T ∘ F i) (fun i => T ∘ G i) (T μX) (T μY) d ω =
        T (Real.sqrt v • partXY X Y μX μY d ω +
          Real.sqrt (1 - v) • partFG F G μX μY d ω) := by
    intro X Y F G μX μY d v ω
    rw [hpartXY X Y F G μX μY d ω, hpartFG X Y F G μX μY d ω, ← hsmul, ← hsmul, ← hadd]
  exact ⟨hadd, hsmul, hcont, hinj, hrange, hnormSum, hpartXY, hpartFG, hsqrt, hpartFG,
    hcoord1, hcoord2, hleft, hright⟩
  /- @proof-region region.target-node.session.c51bc0e93738cb75 end -/

end Statlib.Imported

end

