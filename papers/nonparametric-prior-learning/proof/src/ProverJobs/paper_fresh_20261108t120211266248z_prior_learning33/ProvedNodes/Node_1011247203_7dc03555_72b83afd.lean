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
theorem statopia_math_node_1011247203_7dc03555 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [MeasurableSpace U] [BorelSpace U]
    (e : HilbertBasis ℕ ℝ U) (a : ℕ → ℝ) (m : U),
    Measurable (fun u : U => ∑' k : ℕ, a k * inner ℝ (e k) (u - m)) := by
  /- @proof-region region.target-node.session.7fb9cb3908783bd1 begin -/
  classical
  intro U _ _ _ _ _ _ e a m
  let f : ℕ → U → ℝ := fun k u => a k * inner ℝ (e k) (u - m)
  have hf : ∀ k, Measurable (f k) := by
    intro k
    dsimp [f]
    exact measurable_const.mul (measurable_const.inner (measurable_id.sub measurable_const))
  let P : U → ENNReal := fun u => ∑' k : ℕ, ENNReal.ofReal (f k u)
  let N : U → ENNReal := fun u => ∑' k : ℕ, ENNReal.ofReal (-(f k u))
  have hP : Measurable P := by
    dsimp [P]
    exact Measurable.ennreal_tsum fun k => (hf k).ennreal_ofReal
  have hN : Measurable N := by
    dsimp [N]
    exact Measurable.ennreal_tsum fun k => (hf k).neg.ennreal_ofReal
  let S : Set U := {u | P u < ⊤ ∧ N u < ⊤}
  have hS : MeasurableSet S := by
    dsimp [S]
    exact (hP measurableSet_Iio).inter (hN measurableSet_Iio)
  have hB : Measurable (fun u : U => (P u).toReal - (N u).toReal) :=
    (hP.ennreal_toReal).sub (hN.ennreal_toReal)
  have hEq : ∀ u : U, (∑' k : ℕ, f k u) =
      if u ∈ S then (P u).toReal - (N u).toReal else 0 := by
    intro u
    by_cases hu : u ∈ S
    · rw [if_pos hu]
      have hPfin : P u < ⊤ := hu.1
      have hNfin : N u < ⊤ := hu.2
      have hPne : P u ≠ ⊤ := ne_of_lt hPfin
      have hNne : N u ≠ ⊤ := ne_of_lt hNfin
      let p : ℕ → ℝ := fun k => max (f k u) 0
      let q : ℕ → ℝ := fun k => max (-(f k u)) 0
      have hp_nonneg : ∀ k, 0 ≤ p k := fun k => le_max_right _ _
      have hq_nonneg : ∀ k, 0 ≤ q k := fun k => le_max_right _ _
      have hofp : ∀ k, ENNReal.ofReal (p k) = ENNReal.ofReal (f k u) := by
        intro k
        dsimp [p]
        by_cases hk : 0 ≤ f k u
        · rw [max_eq_left hk]
        · have hk' : f k u ≤ 0 := le_of_not_ge hk
          rw [max_eq_right hk']
          simp [ENNReal.ofReal_of_nonpos hk']
      have hofq : ∀ k, ENNReal.ofReal (q k) = ENNReal.ofReal (-(f k u)) := by
        intro k
        dsimp [q]
        by_cases hk : 0 ≤ -(f k u)
        · rw [max_eq_left hk]
        · have hk' : -(f k u) ≤ 0 := le_of_not_ge hk
          rw [max_eq_right hk']
          simp [ENNReal.ofReal_of_nonpos hk']
      have hp_summable : Summable p := by
        refine summable_of_sum_range_le hp_nonneg (c := (P u).toReal) ?_
        intro n
        have hsum_eq : ENNReal.ofReal (∑ k ∈ Finset.range n, p k) =
            ∑ k ∈ Finset.range n, ENNReal.ofReal (p k) :=
          ENNReal.ofReal_sum_of_nonneg (fun k hk => hp_nonneg k)
        have hterm : (∑ k ∈ Finset.range n, ENNReal.ofReal (p k)) =
            ∑ k ∈ Finset.range n, ENNReal.ofReal (f k u) :=
          Finset.sum_congr rfl (fun k hk => hofp k)
        have hle : (∑ k ∈ Finset.range n, ENNReal.ofReal (f k u)) ≤ P u := by
          change (∑ k ∈ Finset.range n, ENNReal.ofReal (f k u)) ≤
            ∑' k : ℕ, ENNReal.ofReal (f k u)
          exact ENNReal.sum_le_tsum _
        have hofle : ENNReal.ofReal (∑ k ∈ Finset.range n, p k) ≤ P u := by
          rw [hsum_eq, hterm]
          exact hle
        exact (ENNReal.ofReal_le_iff_le_toReal hPne).1 hofle
      have hq_summable : Summable q := by
        refine summable_of_sum_range_le hq_nonneg (c := (N u).toReal) ?_
        intro n
        have hsum_eq : ENNReal.ofReal (∑ k ∈ Finset.range n, q k) =
            ∑ k ∈ Finset.range n, ENNReal.ofReal (q k) :=
          ENNReal.ofReal_sum_of_nonneg (fun k hk => hq_nonneg k)
        have hterm : (∑ k ∈ Finset.range n, ENNReal.ofReal (q k)) =
            ∑ k ∈ Finset.range n, ENNReal.ofReal (-(f k u)) :=
          Finset.sum_congr rfl (fun k hk => hofq k)
        have hle : (∑ k ∈ Finset.range n, ENNReal.ofReal (-(f k u))) ≤ N u := by
          change (∑ k ∈ Finset.range n, ENNReal.ofReal (-(f k u))) ≤
            ∑' k : ℕ, ENNReal.ofReal (-(f k u))
          exact ENNReal.sum_le_tsum _
        have hofle : ENNReal.ofReal (∑ k ∈ Finset.range n, q k) ≤ N u := by
          rw [hsum_eq, hterm]
          exact hle
        exact (ENNReal.ofReal_le_iff_le_toReal hNne).1 hofle
      have hsub : Summable (fun k => p k - q k) := hp_summable.sub hq_summable
      have htsum_sub : (∑' k : ℕ, (p k - q k)) = (∑' k : ℕ, p k) - (∑' k : ℕ, q k) := by
        have hh : HasSum (fun k : ℕ => p k - q k) ((∑' k : ℕ, p k) - (∑' k : ℕ, q k)) :=
          hp_summable.hasSum.sub hq_summable.hasSum
        exact hh.tsum_eq
      have hP_eq : ENNReal.ofReal (∑' k : ℕ, p k) = P u := by
        calc
          ENNReal.ofReal (∑' k : ℕ, p k) = ∑' k : ℕ, ENNReal.ofReal (p k) :=
            ENNReal.ofReal_tsum_of_nonneg hp_nonneg hp_summable
          _ = ∑' k : ℕ, ENNReal.ofReal (f k u) := tsum_congr hofp
          _ = P u := rfl
      have hP_toReal : (P u).toReal = ∑' k : ℕ, p k := by
        rw [← hP_eq]
        exact ENNReal.toReal_ofReal (tsum_nonneg hp_nonneg)
      have hN_eq : ENNReal.ofReal (∑' k : ℕ, q k) = N u := by
        calc
          ENNReal.ofReal (∑' k : ℕ, q k) = ∑' k : ℕ, ENNReal.ofReal (q k) :=
            ENNReal.ofReal_tsum_of_nonneg hq_nonneg hq_summable
          _ = ∑' k : ℕ, ENNReal.ofReal (-(f k u)) := tsum_congr hofq
          _ = N u := rfl
      have hN_toReal : (N u).toReal = ∑' k : ℕ, q k := by
        rw [← hN_eq]
        exact ENNReal.toReal_ofReal (tsum_nonneg hq_nonneg)
      have hg_eq : ∀ k, f k u = p k - q k := by
        intro k
        dsimp [p, q]
        by_cases hk : 0 ≤ f k u
        · rw [max_eq_left hk, max_eq_right (by linarith : -(f k u) ≤ 0)]
          ring
        · have hk' : f k u ≤ 0 := le_of_not_ge hk
          rw [max_eq_right hk', max_eq_left (by linarith : 0 ≤ -(f k u))]
          ring
      calc
        (∑' k : ℕ, f k u) = ∑' k : ℕ, (p k - q k) := tsum_congr hg_eq
        _ = (∑' k : ℕ, p k) - (∑' k : ℕ, q k) := htsum_sub
        _ = (P u).toReal - (N u).toReal := by rw [hP_toReal, hN_toReal]
    · rw [if_neg hu]
      refine tsum_eq_zero_of_not_summable ?_
      intro hsum
      exact hu ⟨hsum.tsum_ofReal_lt_top, hsum.neg.tsum_ofReal_lt_top⟩
  change Measurable (fun u : U => ∑' k : ℕ, f k u)
  rw [funext hEq]
  exact Measurable.ite hS hB measurable_const
  /- @proof-region region.target-node.session.7fb9cb3908783bd1 end -/

end Statlib.Imported
end

