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
theorem statopia_math_node_1218121120_7255afae : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [MeasurableSpace U] [BorelSpace U]
    (e : HilbertBasis ℕ ℝ U),
    (inferInstance : MeasurableSpace U)
      = MeasurableSpace.generateFrom
          {s : Set U | ∃ (n : ℕ) (C : Set (Fin n → ℝ)), MeasurableSet C ∧
            s = (fun u : U => fun i : Fin n => inner ℝ (e i) u) ⁻¹' C} := by
  /- @proof-region region.target-node.session.b31d6428b53db485 begin -/
  intro U _ _ _ _ _ _ e
  classical
  set S : Set (Set U) := {s : Set U | ∃ (n : ℕ) (C : Set (Fin n → ℝ)), MeasurableSet C ∧
    s = (fun u : U => fun i : Fin n => inner ℝ (e i) u) ⁻¹' C} with hS
  rw [show (inferInstance : MeasurableSpace U) = borel U from BorelSpace.measurable_eq]
  refine le_antisymm ?_ ?_
  · change MeasurableSpace.generateFrom {s : Set U | IsOpen s} ≤ MeasurableSpace.generateFrom S
    have hclosed : ∀ (a : U) (r : ℝ),
        @MeasurableSet U (MeasurableSpace.generateFrom S) {u : U | ‖u - a‖ ≤ r} := by
      intro a r
      by_cases hr : 0 ≤ r
      · have hcyl : ∀ n : ℕ, @MeasurableSet U (MeasurableSpace.generateFrom S)
            {u : U | ∑ i : Fin n, (inner ℝ (e i) (u - a)) ^ 2 ≤ r ^ 2} := by
          intro n
          refine MeasurableSpace.measurableSet_generateFrom ?_
          refine ⟨n, {x : Fin n → ℝ | ∑ i : Fin n, (x i - inner ℝ (e i) a) ^ 2 ≤ r ^ 2}, ?_, ?_⟩
          · have hcont : Continuous fun x : Fin n → ℝ =>
                ∑ i : Fin n, (x i - inner ℝ (e i) a) ^ 2 := by
              apply continuous_finset_sum
              intro i _
              exact ((continuous_apply i).sub continuous_const).pow 2
            exact (isClosed_le hcont continuous_const).measurableSet
          · ext u
            simp only [Set.mem_setOf_eq, Set.mem_preimage, inner_sub_right]
        have hEqint : {u : U | ‖u - a‖ ≤ r} = ⋂ n : ℕ,
            {u : U | ∑ i : Fin n, (inner ℝ (e i) (u - a)) ^ 2 ≤ r ^ 2} := by
          ext u
          simp only [Set.mem_setOf_eq, Set.mem_iInter]
          constructor
          · intro hu n
            have hbase : HasSum (fun i : ℕ => (inner ℝ (e i) (u - a)) ^ 2) (‖u - a‖ ^ 2) := by
              have h := e.hasSum_inner_mul_inner (u - a) (u - a)
              have hfun : (fun i : ℕ => inner ℝ (u - a) (e i) * inner ℝ (e i) (u - a))
                  = fun i : ℕ => (inner ℝ (e i) (u - a)) ^ 2 := by
                funext i
                rw [real_inner_comm (u - a) (e i), pow_two]
              rw [hfun] at h
              rwa [real_inner_self_eq_norm_sq] at h
            have h2 : ‖u - a‖ ^ 2 ≤ r ^ 2 := by nlinarith [norm_nonneg (u - a)]
            calc ∑ i : Fin n, (inner ℝ (e i) (u - a)) ^ 2
                = ∑ i ∈ Finset.range n, (inner ℝ (e i) (u - a)) ^ 2 :=
                  Fin.sum_univ_eq_sum_range (fun i => (inner ℝ (e i) (u - a)) ^ 2) n
              _ ≤ ∑' i : ℕ, (inner ℝ (e i) (u - a)) ^ 2 :=
                  hbase.summable.sum_le_tsum (Finset.range n) (fun i _ => by positivity)
              _ = ‖u - a‖ ^ 2 := hbase.tsum_eq
              _ ≤ r ^ 2 := h2
          · intro hu
            have hbase : HasSum (fun i : ℕ => (inner ℝ (e i) (u - a)) ^ 2) (‖u - a‖ ^ 2) := by
              have h := e.hasSum_inner_mul_inner (u - a) (u - a)
              have hfun : (fun i : ℕ => inner ℝ (u - a) (e i) * inner ℝ (e i) (u - a))
                  = fun i : ℕ => (inner ℝ (e i) (u - a)) ^ 2 := by
                funext i
                rw [real_inner_comm (u - a) (e i), pow_two]
              rw [hfun] at h
              rwa [real_inner_self_eq_norm_sq] at h
            have hsum : ∀ n : ℕ, ∑ i ∈ Finset.range n, (inner ℝ (e i) (u - a)) ^ 2 ≤ r ^ 2 := by
              intro n
              rw [← Fin.sum_univ_eq_sum_range (fun i => (inner ℝ (e i) (u - a)) ^ 2) n]
              exact hu n
            have hlim := (hasSum_iff_tendsto_nat_of_nonneg (fun i => by positivity)
              (‖u - a‖ ^ 2)).1 hbase
            have h2 : ‖u - a‖ ^ 2 ≤ r ^ 2 :=
              le_of_tendsto_of_tendsto hlim tendsto_const_nhds (Eventually.of_forall hsum)
            have hmul : ‖u - a‖ * ‖u - a‖ ≤ r * r := by rwa [← pow_two, ← pow_two]
            exact (mul_self_le_mul_self_iff (norm_nonneg _) hr).2 hmul
        rw [hEqint]
        exact MeasurableSet.iInter hcyl
      · have h0 : {u : U | ‖u - a‖ ≤ r} = ∅ := by
          ext u
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
          exact lt_of_lt_of_le (not_le.1 hr) (norm_nonneg _)
        rw [h0]
        exact MeasurableSpace.measurableSet_generateFrom ⟨1, ∅, MeasurableSet.empty, by simp⟩
    have hopen : ∀ V : Set U, IsOpen V → @MeasurableSet U (MeasurableSpace.generateFrom S) V := by
      intro V hV
      have hd : DenseRange (TopologicalSpace.denseSeq U) := TopologicalSpace.denseRange_denseSeq U
      have hdense : ∀ (u : U) (δ : ℝ), 0 < δ →
          ∃ n : ℕ, dist u (TopologicalSpace.denseSeq U n) < δ := by
        exact fun u δ hδ => hd.exists_dist_lt u hδ
      have hEq : V = ⋃ p : ℕ × ℚ, (if TopologicalSpace.denseSeq U p.1 ∈ V ∧
          Metric.closedBall (TopologicalSpace.denseSeq U p.1) (p.2 : ℝ) ⊆ V
          then Metric.closedBall (TopologicalSpace.denseSeq U p.1) (p.2 : ℝ) else ∅) := by
        refine Set.Subset.antisymm ?_ ?_
        · intro u hu
          obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.1 hV u hu
          obtain ⟨n, hn⟩ := hdense u (ε / 2) (by linarith)
          obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show dist u (TopologicalSpace.denseSeq U n) <
            ε - dist u (TopologicalSpace.denseSeq U n) from by linarith)
          have hcond : TopologicalSpace.denseSeq U n ∈ V ∧
              Metric.closedBall (TopologicalSpace.denseSeq U n) (q : ℝ) ⊆ V := by
            constructor
            · refine hsub ?_
              rw [Metric.mem_ball, dist_comm]
              linarith
            · intro y hy
              rw [Metric.mem_closedBall, dist_comm y] at hy
              refine hsub ?_
              rw [Metric.mem_ball, dist_comm y u]
              linarith [dist_triangle u (TopologicalSpace.denseSeq U n) y]
          rw [Set.mem_iUnion]
          refine ⟨(n, q), ?_⟩
          rw [if_pos hcond, Metric.mem_closedBall]
          exact le_of_lt hq1
        · intro u hu
          rw [Set.mem_iUnion] at hu
          obtain ⟨p, hp⟩ := hu
          by_cases hcond : TopologicalSpace.denseSeq U p.1 ∈ V ∧
              Metric.closedBall (TopologicalSpace.denseSeq U p.1) (p.2 : ℝ) ⊆ V
          · rw [if_pos hcond] at hp
            exact hcond.2 hp
          · rw [if_neg hcond] at hp
            exact absurd hp (by simp)
      rw [hEq]
      refine MeasurableSet.iUnion (fun p : ℕ × ℚ => ?_)
      by_cases hcond : TopologicalSpace.denseSeq U p.1 ∈ V ∧
          Metric.closedBall (TopologicalSpace.denseSeq U p.1) (p.2 : ℝ) ⊆ V
      · rw [if_pos hcond]
        have hc : Metric.closedBall (TopologicalSpace.denseSeq U p.1) (p.2 : ℝ) =
            {u : U | ‖u - TopologicalSpace.denseSeq U p.1‖ ≤ (p.2 : ℝ)} := by
          ext u
          rw [Metric.mem_closedBall, Set.mem_setOf_eq, dist_eq_norm]
        rw [hc]
        exact hclosed _ _
      · rw [if_neg hcond]
        exact MeasurableSpace.measurableSet_generateFrom ⟨1, ∅, MeasurableSet.empty, by simp⟩
    exact MeasurableSpace.generateFrom_le fun t ht => hopen t ht
  · refine MeasurableSpace.generateFrom_le ?_
    rintro s hs
    obtain ⟨n, C, hC, rfl⟩ := hs
    have hcont : Continuous fun u : U => fun i : Fin n => inner ℝ (e i) u :=
      continuous_pi fun i => continuous_const.inner continuous_id
    rw [← BorelSpace.measurable_eq]
    exact hcont.measurable hC
  /- @proof-region region.target-node.session.b31d6428b53db485 end -/

end Statlib.Imported
end

