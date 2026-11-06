import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_26450f09d763592440f3

namespace PaperProofTasks.ResidualE2ESupport20261106
open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_2032205188_a4903375 : ∀ (N : ℕ) [NeZero N]
    {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → Matrix (Fin N) (Fin N) ℂ)
    (hX : ∀ ω : Ω, (X ω).IsHermitian)
    (hXmeas : ∀ i j : Fin N, Measurable fun ω : Ω => X ω i j),
    Measurable fun ω : Ω => sSup (Set.range fun i : Fin N => (hX ω).eigenvalues i) := by
  /- @proof-region region.target-node.session.15e656a24b5ec76b begin -/
  intro N _ Ω _ X hX hXmeas
  classical
  have hterm : ∀ v : Fin N → ℂ, Measurable fun ω : Ω =>
      (∑ i : Fin N, ∑ j : Fin N, (star (v i) * v j) * X ω i j).re := by
    intro v
    exact Complex.measurable_re.comp
      (Finset.measurable_sum _ fun i _ =>
        Finset.measurable_sum _ fun j _ => measurable_const.mul (hXmeas i j))
  obtain ⟨V, hV⟩ : ∃ V : ℕ → (Fin N → ℂ), DenseRange V :=
    ⟨TopologicalSpace.denseSeq (Fin N → ℂ), TopologicalSpace.denseRange_denseSeq (Fin N → ℂ)⟩
  have hcont : ∀ (A : Matrix (Fin N) (Fin N) ℂ) (t : ℝ), Continuous fun v : Fin N → ℂ =>
      (∑ i : Fin N, ∑ j : Fin N, (star (v i) * v j) * A i j).re
        - t * ∑ i : Fin N, ‖v i‖ ^ 2 := by
    intro A t
    have hs : Continuous fun v : Fin N → ℂ =>
        (∑ i : Fin N, ∑ j : Fin N, (star (v i) * v j) * A i j).re := by
      refine Complex.continuous_re.comp ?_
      refine continuous_finset_sum _ ?_
      intro i _
      refine continuous_finset_sum _ ?_
      intro j _
      exact ((continuous_star.comp (continuous_apply i)).mul (continuous_apply j)).mul
        continuous_const
    have hn : Continuous fun v : Fin N → ℂ => t * ∑ i : Fin N, ‖v i‖ ^ 2 := by
      have h : Continuous fun v : Fin N → ℂ => ∑ i : Fin N, ‖v i‖ ^ 2 := by
        refine continuous_finset_sum _ ?_
        intro i _
        exact (continuous_norm.comp (continuous_apply i)).pow 2
      simpa only [Pi.mul_apply] using continuous_const.mul h
    exact hs.sub hn
  have hlev : ∀ t : ℝ, MeasurableSet {ω : Ω |
      sSup (Set.range fun i : Fin N => (hX ω).eigenvalues i) ≤ t} := by
    intro t
    have hset : {ω : Ω | sSup (Set.range fun i : Fin N => (hX ω).eigenvalues i) ≤ t}
        = ⋂ k : ℕ, {ω : Ω | (∑ i : Fin N, ∑ j : Fin N, (star (V k i) * V k j) * X ω i j).re
            ≤ t * ∑ i : Fin N, ‖V k i‖ ^ 2} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro h k
        exact (statopia_math_node_3044336349_4fb621ca N (X ω) (hX ω) t).mp h (V k)
      · intro h
        refine (statopia_math_node_3044336349_4fb621ca N (X ω) (hX ω) t).mpr fun v => ?_
        by_contra hcon
        rw [not_le] at hcon
        have hf : ∀ k : ℕ, (∑ i : Fin N, ∑ j : Fin N, (star (V k i) * V k j) * X ω i j).re
            - t * ∑ i : Fin N, ‖V k i‖ ^ 2 ≤ 0 := by
          intro k
          have hk := h k
          linarith
        have hpos : 0 < (∑ i : Fin N, ∑ j : Fin N, (star (v i) * v j) * X ω i j).re
            - t * ∑ i : Fin N, ‖v i‖ ^ 2 := by linarith
        have hopen : IsOpen {u : Fin N → ℂ | 0 <
            (∑ i : Fin N, ∑ j : Fin N, (star (u i) * u j) * X ω i j).re
              - t * ∑ i : Fin N, ‖u i‖ ^ 2} :=
          isOpen_lt continuous_const (hcont (X ω) t)
        obtain ⟨k, hk⟩ := hV.exists_mem_open hopen ⟨v, hpos⟩
        have hk2 := hf k
        simp only [Set.mem_setOf_eq] at hk
        linarith
    rw [hset]
    exact MeasurableSet.iInter fun k => measurableSet_le (hterm (V k)) measurable_const
  exact measurable_of_Iic hlev
  /- @proof-region region.target-node.session.15e656a24b5ec76b end -/

end Statlib.Imported

