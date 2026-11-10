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
theorem statopia_math_node_3300259176_dcd675c6 : ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ)
    (hY_meas : ∀ k : ℕ, Measurable (Y k))
    (hY_indep : ProbabilityTheory.iIndepFun Y μ)
    (hY_mean : ∀ k : ℕ, (∫ ω, Y k ω ∂μ) = 0)
    (hY_memLp : ∀ k : ℕ, MeasureTheory.MemLp (Y k) 2 μ),
    MeasureTheory.Submartingale (fun n ω => ∑ k ∈ Finset.range (n + 1), Y k ω)
      (MeasureTheory.Filtration.natural (β := fun _ => ℝ) Y
        (fun k => (hY_meas k).stronglyMeasurable)) μ := by
  /- @proof-region region.target-node.session.910998ce336e3a89 begin -/
  intro Ω _ μ _ Y hY_meas hY_indep hY_mean hY_memLp
  let hf : ∀ k : ℕ, StronglyMeasurable (Y k) := fun k => (hY_meas k).stronglyMeasurable
  let ℱ := Filtration.natural (β := fun _ => ℝ) Y hf
  let S : ℕ → Ω → ℝ := fun n ω => ∑ k ∈ Finset.range (n + 1), Y k ω
  have hint : ∀ n : ℕ, Integrable (S n) μ := by
    intro n
    have hmem : MemLp (S n) 2 μ :=
      memLp_finset_sum (Finset.range (n + 1)) (fun k _ => hY_memLp k)
    exact hmem.integrable (by norm_num)
  have hadaptY : StronglyAdapted ℱ Y := Filtration.stronglyAdapted_natural (u := Y) hf
  have hstrong : StronglyAdapted ℱ S := by
    intro n
    have h : StronglyMeasurable[ℱ n] (∑ k ∈ Finset.range (n + 1), Y k) := by
      apply Finset.stronglyMeasurable_sum
      intro k hk
      have hk' : k ≤ n := by
        rw [Finset.mem_range] at hk
        omega
      exact hadaptY.stronglyMeasurable_le hk'
    change StronglyMeasurable[ℱ n] (fun ω => ∑ k ∈ Finset.range (n + 1), Y k ω)
    rw [show (fun ω => ∑ k ∈ Finset.range (n + 1), Y k ω) = (∑ k ∈ Finset.range (n + 1), Y k) from by
      funext a
      rw [Finset.sum_apply]]
    exact h
  have hce : ∀ i : ℕ, S i =ᵐ[μ] μ[S (i + 1) | ℱ i] := by
    intro i
    have hSY : S (i + 1) =ᵐ[μ] S i + Y (i + 1) := by
      filter_upwards with ω
      have h1 : S (i + 1) ω = ∑ k ∈ Finset.range ((i + 1) + 1), Y k ω := rfl
      have h2 : S i ω = ∑ k ∈ Finset.range (i + 1), Y k ω := rfl
      rw [Pi.add_apply, h1, h2, Finset.sum_range_succ (n := i + 1)]
    have h1e : μ[S i | ℱ i] = S i :=
      condExp_of_stronglyMeasurable (ℱ.le i) (hstrong i) (hint i)
    have hYint : Integrable (Y (i + 1)) μ := (hY_memLp (i + 1)).integrable (by norm_num)
    have h2 : μ[Y (i + 1) | ℱ i] =ᵐ[μ] (0 : Ω → ℝ) := by
      have h := iIndepFun.condExp_natural_ae_eq_of_lt (μ := μ) (f := Y) hf hY_indep (Nat.lt_succ_self i)
      simp only [hY_mean] at h
      exact h
    have hadd : μ[(S i) + Y (i + 1) | ℱ i] =ᵐ[μ] μ[S i | ℱ i] + μ[Y (i + 1) | ℱ i] :=
      condExp_add (hint i) hYint (ℱ i)
    have hsum : (μ[S i | ℱ i] + μ[Y (i + 1) | ℱ i]) =ᵐ[μ] S i := by
      filter_upwards [h2] with ω h2ω
      rw [Pi.add_apply, h2ω, h1e]
      simp
    have hstep3 : μ[(S i) + Y (i + 1) | ℱ i] =ᵐ[μ] μ[S (i + 1) | ℱ i] :=
      condExp_congr_ae hSY.symm
    exact hsum.symm.trans (hadd.symm.trans hstep3)
  have hmart : Martingale S ℱ μ := martingale_nat hstrong hint hce
  exact hmart.submartingale
  /- @proof-region region.target-node.session.910998ce336e3a89 end -/

end Statlib.Imported
end

