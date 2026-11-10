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
theorem statopia_math_node_2860392294_355ed9db : ∀ (Ω : Type*) [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (hFmono : ∀ n : ℕ, F n ≤ F (n + 1))
    (hFle : ∀ n : ℕ, F n ≤ m0)
    (h : ℕ → Ω → ℝ)
    (hmeas : ∀ n : ℕ, @Measurable Ω ℝ (F n) (by infer_instance) (h n))
    (hint : ∀ n : ℕ, Integrable (fun ω => (h n ω) ^ 2) μ)
    (hart : ∀ (n : ℕ) (B : Set Ω), @MeasurableSet Ω (F n) B →
      ∫ ω in B, h (n + 1) ω ∂μ = ∫ ω in B, h n ω ∂μ)
    (m n : ℕ) (hmn : n ≤ m),
    ∫ ω, h m ω * h n ω ∂μ = ∫ ω, (h n ω) ^ 2 ∂μ := by
  /- @proof-region region.target-node.session.e185cae8ccabbddd begin -/
  intro Ω m0 μ hprob F hFmono hFle h hmeas hint hart m n hmn
  have hmono : Monotone F := monotone_nat_of_le_succ hFmono
  have hset : ∀ k : ℕ, n ≤ k → ∀ B : Set Ω,
      @MeasurableSet Ω (F n) B → ∫ ω in B, h k ω ∂μ = ∫ ω in B, h n ω ∂μ := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => intro B _; rfl
    | succ k hnk ih =>
        intro B hB
        have hBFk : @MeasurableSet Ω (F k) B := hmono hnk B hB
        exact (hart k B hBFk).trans (ih B hB)
  have hasm : ∀ k : ℕ, AEStronglyMeasurable (h k) μ := fun k =>
    (hmeas k).aestronglyMeasurable.mono (hFle k)
  have hmem : ∀ k : ℕ, MemLp (h k) 2 μ := fun k =>
    (MeasureTheory.memLp_two_iff_integrable_sq (hasm k)).mpr (hint k)
  have hInt : ∀ k : ℕ, Integrable (h k) μ := by
    intro k
    have h2 : Integrable (fun ω => ‖h k ω‖ ^ 2 + 1) μ :=
      ((MeasureTheory.memLp_two_iff_integrable_sq_norm (hasm k)).mp (hmem k)).add
        (integrable_const (1 : ℝ))
    refine h2.mono' (hasm k) ?_
    filter_upwards with ω
    nlinarith [sq_nonneg (‖h k ω‖ - 1), norm_nonneg (h k ω)]
  haveI : SigmaFinite (μ.trim (hFle n)) := inferInstance
  have hcond : h n =ᵐ[μ] μ[h m | F n] := by
    refine MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq (hFle n) ?_ ?_ ?_ ?_
    · exact hInt m
    · intro s hs hμs
      exact (hInt n).integrableOn
    · intro s hs hμs
      exact (hset m hmn s hs).symm
    · exact Measurable.aestronglyMeasurable (hmeas n)
  set fm : Lp ℝ 2 μ := MemLp.toLp (h m) (hmem m) with hfm
  set fn : Lp ℝ 2 μ := MemLp.toLp (h n) (hmem n) with hfn
  have hfm_ae : (↑↑fm : Ω → ℝ) =ᵐ[μ] h m := by
    rw [hfm]
    exact MeasureTheory.MemLp.coeFn_toLp (hmem m)
  have hfn_ae : (↑↑fn : Ω → ℝ) =ᵐ[μ] h n := by
    rw [hfn]
    exact MeasureTheory.MemLp.coeFn_toLp (hmem n)
  have hP_ae : (↑↑↑((condExpL2 ℝ ℝ (hFle n)) fm) : Ω → ℝ) =ᵐ[μ] h n := by
    rw [hfm]
    exact (MeasureTheory.MemLp.condExpL2_ae_eq_condExp (E := ℝ) (𝕜 := ℝ)
      (hFle n) (hmem m)).trans hcond.symm
  have hinner : inner ℝ (↑((condExpL2 ℝ ℝ (hFle n)) fm)) fn = inner ℝ fm fn :=
    MeasureTheory.inner_condExpL2_eq_inner_fun (hFle n) fm fn
      ((Measurable.aestronglyMeasurable (hmeas n)).congr hfn_ae.symm)
  set Fm : Ω → ℝ := ↑↑fm with hFm
  set Fn : Ω → ℝ := ↑↑fn with hFn
  set PF : Ω → ℝ := ↑↑↑((condExpL2 ℝ ℝ (hFle n)) fm) with hPF
  have hFm_ae : Fm =ᵐ[μ] h m := by
    rw [hFm]; exact hfm_ae
  have hFn_ae : Fn =ᵐ[μ] h n := by
    rw [hFn]; exact hfn_ae
  have hPF_ae : PF =ᵐ[μ] h n := by
    rw [hPF]; exact hP_ae
  have hmain : ∫ ω, inner ℝ (PF ω) (Fn ω) ∂μ = ∫ ω, inner ℝ (Fm ω) (Fn ω) ∂μ := by
    rw [hPF, hFm]
    simpa only [MeasureTheory.L2.inner_def] using hinner
  have hright : ∫ ω, inner ℝ (Fm ω) (Fn ω) ∂μ = ∫ ω, h m ω * h n ω ∂μ := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hFm_ae, hFn_ae] with ω h1 h2
    rw [h1, h2]
    simp
    ring
  have hleft : ∫ ω, inner ℝ (PF ω) (Fn ω) ∂μ = ∫ ω, h n ω * h n ω ∂μ := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hPF_ae, hFn_ae] with ω h1 h2
    rw [h1, h2]
    simp
    ring
  have hsq : ∫ ω, h n ω * h n ω ∂μ = ∫ ω, (h n ω) ^ 2 ∂μ := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with ω
    ring
  calc ∫ ω, h m ω * h n ω ∂μ = ∫ ω, inner ℝ (Fm ω) (Fn ω) ∂μ := hright.symm
    _ = ∫ ω, inner ℝ (PF ω) (Fn ω) ∂μ := hmain.symm
    _ = ∫ ω, h n ω * h n ω ∂μ := hleft
    _ = ∫ ω, (h n ω) ^ 2 ∂μ := hsq
  /- @proof-region region.target-node.session.e185cae8ccabbddd end -/

end Statlib.Imported
end

