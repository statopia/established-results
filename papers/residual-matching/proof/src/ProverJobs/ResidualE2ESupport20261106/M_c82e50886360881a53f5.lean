import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_f563494b66a5583a8f7d

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
theorem statopia_math_node_3733483906_a137eb95 : ∀ (m n : ℕ),
    ProbabilityTheory.IsGaussian
      (MeasureTheory.Measure.pi
        (fun _ : Fin m =>
          MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1))) := by
  /- @proof-region region.target-node.session.f562b9b82907e549 begin -/
  intro m n
  have hmap : MeasureTheory.Measure.map (fun g : Fin m → Fin n → ℝ => fun p : Fin m × Fin n => g p.1 p.2)
      (MeasureTheory.Measure.pi (fun _ : Fin m => MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)))
      = MeasureTheory.Measure.pi (fun _ : Fin m × Fin n => ProbabilityTheory.gaussianReal 0 1) := by
    refine (MeasureTheory.Measure.pi_eq (μ := fun _ : Fin m × Fin n => ProbabilityTheory.gaussianReal 0 1) ?_).symm
    intro s hs
    have hpre : (fun g : Fin m → Fin n → ℝ => fun p : Fin m × Fin n => g p.1 p.2) ⁻¹' (Set.univ.pi s)
        = Set.univ.pi (fun i : Fin m => Set.univ.pi (fun j : Fin n => s (i, j))) := by
      ext g
      simp only [Set.mem_preimage, Set.mem_univ_pi, Prod.forall]
    rw [MeasureTheory.Measure.map_apply (by measurability) (MeasurableSet.univ_pi hs)]
    rw [hpre]
    rw [MeasureTheory.Measure.pi_pi]
    simp only [MeasureTheory.Measure.pi_pi]
    rw [Fintype.prod_prod_type]
  let cE : ((Fin m × Fin n) → ℝ) →L[ℝ] (Fin m → Fin n → ℝ) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun ω i j => ω (i, j)
        map_add' := fun x y => by funext i j; rfl
        map_smul' := fun a x => by funext i j; rfl }
  have hmap2 : MeasureTheory.Measure.map (⇑cE)
      (MeasureTheory.Measure.pi (fun _ : Fin m × Fin n => ProbabilityTheory.gaussianReal 0 1))
      = MeasureTheory.Measure.pi (fun _ : Fin m => MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)) := by
    rw [← hmap]
    rw [MeasureTheory.Measure.map_map]
    · rw [show (⇑cE ∘ (fun g : Fin m → Fin n → ℝ => fun p : Fin m × Fin n => g p.1 p.2)) = id from by
        funext g
        rfl]
      rw [MeasureTheory.Measure.map_id]
    · measurability
    · measurability
  have hGauss_flat : ProbabilityTheory.IsGaussian
      (MeasureTheory.Measure.pi (fun _ : Fin m × Fin n => ProbabilityTheory.gaussianReal 0 1)) := by
    refine ProbabilityTheory.isGaussian_of_map_eq_gaussianReal (fun L => ?_)
    set c : Fin m × Fin n → ℝ := fun p => L (fun q => if q = p then (1 : ℝ) else 0) with hc
    refine ⟨0, ⟨∑ p : Fin m × Fin n, (c p) ^ 2,
      Finset.sum_nonneg fun p _ => sq_nonneg (c p)⟩, ?_⟩
    have hL : (⇑L : ((Fin m × Fin n) → ℝ) → ℝ)
        = fun ω => ∑ p : Fin m × Fin n, c p * ω p := by
      funext ω
      have hω : ω = ∑ p : Fin m × Fin n, ω p • (fun q => if q = p then (1 : ℝ) else 0) := by
        funext q
        rw [Finset.sum_apply]
        rw [Finset.sum_eq_single q]
        · simp
        · intro p _ hp
          simp [Ne.symm hp]
        · intro hq
          exact absurd (Finset.mem_univ q) hq
      conv_lhs => rw [hω]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [map_smul, smul_eq_mul]
      simp only [hc]
      exact mul_comm _ _
    conv_lhs => rw [hL]
    exact statopia_math_node_647033768_7a6b2259 (Fin m × Fin n) c
  haveI : ProbabilityTheory.IsGaussian
      (MeasureTheory.Measure.pi (fun _ : Fin m × Fin n => ProbabilityTheory.gaussianReal 0 1)) := hGauss_flat
  rw [← hmap2]
  exact ProbabilityTheory.isGaussian_map cE
  /- @proof-region region.target-node.session.f562b9b82907e549 end -/

end Statlib.Imported

