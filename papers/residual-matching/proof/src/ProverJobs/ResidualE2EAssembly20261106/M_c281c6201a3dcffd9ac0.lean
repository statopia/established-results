import Lean
import ProverJobs.ResidualE2EAssembly20261106.M_17285beb91dc0986e103
import ProverJobs.ResidualE2EAssembly20261106.M_fa28e8f81da21b420c48

namespace PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656

run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported
open MeasureTheory ProbabilityTheory

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_1308708277_bfca1bc0 : ∀ (m r : ℕ) (hm : 0 < m) (hr : 1 ≤ r)
    (sig : Fin r → ℝ) (hsig : ∀ t, 0 ≤ sig t)
    (U : Matrix (Fin m) (Fin r) ℝ) (mu0 mubar : ℝ)
    (hmu0 : mu0 ≤ mubar) (hmubar : 0 ≤ mubar)
    (hinc : twoInfNorm U ≤ Real.sqrt (mu0 * (r : ℝ) / (m : ℝ))),
    twoInfNorm (U * Matrix.diagonal (fun t => Real.sqrt (sig t))) ≤
      Real.sqrt (SMax sig) * Real.sqrt (mubar * (r : ℝ) / (m : ℝ)) := by
  /- @proof-region region.target-node.session.da29d3783b9ed029 begin -/
  intro m r hm hr sig hsig U mu0 mubar hmu0 hmubar hinc
  haveI hne : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := by positivity
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hrm : (0 : ℝ) ≤ (r : ℝ) / (m : ℝ) := div_nonneg hr0 (le_of_lt hm0)
  have hbdd_sig : BddAbove (Set.range sig) := Finite.bddAbove_range sig
  have hbdd_row : BddAbove (Set.range (fun i : Fin m => Real.sqrt (∑ j : Fin r, U i j ^ 2))) :=
    Finite.bddAbove_range _
  have hsig_le : ∀ t : Fin r, sig t ≤ SMax sig := fun t => le_ciSup hbdd_sig t
  have hSMax0 : (0 : ℝ) ≤ SMax sig := le_trans (hsig ⟨0, hr⟩) (hsig_le ⟨0, hr⟩)
  have hC0 : (0 : ℝ) ≤ Real.sqrt (SMax sig) := Real.sqrt_nonneg _
  have hstep : twoInfNorm (U * Matrix.diagonal (fun t => Real.sqrt (sig t)))
      ≤ Real.sqrt (SMax sig) * twoInfNorm U := by
    simp only [twoInfNorm]
    refine ciSup_le (fun i => ?_)
    have hsq : (∑ j : Fin r,
        (U * Matrix.diagonal (fun t => Real.sqrt (sig t))) i j ^ 2)
        = ∑ j : Fin r, U i j ^ 2 * sig j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Matrix.mul_diagonal, mul_pow, Real.sq_sqrt (hsig j)]
    rw [hsq]
    calc Real.sqrt (∑ j : Fin r, U i j ^ 2 * sig j)
        ≤ Real.sqrt (SMax sig * ∑ j : Fin r, U i j ^ 2) := by
          apply Real.sqrt_le_sqrt
          calc ∑ j : Fin r, U i j ^ 2 * sig j
              = ∑ j : Fin r, sig j * U i j ^ 2 :=
                Finset.sum_congr rfl (fun j _ => mul_comm _ _)
            _ ≤ ∑ j : Fin r, SMax sig * U i j ^ 2 :=
                Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hsig_le j) (sq_nonneg _))
            _ = SMax sig * ∑ j : Fin r, U i j ^ 2 := by
                rw [Finset.mul_sum]
      _ = Real.sqrt (SMax sig) * Real.sqrt (∑ j : Fin r, U i j ^ 2) := Real.sqrt_mul hSMax0 _
      _ ≤ Real.sqrt (SMax sig) * ⨆ i : Fin m, Real.sqrt (∑ j : Fin r, U i j ^ 2) :=
          mul_le_mul_of_nonneg_left (le_ciSup hbdd_row i) hC0
  have hfin : Real.sqrt (SMax sig) * twoInfNorm U
      ≤ Real.sqrt (SMax sig) * Real.sqrt (mubar * (r : ℝ) / (m : ℝ)) := by
    refine le_trans (mul_le_mul_of_nonneg_left hinc hC0) ?_
    apply mul_le_mul_of_nonneg_left _ hC0
    apply Real.sqrt_le_sqrt
    rw [show mu0 * (r : ℝ) / (m : ℝ) = mu0 * ((r : ℝ) / (m : ℝ)) from by ring,
      show mubar * (r : ℝ) / (m : ℝ) = mubar * ((r : ℝ) / (m : ℝ)) from by ring]
    exact mul_le_mul_of_nonneg_right hmu0 hrm
  calc twoInfNorm (U * Matrix.diagonal (fun t => Real.sqrt (sig t)))
      ≤ Real.sqrt (SMax sig) * twoInfNorm U := hstep
    _ ≤ Real.sqrt (SMax sig) * Real.sqrt (mubar * (r : ℝ) / (m : ℝ)) := hfin
  /- @proof-region region.target-node.session.da29d3783b9ed029 end -/

end

end Statlib.Imported

