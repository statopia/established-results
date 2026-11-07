import Lean
import ProverJobs.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.Vocabulary
import ProverJobs.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.Base

namespace PaperProofTasks.job_paper_370f7a68a9a1447a9d903f9a55f08bd5

open scoped BigOperators
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.Statlib.Imported

noncomputable section
open scoped BigOperators
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_283558168_72fffefb : ∀ (p : ℕ) (hp : 0 < p) (beta : ℝ)
    (hbeta : 0 < beta) (y : Fin p → ℝ),
    ContDiff ℝ 3 (Fbeta p beta y) ∧
      ∀ w : Fin p → ℝ,
        0 < (∑ m : Fin p, Real.exp (beta * (w m - y m))) ∧
          (∀ j : Fin p,
            0 < Real.exp (beta * (w j - y j)) /
              (∑ m : Fin p, Real.exp (beta * (w m - y m)))) ∧
          (∑ j : Fin p,
              Real.exp (beta * (w j - y j)) /
                (∑ m : Fin p, Real.exp (beta * (w m - y m))) = (1 : ℝ)) ∧
          (∀ u : Fin p → ℝ,
            fderiv ℝ (Fbeta p beta y) w u
              = ∑ j : Fin p,
                  (Real.exp (beta * (w j - y j)) /
                    (∑ m : Fin p, Real.exp (beta * (w m - y m)))) * u j) := by
  /- @proof-region region.target-node.session.d9628ca20264c316 begin -/
  intro p hp beta hbeta y
  refine ⟨?_, ?_⟩
  · unfold Fbeta
    have hSpos : ∀ w : Fin p → ℝ, 0 < ∑ j : Fin p, Real.exp (beta * (w j - y j)) := by
      intro w
      apply Finset.sum_pos
      · intro j _
        exact Real.exp_pos _
      · exact ⟨⟨0, hp⟩, Finset.mem_univ _⟩
    have hS : ContDiff ℝ 3 (fun w : Fin p → ℝ => ∑ j : Fin p, Real.exp (beta * (w j - y j))) := by
      fun_prop
    have hlog : ContDiff ℝ 3 (Real.log ∘ fun w : Fin p → ℝ => ∑ j : Fin p, Real.exp (beta * (w j - y j))) :=
      ContDiffOn.comp_contDiff Real.contDiffOn_log hS (fun w => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact ne_of_gt (hSpos w))
    exact hlog.const_smul beta⁻¹
  · intro w
    have hZpos : 0 < ∑ m : Fin p, Real.exp (beta * (w m - y m)) := by
      apply Finset.sum_pos
      · intro m _
        exact Real.exp_pos _
      · exact ⟨⟨0, hp⟩, Finset.mem_univ _⟩
    refine ⟨hZpos, ?_, ?_, ?_⟩
    · intro j
      exact div_pos (Real.exp_pos _) hZpos
    · rw [← Finset.sum_div]
      exact div_self (ne_of_gt hZpos)
    · intro u
      unfold Fbeta
      have hBdiff : ∀ m : Fin p, DifferentiableAt ℝ (fun w : Fin p → ℝ => beta * (w m - y m)) w := by
        intro m
        fun_prop
      have hSdiff : DifferentiableAt ℝ (fun w : Fin p → ℝ => ∑ m : Fin p, Real.exp (beta * (w m - y m))) w := by
        fun_prop
      have hBapply : ∀ m : Fin p, fderiv ℝ (fun w : Fin p → ℝ => beta * (w m - y m)) w u = beta * u m := by
        intro m
        have hgm : HasDerivAt (fun t : ℝ => beta * (t - y m)) beta (w m) := by
          have h := ((hasDerivAt_id (w m)).sub (hasDerivAt_const (w m) (y m))).const_mul beta
          simpa using h
        have hlin : HasFDerivAt (fun w : Fin p → ℝ => w m) (ContinuousLinearMap.proj m : (Fin p → ℝ) →L[ℝ] ℝ) w := by
          simpa [ContinuousLinearMap.proj_apply] using ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.proj m : (Fin p → ℝ) →L[ℝ] ℝ)
        have hb : HasFDerivAt (fun w : Fin p → ℝ => beta * (w m - y m)) (beta • (ContinuousLinearMap.proj m : (Fin p → ℝ) →L[ℝ] ℝ)) w :=
          HasDerivAt.comp_hasFDerivAt (f := fun w : Fin p → ℝ => w m) w hgm hlin
        rw [hb.fderiv, ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
      have hAdiff : ∀ m : Fin p, DifferentiableAt ℝ (fun w : Fin p → ℝ => Real.exp (beta * (w m - y m))) w := by
        intro m
        fun_prop
      have hSapply : fderiv ℝ (fun w : Fin p → ℝ => ∑ m : Fin p, Real.exp (beta * (w m - y m))) w u
          = ∑ m : Fin p, Real.exp (beta * (w m - y m)) * (beta * u m) := by
        have hfun : (fun w : Fin p → ℝ => ∑ m : Fin p, Real.exp (beta * (w m - y m)))
            = (∑ m : Fin p, fun w : Fin p → ℝ => Real.exp (beta * (w m - y m))) := by
          funext w
          rw [Finset.sum_apply]
        rw [hfun]
        rw [fderiv_sum (A := fun (m : Fin p) (w : Fin p → ℝ) => Real.exp (beta * (w m - y m))) (fun m _ => hAdiff m)]
        rw [ContinuousLinearMap.sum_apply]
        apply Finset.sum_congr rfl
        intro m _
        rw [fderiv_exp (hBdiff m), ContinuousLinearMap.smul_apply, hBapply m, smul_eq_mul]
      have hlogderiv : HasDerivAt Real.log ((∑ m : Fin p, Real.exp (beta * (w m - y m)))⁻¹) (∑ m : Fin p, Real.exp (beta * (w m - y m))) :=
        Real.hasDerivAt_log (ne_of_gt hZpos)
      have hcomp : HasFDerivAt (fun w : Fin p → ℝ => Real.log (∑ m : Fin p, Real.exp (beta * (w m - y m))))
          ((∑ m : Fin p, Real.exp (beta * (w m - y m)))⁻¹ • fderiv ℝ (fun w : Fin p → ℝ => ∑ m : Fin p, Real.exp (beta * (w m - y m))) w) w :=
        HasDerivAt.comp_hasFDerivAt (h₂ := Real.log) (f := fun w : Fin p → ℝ => ∑ m : Fin p, Real.exp (beta * (w m - y m))) w hlogderiv hSdiff.hasFDerivAt
      have hfull : HasFDerivAt (fun w : Fin p → ℝ => beta⁻¹ * Real.log (∑ m : Fin p, Real.exp (beta * (w m - y m))))
          (beta⁻¹ • ((∑ m : Fin p, Real.exp (beta * (w m - y m)))⁻¹ • fderiv ℝ (fun w : Fin p → ℝ => ∑ m : Fin p, Real.exp (beta * (w m - y m))) w)) w :=
        hcomp.const_mul beta⁻¹
      have hderiv : fderiv ℝ (fun w : Fin p → ℝ => beta⁻¹ * Real.log (∑ m : Fin p, Real.exp (beta * (w m - y m)))) w u
          = beta⁻¹ * ((∑ m : Fin p, Real.exp (beta * (w m - y m)))⁻¹ * (∑ m : Fin p, Real.exp (beta * (w m - y m)) * (beta * u m))) := by
        rw [hfull.fderiv, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, hSapply, smul_eq_mul, smul_eq_mul]
      have hsum1 : (∑ m : Fin p, Real.exp (beta * (w m - y m)) * (beta * u m))
          = beta * (∑ m : Fin p, Real.exp (beta * (w m - y m)) * u m) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        ring
      have hsum2 : (∑ j : Fin p, Real.exp (beta * (w j - y j)) / (∑ m : Fin p, Real.exp (beta * (w m - y m))) * u j)
          = (∑ m : Fin p, Real.exp (beta * (w m - y m)))⁻¹ * (∑ j : Fin p, Real.exp (beta * (w j - y j)) * u j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [div_eq_mul_inv]
        ring
      have hfin : beta⁻¹ * ((∑ m : Fin p, Real.exp (beta * (w m - y m)))⁻¹ * (beta * (∑ j : Fin p, Real.exp (beta * (w j - y j)) * u j)))
          = (∑ m : Fin p, Real.exp (beta * (w m - y m)))⁻¹ * (∑ j : Fin p, Real.exp (beta * (w j - y j)) * u j) := by
        have hb1 : beta⁻¹ * beta = 1 := inv_mul_cancel₀ (ne_of_gt hbeta)
        calc beta⁻¹ * ((∑ m : Fin p, Real.exp (beta * (w m - y m)))⁻¹ * (beta * (∑ j : Fin p, Real.exp (beta * (w j - y j)) * u j)))
            = (beta⁻¹ * beta) * ((∑ m : Fin p, Real.exp (beta * (w m - y m)))⁻¹ * (∑ j : Fin p, Real.exp (beta * (w j - y j)) * u j)) := by ring
          _ = (∑ m : Fin p, Real.exp (beta * (w m - y m)))⁻¹ * (∑ j : Fin p, Real.exp (beta * (w j - y j)) * u j) := by rw [hb1, one_mul]
      rw [hderiv, hsum1, hsum2]
      exact hfin
  /- @proof-region region.target-node.session.d9628ca20264c316 end -/

end Statlib.Imported
end

