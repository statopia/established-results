import Lean
import ProverJobs.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.Vocabulary
import ProverJobs.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.Base
import ProverJobs.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.ProvedNodes.Node_1495323798_70bc3ebb_5ac2e183
import ProverJobs.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.ProvedNodes.Node_283558168_72fffefb_dab35fce

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
theorem statopia_math_node_852268732_73371193 : ∀ (p : ℕ) (hp : 0 < p) (beta : ℝ)
    (hbeta : 0 < beta) (y w : Fin p → ℝ),
    (∀ u v : Fin p → ℝ,
        (fderiv ℝ (fderiv ℝ (Fbeta p beta y)) w u) v
          = beta * ((∑ j : Fin p,
                (Real.exp (beta * (w j - y j))
                    / (∑ m : Fin p, Real.exp (beta * (w m - y m)))) * u j * v j)
              - (∑ j : Fin p,
                (Real.exp (beta * (w j - y j))
                    / (∑ m : Fin p, Real.exp (beta * (w m - y m)))) * u j)
                * (∑ k : Fin p,
                (Real.exp (beta * (w k - y k))
                    / (∑ m : Fin p, Real.exp (beta * (w m - y m)))) * v k))) ∧
      (∀ j k l : Fin p,
        (iteratedFDeriv ℝ 3 (Fbeta p beta y) w)
            (fun i : Fin 3 => Pi.single (![j, k, l] i) (1 : ℝ))
          = beta ^ 2 *
              ((Real.exp (beta * (w j - y j))
                    / (∑ m : Fin p, Real.exp (beta * (w m - y m))))
                  * (if j = k then (1 : ℝ) else 0)
                  * (if j = l then (1 : ℝ) else 0)
                - (Real.exp (beta * (w j - y j))
                    / (∑ m : Fin p, Real.exp (beta * (w m - y m))))
                  * (Real.exp (beta * (w l - y l))
                    / (∑ m : Fin p, Real.exp (beta * (w m - y m))))
                  * (if j = k then (1 : ℝ) else 0)
                - (Real.exp (beta * (w j - y j))
                    / (∑ m : Fin p, Real.exp (beta * (w m - y m))))
                  * (Real.exp (beta * (w k - y k))
                    / (∑ m : Fin p, Real.exp (beta * (w m - y m))))
                  * (if j = l then (1 : ℝ) else 0)
                - (Real.exp (beta * (w j - y j))
                    / (∑ m : Fin p, Real.exp (beta * (w m - y m))))
                  * (Real.exp (beta * (w k - y k))
                    / (∑ m : Fin p, Real.exp (beta * (w m - y m))))
                  * (if k = l then (1 : ℝ) else 0)
                + 2 * (Real.exp (beta * (w j - y j))
                    / (∑ m : Fin p, Real.exp (beta * (w m - y m))))
                  * (Real.exp (beta * (w k - y k))
                    / (∑ m : Fin p, Real.exp (beta * (w m - y m))))
                  * (Real.exp (beta * (w l - y l))
                    / (∑ m : Fin p, Real.exp (beta * (w m - y m)))))) := by
  /- @proof-region region.target-node.session.e5599c62df107aae begin -/
  intro p hp beta hbeta y w
  obtain ⟨hcd, hrest⟩ := statopia_math_node_283558168_72fffefb p hp beta hbeta y
  set S : (Fin p → ℝ) → ℝ := fun w => ∑ m : Fin p, Real.exp (beta * (w m - y m)) with hS
  set Ee : Fin p → (Fin p → ℝ) → ℝ := fun j w => Real.exp (beta * (w j - y j)) with hEe
  set P : Fin p → (Fin p → ℝ) → ℝ := fun j w => Ee j w / S w with hP
  have hSpos : ∀ w, 0 < S w := by
    intro w
    have h := (hrest w).1
    simpa only [hS] using h
  have hPpos : ∀ w j, 0 < P j w := by
    intro w j
    have h := (hrest w).2.1 j
    simpa only [hP, hEe, hS] using h
  have hsum1 : ∀ w, (∑ j, P j w) = 1 := by
    intro w
    have h := (hrest w).2.2.1
    simpa only [hP, hEe, hS] using h
  have hd : ∀ w' u, fderiv ℝ (Fbeta p beta y) w' u = ∑ j, P j w' * u j := by
    intro w' u
    have h := (hrest w').2.2.2 u
    simpa only [hP, hEe, hS] using h
  set pj : Fin p → ((Fin p → ℝ) →L[ℝ] ℝ) :=
    fun j => (ContinuousLinearMap.proj j : (Fin p → ℝ) →L[ℝ] ℝ) with hpj
  have hpjapp : ∀ (j : Fin p) (a : Fin p → ℝ), pj j a = a j := by
    intro j a
    have h : (ContinuousLinearMap.proj j : (Fin p → ℝ) →L[ℝ] ℝ) a = a j :=
      ContinuousLinearMap.proj_apply j a
    simpa [hpj] using h
  have hElin : ∀ (j : Fin p), HasFDerivAt (fun z : Fin p → ℝ => z j - y j) (pj j) w := by
    intro j
    have h0 : HasFDerivAt (fun z : Fin p → ℝ => (ContinuousLinearMap.proj j : (Fin p → ℝ) →L[ℝ] ℝ) z)
        (ContinuousLinearMap.proj j : (Fin p → ℝ) →L[ℝ] ℝ) w :=
      (ContinuousLinearMap.proj j : (Fin p → ℝ) →L[ℝ] ℝ).hasFDerivAt
    have h1 : HasFDerivAt (fun z : Fin p → ℝ => z j) (pj j) w := by
      simpa [hpj] using h0
    exact h1.sub_const (y j)
  have hEderiv : ∀ (j : Fin p), HasFDerivAt (fun z : Fin p → ℝ => Ee j z) ((beta * Ee j w) • pj j) w := by
    intro j
    have h2 : HasFDerivAt (fun z : Fin p → ℝ => beta * (z j - y j)) (beta • pj j) w :=
      (hElin j).const_mul beta
    have hexp : HasFDerivAt Real.exp
        (ContinuousLinearMap.toSpanSingleton ℝ (Real.exp (beta * (w j - y j)))) (beta * (w j - y j)) :=
      (Real.hasDerivAt_exp (beta * (w j - y j))).hasFDerivAt
    have h3 : HasFDerivAt (fun z : Fin p → ℝ => Real.exp (beta * (z j - y j)))
        ((ContinuousLinearMap.toSpanSingleton ℝ (Real.exp (beta * (w j - y j)))).comp (beta • pj j)) w :=
      HasFDerivAt.comp (x := w) (g := Real.exp) hexp h2
    have h4 : (ContinuousLinearMap.toSpanSingleton ℝ (Real.exp (beta * (w j - y j)))).comp (beta • pj j)
        = (beta * Ee j w) • pj j := by
      ext z
      simp [hpjapp]
      ring
    rw [h4] at h3
    simpa [hEe] using h3
  have hSderiv : HasFDerivAt (fun z : Fin p → ℝ => S z) (∑ k, (beta * Ee k w) • pj k) w := by
    have h : HasFDerivAt (∑ k, fun z : Fin p → ℝ => Ee k z) (∑ k, (beta * Ee k w) • pj k) w := by
      have hsum := HasFDerivAt.sum (u := (Finset.univ : Finset (Fin p)))
        (fun k (_ : k ∈ Finset.univ) => hEderiv k)
      simpa using hsum
    have hfun : (∑ k, fun z : Fin p → ℝ => Ee k z) = fun z => ∑ k, Ee k z := by
      funext z
      simp [Finset.sum_apply]
    rw [hfun] at h
    simpa [hS] using h
  have hPfderiv : ∀ j : Fin p,
      HasFDerivAt (fun z : Fin p → ℝ => P j z) ((beta * P j w) • (pj j - ∑ k, P k w • pj k)) w := by
    intro j
    have hinv : HasFDerivAt (fun z : Fin p → ℝ => (S z)⁻¹)
        ((ContinuousLinearMap.toSpanSingleton ℝ (-(S w ^ 2)⁻¹)).comp (∑ k, (beta * Ee k w) • pj k)) w :=
      HasFDerivAt.comp (x := w) (g := fun t : ℝ => t⁻¹)
        (hasFDerivAt_inv (ne_of_gt (hSpos w))) hSderiv
    have hraw : HasFDerivAt (fun z : Fin p → ℝ => Ee j z • (S z)⁻¹)
        (Ee j w • ((ContinuousLinearMap.toSpanSingleton ℝ (-(S w ^ 2)⁻¹)).comp (∑ k, (beta * Ee k w) • pj k))
          + ((beta * Ee j w) • pj j).smulRight ((S w)⁻¹)) w :=
      HasFDerivAt.smul (hEderiv j) hinv
    have hfun : (fun z : Fin p → ℝ => Ee j z • (S z)⁻¹) = fun z => P j z := by
      funext z
      simp only [hP, smul_eq_mul, div_eq_mul_inv]
    rw [hfun] at hraw
    have hclm : Ee j w • ((ContinuousLinearMap.toSpanSingleton ℝ (-(S w ^ 2)⁻¹)).comp (∑ k, (beta * Ee k w) • pj k))
          + ((beta * Ee j w) • pj j).smulRight ((S w)⁻¹)
        = (beta * P j w) • (pj j - ∑ k, P k w • pj k) := by
      ext z
      have h1 : (∑ k : Fin p, beta * Ee k w * z k) = beta * (∑ k : Fin p, Ee k w * z k) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      have h2 : (∑ k : Fin p, P k w * z k) = (∑ k : Fin p, Ee k w * z k) / S w := by
        simp only [hP]
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.toSpanSingleton_apply, hpjapp, smul_eq_mul]
      rw [h1, h2, hP]
      have hSne : S w ≠ 0 := ne_of_gt (hSpos w)
      field_simp
      ring
    rw [hclm] at hraw
    exact hraw
  have hmfderiv : HasFDerivAt (fun z : Fin p → ℝ => ∑ j, P j z • pj j)
      (∑ j, ((beta * P j w) • (pj j - ∑ k, P k w • pj k)).smulRight (pj j)) w := by
    have hterm : ∀ j ∈ (Finset.univ : Finset (Fin p)),
        HasFDerivAt (fun z : Fin p → ℝ => P j z • pj j)
          (((beta * P j w) • (pj j - ∑ k, P k w • pj k)).smulRight (pj j)) w :=
      fun j _ => (hPfderiv j).smul_const (pj j)
    have hsum := HasFDerivAt.sum hterm
    have hfun : (∑ j, fun z : Fin p → ℝ => P j z • pj j) = fun z => ∑ j, P j z • pj j := by
      funext z
      simp [Finset.sum_apply]
    rw [hfun] at hsum
    simpa using hsum
  have hmfun : fderiv ℝ (Fbeta p beta y) = fun z => ∑ j, P j z • pj j := by
    funext z
    ext a
    rw [hd z a]
    simp [hpjapp, smul_eq_mul]
  have hfderiv2 : fderiv ℝ (fderiv ℝ (Fbeta p beta y)) w
      = ∑ j, ((beta * P j w) • (pj j - ∑ k, P k w • pj k)).smulRight (pj j) := by
    have h := hmfderiv
    rw [← hmfun] at h
    exact h.fderiv
  have hB : ∀ u v : Fin p → ℝ,
      (fderiv ℝ (fderiv ℝ (Fbeta p beta y)) w u) v
        = beta * ((∑ j : Fin p,
              (Real.exp (beta * (w j - y j))
                  / (∑ m : Fin p, Real.exp (beta * (w m - y m)))) * u j * v j)
            - (∑ j : Fin p,
              (Real.exp (beta * (w j - y j))
                  / (∑ m : Fin p, Real.exp (beta * (w m - y m)))) * u j)
              * (∑ k : Fin p,
              (Real.exp (beta * (w k - y k))
                  / (∑ m : Fin p, Real.exp (beta * (w m - y m)))) * v k)) := by
    intro u v
    have hval : (fderiv ℝ (fderiv ℝ (Fbeta p beta y)) w u) v
        = ∑ j, (beta * P j w * (u j - ∑ k, P k w * u k)) * v j := by
      rw [hfderiv2]
      simp [hpjapp, smul_eq_mul]
    rw [hval]
    have key : (∑ j : Fin p, (beta * P j w * (u j - ∑ k, P k w * u k)) * v j)
        = beta * (∑ j : Fin p, P j w * u j * v j)
          - beta * (∑ j : Fin p, P j w * u j) * (∑ j : Fin p, P j w * v j) := by
      have step1 : (∑ j : Fin p, (beta * P j w * (u j - ∑ k, P k w * u k)) * v j)
          = ∑ j : Fin p,
              (beta * (P j w * u j * v j) - (beta * (∑ k : Fin p, P k w * u k)) * (P j w * v j)) :=
        Finset.sum_congr rfl (fun j _ => by ring)
      rw [step1, Finset.sum_sub_distrib]
      simp only [Finset.mul_sum]
    rw [key]
    simp only [hP, hEe, hS]
    ring
  constructor
  · intro u v
    exact hB u v
  · intro j k l
    exact statopia_math_node_1495323798_70bc3ebb p hp beta hbeta y w hB j k l
  /- @proof-region region.target-node.session.e5599c62df107aae end -/

end Statlib.Imported
end

