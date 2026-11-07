import Lean
import ProverJobs.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.Vocabulary
import ProverJobs.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.Base
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
theorem statopia_math_node_1495323798_70bc3ebb : ∀ (p : ℕ) (hp : 0 < p) (beta : ℝ) (hbeta : 0 < beta)
    (y : Fin p → ℝ) (w : Fin p → ℝ)
    (hB : ∀ u v : Fin p → ℝ,
      (fderiv ℝ (fderiv ℝ (Fbeta p beta y)) w u) v
        = beta * ((∑ j : Fin p,
              (Real.exp (beta * (w j - y j)) /
                (∑ m : Fin p, Real.exp (beta * (w m - y m)))) * u j * v j)
            - (∑ j : Fin p,
              (Real.exp (beta * (w j - y j)) /
                (∑ m : Fin p, Real.exp (beta * (w m - y m)))) * u j)
              * (∑ k : Fin p,
                (Real.exp (beta * (w k - y k)) /
                  (∑ m : Fin p, Real.exp (beta * (w m - y m)))) * v k)))
    (j k l : Fin p),
    (iteratedFDeriv ℝ 3 (Fbeta p beta y) w) (fun i : Fin 3 => Pi.single (![j, k, l] i) (1 : ℝ))
      = beta ^ 2 *
          ((Real.exp (beta * (w j - y j)) / (∑ m : Fin p, Real.exp (beta * (w m - y m))))
              * (if j = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
            - (Real.exp (beta * (w j - y j)) / (∑ m : Fin p, Real.exp (beta * (w m - y m))))
              * (Real.exp (beta * (w l - y l)) / (∑ m : Fin p, Real.exp (beta * (w m - y m))))
              * (if j = k then (1 : ℝ) else 0)
            - (Real.exp (beta * (w j - y j)) / (∑ m : Fin p, Real.exp (beta * (w m - y m))))
              * (Real.exp (beta * (w k - y k)) / (∑ m : Fin p, Real.exp (beta * (w m - y m))))
              * (if j = l then (1 : ℝ) else 0)
            - (Real.exp (beta * (w j - y j)) / (∑ m : Fin p, Real.exp (beta * (w m - y m))))
              * (Real.exp (beta * (w k - y k)) / (∑ m : Fin p, Real.exp (beta * (w m - y m))))
              * (if k = l then (1 : ℝ) else 0)
            + 2 * (Real.exp (beta * (w j - y j)) / (∑ m : Fin p, Real.exp (beta * (w m - y m))))
              * (Real.exp (beta * (w k - y k)) / (∑ m : Fin p, Real.exp (beta * (w m - y m))))
              * (Real.exp (beta * (w l - y l)) / (∑ m : Fin p, Real.exp (beta * (w m - y m))))) := by
  /- @proof-region region.target-node.session.b8526d7db68fd88f begin -/
  intro p hp beta hbeta y w hB j k l
  obtain ⟨hCont, hprops⟩ := statopia_math_node_283558168_72fffefb p hp beta hbeta y
  set P : Fin p → (Fin p → ℝ) → ℝ :=
    fun i z => Real.exp (beta * (z i - y i)) / (∑ m : Fin p, Real.exp (beta * (z m - y m))) with hP
  have hgrad : ∀ (z u : Fin p → ℝ), fderiv ℝ (Fbeta p beta y) z u = ∑ i, P i z * u i := by
    intro z u
    simpa only [hP] using (hprops z).2.2.2 u
  have hZi : ∀ z : Fin p → ℝ, (0:ℝ) < ∑ m : Fin p, Real.exp (beta * (z m - y m)) :=
    fun z => (hprops z).1
  have hN : ∀ (i : Fin p) (z : Fin p → ℝ),
      HasFDerivAt (fun z' : Fin p → ℝ => Real.exp (beta * (z' i - y i)))
        ((Real.exp (beta * (z i - y i)) * beta) • (ContinuousLinearMap.proj i : (Fin p → ℝ) →L[ℝ] ℝ)) z := by
    intro i z
    have h1 : HasFDerivAt (fun z' : Fin p → ℝ => z' i - y i)
        (ContinuousLinearMap.proj i : (Fin p → ℝ) →L[ℝ] ℝ) z := by
      have h0 := (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.proj i : (Fin p → ℝ) →L[ℝ] ℝ) (x := z)).sub_const (y i)
      simpa only [ContinuousLinearMap.proj_apply] using h0
    have hg : HasFDerivAt (fun z' : Fin p → ℝ => beta * (z' i - y i))
        (beta • (ContinuousLinearMap.proj i : (Fin p → ℝ) →L[ℝ] ℝ)) z := h1.const_mul beta
    have hc := (Real.hasDerivAt_exp (beta * (z i - y i))).comp_hasFDerivAt z hg
    simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using hc
  have hZ : ∀ z : Fin p → ℝ,
      HasFDerivAt (fun z' : Fin p → ℝ => ∑ m : Fin p, Real.exp (beta * (z' m - y m)))
        (∑ m : Fin p, (Real.exp (beta * (z m - y m)) * beta) • (ContinuousLinearMap.proj m : (Fin p → ℝ) →L[ℝ] ℝ)) z := by
    intro z
    have h := HasFDerivAt.sum (u := Finset.univ) (fun m _ => hN m z)
    exact h.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq (funext (fun z' => by
      simp only [Finset.sum_apply])))
  have hEZ : ∀ (i : Fin p) (z : Fin p → ℝ),
      Real.exp (beta * (z i - y i)) = P i z * (∑ m : Fin p, Real.exp (beta * (z m - y m))) := by
    intro i z
    have hZne : (∑ m : Fin p, Real.exp (beta * (z m - y m))) ≠ 0 := ne_of_gt (hZi z)
    simp only [hP]
    field_simp
  have hsumEZ : ∀ (z v : Fin p → ℝ),
      (∑ m : Fin p, Real.exp (beta * (z m - y m)) * v m)
        = (∑ m : Fin p, Real.exp (beta * (z m - y m))) * (∑ m : Fin p, P m z * v m) := by
    intro z v
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [hEZ m z]
    ring
  have hsum2 : ∀ (z v : Fin p → ℝ) (b : ℝ),
      (∑ m : Fin p, Real.exp (beta * (z m - y m)) * b * v m)
        = b * ((∑ m : Fin p, Real.exp (beta * (z m - y m))) * (∑ m : Fin p, P m z * v m)) := by
    intro z v b
    rw [show (∑ m : Fin p, Real.exp (beta * (z m - y m)) * b * v m)
        = ∑ m : Fin p, b * (Real.exp (beta * (z m - y m)) * v m) from by
      apply Finset.sum_congr rfl
      intro m _
      ring]
    rw [← Finset.mul_sum, hsumEZ z v]
  have hPi : ∀ (i : Fin p) (z v : Fin p → ℝ),
      fderiv ℝ (fun z' : Fin p → ℝ => P i z') z v
        = beta * P i z * (v i - ∑ m : Fin p, P m z * v m) := by
    intro i z v
    have hZne : (∑ m : Fin p, Real.exp (beta * (z m - y m))) ≠ 0 := ne_of_gt (hZi z)
    have hmain := (hN i z).mul
      ((hasDerivAt_inv (x := (∑ m : Fin p, Real.exp (beta * (z m - y m)))) hZne).comp_hasFDerivAt z (hZ z))
    have hfun : (fun z' : Fin p → ℝ => P i z') =
        ((fun z' => Real.exp (beta * (z' i - y i))) *
          ((fun y => y⁻¹) ∘ fun z' => ∑ m : Fin p, Real.exp (beta * (z' m - y m)))) := by
      funext z'
      simp only [hP, div_eq_mul_inv, Pi.mul_apply, Function.comp_apply]
    rw [hfun, hmain.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
      Function.comp_apply]
    rw [hsum2 z v beta, hEZ i z]
    field_simp
    try ring
  have hA2 : ContDiff ℝ (2 : WithTop ℕ∞) (fderiv ℝ (Fbeta p beta y)) :=
    hCont.fderiv_right (m := (2 : WithTop ℕ∞)) (by norm_num)
  set m3 : Fin 3 → (Fin p → ℝ) := fun i => Pi.single (![j, k, l] i) 1 with hm3
  have hfun_eq : (fun z : Fin p → ℝ => fderiv ℝ (Fbeta p beta y) z (Pi.single l (1 : ℝ))) = P l := by
    funext z
    have hsingle : (∑ i : Fin p, P i z * (Pi.single l (1 : ℝ) : Fin p → ℝ) i) = P l z := by
      rw [Finset.sum_eq_single (f := fun i => P i z * (Pi.single l (1 : ℝ) : Fin p → ℝ) i) l
        (fun i _ hil => by
          show P i z * (Pi.single l (1 : ℝ) : Fin p → ℝ) i = 0
          rw [Pi.single_eq_of_ne hil, mul_zero])
        (fun hl => absurd (Finset.mem_univ l) hl)]
      rw [Pi.single_eq_same, mul_one]
    rw [hgrad z (Pi.single l (1 : ℝ)), hsingle]
  have hm_last : m3 (Fin.last 2) = Pi.single l 1 := by
    rw [hm3]; simp
  have hm0 : (Fin.init m3) 0 = Pi.single j 1 := by
    show m3 0 = Pi.single j 1
    rw [hm3]; simp
  have hm1 : (Fin.init m3) 1 = Pi.single k 1 := by
    show m3 1 = Pi.single k 1
    rw [hm3]; simp
  have hRed : (iteratedFDeriv ℝ 3 (Fbeta p beta y) w) m3
      = ((fderiv ℝ (fderiv ℝ (P l)) w) (Pi.single j 1)) (Pi.single k 1) := by
    have hC := iteratedFDeriv_clm_apply_const_apply (n := (2 : WithTop ℕ∞))
      (c := fderiv ℝ (Fbeta p beta y)) hA2 (i := 2) (by norm_num)
      (x := w) (u := Pi.single l (1 : ℝ)) (m := Fin.init m3)
    rw [iteratedFDeriv_succ_apply_right, hm_last,
      show (fun z : Fin p → ℝ => fderiv ℝ (Fbeta p beta y) z) = fderiv ℝ (Fbeta p beta y) from funext (fun z => rfl),
      ← hC, hfun_eq]
    rw [iteratedFDeriv_two_apply]
    rw [hm0, hm1]
  set cl : (Fin p → ℝ) → ℝ :=
    fun z => fderiv ℝ (Fbeta p beta y) z (Pi.single l (1 : ℝ)) with hcl
  have hcl_eq : cl = P l := by
    rw [hcl]; exact hfun_eq
  have hPl_cont : ContDiff ℝ (2 : WithTop ℕ∞) cl := by
    rw [hcl]
    exact hA2.clm_apply contDiff_const
  have hContHp : ContDiff ℝ (1 : WithTop ℕ∞) (fderiv ℝ cl) :=
    hPl_cont.fderiv_right (m := (1 : WithTop ℕ∞)) (by norm_num)
  have hDP : ∀ i : Fin p, HasFDerivAt (fun z => P i z) (fderiv ℝ (fun z => P i z) w) w := by
    intro i
    have hZne : (∑ m : Fin p, Real.exp (beta * (w m - y m))) ≠ 0 := ne_of_gt (hZi w)
    have hmain := (hN i w).mul
      ((hasDerivAt_inv (x := (∑ m : Fin p, Real.exp (beta * (w m - y m)))) hZne).comp_hasFDerivAt w (hZ w))
    have hfun : (fun z' : Fin p → ℝ => P i z') =
        ((fun z' => Real.exp (beta * (z' i - y i))) *
          ((fun y => y⁻¹) ∘ fun z' => ∑ m : Fin p, Real.exp (beta * (z' m - y m)))) := by
      funext z'
      simp only [hP, div_eq_mul_inv, Pi.mul_apply, Function.comp_apply]
    rw [← hfun] at hmain
    rw [hmain.fderiv]
    exact hmain
  have hsingle_of : ∀ (i : Fin p) (z : Fin p → ℝ),
      (∑ m : Fin p, P m z * (Pi.single i (1 : ℝ) : Fin p → ℝ) m) = P i z := by
    intro i z
    rw [Finset.sum_eq_single (f := fun m => P m z * (Pi.single i (1 : ℝ) : Fin p → ℝ) m) i
      (fun m _ hmi => by
        show P m z * (Pi.single i (1 : ℝ) : Fin p → ℝ) m = 0
        rw [Pi.single_eq_of_ne hmi, mul_zero])
      (fun hi => absurd (Finset.mem_univ i) hi)]
    rw [Pi.single_eq_same, mul_one]
  have hQeq : (fun y : Fin p → ℝ => (fderiv ℝ cl y) (Pi.single k (1 : ℝ)))
      = fun z => beta * (P l z * (((Pi.single k (1 : ℝ) : Fin p → ℝ)) l - P k z)) := by
    funext z
    rw [hcl_eq]
    rw [show P l = (fun z' : Fin p → ℝ => P l z') from (funext (fun z' => rfl)).symm]
    rw [hPi l z (Pi.single k (1 : ℝ)), hsingle_of k z]
    ring
  have hclm : fderiv ℝ (fun y : Fin p → ℝ => (fderiv ℝ cl y) (Pi.single k (1 : ℝ))) w (Pi.single j (1 : ℝ))
      = ((fderiv ℝ (fderiv ℝ cl) w) (Pi.single j (1 : ℝ))) (Pi.single k (1 : ℝ)) := by
    have h := iteratedFDeriv_clm_apply_const_apply (n := (1 : WithTop ℕ∞))
      (c := fderiv ℝ cl) hContHp (i := 1) (by norm_num)
      (x := w) (u := Pi.single k (1 : ℝ)) (m := (fun _ : Fin 1 => Pi.single j (1 : ℝ)))
    simpa only [iteratedFDeriv_one_apply] using h
  rw [hRed, ← hcl_eq, ← hclm, hQeq]
  have hQfun : HasFDerivAt
      (fun z : Fin p → ℝ => beta * (P l z * (((Pi.single k (1 : ℝ) : Fin p → ℝ)) l - P k z)))
      (beta • ((P l w) • ((0 : (Fin p → ℝ) →L[ℝ] ℝ) - fderiv ℝ (fun z => P k z) w) +
        (((Pi.single k (1 : ℝ) : Fin p → ℝ)) l - P k w) • (fderiv ℝ (fun z => P l z) w))) w := by
    have hb : HasFDerivAt (fun z : Fin p → ℝ => ((Pi.single k (1 : ℝ) : Fin p → ℝ)) l - P k z)
        ((0 : (Fin p → ℝ) →L[ℝ] ℝ) - fderiv ℝ (fun z => P k z) w) w :=
      (hasFDerivAt_const (((Pi.single k (1 : ℝ) : Fin p → ℝ)) l) w).sub (hDP k)
    have hp : HasFDerivAt (fun z : Fin p → ℝ => P l z * (((Pi.single k (1 : ℝ) : Fin p → ℝ)) l - P k z))
        ((P l w) • ((0 : (Fin p → ℝ) →L[ℝ] ℝ) - fderiv ℝ (fun z => P k z) w) +
          (((Pi.single k (1 : ℝ) : Fin p → ℝ)) l - P k w) • (fderiv ℝ (fun z => P l z) w)) w :=
      (hDP l).mul hb
    exact hp.const_mul beta
  rw [hQfun.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.zero_apply, smul_eq_mul]
  rw [hPi l w (Pi.single j (1 : ℝ)), hPi k w (Pi.single j (1 : ℝ)), hsingle_of j w,
    Pi.single_apply, Pi.single_apply, Pi.single_apply]
  simp only [hP]
  have hZne : (∑ m : Fin p, Real.exp (beta * (w m - y m))) ≠ 0 := ne_of_gt (hZi w)
  by_cases hjk : j = k
  · by_cases hjl : j = l
    · by_cases hkl : k = l
      · simp [hjk, hjl, hkl]
        try (field_simp; ring)
      · exact absurd (hjk.symm.trans hjl) hkl
    · by_cases hkl : k = l
      · exact absurd (hjk.trans hkl) hjl
      · have hlk : ¬ (l = k) := fun h => hkl h.symm
        simp [hjk, hjl, hkl, hlk]
        try (field_simp; ring)
  · by_cases hjl : j = l
    · by_cases hkl : k = l
      · exact absurd (hjl.trans hkl.symm) hjk
      · have hkj : ¬ (k = j) := fun h => hjk h.symm
        have hlk : ¬ (l = k) := fun h => hkl h.symm
        simp [hjk, hjl, hkl, hkj, hlk]
        try (field_simp; ring)
    · by_cases hkl : k = l
      · have hkj : ¬ (k = j) := fun h => hjk h.symm
        have hlj : ¬ (l = j) := fun h => hjl h.symm
        simp [hjk, hjl, hkl, hkj, hlj]
        try (field_simp; ring)
      · have hkj : ¬ (k = j) := fun h => hjk h.symm
        have hlj : ¬ (l = j) := fun h => hjl h.symm
        have hlk : ¬ (l = k) := fun h => hkl h.symm
        simp [hjk, hjl, hkl, hkj, hlj, hlk]
        try (field_simp; ring)
  /- @proof-region region.target-node.session.b8526d7db68fd88f end -/

end Statlib.Imported
end

