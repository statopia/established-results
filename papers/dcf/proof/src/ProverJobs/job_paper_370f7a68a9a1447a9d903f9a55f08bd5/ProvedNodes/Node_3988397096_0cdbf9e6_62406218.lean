import Lean
import ProverJobs.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.Vocabulary
import ProverJobs.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.Base
import ProverJobs.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.ProvedNodes.Node_1960475459_46432c8a_a4a43fe7
import ProverJobs.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.ProvedNodes.Node_283558168_72fffefb_dab35fce
import ProverJobs.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.ProvedNodes.Node_852268732_73371193_95582096

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
theorem statopia_math_node_3988397096_0cdbf9e6 : ∀ (p : ℕ) (hp : 0 < p) (beta : ℝ) (hbeta : 0 < beta)
    (phi : ℝ) (hphi : 0 < phi) (y : Fin p → ℝ)
    (phi0 : ℝ → ℝ) (hphi0 : ContDiff ℝ 3 phi0),
    ContDiff ℝ 3 (fun w : Fin p → ℝ => phi0 (phi * Fbeta p beta y w)) ∧
      ∀ (w : Fin p → ℝ) (j k l : Fin p),
        let Z : ℝ := ∑ m : Fin p, Real.exp (beta * (w m - y m))
        (iteratedFDeriv ℝ 3 (fun v : Fin p → ℝ => phi0 (phi * Fbeta p beta y v)) w)
            (fun i : Fin 3 => Pi.single (![j, k, l] i) (1 : ℝ))
          = iteratedDeriv 3 (fun t : ℝ => phi0 (phi * t)) (Fbeta p beta y w)
              * (Real.exp (beta * (w j - y j)) / Z)
              * (Real.exp (beta * (w k - y k)) / Z)
              * (Real.exp (beta * (w l - y l)) / Z)
            + iteratedDeriv 2 (fun t : ℝ => phi0 (phi * t)) (Fbeta p beta y w) * beta
              * ((Real.exp (beta * (w j - y j)) / Z) * (Real.exp (beta * (w k - y k)) / Z)
                    * ((if j = l then (1 : ℝ) else 0) - (Real.exp (beta * (w l - y l)) / Z))
                 + (Real.exp (beta * (w j - y j)) / Z) * (Real.exp (beta * (w k - y k)) / Z)
                    * ((if k = l then (1 : ℝ) else 0) - (Real.exp (beta * (w l - y l)) / Z))
                 + (Real.exp (beta * (w l - y l)) / Z)
                    * ((Real.exp (beta * (w j - y j)) / Z) * (if j = k then (1 : ℝ) else 0)
                        - (Real.exp (beta * (w j - y j)) / Z) * (Real.exp (beta * (w k - y k)) / Z)))
            + deriv (fun t : ℝ => phi0 (phi * t)) (Fbeta p beta y w) * beta ^ 2
              * ((Real.exp (beta * (w j - y j)) / Z) * (if j = k then (1 : ℝ) else 0)
                    * (if j = l then (1 : ℝ) else 0)
                 - (Real.exp (beta * (w j - y j)) / Z) * (Real.exp (beta * (w l - y l)) / Z)
                    * (if j = k then (1 : ℝ) else 0)
                 - (Real.exp (beta * (w j - y j)) / Z) * (Real.exp (beta * (w k - y k)) / Z)
                    * (if j = l then (1 : ℝ) else 0)
                 - (Real.exp (beta * (w j - y j)) / Z) * (Real.exp (beta * (w k - y k)) / Z)
                    * (if k = l then (1 : ℝ) else 0)
                 + 2 * (Real.exp (beta * (w j - y j)) / Z) * (Real.exp (beta * (w k - y k)) / Z)
                    * (Real.exp (beta * (w l - y l)) / Z)) := by
  /- @proof-region region.target-node.session.7ce3fa5ab9a1985e begin -/
  intro p hp beta hbeta phi hphi y phi0 hphi0
  have hlin : ContDiff ℝ 3 (fun t : ℝ => phi * t) := by
    simpa [smul_eq_mul] using (phi • (1 : ℝ →L[ℝ] ℝ)).contDiff
  have hg : ContDiff ℝ 3 (fun t : ℝ => phi0 (phi * t)) := hphi0.comp hlin
  have hFs : ContDiff ℝ 3 (Fbeta p beta y) :=
    (statopia_math_node_283558168_72fffefb p hp beta hbeta y).1
  refine ⟨hg.comp hFs, ?_⟩
  intro w j k l
  dsimp only
  let g : ℝ → ℝ := fun t => phi0 (phi * t)
  let F : (Fin p → ℝ) → ℝ := Fbeta p beta y
  let K : (Fin p → ℝ) → ℝ := fun v => phi0 (phi * Fbeta p beta y v)
  obtain ⟨hZpos, hpospi, hsumpi, hfderiv⟩ :=
    (statopia_math_node_283558168_72fffefb p hp beta hbeta y).2 w
  obtain ⟨hBf, hCf⟩ := statopia_math_node_852268732_73371193 p hp beta hbeta y w
  have e3 : ((2 : WithTop ℕ∞) + 1) = 3 := by norm_num
  have e2 : ((1 : WithTop ℕ∞) + 1) = 2 := by norm_num
  have e1 : ((0 : WithTop ℕ∞) + 1) = 1 := by norm_num
  have hgiff := (contDiff_succ_iff_deriv (f₂ := g)).mp (e3 ▸ hg)
  have hgiff2 := (contDiff_succ_iff_deriv (f₂ := deriv g)).mp (e2 ▸ hgiff.2.2)
  have hgiff3 := (contDiff_succ_iff_deriv (f₂ := deriv (deriv g))).mp (e1 ▸ hgiff2.2.2)
  have hgd0 : Differentiable ℝ g := hgiff.1
  have hgd1 : Differentiable ℝ (deriv g) := hgiff2.1
  have hgd2 : Differentiable ℝ (deriv (deriv g)) := hgiff3.1
  have hderiv0 : ∀ s : ℝ, HasDerivAt g (deriv g s) s := by
    intro s
    have h2 : HasDerivAt g ((fderiv ℝ g s) 1) s :=
      hasFDerivAt_iff_hasDerivAt.mp (hgd0 s).hasFDerivAt
    exact h2.deriv ▸ h2
  have hderiv1 : ∀ s : ℝ, HasDerivAt (deriv g) (deriv (deriv g) s) s := by
    intro s
    have h2 : HasDerivAt (deriv g) ((fderiv ℝ (deriv g) s) 1) s :=
      hasFDerivAt_iff_hasDerivAt.mp (hgd1 s).hasFDerivAt
    exact h2.deriv ▸ h2
  have hderiv2 : ∀ s : ℝ, HasDerivAt (deriv (deriv g)) (deriv (deriv (deriv g)) s) s := by
    intro s
    have h2 : HasDerivAt (deriv (deriv g)) ((fderiv ℝ (deriv (deriv g)) s) 1) s :=
      hasFDerivAt_iff_hasDerivAt.mp (hgd2 s).hasFDerivAt
    exact h2.deriv ▸ h2
  have hFd : Differentiable ℝ F := hFs.differentiable (by norm_num)
  have hFc2 : ContDiff ℝ 2 (fderiv ℝ F) := hFs.fderiv_right (by norm_num)
  have hFd2 : Differentiable ℝ (fderiv ℝ F) := hFc2.differentiable (by norm_num)
  have hFc1 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ F)) := hFc2.fderiv_right (by norm_num)
  have hFd3 : Differentiable ℝ (fderiv ℝ (fderiv ℝ F)) := hFc1.differentiable (by norm_num)
  have hid1 : iteratedDeriv 1 g = deriv g := by
    simpa using (iteratedDeriv_succ' (n := 0) (f := g))
  have hid2 : iteratedDeriv 2 g = deriv (deriv g) := by
    rw [iteratedDeriv_succ (n := 1), hid1]
  have hid3 : iteratedDeriv 3 g = deriv (deriv (deriv g)) := by
    rw [iteratedDeriv_succ (n := 2), hid2]
  have hIderiv1 : ∀ s : ℝ, HasDerivAt (deriv g) (iteratedDeriv 2 g s) s := by
    intro s
    simpa [hid2] using hderiv1 s
  have hIderiv2 : ∀ s : ℝ, HasDerivAt (iteratedDeriv 2 g) (iteratedDeriv 3 g s) s := by
    intro s
    simpa [hid2, hid3] using hderiv2 s
  have hK1 : ∀ x : Fin p → ℝ, HasFDerivAt K ((deriv g (F x)) • fderiv ℝ F x) x := by
    intro x
    exact (hderiv0 (F x)).comp_hasFDerivAt x ((hFd x).hasFDerivAt)
  have hslot : ∀ (f : (Fin p → ℝ) → ℝ) (x : Fin p → ℝ) (mm : Fin 3 → Fin p → ℝ),
      (iteratedFDeriv ℝ 3 f x) mm
        = (((fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x) (mm 0)) (mm 1)) (mm 2) := by
    intro f x mm
    rw [iteratedFDeriv_succ_apply_right]
    rw [show (fun y : Fin p → ℝ => fderiv ℝ f y) = fderiv ℝ f from rfl]
    rw [iteratedFDeriv_two_apply]
    have h1 : (Fin.init mm) 0 = mm 0 := rfl
    have h2 : (Fin.init mm) 1 = mm 1 := rfl
    have h3 : (Fin.last 2 : Fin 3) = 2 := by decide
    rw [h1, h2, h3]
  have hK2 : ∀ (y a b : Fin p → ℝ),
      ((fderiv ℝ (fderiv ℝ K) y) a) b
        = iteratedDeriv 2 g (F y) * (fderiv ℝ F y a) * (fderiv ℝ F y b)
          + deriv g (F y) * (((fderiv ℝ (fderiv ℝ F) y) a) b) := by
    intro y a b
    have hc : HasFDerivAt (fun z => deriv g (F z))
        ((iteratedDeriv 2 g (F y)) • fderiv ℝ F y) y :=
      (hIderiv1 (F y)).comp_hasFDerivAt y ((hFd y).hasFDerivAt)
    have hA : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) y) y :=
      (hFd2 y).hasFDerivAt
    have hsm : HasFDerivAt (fun z => (deriv g (F z)) • fderiv ℝ F z)
        ((deriv g (F y)) • fderiv ℝ (fderiv ℝ F) y
          + ((iteratedDeriv 2 g (F y)) • fderiv ℝ F y).smulRight (fderiv ℝ F y)) y :=
      hc.smul hA
    have hEq : fderiv ℝ K = fun z => (deriv g (F z)) • fderiv ℝ F z := by
      funext z
      exact (hK1 z).fderiv
    have h2 : fderiv ℝ (fderiv ℝ K) y
        = (deriv g (F y)) • fderiv ℝ (fderiv ℝ F) y
          + ((iteratedDeriv 2 g (F y)) • fderiv ℝ F y).smulRight (fderiv ℝ F y) := by
      rw [hEq]
      exact hsm.fderiv
    rw [h2]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul]
    ring
  have hconst : ∀ u : Fin p → ℝ,
      HasFDerivAt (fun _ : Fin p → ℝ => u) (0 : (Fin p → ℝ) →L[ℝ] (Fin p → ℝ)) w := by
    intro u
    have h1 : HasDerivAt (fun _ : ℝ => (1 : ℝ)) (0 : ℝ) (F w) := hasDerivAt_const (F w) 1
    have h2 : HasFDerivAt (fun _ : Fin p → ℝ => (1 : ℝ)) (0 : (Fin p → ℝ) →L[ℝ] ℝ) w := by
      simpa using h1.comp_hasFDerivAt w ((hFd w).hasFDerivAt)
    have h3 : HasFDerivAt (fun y : Fin p → ℝ => (1 : ℝ) • u)
        ((0 : (Fin p → ℝ) →L[ℝ] ℝ).smulRight u) w := h2.smul_const u
    have h4 : ((0 : (Fin p → ℝ) →L[ℝ] ℝ).smulRight u) = (0 : (Fin p → ℝ) →L[ℝ] (Fin p → ℝ)) := by
      ext v
      simp
    rw [h4] at h3
    exact h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => (one_smul ℝ u).symm)
  have hv1 : ∀ (x a u : Fin p → ℝ),
      fderiv ℝ (fun y => (fderiv ℝ F y) u) x a = ((fderiv ℝ (fderiv ℝ F) x) a) u := by
    intro x a u
    have h := iteratedFDeriv_clm_apply_const_apply (𝕜 := ℝ) (n := (2 : WithTop ℕ∞))
      (c := fderiv ℝ F) hFc2 (i := 1) (by norm_num) (x := x) (u := u) (m := fun _ : Fin 1 => a)
    simp only [iteratedFDeriv_one_apply] at h
    simpa using h
  have hv2 : ∀ (x a : Fin p → ℝ),
      fderiv ℝ (fun y => iteratedDeriv 2 g (F y)) x a
        = iteratedDeriv 3 g (F x) * (fderiv ℝ F x a) := by
    intro x a
    have hd : fderiv ℝ (fun y => iteratedDeriv 2 g (F y)) x
        = (iteratedDeriv 3 g (F x)) • fderiv ℝ F x :=
      ((hIderiv2 (F x)).comp_hasFDerivAt x ((hFd x).hasFDerivAt)).fderiv
    rw [hd]
    simp [ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hv4 : ∀ (x a : Fin p → ℝ),
      fderiv ℝ (fun y => deriv g (F y)) x a = iteratedDeriv 2 g (F x) * (fderiv ℝ F x a) := by
    intro x a
    have hd : fderiv ℝ (fun y => deriv g (F y)) x = (iteratedDeriv 2 g (F x)) • fderiv ℝ F x :=
      ((hIderiv1 (F x)).comp_hasFDerivAt x ((hFd x).hasFDerivAt)).fderiv
    rw [hd]
    simp [ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hv3 : ∀ (x a u v : Fin p → ℝ),
      fderiv ℝ (fun y => ((fderiv ℝ (fderiv ℝ F) y) u) v) x a
        = (iteratedFDeriv ℝ 3 F x) (fun i : Fin 3 => ![a, u, v] i) := by
    intro x a u v
    have hfun : (fun y => ((fderiv ℝ (fderiv ℝ F) y) u) v)
        = fun y => (iteratedFDeriv ℝ 2 F y) (fun i : Fin 2 => ![u, v] i) := by
      funext y
      rw [iteratedFDeriv_two_apply]
      simp
    rw [hfun]
    have hIF2 : ContDiff ℝ 1 (iteratedFDeriv ℝ 2 F) :=
      hFs.iteratedFDeriv_right (i := 2) (by norm_num)
    have hd : HasFDerivAt (iteratedFDeriv ℝ 2 F) (fderiv ℝ (iteratedFDeriv ℝ 2 F) x) x :=
      (hIF2.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    have hstep : HasFDerivAt (fun y => (iteratedFDeriv ℝ 2 F y) (fun i : Fin 2 => ![u, v] i))
        ((fderiv ℝ (iteratedFDeriv ℝ 2 F) x).flipMultilinear (fun i : Fin 2 => ![u, v] i)) x :=
      hd.continuousMultilinear_apply_const (fun i : Fin 2 => ![u, v] i)
    rw [hstep.fderiv]
    have h3 := iteratedFDeriv_succ_apply_left (𝕜 := ℝ) (n := 2) (f := F) (x := x)
      (m := fun i : Fin 3 => ![a, u, v] i)
    rw [h3]
    have e1 : (![a, u, v] : Fin 3 → Fin p → ℝ) 0 = a := by simp
    have e2 : Fin.tail (![a, u, v] : Fin 3 → Fin p → ℝ) = ![u, v] := by
      funext i
      fin_cases i <;> simp [Fin.tail]
    rw [e1, e2]
    simp
  have hKsm : ContDiff ℝ 3 K := hg.comp hFs
  have hEval3 : ∀ (a u v : Fin p → ℝ),
      (iteratedFDeriv ℝ 3 K w) (fun i : Fin 3 => ![a, u, v] i)
        = fderiv ℝ (fun y => (iteratedFDeriv ℝ 2 K y) (fun i : Fin 2 => ![u, v] i)) w a := by
    intro a u v
    have hIF2K : ContDiff ℝ 1 (iteratedFDeriv ℝ 2 K) :=
      hKsm.iteratedFDeriv_right (i := 2) (by norm_num)
    have hdK : HasFDerivAt (iteratedFDeriv ℝ 2 K) (fderiv ℝ (iteratedFDeriv ℝ 2 K) w) w :=
      (hIF2K.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    have hstepK : HasFDerivAt (fun y => (iteratedFDeriv ℝ 2 K y) (fun i : Fin 2 => ![u, v] i))
        ((fderiv ℝ (iteratedFDeriv ℝ 2 K) w).flipMultilinear (fun i : Fin 2 => ![u, v] i)) w :=
      hdK.continuousMultilinear_apply_const (fun i : Fin 2 => ![u, v] i)
    rw [hstepK.fderiv]
    have h3K := iteratedFDeriv_succ_apply_left (𝕜 := ℝ) (n := 2) (f := K) (x := w)
      (m := fun i : Fin 3 => ![a, u, v] i)
    rw [h3K]
    have e1 : (![a, u, v] : Fin 3 → Fin p → ℝ) 0 = a := by simp
    have e2 : Fin.tail (![a, u, v] : Fin 3 → Fin p → ℝ) = ![u, v] := by
      funext i
      fin_cases i <;> simp [Fin.tail]
    rw [e1, e2]
    simp
  have hPsi : ∀ (y u v : Fin p → ℝ),
      (iteratedFDeriv ℝ 2 K y) (fun i : Fin 2 => ![u, v] i)
        = iteratedDeriv 2 g (F y) * (fderiv ℝ F y u) * (fderiv ℝ F y v)
          + deriv g (F y) * (((fderiv ℝ (fderiv ℝ F) y) u) v) := by
    intro y u v
    rw [iteratedFDeriv_two_apply]
    simpa using hK2 y u v
  have hDeriv : ∀ (a u v : Fin p → ℝ),
      fderiv ℝ (fun y => (iteratedFDeriv ℝ 2 K y) (fun i : Fin 2 => ![u, v] i)) w a
        = iteratedDeriv 3 g (F w) * (fderiv ℝ F w a) * (fderiv ℝ F w u) * (fderiv ℝ F w v)
          + iteratedDeriv 2 g (F w) * ((((fderiv ℝ (fderiv ℝ F) w) a) u) * (fderiv ℝ F w v)
              + (fderiv ℝ F w u) * (((fderiv ℝ (fderiv ℝ F) w) a) v)
              + (((fderiv ℝ (fderiv ℝ F) w) u) v) * (fderiv ℝ F w a))
          + deriv g (F w) * ((iteratedFDeriv ℝ 3 F w) (fun i : Fin 3 => ![a, u, v] i)) := by
    intro a u v
    have hfunPsi : (fun y => (iteratedFDeriv ℝ 2 K y) (fun i : Fin 2 => ![u, v] i))
        = fun y => iteratedDeriv 2 g (F y) * (fderiv ℝ F y u) * (fderiv ℝ F y v)
            + deriv g (F y) * (((fderiv ℝ (fderiv ℝ F) y) u) v) := by
      funext y
      exact hPsi y u v
    have hd2 : HasFDerivAt (fun y => iteratedDeriv 2 g (F y))
        ((iteratedDeriv 3 g (F w)) • fderiv ℝ F w) w :=
      (hIderiv2 (F w)).comp_hasFDerivAt w ((hFd w).hasFDerivAt)
    have hd1 : HasFDerivAt (fun y => deriv g (F y))
        ((iteratedDeriv 2 g (F w)) • fderiv ℝ F w) w :=
      (hIderiv1 (F w)).comp_hasFDerivAt w ((hFd w).hasFDerivAt)
    have hAu : HasFDerivAt (fun y => (fderiv ℝ F y) u)
        (fderiv ℝ (fun y => (fderiv ℝ F y) u) w) w :=
      ((hFd2 w).hasFDerivAt.clm_apply (hconst u)).differentiableAt.hasFDerivAt
    have hAv : HasFDerivAt (fun y => (fderiv ℝ F y) v)
        (fderiv ℝ (fun y => (fderiv ℝ F y) v) w) w :=
      ((hFd2 w).hasFDerivAt.clm_apply (hconst v)).differentiableAt.hasFDerivAt
    have hBu : HasFDerivAt (fun y => (fderiv ℝ (fderiv ℝ F) y) u)
        (fderiv ℝ (fun y => (fderiv ℝ (fderiv ℝ F) y) u) w) w :=
      ((hFd3 w).hasFDerivAt.clm_apply (hconst u)).differentiableAt.hasFDerivAt
    have hBuv : HasFDerivAt (fun y => ((fderiv ℝ (fderiv ℝ F) y) u) v)
        (fderiv ℝ (fun y => ((fderiv ℝ (fderiv ℝ F) y) u) v) w) w :=
      (hBu.clm_apply (hconst v)).differentiableAt.hasFDerivAt
    have hA : HasFDerivAt
        (fun y => iteratedDeriv 2 g (F y) * (fderiv ℝ F y u) * (fderiv ℝ F y v)) _ w :=
      (hd2.mul hAu).mul hAv
    have hB : HasFDerivAt (fun y => deriv g (F y) * (((fderiv ℝ (fderiv ℝ F) y) u) v)) _ w :=
      hd1.mul hBuv
    have hsum : HasFDerivAt
        (fun y => iteratedDeriv 2 g (F y) * (fderiv ℝ F y u) * (fderiv ℝ F y v)
          + deriv g (F y) * (((fderiv ℝ (fderiv ℝ F) y) u) v)) _ w :=
      hA.add hB
    rw [hfunPsi, hsum.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      Pi.mul_apply, hv1, hv2, hv3, hv4]
    ring
  have hmain : ∀ (a u v : Fin p → ℝ),
      (iteratedFDeriv ℝ 3 K w) (fun i : Fin 3 => ![a, u, v] i)
        = iteratedDeriv 3 g (F w) * (fderiv ℝ F w a) * (fderiv ℝ F w u) * (fderiv ℝ F w v)
          + iteratedDeriv 2 g (F w) * ((((fderiv ℝ (fderiv ℝ F) w) a) u) * (fderiv ℝ F w v)
              + (fderiv ℝ F w u) * (((fderiv ℝ (fderiv ℝ F) w) a) v)
              + (((fderiv ℝ (fderiv ℝ F) w) u) v) * (fderiv ℝ F w a))
          + deriv g (F w) * ((iteratedFDeriv ℝ 3 F w) (fun i : Fin 3 => ![a, u, v] i)) := by
    intro a u v
    rw [hEval3 a u v, hDeriv a u v]
  have hsingle : ∀ (f : Fin p → ℝ) (q : Fin p),
      (∑ b : Fin p, f b * (Pi.single q (1 : ℝ) : Fin p → ℝ) b) = f q := by
    intro f q
    have hsum : (∑ b : Fin p, f b * (Pi.single q (1 : ℝ) : Fin p → ℝ) b)
        = f q * (Pi.single q (1 : ℝ) : Fin p → ℝ) q := by
      refine Finset.sum_eq_single q ?_ ?_
      · intro b _ hb
        simp [Ne.symm hb]
      · intro hq
        exact absurd (Finset.mem_univ q) hq
    rw [hsum]
    simp
  have hA1 : ∀ q : Fin p,
      (∑ b : Fin p, (Real.exp (beta * (w b - y b)) / (∑ m : Fin p, Real.exp (beta * (w m - y m))))
        * (Pi.single q (1 : ℝ) : Fin p → ℝ) b)
        = Real.exp (beta * (w q - y q)) / (∑ m : Fin p, Real.exp (beta * (w m - y m))) :=
    fun q => hsingle
      (fun b => Real.exp (beta * (w b - y b)) / (∑ m : Fin p, Real.exp (beta * (w m - y m)))) q
  have hPv : ∀ q : Fin p, (fderiv ℝ F w) (Pi.single q (1 : ℝ))
      = Real.exp (beta * (w q - y q)) / (∑ m : Fin p, Real.exp (beta * (w m - y m))) := by
    intro q
    exact (hfderiv (Pi.single q (1 : ℝ))).trans (hA1 q)
  have hS1 : ∀ a b : Fin p,
      (∑ c : Fin p, (Real.exp (beta * (w c - y c)) / (∑ m : Fin p, Real.exp (beta * (w m - y m))))
        * (Pi.single a (1 : ℝ) : Fin p → ℝ) c * (Pi.single b (1 : ℝ) : Fin p → ℝ) c)
        = (Real.exp (beta * (w a - y a)) / (∑ m : Fin p, Real.exp (beta * (w m - y m))))
          * (if a = b then (1 : ℝ) else 0) := by
    intro a b
    have h1 := hsingle (fun c => (Real.exp (beta * (w c - y c)) / (∑ m : Fin p, Real.exp (beta * (w m - y m))))
      * (Pi.single b (1 : ℝ) : Fin p → ℝ) c) a
    have hstep : (∑ c : Fin p, (Real.exp (beta * (w c - y c)) / (∑ m : Fin p, Real.exp (beta * (w m - y m))))
        * (Pi.single a (1 : ℝ) : Fin p → ℝ) c * (Pi.single b (1 : ℝ) : Fin p → ℝ) c)
        = (∑ c : Fin p, ((Real.exp (beta * (w c - y c)) / (∑ m : Fin p, Real.exp (beta * (w m - y m))))
          * (Pi.single b (1 : ℝ) : Fin p → ℝ) c) * (Pi.single a (1 : ℝ) : Fin p → ℝ) c) := by
      apply Finset.sum_congr rfl
      intro c _
      ring
    rw [hstep, h1]
    by_cases hab : a = b
    · subst hab
      simp
    · have h0 : (Pi.single b (1 : ℝ) : Fin p → ℝ) a = 0 := by
        simp [Pi.single_eq_of_ne, Ne.symm hab]
      rw [h0, if_neg hab, mul_zero]
  have hBv : ∀ a b : Fin p,
      ((fderiv ℝ (fderiv ℝ F) w) (Pi.single a (1 : ℝ))) (Pi.single b (1 : ℝ))
      = beta * ((Real.exp (beta * (w a - y a)) / (∑ m : Fin p, Real.exp (beta * (w m - y m))))
          * (if a = b then (1 : ℝ) else 0)
        - (Real.exp (beta * (w a - y a)) / (∑ m : Fin p, Real.exp (beta * (w m - y m))))
          * (Real.exp (beta * (w b - y b)) / (∑ m : Fin p, Real.exp (beta * (w m - y m))))) := by
    intro a b
    have h1 := hBf (Pi.single a (1 : ℝ)) (Pi.single b (1 : ℝ))
    have h2 : beta * ((∑ c : Fin p, (Real.exp (beta * (w c - y c)) / (∑ m : Fin p, Real.exp (beta * (w m - y m))))
          * (Pi.single a (1 : ℝ) : Fin p → ℝ) c * (Pi.single b (1 : ℝ) : Fin p → ℝ) c)
        - (∑ c : Fin p, (Real.exp (beta * (w c - y c)) / (∑ m : Fin p, Real.exp (beta * (w m - y m))))
          * (Pi.single a (1 : ℝ) : Fin p → ℝ) c)
          * (∑ c : Fin p, (Real.exp (beta * (w c - y c)) / (∑ m : Fin p, Real.exp (beta * (w m - y m))))
            * (Pi.single b (1 : ℝ) : Fin p → ℝ) c))
        = beta * ((Real.exp (beta * (w a - y a)) / (∑ m : Fin p, Real.exp (beta * (w m - y m))))
            * (if a = b then (1 : ℝ) else 0)
          - (Real.exp (beta * (w a - y a)) / (∑ m : Fin p, Real.exp (beta * (w m - y m))))
            * (Real.exp (beta * (w b - y b)) / (∑ m : Fin p, Real.exp (beta * (w m - y m))))) := by
      rw [hS1 a b, hA1 a, hA1 b]
    exact h1.trans h2
  have hCf' : (iteratedFDeriv ℝ 3 F w) (fun i : Fin 3 => Pi.single (![j, k, l] i) (1 : ℝ))
      = beta ^ 2 * _ := hCf j k l
  have hKfun : (fun v : Fin p → ℝ => phi0 (phi * Fbeta p beta y v)) = K := rfl
  have hslots : (fun i : Fin 3 => Pi.single (![j, k, l] i) (1 : ℝ))
      = (fun i : Fin 3 =>
        (![Pi.single j (1 : ℝ), Pi.single k (1 : ℝ), Pi.single l (1 : ℝ)] : Fin 3 → Fin p → ℝ) i) := by
    funext i
    fin_cases i <;> rfl
  have hgg1 : deriv g (F w) = deriv (fun t : ℝ => phi0 (phi * t)) (Fbeta p beta y w) := rfl
  have hgg2 : iteratedDeriv 2 g (F w)
      = iteratedDeriv 2 (fun t : ℝ => phi0 (phi * t)) (Fbeta p beta y w) := rfl
  have hgg3 : iteratedDeriv 3 g (F w)
      = iteratedDeriv 3 (fun t : ℝ => phi0 (phi * t)) (Fbeta p beta y w) := rfl
  rw [hKfun, hslots, hmain (Pi.single j (1 : ℝ)) (Pi.single k (1 : ℝ)) (Pi.single l (1 : ℝ)),
    ← hslots, hPv j, hPv k, hPv l, hBv j k, hBv j l, hBv k l, hCf', hgg1, hgg2, hgg3]
  ring
  /- @proof-region region.target-node.session.7ce3fa5ab9a1985e end -/

end Statlib.Imported
end

