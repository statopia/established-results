import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base

namespace PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Statlib.StatFoundation.RandomVariable.Gaussian
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Statlib.StatFoundation.RandomVariable.Gaussian
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_3323695585_5e8b63c6 : ∀ (phi0 : ℝ → ℝ) (hphi0_cont : ContDiff ℝ 3 phi0)
    (hc1 : Continuous fun t : ℝ => deriv phi0 t)
    (hc2 : Continuous fun t : ℝ => deriv (deriv phi0) t)
    (p : ℕ) (hp : 0 < Real.log (p : ℝ)) (phi : ℝ) (hphi : 1 ≤ phi)
    (y : Fin p → ℝ) (j k : Fin p),
    (let beta : ℝ := phi * Real.log (p : ℝ)
     let S : (Fin p → ℝ) → ℝ := fun w => ∑ i : Fin p, Real.exp (beta * (w i - y i))
     let kappa : (Fin p → ℝ) → ℝ := fun w => phi0 (phi * (beta⁻¹ * Real.log (S w)))
     (∀ w : Fin p → ℝ,
        (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ kappa z) (Pi.single j (1 : ℝ))) w)
            (Pi.single k (1 : ℝ))
          = deriv (deriv phi0) (phi * (beta⁻¹ * Real.log (S w)))
              * (phi ^ 2 * ((Real.exp (beta * (w j - y j)) / S w) *
                  (Real.exp (beta * (w k - y k)) / S w)))
            + deriv phi0 (phi * (beta⁻¹ * Real.log (S w))) * (phi * beta)
              * ((if j = k then (1 : ℝ) else 0) * (Real.exp (beta * (w j - y j)) / S w)
                 - (Real.exp (beta * (w j - y j)) / S w) *
                    (Real.exp (beta * (w k - y k)) / S w))) ∧
     (Continuous fun w : Fin p → ℝ =>
        (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ kappa z) (Pi.single j (1 : ℝ))) w)
          (Pi.single k (1 : ℝ)))) := by
  /- @proof-region region.target-node.session.93b1bc721825fb66 begin -/
  intro phi0 hphi0_cont hc1 hc2 p hp phi hphi y j k
  dsimp only
  set beta : ℝ := phi * Real.log (p : ℝ) with hbeta
  have hphi_pos : (0:ℝ) < phi := lt_of_lt_of_le zero_lt_one hphi
  have hbeta_pos : 0 < beta := by rw [hbeta]; positivity
  have hbeta_ne : beta ≠ 0 := hbeta_pos.ne'
  set e : Fin p → (Fin p → ℝ) → ℝ := fun i w => Real.exp (beta * (w i - y i)) with he
  set Sf : (Fin p → ℝ) → ℝ := fun w => ∑ i, e i w with hSf
  set kappa : (Fin p → ℝ) → ℝ := fun w => phi0 (phi * (beta⁻¹ * Real.log (Sf w))) with hkappa
  have hp_ne : p ≠ 0 := by
    rintro rfl
    simp [Real.log_zero] at hp
  have hp_pos_nat : 0 < p := Nat.pos_of_ne_zero hp_ne
  have hS_pos : ∀ w : Fin p → ℝ, 0 < Sf w := by
    intro w
    rw [hSf]
    refine Finset.sum_pos (fun i _ => ?_) ⟨⟨0, hp_pos_nat⟩, Finset.mem_univ _⟩
    simp only [he]
    exact Real.exp_pos _
  set DS : (Fin p → ℝ) → (Fin p → ℝ) →L[ℝ] ℝ :=
    fun w => ∑ i : Fin p, (beta * e i w) • (ContinuousLinearMap.proj i : (Fin p → ℝ) →L[ℝ] ℝ) with hDS
  set T : (Fin p → ℝ) → (Fin p → ℝ) →L[ℝ] ℝ :=
    fun w => phi • (beta⁻¹ • ((Sf w)⁻¹ • DS w)) with hT
  set t : (Fin p → ℝ) → ℝ := fun w => phi * (beta⁻¹ * Real.log (Sf w)) with ht
  set Af : (Fin p → ℝ) → ℝ := fun w => deriv phi0 (t w) with hAf
  set Bf : (Fin p → ℝ) → ℝ := fun w => phi * (e j w / Sf w) with hBf
  set g : (Fin p → ℝ) → ℝ := fun w => Af w * Bf w with hg
  set DB : (Fin p → ℝ) → (Fin p → ℝ) →L[ℝ] ℝ :=
    fun w => (phi * (beta * e j w) / Sf w) • (ContinuousLinearMap.proj j)
      - (phi * e j w / (Sf w) ^ 2) • DS w with hDB
  set DA : (Fin p → ℝ) → (Fin p → ℝ) →L[ℝ] ℝ :=
    fun w => (fderiv ℝ (deriv phi0) (t w)).comp (T w) with hDA
  have hcoord : ∀ (i : Fin p) (w : Fin p → ℝ),
      HasFDerivAt (fun z : Fin p → ℝ => z i) ((ContinuousLinearMap.proj i : (Fin p → ℝ) →L[ℝ] ℝ)) w := by
    intro i w
    exact ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.proj i : (Fin p → ℝ) →L[ℝ] ℝ)
  have hconst0 : ∀ w : Fin p → ℝ,
      HasFDerivAt (fun _ : Fin p → ℝ => (0:ℝ)) (0 : (Fin p → ℝ) →L[ℝ] ℝ) w := by
    intro w
    simpa using ContinuousLinearMap.hasFDerivAt (0 : (Fin p → ℝ) →L[ℝ] ℝ) (x := w)
  have he_deriv : ∀ (i : Fin p) (w : Fin p → ℝ),
      HasFDerivAt (fun z : Fin p → ℝ => e i z)
        ((beta * e i w) • ((ContinuousLinearMap.proj i : (Fin p → ℝ) →L[ℝ] ℝ))) w := by
    intro i w
    have hsub : HasFDerivAt (fun x : ℝ => x - y i) (ContinuousLinearMap.id ℝ ℝ) (w i) :=
      hasFDerivAt_sub_const (y i)
    have hd : HasDerivAt (fun x : ℝ => x - y i) (1:ℝ) (w i) := by
      simpa using hsub.hasDerivAt
    have hcomp := hd.comp_hasFDerivAt w (hcoord i w)
    have h1 : HasFDerivAt (fun z : Fin p → ℝ => z i - y i)
        ((ContinuousLinearMap.proj i : (Fin p → ℝ) →L[ℝ] ℝ)) w := by
      simpa [Function.comp_def] using hcomp
    have h2 := h1.const_mul beta
    have hexp := (Real.hasDerivAt_exp (beta * (w i - y i))).comp_hasFDerivAt w h2
    have hval : Real.exp (beta * (w i - y i)) • (beta • (ContinuousLinearMap.proj i : (Fin p → ℝ) →L[ℝ] ℝ))
        = (beta * Real.exp (beta * (w i - y i))) • (ContinuousLinearMap.proj i : (Fin p → ℝ) →L[ℝ] ℝ) := by
      rw [smul_smul]
      congr 1
      ring
    have hfun : (fun z : Fin p → ℝ => e i z)
        = Real.exp ∘ (fun z : Fin p → ℝ => beta * (z i - y i)) := by
      funext z
      simp only [he, Function.comp_apply]
    have hexp' : HasFDerivAt (Real.exp ∘ (fun z : Fin p → ℝ => beta * (z i - y i)))
        ((beta * Real.exp (beta * (w i - y i))) • (ContinuousLinearMap.proj i : (Fin p → ℝ) →L[ℝ] ℝ)) w :=
      hval ▸ hexp
    rw [hfun]
    simpa only [he] using hexp'
  have hS_deriv : ∀ w : Fin p → ℝ, HasFDerivAt Sf (DS w) w := by
    intro w
    have hsum : ∀ s : Finset (Fin p),
        HasFDerivAt (fun z : Fin p → ℝ => ∑ i ∈ s, e i z)
          (∑ i ∈ s, (beta * e i w) • (ContinuousLinearMap.proj i : (Fin p → ℝ) →L[ℝ] ℝ)) w := by
      intro s
      induction s using Finset.induction with
      | empty => simpa using hconst0 w
      | insert a s ha ih =>
          have h := (he_deriv a w).add ih
          simpa [Finset.sum_insert ha, Pi.add_apply] using h
    have hu := hsum Finset.univ
    simpa [hSf, hDS] using hu
  have hlog_deriv : ∀ w : Fin p → ℝ,
      HasFDerivAt (fun z : Fin p → ℝ => Real.log (Sf z)) ((Sf w)⁻¹ • DS w) w := by
    intro w
    have h := (Real.hasDerivAt_log (ne_of_gt (hS_pos w))).comp_hasFDerivAt w (hS_deriv w)
    simpa [Function.comp_def] using h
  have ht_deriv : ∀ w : Fin p → ℝ, HasFDerivAt t (T w) w := by
    intro w
    have h0 : HasDerivAt (fun s : ℝ => s) (1:ℝ) (Real.log (Sf w)) := by
      simpa using hasDerivAt_id (Real.log (Sf w))
    have h1 := h0.const_mul beta⁻¹
    have h2 := h1.const_mul phi
    have houter : HasDerivAt (fun s : ℝ => phi * (beta⁻¹ * s)) (phi * beta⁻¹) (Real.log (Sf w)) := by
      simpa using h2
    have hcomp := houter.comp_hasFDerivAt w (hlog_deriv w)
    have hfun : ((fun s : ℝ => phi * (beta⁻¹ * s)) ∘ (fun z : Fin p → ℝ => Real.log (Sf z))) = t := by
      funext z
      simp only [Function.comp_apply, ht]
    have hder : (phi * beta⁻¹) • ((Sf w)⁻¹ • DS w) = T w := by
      rw [hT]
      simp only [smul_smul, mul_assoc]
    rw [hfun, hder] at hcomp
    exact hcomp
  have hphi0_deriv : ∀ s : ℝ, HasFDerivAt phi0 (fderiv ℝ phi0 s) s := by
    intro s
    have hd : DifferentiableAt ℝ phi0 s := (hphi0_cont.contDiffAt (x := s)).differentiableAt (by norm_num)
    exact hd.hasFDerivAt
  have hderiv_diff : ∀ s : ℝ, HasFDerivAt (deriv phi0) (fderiv ℝ (deriv phi0) s) s := by
    have hjoint : ContDiff ℝ 2 (fun p : ℝ × ℝ => (fderiv ℝ phi0 p.1) p.2) :=
      hphi0_cont.contDiff_fderiv_apply (m := 2) (n := 3) (by norm_num)
    have hcomp : ContDiff ℝ 2
        ((fun p : ℝ × ℝ => (fderiv ℝ phi0 p.1) p.2) ∘ (fun s : ℝ => (s, (1:ℝ)))) := by
      refine hjoint.comp ?_
      fun_prop
    have hdc : ContDiff ℝ 2 (deriv phi0) := by
      convert hcomp using 1
    intro s

    have hd : DifferentiableAt ℝ (deriv phi0) s :=
      (hdc.contDiffAt (x := s)).differentiableAt (by norm_num)
    exact hd.hasFDerivAt

  have hkappa_deriv : ∀ w : Fin p → ℝ,
      HasFDerivAt kappa ((fderiv ℝ phi0 (t w)).comp (T w)) w := by
    intro w
    have h := HasFDerivAt.comp w (hphi0_deriv (t w)) (ht_deriv w)
    have hfun : kappa = phi0 ∘ t := by
      funext z
      simp only [hkappa, ht, Function.comp_apply]

    rw [hfun]
    exact h
  have hAf_deriv : ∀ w : Fin p → ℝ, HasFDerivAt Af (DA w) w := by
    intro w
    have h := HasFDerivAt.comp w (hderiv_diff (t w)) (ht_deriv w)
    have hfun : Af = deriv phi0 ∘ t := by
      funext z
      simp only [hAf, Function.comp_apply]
    rw [hfun]
    exact h
  have hBf_deriv : ∀ w : Fin p → ℝ, HasFDerivAt Bf (DB w) w := by
    intro w
    have hSne : Sf w ≠ 0 := (hS_pos w).ne'
    have hinvderiv : HasDerivAt (fun u : ℝ => u⁻¹) (-((Sf w) ^ 2)⁻¹) (Sf w) :=
      hasDerivAt_inv hSne
    have hinv : HasFDerivAt (fun z : Fin p → ℝ => (Sf z)⁻¹) (-(((Sf w) ^ 2)⁻¹ • DS w)) w := by
      have h := hinvderiv.comp_hasFDerivAt w (hS_deriv w)
      simpa [Function.comp_def] using h


    have hmul := (he_deriv j w).mul hinv
    have hcm := hmul.const_mul phi
    have hfun : Bf = fun z : Fin p → ℝ => phi * (e j z * (Sf z)⁻¹) := by
      funext z
      simp only [hBf, div_eq_mul_inv]
    rw [hfun]
    convert hcm using 1
    ext v
    simp only [hDB, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.proj_apply,
      smul_eq_mul, div_eq_mul_inv]
    field_simp
    ring

  have hg_deriv : ∀ w : Fin p → ℝ, HasFDerivAt g (Af w • DB w + Bf w • DA w) w := by
    intro w
    have h := (hAf_deriv w).mul (hBf_deriv w)
    have hfun : g = Af * Bf := by
      funext z
      simp only [hg, Pi.mul_apply]
    rw [hfun]
    convert h using 1 <;> abel
  have hDS_single : ∀ (w : Fin p → ℝ) (i₀ : Fin p), DS w (Pi.single i₀ 1) = beta * e i₀ w := by
    intro w i₀
    rw [hDS]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i₀]
    · simp
    · intro i _ hi
      simp [Pi.single, hi]
    · intro h
      exact absurd (Finset.mem_univ i₀) h
  have hfderiv_smul : ∀ (f : ℝ → ℝ) (s c : ℝ), (fderiv ℝ f s) c = c * deriv f s := by
    intro f s c
    calc (fderiv ℝ f s) c = (fderiv ℝ f s) (c • (1:ℝ)) := by rw [smul_eq_mul, mul_one]
      _ = c • ((fderiv ℝ f s) 1) := by rw [ContinuousLinearMap.map_smul]
      _ = c • deriv f s := by rw [fderiv_apply_one_eq_deriv]
      _ = c * deriv f s := by rw [smul_eq_mul]
  have hkappa_eq : ∀ w : Fin p → ℝ, (fderiv ℝ kappa w) (Pi.single j 1) = g w := by
    intro w
    have hSne : Sf w ≠ 0 := (hS_pos w).ne'
    have hTj : T w (Pi.single j (1:ℝ)) = phi * (beta⁻¹ * ((Sf w)⁻¹ * (beta * e j w))) := by
      simp only [hT, ContinuousLinearMap.smul_apply, smul_eq_mul, hDS_single w j]
    rw [(hkappa_deriv w).fderiv, ContinuousLinearMap.comp_apply, hTj, hfderiv_smul phi0 (t w)]
    simp only [hg, hAf, hBf]
    field_simp


  have main : (∀ w : Fin p → ℝ,
      (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ kappa z) (Pi.single j (1:ℝ))) w) (Pi.single k (1:ℝ))
        = deriv (deriv phi0) (phi * (beta⁻¹ * Real.log (Sf w)))
            * (phi ^ 2 * ((e j w / Sf w) * (e k w / Sf w)))
          + deriv phi0 (phi * (beta⁻¹ * Real.log (Sf w))) * (phi * beta)
            * ((if j = k then (1:ℝ) else 0) * (e j w / Sf w)
               - (e j w / Sf w) * (e k w / Sf w))) ∧
      Continuous (fun w : Fin p → ℝ =>
        (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ kappa z) (Pi.single j (1:ℝ))) w) (Pi.single k (1:ℝ))) := by
    have hsingle : (Pi.single k (1:ℝ) : Fin p → ℝ) j = (if j = k then (1:ℝ) else 0) := by
      by_cases h : j = k
      · subst h
        simp
      · simp [Pi.single, h]
    have hmain1 : ∀ w : Fin p → ℝ,
        (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ kappa z) (Pi.single j (1:ℝ))) w) (Pi.single k (1:ℝ))
          = deriv (deriv phi0) (t w) * (phi ^ 2 * ((e j w / Sf w) * (e k w / Sf w)))
            + deriv phi0 (t w) * (phi * beta)
              * ((if j = k then (1:ℝ) else 0) * (e j w / Sf w) - (e j w / Sf w) * (e k w / Sf w)) := by
      intro w
      have hSne : Sf w ≠ 0 := (hS_pos w).ne'
      have hFeq : (fun z : Fin p → ℝ => (fderiv ℝ kappa z) (Pi.single j (1:ℝ))) = g := by
        funext z
        exact hkappa_eq z
      rw [hFeq, (hg_deriv w).fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      simp only [hDB, hDA, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
        hDS_single w k, hT, hfderiv_smul, hAf, hBf, hsingle]
      field_simp
      ring
    refine ⟨fun w => ?_, ?_⟩
    · simpa only [ht] using hmain1 w
    · have hSfc : Continuous Sf := by
        rw [continuous_iff_continuousAt]
        intro w
        exact (hS_deriv w).continuousAt
      have htc : Continuous t := by
        rw [continuous_iff_continuousAt]
        intro w
        exact (ht_deriv w).continuousAt
      have hD1c : Continuous (fun w : Fin p → ℝ => deriv phi0 (t w)) := hc1.comp htc
      have hD2c : Continuous (fun w : Fin p → ℝ => deriv (deriv phi0) (t w)) := hc2.comp htc
      have hejc : Continuous (fun w : Fin p → ℝ => e j w) := by
        rw [continuous_iff_continuousAt]
        intro w
        exact (he_deriv j w).continuousAt
      have hekc : Continuous (fun w : Fin p → ℝ => e k w) := by
        rw [continuous_iff_continuousAt]
        intro w
        exact (he_deriv k w).continuousAt
      have hjc : Continuous (fun w : Fin p → ℝ => e j w / Sf w) :=
        hejc.div hSfc (fun x => (hS_pos x).ne')
      have hkc : Continuous (fun w : Fin p → ℝ => e k w / Sf w) :=
        hekc.div hSfc (fun x => (hS_pos x).ne')

      have h1c : Continuous (fun w : Fin p → ℝ => phi ^ 2 * ((e j w / Sf w) * (e k w / Sf w))) :=
        continuous_const.mul (hjc.mul hkc)
      have h2c : Continuous (fun w : Fin p → ℝ =>
          deriv (deriv phi0) (t w) * (phi ^ 2 * ((e j w / Sf w) * (e k w / Sf w)))) :=
        hD2c.mul h1c
      have h3c : Continuous (fun w : Fin p → ℝ =>
          (if j = k then (1:ℝ) else 0) * (e j w / Sf w) - (e j w / Sf w) * (e k w / Sf w)) :=
        (continuous_const.mul hjc).sub (hjc.mul hkc)
      have h4c : Continuous (fun w : Fin p → ℝ =>
          deriv phi0 (t w) * (phi * beta) *
            ((if j = k then (1:ℝ) else 0) * (e j w / Sf w) - (e j w / Sf w) * (e k w / Sf w))) :=
        (hD1c.mul continuous_const).mul h3c
      exact (h2c.add h4c).congr (fun w => (hmain1 w).symm)

  simpa only [hbeta, he, hSf, hkappa] using main

  /- @proof-region region.target-node.session.93b1bc721825fb66 end -/

end

end Statlib.Imported

