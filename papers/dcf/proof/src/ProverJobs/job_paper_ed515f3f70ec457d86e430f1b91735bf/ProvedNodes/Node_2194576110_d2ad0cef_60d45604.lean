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
theorem statopia_math_node_2194576110_d2ad0cef : ∀ (p : ℕ) (hp : 2 ≤ p)
    (phi : ℝ) (hphi : 1 ≤ phi)
    (phi0 : ℝ → ℝ)
    (hphi0_cont : ContDiff ℝ 3 phi0)
    (hphi0_left : ∀ z : ℝ, z ≤ 0 → phi0 z = 1)
    (hphi0_right : ∀ z : ℝ, 1 ≤ z → phi0 z = 0)
    (hphi0_range : ∀ z : ℝ, phi0 z ∈ Set.Icc (0 : ℝ) 1)
    (y : Fin p → ℝ),
    (let kappa : (Fin p → ℝ) → ℝ := fun w => phi0 (phi * ((phi * Real.log (p : ℝ))⁻¹ * Real.log (∑ j : Fin p, Real.exp ((phi * Real.log (p : ℝ)) * (w j - y j))))); ContDiff ℝ 3 kappa ∧
      (∀ w : Fin p → ℝ, 0 ≤ kappa w ∧ kappa w ≤ 1) ∧
      (∀ w : Fin p → ℝ, (∀ j : Fin p, w j ≤ y j - phi⁻¹) → kappa w = 1) ∧
      (∀ w : Fin p → ℝ, phi⁻¹ ≤ (⨆ j : Fin p, (w j - y j)) → kappa w = 0) ∧
      (∀ (d : Fin 3 → Fin p) (w : Fin p → ℝ),
        (⨆ j : Fin p, (w j - y j)) < -phi⁻¹ →
          iteratedFDeriv ℝ 3 kappa w (fun t : Fin 3 => Pi.single (d t) (1 : ℝ)) = 0) ∧
      (∀ (d : Fin 3 → Fin p) (w : Fin p → ℝ),
        phi⁻¹ < (⨆ j : Fin p, (w j - y j)) →
          iteratedFDeriv ℝ 3 kappa w (fun t : Fin 3 => Pi.single (d t) (1 : ℝ)) = 0) ∧
      (∀ d : Fin 3 → Fin p,
        Function.support (fun w : Fin p → ℝ =>
            iteratedFDeriv ℝ 3 kappa w (fun t : Fin 3 => Pi.single (d t) (1 : ℝ)))
          ⊆ {w : Fin p → ℝ | -phi⁻¹ ≤ (⨆ j : Fin p, (w j - y j)) ∧
              (⨆ j : Fin p, (w j - y j)) ≤ phi⁻¹}) ∧
      (∀ w : Fin p → ℝ,
        Set.indicator {w : Fin p → ℝ | ∀ j : Fin p, w j ≤ y j - phi⁻¹}
            (fun _ => (1 : ℝ)) w ≤ kappa w ∧
          kappa w ≤ Set.indicator {w : Fin p → ℝ | ∀ j : Fin p, w j ≤ y j + phi⁻¹}
            (fun _ => (1 : ℝ)) w)) := by
  /- @proof-region region.target-node.session.dca13f7e30730842 begin -/
  intro p hp phi hphi phi0 hphi0_smooth hphi0_left hphi0_right hphi0_range y
  let beta : ℝ := phi * Real.log (p : ℝ)
  let F : (Fin p → ℝ) → ℝ := fun w => beta⁻¹ * Real.log (∑ j : Fin p, Real.exp (beta * (w j - y j)))
  let kappa : (Fin p → ℝ) → ℝ := fun w => phi0 (phi * F w)
  haveI : Nonempty (Fin p) := ⟨⟨0, by omega⟩⟩
  have hphi_pos : 0 < phi := lt_of_lt_of_le zero_lt_one hphi
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by linarith)
  have hbeta_pos : 0 < beta := by
    show (0 : ℝ) < phi * Real.log (p : ℝ)
    exact mul_pos hphi_pos hlogp
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hbeta_inv_log : beta⁻¹ * Real.log (p : ℝ) = phi⁻¹ := by
    show (phi * Real.log (p : ℝ))⁻¹ * Real.log (p : ℝ) = phi⁻¹
    field_simp [hphi_pos.ne', hlogp.ne']

  have hS_pos : ∀ w : Fin p → ℝ, 0 < ∑ j : Fin p, Real.exp (beta * (w j - y j)) := by
    intro w
    exact Finset.sum_pos (fun j _ => Real.exp_pos _) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hS_smooth : ContDiff ℝ 3 (fun w : Fin p → ℝ => ∑ j : Fin p, Real.exp (beta * (w j - y j))) := by
    fun_prop
  have hM_ge : ∀ (v : Fin p → ℝ) (i : Fin p), v i - y i ≤ ⨆ j : Fin p, (v j - y j) :=
    fun v i => le_ciSup (Finite.bddAbove_range (fun j : Fin p => v j - y j)) i
  have hF_ge : ∀ w : Fin p → ℝ, (⨆ i : Fin p, (w i - y i)) ≤ F w := by
    intro w
    show (⨆ i : Fin p, (w i - y i))
      ≤ beta⁻¹ * Real.log (∑ j : Fin p, Real.exp (beta * (w j - y j)))
    refine ciSup_le (fun i => ?_)
    have hterm : Real.exp (beta * (w i - y i))
        ≤ ∑ j : Fin p, Real.exp (beta * (w j - y j)) :=
      Finset.single_le_sum (f := fun j : Fin p => Real.exp (beta * (w j - y j)))
        (fun j _ => le_of_lt (Real.exp_pos _)) (Finset.mem_univ i)
    have hlog : beta * (w i - y i)
        ≤ Real.log (∑ j : Fin p, Real.exp (beta * (w j - y j))) := by
      have h := Real.log_le_log (Real.exp_pos (beta * (w i - y i))) hterm
      rwa [Real.log_exp] at h
    have hstep := mul_le_mul_of_nonneg_left hlog (le_of_lt (inv_pos.mpr hbeta_pos))
    rwa [← mul_assoc, inv_mul_cancel₀ hbeta_pos.ne', one_mul] at hstep
  have hF_le : ∀ w : Fin p → ℝ, F w ≤ (⨆ i : Fin p, (w i - y i)) + phi⁻¹ := by
    intro w
    show beta⁻¹ * Real.log (∑ j : Fin p, Real.exp (beta * (w j - y j)))
      ≤ (⨆ i : Fin p, (w i - y i)) + phi⁻¹
    have hsum : (∑ j : Fin p, Real.exp (beta * (w j - y j)))
        ≤ (p : ℝ) * Real.exp (beta * (⨆ i : Fin p, (w i - y i))) := by
      have hstep : ∀ j : Fin p, Real.exp (beta * (w j - y j))
          ≤ Real.exp (beta * (⨆ i : Fin p, (w i - y i))) := by
        intro j
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hM_ge w j) (le_of_lt hbeta_pos))
      calc (∑ j : Fin p, Real.exp (beta * (w j - y j)))
          ≤ ∑ j : Fin p, Real.exp (beta * (⨆ i : Fin p, (w i - y i))) :=
            Finset.sum_le_sum (fun j _ => hstep j)
        _ = (p : ℝ) * Real.exp (beta * (⨆ i : Fin p, (w i - y i))) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hexppos : (0 : ℝ) < Real.exp (beta * (⨆ i : Fin p, (w i - y i))) := Real.exp_pos _
    have hlog1 : Real.log (∑ j : Fin p, Real.exp (beta * (w j - y j)))
        ≤ Real.log ((p : ℝ) * Real.exp (beta * (⨆ i : Fin p, (w i - y i)))) :=
      Real.log_le_log (hS_pos w) hsum
    have hlog2 : Real.log ((p : ℝ) * Real.exp (beta * (⨆ i : Fin p, (w i - y i))))
        = Real.log (p : ℝ) + beta * (⨆ i : Fin p, (w i - y i)) := by
      rw [Real.log_mul hppos.ne' hexppos.ne', Real.log_exp]
    calc beta⁻¹ * Real.log (∑ j : Fin p, Real.exp (beta * (w j - y j)))
        ≤ beta⁻¹ * (Real.log (p : ℝ) + beta * (⨆ i : Fin p, (w i - y i))) := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (inv_pos.mpr hbeta_pos))
          exact le_trans hlog1 (le_of_eq hlog2)
      _ = (⨆ i : Fin p, (w i - y i)) + phi⁻¹ := by
          rw [mul_add, hbeta_inv_log, ← mul_assoc, inv_mul_cancel₀ hbeta_pos.ne', one_mul,
            add_comm]
  have hF_smooth : ContDiff ℝ 3 F := by
    show ContDiff ℝ 3
      (fun w : Fin p → ℝ => beta⁻¹ * Real.log (∑ j : Fin p, Real.exp (beta * (w j - y j))))
    have hlog : ContDiff ℝ 3
        (Real.log ∘ fun w : Fin p → ℝ => ∑ j : Fin p, Real.exp (beta * (w j - y j))) := by
      refine contDiffOn_univ.mp ?_
      exact Real.contDiffOn_log.comp hS_smooth.contDiffOn (fun w _ => ne_of_gt (hS_pos w))
    have hc : ContDiff ℝ 3 (fun _ : Fin p → ℝ => beta⁻¹) := contDiff_const
    have hmul := hc.mul hlog
    simpa only [Pi.mul_apply, Function.comp_def] using hmul
  have hkappa_smooth : ContDiff ℝ 3 kappa := by
    show ContDiff ℝ 3 (fun w : Fin p → ℝ => phi0 (phi * F w))
    have h1 : ContDiff ℝ 3 (fun w : Fin p → ℝ => phi * F w) := by
      have hc : ContDiff ℝ 3 (fun _ : Fin p → ℝ => phi) := contDiff_const
      have hmul := hc.mul hF_smooth
      simpa only [Pi.mul_apply] using hmul
    simpa only [Function.comp_def] using hphi0_smooth.comp h1
  have hrange : ∀ w : Fin p → ℝ, 0 ≤ kappa w ∧ kappa w ≤ 1 := by
    intro w
    exact hphi0_range (phi * F w)
  have h_i : ∀ w : Fin p → ℝ, (∀ j : Fin p, w j ≤ y j - phi⁻¹) → kappa w = 1 := by
    intro w hw
    show phi0 (phi * F w) = 1
    apply hphi0_left
    have hM : (⨆ i : Fin p, (w i - y i)) ≤ -phi⁻¹ := ciSup_le (fun i => by linarith [hw i])
    have h1 : F w ≤ 0 := by linarith [hF_le w]
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hphi_pos) h1
  have h_ii : ∀ w : Fin p → ℝ, phi⁻¹ ≤ (⨆ j : Fin p, (w j - y j)) → kappa w = 0 := by
    intro w hw
    show phi0 (phi * F w) = 0
    apply hphi0_right
    have h1 : phi⁻¹ ≤ F w := le_trans hw (hF_ge w)
    have h2 : phi * phi⁻¹ ≤ phi * F w := mul_le_mul_of_nonneg_left h1 (le_of_lt hphi_pos)
    rwa [mul_inv_cancel₀ hphi_pos.ne'] at h2
  have h_iii : ∀ (d : Fin 3 → Fin p) (w : Fin p → ℝ),
      ((⨆ i : Fin p, (w i - y i)) < -phi⁻¹ ∨ phi⁻¹ < (⨆ i : Fin p, (w i - y i))) →
      iteratedFDeriv ℝ 3 kappa w (fun t : Fin 3 => Pi.single (d t) (1 : ℝ)) = 0 := by
    intro d w hw
    rcases hw with hlt | hgt
    · have hlt' : ∀ i : Fin p, w i < y i - phi⁻¹ := by
        intro i
        have h1 := hM_ge w i
        linarith
      have hev : ∀ᶠ v : Fin p → ℝ in nhds w, ∀ i : Fin p, v i < y i - phi⁻¹ := by
        rw [Filter.eventually_all]
        intro i
        have hopen : IsOpen ((fun v : Fin p → ℝ => v i) ⁻¹' Set.Iio (y i - phi⁻¹)) :=
          isOpen_Iio.preimage (continuous_apply i)
        exact hopen.mem_nhds
          (show w ∈ (fun v : Fin p → ℝ => v i) ⁻¹' Set.Iio (y i - phi⁻¹) from hlt' i)
      have hwk : kappa w = 1 := h_i w (fun i => le_of_lt (hlt' i))
      have hmem : (fun _ : Fin p → ℝ => (1 : ℝ)) =ᶠ[nhdsWithin w Set.univ] kappa := by
        rw [nhdsWithin_univ]
        refine hev.mono ?_
        intro v hv
        exact (h_i v (fun i => le_of_lt (hv i))).symm
      have hvalWithin : iteratedFDerivWithin ℝ 3 (fun _ : Fin p → ℝ => (1 : ℝ)) Set.univ w
          = iteratedFDerivWithin ℝ 3 kappa Set.univ w :=
        Filter.EventuallyEq.iteratedFDerivWithin_eq (𝕜 := ℝ) (s := Set.univ) (f := kappa)
          (f₁ := fun _ : Fin p → ℝ => (1 : ℝ)) (x := w) hmem hwk.symm 3
      have hz : iteratedFDeriv ℝ 3 (fun _ : Fin p → ℝ => (1 : ℝ)) = 0 :=
        iteratedFDeriv_const_of_ne (by norm_num) 1
      rw [← iteratedFDerivWithin_univ, ← hvalWithin, iteratedFDerivWithin_univ, hz]
      simp
    · obtain ⟨i₀, hi₀⟩ : ∃ i : Fin p, phi⁻¹ < w i - y i := by
        by_contra hcon
        push_neg at hcon
        have hle : (⨆ i : Fin p, (w i - y i)) ≤ phi⁻¹ := ciSup_le hcon
        linarith
      have hev : ∀ᶠ v : Fin p → ℝ in nhds w, phi⁻¹ < v i₀ - y i₀ := by
        have hopen : IsOpen ((fun v : Fin p → ℝ => v i₀) ⁻¹' Set.Ioi (y i₀ + phi⁻¹)) :=
          isOpen_Ioi.preimage (continuous_apply i₀)
        have hset : ((fun v : Fin p → ℝ => v i₀) ⁻¹' Set.Ioi (y i₀ + phi⁻¹)) ∈ nhds w :=
          hopen.mem_nhds
            (show w ∈ (fun v : Fin p → ℝ => v i₀) ⁻¹' Set.Ioi (y i₀ + phi⁻¹) from by
              show y i₀ + phi⁻¹ < w i₀
              linarith)
        refine Filter.Eventually.mono hset (fun v hv => ?_)
        have hv1 : y i₀ + phi⁻¹ < v i₀ := hv
        linarith
      have hwk : kappa w = 0 := h_ii w (le_trans (le_of_lt hi₀) (hM_ge w i₀))
      have hmem : (fun _ : Fin p → ℝ => (0 : ℝ)) =ᶠ[nhdsWithin w Set.univ] kappa := by
        rw [nhdsWithin_univ]
        refine hev.mono ?_
        intro v hv
        have hv' : phi⁻¹ ≤ (⨆ i : Fin p, (v i - y i)) :=
          le_trans (le_of_lt hv) (hM_ge v i₀)
        exact (h_ii v hv').symm
      have hvalWithin : iteratedFDerivWithin ℝ 3 (fun _ : Fin p → ℝ => (0 : ℝ)) Set.univ w
          = iteratedFDerivWithin ℝ 3 kappa Set.univ w :=
        Filter.EventuallyEq.iteratedFDerivWithin_eq (𝕜 := ℝ) (s := Set.univ) (f := kappa)
          (f₁ := fun _ : Fin p → ℝ => (0 : ℝ)) (x := w) hmem hwk.symm 3
      have hz : iteratedFDeriv ℝ 3 (fun _ : Fin p → ℝ => (0 : ℝ)) = 0 :=
        iteratedFDeriv_zero_fun
      rw [← iteratedFDerivWithin_univ, ← hvalWithin, iteratedFDerivWithin_univ, hz]
      simp
  have h_supp : ∀ d : Fin 3 → Fin p,
      Function.support
          (fun w : Fin p → ℝ =>
            iteratedFDeriv ℝ 3 kappa w (fun t : Fin 3 => Pi.single (d t) (1 : ℝ)))
          ⊆ {w : Fin p → ℝ | -phi⁻¹ ≤ (⨆ j : Fin p, (w j - y j)) ∧
              (⨆ j : Fin p, (w j - y j)) ≤ phi⁻¹} := by
    intro d w hw
    have h1 : ¬ ((⨆ i : Fin p, (w i - y i)) < -phi⁻¹) := by
      intro h
      exact hw (h_iii d w (Or.inl h))
    have h2 : ¬ (phi⁻¹ < (⨆ i : Fin p, (w i - y i))) := by
      intro h
      exact hw (h_iii d w (Or.inr h))
    exact ⟨le_of_not_gt h1, le_of_not_gt h2⟩
  have h_sandwich : ∀ w : Fin p → ℝ,
      Set.indicator {w : Fin p → ℝ | ∀ j : Fin p, w j ≤ y j - phi⁻¹}
          (fun _ => (1 : ℝ)) w ≤ kappa w ∧
        kappa w ≤ Set.indicator {w : Fin p → ℝ | ∀ j : Fin p, w j ≤ y j + phi⁻¹}
          (fun _ => (1 : ℝ)) w := by
    intro w
    constructor
    · by_cases h : ∀ j : Fin p, w j ≤ y j - phi⁻¹
      · have hmem : w ∈ {w : Fin p → ℝ | ∀ j : Fin p, w j ≤ y j - phi⁻¹} := h
        rw [Set.indicator_of_mem hmem]
        simpa using le_of_eq (h_i w h).symm
      · have hmem : w ∉ {w : Fin p → ℝ | ∀ j : Fin p, w j ≤ y j - phi⁻¹} := h
        have hz : Set.indicator {w : Fin p → ℝ | ∀ j : Fin p, w j ≤ y j - phi⁻¹}
            (fun _ => (1 : ℝ)) w = 0 := by
          simp [Set.indicator, hmem]
        rw [hz]
        exact (hrange w).1
    · by_cases h : ∀ j : Fin p, w j ≤ y j + phi⁻¹
      · have hmem : w ∈ {w : Fin p → ℝ | ∀ j : Fin p, w j ≤ y j + phi⁻¹} := h
        rw [Set.indicator_of_mem hmem]
        simpa using (hrange w).2
      · have hmem : w ∉ {w : Fin p → ℝ | ∀ j : Fin p, w j ≤ y j + phi⁻¹} := h
        have hz : Set.indicator {w : Fin p → ℝ | ∀ j : Fin p, w j ≤ y j + phi⁻¹}
            (fun _ => (1 : ℝ)) w = 0 := by
          simp [Set.indicator, hmem]
        rw [hz]
        push_neg at h
        obtain ⟨j, hj⟩ := h
        have hle : phi⁻¹ ≤ (⨆ i : Fin p, (w i - y i)) :=
          le_trans (le_of_lt (by linarith : phi⁻¹ < w j - y j)) (hM_ge w j)
        exact le_of_eq (h_ii w hle)
  exact ⟨hkappa_smooth, hrange, h_i, h_ii, fun d w h => h_iii d w (Or.inl h),
    fun d w h => h_iii d w (Or.inr h), h_supp, h_sandwich⟩

  /- @proof-region region.target-node.session.dca13f7e30730842 end -/

end

end Statlib.Imported

