import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_2945293653_548ae0bd_878bb98d

namespace PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace DCFDirectionalTaylor
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `DCFDirectionalTaylor then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.DCFDirectionalTaylor))
noncomputable section

/-- A scalar directional Taylor bound. The second derivative bound is taken
at one common segment point; there is no sum of coordinate suprema. -/
theorem c2_directional_remainder (p : ℕ) (F : (Fin p → ℝ) → ℝ)
    (hf : ContDiff ℝ 2 F) (x d : Fin p → ℝ) (C : ℝ)
    (hC : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      |(fderiv ℝ (fun y => (fderiv ℝ F y) d) (x + s • d)) d| ≤ C) :
    |F (x+d) - F x - (fderiv ℝ F x) d| ≤ C/2 := by
  let g : ℝ → ℝ := fun s => F (x + s • d)
  let gp : ℝ → ℝ := fun s => (fderiv ℝ F (x+s • d)) d
  let gpp : ℝ → ℝ := fun s =>
    (fderiv ℝ (fun y => (fderiv ℝ F y) d) (x+s • d)) d
  have hFdiff : Differentiable ℝ F := hf.differentiable (by norm_num)
  have hGdiff : Differentiable ℝ (fun y => (fderiv ℝ F y) d) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable (by norm_num)
  have hcurve : ∀ s : ℝ, HasDerivAt (fun t : ℝ => x+t • d) d s := by
    intro s
    simpa using ((hasDerivAt_id s).smul_const d).const_add x
  have hg : ∀ s, HasDerivAt g (gp s) s := by
    intro s
    exact (hFdiff (x+s • d)).hasFDerivAt.comp_hasDerivAt s (hcurve s)
  have hgp : ∀ s, HasDerivAt gp (gpp s) s := by
    intro s
    exact (hGdiff (x+s • d)).hasFDerivAt.comp_hasDerivAt s (hcurve s)
  have hMVT : ∀ s ∈ Set.Icc (0 : ℝ) 1, |gp s-gp 0| ≤ C*s := by
    intro s hs
    have hdiff : ∀ t ∈ Set.Icc (0 : ℝ) s, DifferentiableAt ℝ gp t :=
      fun t _ => (hgp t).differentiableAt
    have hb : ∀ t ∈ Set.Icc (0 : ℝ) s, ‖deriv gp t‖ ≤ C := by
      intro t ht
      rw [(hgp t).deriv]
      exact hC t ⟨ht.1, le_trans ht.2 hs.2⟩
    have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hb (convex_Icc (0 : ℝ) s)
      ⟨le_rfl, hs.1⟩ ⟨hs.1, le_rfl⟩
    simpa [Real.norm_eq_abs, abs_of_nonneg hs.1] using h
  let Phi : ℝ → ℝ := fun t => g t-g 0-t*gp 0
  have hPhi : ∀ t, HasDerivAt Phi (gp t-gp 0) t := by
    intro t
    simpa using ((hg t).sub (hasDerivAt_const t (g 0))).sub
      ((hasDerivAt_id t).mul_const (gp 0))
  have hcont : Continuous (fun t => gp t-gp 0) :=
    (show Differentiable ℝ gp from fun t => (hgp t).differentiableAt).continuous.sub continuous_const
  have hFTC : g 1-g 0-gp 0 = ∫ s in (0 : ℝ)..1, gp s-gp 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := Phi) (a := (0 : ℝ)) (b := 1)
      (fun t _ => hPhi t) (hcont.intervalIntegrable 0 1)
    rw [h]
    dsimp [Phi]
    ring
  have hbound : |∫ s in (0 : ℝ)..1, gp s-gp 0| ≤ C/2 := by
    have h1 : |∫ s in (0 : ℝ)..1, gp s-gp 0| ≤ ∫ s in (0 : ℝ)..1, |gp s-gp 0| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    have h2 : (∫ s in (0 : ℝ)..1, |gp s-gp 0|) ≤ ∫ s in (0 : ℝ)..1, C*s := by
      exact intervalIntegral.integral_mono_on (by norm_num)
        (hcont.abs.intervalIntegrable 0 1)
        ((continuous_const.mul continuous_id).intervalIntegrable 0 1) hMVT
    have h3 : (∫ s in (0 : ℝ)..1, C*s) = C/2 := by
      rw [intervalIntegral.integral_const_mul]
      have hid : (∫ s in (0 : ℝ)..1, s) = 1/2 := by
        have hd : ∀ t : ℝ, HasDerivAt (fun u : ℝ => (1/2)*(u*u)) t t := by
          intro t
          have hbase : HasDerivAt (fun u : ℝ => (1/2)*(u*u)) ((1/2)*(t+t)) t := by
            simpa [smul_eq_mul] using
              ((hasDerivAt_id t).smul (hasDerivAt_id t)).const_mul ((1 : ℝ)/2)
          convert hbase using 1
          ring
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := fun u : ℝ => (1/2)*(u*u)) (f' := fun s : ℝ => s)
          (fun t _ => hd t) (continuous_id.intervalIntegrable 0 1)]
        norm_num
      rw [hid]
      ring
    exact le_trans h1 (le_trans h2 h3.le)
  have hmain : |g 1-g 0-gp 0| ≤ C/2 := by rw [hFTC]; exact hbound
  simpa [g, gp] using hmain

/-- Expansion respects the direction order outer x, middle y, final z. -/
theorem nested_trilinear_coordinates (p : ℕ)
    (T : (Fin p → ℝ) →L[ℝ] ((Fin p → ℝ) →L[ℝ] ((Fin p → ℝ) →L[ℝ] ℝ)))
    (x y z : Fin p → ℝ) :
    ((T x) y) z = ∑ j, ∑ k, ∑ l,
      ((T (Pi.single j 1)) (Pi.single k 1)) (Pi.single l 1) * x j * y k * z l := by
  have hexp (d : Fin p → ℝ) : (∑ j, d j • (Pi.single j (1 : ℝ) : Fin p → ℝ)) = d := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      rw [Pi.single_eq_of_ne (Ne.symm hb), mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  calc ((T x) y) z = ((T (∑ j, x j • (Pi.single j 1 : Fin p → ℝ)))
      (∑ k, y k • (Pi.single k 1 : Fin p → ℝ))) (∑ l, z l • (Pi.single l 1 : Fin p → ℝ)) := by
        rw [hexp x, hexp y, hexp z]
    _ = ∑ l, ∑ k, ∑ j,
        ((T (Pi.single j 1)) (Pi.single k 1)) (Pi.single l 1) * x j * y k * z l := by
      simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.smul_apply, Finset.mul_sum, smul_eq_mul]
      refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ =>
        Finset.sum_congr rfl (fun j _ => ?_)))
      ring
    _ = ∑ l, ∑ j, ∑ k,
        ((T (Pi.single j 1)) (Pi.single k 1)) (Pi.single l 1) * x j * y k * z l :=
      Finset.sum_congr rfl (fun l _ => Finset.sum_comm)
    _ = ∑ j, ∑ l, ∑ k,
        ((T (Pi.single j 1)) (Pi.single k 1)) (Pi.single l 1) * x j * y k * z l := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun j _ => Finset.sum_comm)

/-- Pointwise common-point total derivative budget controls any directions,
without taking a supremum of each coordinate separately. -/
theorem nested_trilinear_bound (p : ℕ) (hp : 0 < p)
    (T : (Fin p → ℝ) →L[ℝ] ((Fin p → ℝ) →L[ℝ] ((Fin p → ℝ) →L[ℝ] ℝ)))
    (x y z : Fin p → ℝ) (B : ℝ)
    (hB : (∑ j, ∑ k, ∑ l,
      |((T (Pi.single j 1)) (Pi.single k 1)) (Pi.single l 1)|) ≤ B) :
    |((T x) y) z| ≤ B * Statlib.Imported.maxAbs x * Statlib.Imported.maxAbs y * Statlib.Imported.maxAbs z := by
  have hcoord (d : Fin p → ℝ) (j : Fin p) : |d j| ≤ Statlib.Imported.maxAbs d := by
    exact le_ciSup (Set.finite_range (fun j : Fin p => |d j|)).bddAbove j
  have hnonneg (d : Fin p → ℝ) : 0 ≤ Statlib.Imported.maxAbs d :=
    le_trans (abs_nonneg (d ⟨0,hp⟩)) (hcoord d ⟨0,hp⟩)
  rw [nested_trilinear_coordinates]
  calc |∑ j, ∑ k, ∑ l,
      ((T (Pi.single j 1)) (Pi.single k 1)) (Pi.single l 1) * x j * y k * z l|
      ≤ ∑ j, ∑ k, ∑ l,
        |((T (Pi.single j 1)) (Pi.single k 1)) (Pi.single l 1)| *
          Statlib.Imported.maxAbs x * Statlib.Imported.maxAbs y * Statlib.Imported.maxAbs z := by
        calc _ ≤ ∑ j, |∑ k, ∑ l,
            ((T (Pi.single j 1)) (Pi.single k 1)) (Pi.single l 1) * x j * y k * z l| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ _ := by
            refine Finset.sum_le_sum (fun j _ => ?_)
            calc _ ≤ ∑ k, |∑ l,
                ((T (Pi.single j 1)) (Pi.single k 1)) (Pi.single l 1) * x j * y k * z l| :=
                  Finset.abs_sum_le_sum_abs _ _
              _ ≤ _ := by
                refine Finset.sum_le_sum (fun k _ => ?_)
                calc _ ≤ ∑ l,
                    |((T (Pi.single j 1)) (Pi.single k 1)) (Pi.single l 1) * x j * y k * z l| :=
                      Finset.abs_sum_le_sum_abs _ _
                  _ ≤ _ := by
                    refine Finset.sum_le_sum (fun l _ => ?_)
                    simp only [abs_mul]
                    exact mul_le_mul
                      (mul_le_mul (mul_le_mul_of_nonneg_left (hcoord x j) (abs_nonneg _))
                        (hcoord y k) (abs_nonneg _) (mul_nonneg (abs_nonneg _) (hnonneg x)))
                      (hcoord z l) (abs_nonneg _)
                      (mul_nonneg (mul_nonneg (abs_nonneg _) (hnonneg x)) (hnonneg y))
    _ = (∑ j, ∑ k, ∑ l,
      |((T (Pi.single j 1)) (Pi.single k 1)) (Pi.single l 1)|) *
        Statlib.Imported.maxAbs x * Statlib.Imported.maxAbs y * Statlib.Imported.maxAbs z := by
          simp only [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB (hnonneg x)) (hnonneg y)) (hnonneg z)

/-- Three directional slots are outer a, middle b, and final c, respectively. -/
theorem derivative_eval_third (p : ℕ) (f : (Fin p → ℝ) → ℝ)
    (hf : ContDiff ℝ 3 f) (w a b c : Fin p → ℝ) :
    (fderiv ℝ (fun y => (fderiv ℝ (fun z => (fderiv ℝ f z) c) y) b) w) a =
      (((fderiv ℝ (fderiv ℝ (fderiv ℝ f)) w) a) b) c := by
  have hstep : ∀ {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
      (F : (Fin p → ℝ) → ((Fin p → ℝ) →L[ℝ] H)) (y u : Fin p → ℝ),
      DifferentiableAt ℝ F y → fderiv ℝ (fun z => F z u) y = (fderiv ℝ F y).flip u := by
    intro H _ _ F y u hF
    have h0 : fderiv ℝ (fun _ : Fin p → ℝ => u) y = 0 := by
      simpa using congrArg
        (fun f : (Fin p → ℝ) →L[ℝ] ((Fin p → ℝ) →L[ℝ] H) => f y)
        (fderiv_const (𝕜 := ℝ) (E := Fin p → ℝ) (F := (Fin p → ℝ) →L[ℝ] H) u)
    have h := fderiv_clm_apply (c := F) (u := fun _ : Fin p → ℝ => u) (x := y)
      hF (differentiableAt_const u)
    rw [h0] at h
    simpa using h
  have hstepA : ∀ {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
      (F : (Fin p → ℝ) → ((Fin p → ℝ) →L[ℝ] H)) (y u t : Fin p → ℝ),
      DifferentiableAt ℝ F y →
        (fderiv ℝ (fun z => F z u) y) t = ((fderiv ℝ F y) t) u := by
    intro H _ _ F y u t hF
    simp only [hstep F y u hF, ContinuousLinearMap.flip_apply]
  have hfd1 : Differentiable ℝ (fderiv ℝ f) :=
    ContDiff.differentiable (ContDiff.fderiv_right hf (m := 2) (by norm_num)) (by norm_num)
  have hfd2 : Differentiable ℝ (fderiv ℝ (fderiv ℝ f)) :=
    ContDiff.differentiable
      (ContDiff.fderiv_right (ContDiff.fderiv_right hf (m := 2) (by norm_num))
        (m := 1) (by norm_num)) (by norm_num)
  have hbr : ∀ (w t u v : Fin p → ℝ),
      (fderiv ℝ (fun y => (fderiv ℝ (fun z => (fderiv ℝ f z) v) y) u) w) t
        = (((fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ f z) y) w) t) u) v := by
    intro w t u v
    have hHd : DifferentiableAt ℝ
        (fun y : Fin p → ℝ => (fderiv ℝ (fun z => fderiv ℝ f z) y) u) w :=
      (hfd2.clm_apply (differentiable_const u)).differentiableAt
    have e1 : (fderiv ℝ (fun y => ((fderiv ℝ (fun z => fderiv ℝ f z) y) u) v) w) t
        = ((fderiv ℝ (fun y => (fderiv ℝ (fun z => fderiv ℝ f z) y) u) w) t) v :=
      hstepA (fun y => (fderiv ℝ (fun z => fderiv ℝ f z) y) u) w v t hHd
    have e2 : ((fderiv ℝ (fun y => (fderiv ℝ (fun z => fderiv ℝ f z) y) u) w) t) v
        = (((fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ f z) y) w) t) u) v :=
      congrArg (fun g : (Fin p → ℝ) →L[ℝ] ℝ => g v)
        (hstepA (fun y => fderiv ℝ (fun z => fderiv ℝ f z) y) w u t
          hfd2.differentiableAt)
    have e0 : (fun y => (fderiv ℝ (fun z => (fderiv ℝ f z) v) y) u)
        = fun y => ((fderiv ℝ (fun z => fderiv ℝ f z) y) u) v := by
      funext y
      exact (congrArg (fun g : (Fin p → ℝ) →L[ℝ] ℝ => g u)
        (hstep (fderiv ℝ f) y v hfd1.differentiableAt)).trans
        (ContinuousLinearMap.flip_apply (fderiv ℝ (fderiv ℝ f) y) u v)
    simp only [e0, e1, e2]

  exact hbr w a b c

/-- Whole-direction Taylor remainder from the total third-coordinate budget at
one common segment point. No coordinatewise suprema occur anywhere. -/
theorem whole_direction_remainder (p : ℕ) (hp : 0 < p)
    (f : (Fin p → ℝ) → ℝ) (hf : ContDiff ℝ 3 f)
    (W U D : Fin p → ℝ) (B : ℝ)
    (hB : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∑ j, ∑ k, ∑ l,
        |(((fderiv ℝ (fderiv ℝ (fderiv ℝ f)) (W+s • U))
          (Pi.single j 1)) (Pi.single k 1)) (Pi.single l 1)|) ≤ B) :
    |(fderiv ℝ f (W+U)) D - (fderiv ℝ f W) D -
      (fderiv ℝ (fun y => (fderiv ℝ f y) D) W) U| ≤
        (B/2) * (Statlib.Imported.maxAbs U)^2 * Statlib.Imported.maxAbs D := by
  have hF : ContDiff ℝ 2 (fun y => (fderiv ℝ f y) D) :=
    (hf.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const
  have hC : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      |(fderiv ℝ (fun y => (fderiv ℝ (fun z => (fderiv ℝ f z) D) y) U)
        (W+s • U)) U| ≤ B*(Statlib.Imported.maxAbs U)^2*Statlib.Imported.maxAbs D := by
    intro s hs
    rw [derivative_eval_third p f hf (W+s • U) U U D]
    calc |(((fderiv ℝ (fderiv ℝ (fderiv ℝ f)) (W+s • U)) U) U) D|
        ≤ B * Statlib.Imported.maxAbs U * Statlib.Imported.maxAbs U *
          Statlib.Imported.maxAbs D :=
            nested_trilinear_bound p hp _ U U D B (hB s hs)
      _ = _ := by ring
  have h := c2_directional_remainder p (fun y => (fderiv ℝ f y) D) hF W U
    (B*(Statlib.Imported.maxAbs U)^2*Statlib.Imported.maxAbs D) hC
  calc _ ≤ (B*(Statlib.Imported.maxAbs U)^2*Statlib.Imported.maxAbs D)/2 := h
    _ = _ := by ring

theorem iterated_third_eq_nested (p : ℕ) (f : (Fin p → ℝ) → ℝ)
    (w a b c : Fin p → ℝ) :
    (iteratedFDeriv ℝ 3 f w) ![a,b,c] =
      (((fderiv ℝ (fderiv ℝ (fderiv ℝ f)) w) a) b) c := by
  rw [iteratedFDeriv_succ_apply_right (n := 2)]
  rw [iteratedFDeriv_succ_apply_right (n := 1)]
  rw [iteratedFDeriv_one_apply]
  rfl

/-- Same bound in the actual source iteratedFDeriv API. -/
theorem whole_direction_remainder_iterated (p : ℕ) (hp : 0 < p)
    (f : (Fin p → ℝ) → ℝ) (hf : ContDiff ℝ 3 f)
    (W U D : Fin p → ℝ) (B : ℝ)
    (hB : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∑ j, ∑ k, ∑ l, |(iteratedFDeriv ℝ 3 f (W+s • U))
        ![Pi.single j 1, Pi.single k 1, Pi.single l 1]|) ≤ B) :
    |(fderiv ℝ f (W+U)) D - (fderiv ℝ f W) D -
      (fderiv ℝ (fun y => (fderiv ℝ f y) D) W) U| ≤
        (B/2) * (Statlib.Imported.maxAbs U)^2 * Statlib.Imported.maxAbs D := by
  apply whole_direction_remainder p hp f hf W U D B
  intro s hs
  simpa only [iterated_third_eq_nested] using hB s hs

/-- Evaluation of the derivative-valued map in its final argument. -/
theorem derivative_eval_two (p : ℕ) (f : (Fin p → ℝ) → ℝ)
    (hf : ContDiff ℝ 3 f) (w u d : Fin p → ℝ) :
    (fderiv ℝ (fun y => (fderiv ℝ f y) d) w) u =
      ((fderiv ℝ (fderiv ℝ f) w) u) d := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) w :=
    ((hf.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num)) w
  have h0 : fderiv ℝ (fun _ : Fin p → ℝ => d) w = 0 := by
    simpa using congrArg
      (fun z : (Fin p → ℝ) →L[ℝ] ((Fin p → ℝ) →L[ℝ] ℝ) => z w)
      (fderiv_const (𝕜 := ℝ) (E := Fin p → ℝ) (F := (Fin p → ℝ) →L[ℝ] ℝ) d)
  have h := fderiv_clm_apply (c := fderiv ℝ f) (u := fun _ : Fin p → ℝ => d) (x := w)
    hfd (differentiableAt_const d)
  rw [h0] at h
  have hstep : fderiv ℝ (fun y => (fderiv ℝ f y) d) w =
      (fderiv ℝ (fderiv ℝ f) w).flip d := by simpa using h
  rw [hstep]
  rfl

theorem clm_coordinates (p : ℕ) (L : (Fin p → ℝ) →L[ℝ] ℝ) (d : Fin p → ℝ) :
    L d = ∑ j, L (Pi.single j 1) * d j := by
  have hsum : (∑ j, d j • (Pi.single j (1 : ℝ) : Fin p → ℝ)) = d := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      rw [Pi.single_eq_of_ne (Ne.symm hb), mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  rw [← hsum]
  simp only [map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hsum]
  ring

/-- Exact equality between the sum of source coordinate remainders times D_j
and the single whole-direction remainder. This is the bad-branch replacement. -/
theorem weighted_coordinate_remainder_eq (p : ℕ) (f : (Fin p → ℝ) → ℝ)
    (hf : ContDiff ℝ 3 f) (W U D : Fin p → ℝ) :
    (∑ j, ((fderiv ℝ f (W+U)) (Pi.single j 1) -
        (fderiv ℝ f W) (Pi.single j 1) -
        ∑ k, (fderiv ℝ (fun z => (fderiv ℝ f z) (Pi.single j 1)) W)
          (Pi.single k 1) * U k) * D j) =
      (fderiv ℝ f (W+U)) D - (fderiv ℝ f W) D -
        (fderiv ℝ (fun y => (fderiv ℝ f y) D) W) U := by
  have hsecond : (fderiv ℝ (fun y => (fderiv ℝ f y) D) W) U =
      ∑ j, (∑ k, (fderiv ℝ (fun z => (fderiv ℝ f z) (Pi.single j 1)) W)
        (Pi.single k 1) * U k) * D j := by
    rw [derivative_eval_two p f hf W U D,
      clm_coordinates p ((fderiv ℝ (fderiv ℝ f) W) U) D]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← derivative_eval_two p f hf W U (Pi.single j 1),
      clm_coordinates p (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j 1)) W) U]
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [← clm_coordinates p (fderiv ℝ f (W+U)) D,
    ← clm_coordinates p (fderiv ℝ f W) D, ← hsecond]

theorem whole_coordinate_remainder_bound (p : ℕ) (hp : 0 < p)
    (f : (Fin p → ℝ) → ℝ) (hf : ContDiff ℝ 3 f)
    (W U D : Fin p → ℝ) (B : ℝ)
    (hB : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∑ j, ∑ k, ∑ l, |(iteratedFDeriv ℝ 3 f (W+s • U))
        ![Pi.single j 1, Pi.single k 1, Pi.single l 1]|) ≤ B) :
    |∑ j, ((fderiv ℝ f (W+U)) (Pi.single j 1) -
        (fderiv ℝ f W) (Pi.single j 1) -
        ∑ k, (fderiv ℝ (fun z => (fderiv ℝ f z) (Pi.single j 1)) W)
          (Pi.single k 1) * U k) * D j| ≤
      (B/2) * (Statlib.Imported.maxAbs U)^2 * Statlib.Imported.maxAbs D := by
  rw [weighted_coordinate_remainder_eq p f hf W U D]
  exact whole_direction_remainder_iterated p hp f hf W U D B hB

/-- Drop-in source form: use the existing hTaylor and the common-point Q sum budget. -/
theorem whole_coordinate_remainder_majorant (p : ℕ) (hp : 0 < p)
    (f : (Fin p → ℝ) → ℝ) (hf : ContDiff ℝ 3 f)
    (W U D : Fin p → ℝ)
    (Q : Fin p → Fin p → Fin p → (Fin p → ℝ) → ℝ) (B : ℝ)
    (hdom : ∀ (d : Fin 3 → Fin p) (w : Fin p → ℝ),
      |(iteratedFDeriv ℝ 3 f w) (fun s : Fin 3 => Pi.single (d s) (1 : ℝ))| ≤
        Q (d 0) (d 1) (d 2) w)
    (hbudget : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∑ j, ∑ k, ∑ l, Q j k l (W+s • U)) ≤ B) :
    |∑ j, ((fderiv ℝ f (W+U)) (Pi.single j 1) -
        (fderiv ℝ f W) (Pi.single j 1) -
        ∑ k, (fderiv ℝ (fun z => (fderiv ℝ f z) (Pi.single j 1)) W)
          (Pi.single k 1) * U k) * D j| ≤
      (B/2) * (Statlib.Imported.maxAbs U)^2 * Statlib.Imported.maxAbs D := by
  apply whole_coordinate_remainder_bound p hp f hf W U D B
  intro s hs
  apply le_trans _ (hbudget s hs)
  refine Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ =>
    Finset.sum_le_sum (fun l _ => ?_)))
  have h := hdom (![j,k,l] : Fin 3 → Fin p) (W+s • U)
  have hvec : (fun a : Fin 3 => Pi.single ((![j,k,l] : Fin 3 → Fin p) a) (1 : ℝ)) =
      ![Pi.single j (1 : ℝ), Pi.single k (1 : ℝ), Pi.single l (1 : ℝ)] := by
    funext a
    fin_cases a <;> rfl
  rw [hvec] at h
  simpa using h

/-- Per-coordinate source Taylor bound, expressed directly through the iterated
third derivative. The three slots are exactly (e_l,e_k,e_j). -/
theorem coordinate_Taylor_iterated (p : ℕ) (f : (Fin p → ℝ) → ℝ)
    (hf : ContDiff ℝ 3 f) (W U : Fin p → ℝ) (j : Fin p)
    (Q : Fin p → Fin p → ℝ)
    (hQ : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ k l : Fin p,
      |(iteratedFDeriv ℝ 3 f (W+s • U))
        ![Pi.single l 1, Pi.single k 1, Pi.single j 1]| ≤ Q k l) :
    |(fderiv ℝ f (W+U)) (Pi.single j 1) -
      (fderiv ℝ f W) (Pi.single j 1) -
      ∑ k, (fderiv ℝ (fun z => (fderiv ℝ f z) (Pi.single j 1)) W)
        (Pi.single k 1) * U k| ≤
      (1/2) * ∑ k, ∑ l, Q k l * |U k| * |U l| := by
  apply Statlib.Imported.statopia_math_node_2945293653_548ae0bd p f hf W U j Q
  intro s hs k l
  rw [derivative_eval_third p f hf (W+s • U)
    (Pi.single l 1) (Pi.single k 1) (Pi.single j 1)]
  rw [← iterated_third_eq_nested p f (W+s • U)
    (Pi.single l 1) (Pi.single k 1) (Pi.single j 1)]
  exact hQ s hs k l




end
end DCFDirectionalTaylor

