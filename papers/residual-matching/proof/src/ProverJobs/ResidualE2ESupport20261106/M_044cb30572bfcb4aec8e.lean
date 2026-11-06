import Statlib.RandomMatrix.SampleCovariance.LeaveOneOut.ResolventEntryBound
import Statlib.RandomMatrix.SampleCovariance.MarchenkoPastur
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053

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
theorem statopia_math_node_2041753363_bb646534 : ∀ (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (p : ℝ) (hp : 0 < p)
    (z : ℂ) (hz : 0 < z.im)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xi Mask : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hXi_meas : ∀ i j, Measurable fun ω => Xi ω i j)
    (hMask_meas : ∀ i j, Measurable fun ω => Mask ω i j),
    IsProbabilityMeasure (stdNormalMatrixMeasure m n) ∧
      Integrable (fun ω : Ω =>
        (((m : ℝ) + (n : ℝ))⁻¹ : ℂ) *
          (((z : ℂ) • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) -
            (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
              (maskedScaled p (Xi ω) (Mask ω))
              (Matrix.transpose (maskedScaled p (Xi ω) (Mask ω)))
              (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)⁻¹).trace) μ ∧
        (∀ ω : Ω,
          ‖(((m : ℝ) + (n : ℝ))⁻¹ : ℂ) *
            (((z : ℂ) • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) -
              (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
                (maskedScaled p (Xi ω) (Mask ω))
                (Matrix.transpose (maskedScaled p (Xi ω) (Mask ω)))
                (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)⁻¹).trace‖ ≤
            z.im⁻¹) ∧
          Integrable (fun g : Fin m → Fin n → ℝ =>
            (((m : ℝ) + (n : ℝ))⁻¹ : ℂ) *
              (((z : ℂ) • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) -
                (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
                  (Matrix.of (fun (i : Fin m) (j : Fin n) => g i j / Real.sqrt (m : ℝ)))
                  (Matrix.transpose
                    (Matrix.of (fun (i : Fin m) (j : Fin n) => g i j / Real.sqrt (m : ℝ))))
                  (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)⁻¹).trace)
            (stdNormalMatrixMeasure m n) ∧
            (∀ g : Fin m → Fin n → ℝ,
              ‖(((m : ℝ) + (n : ℝ))⁻¹ : ℂ) *
                (((z : ℂ) • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) -
                  (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
                    (Matrix.of (fun (i : Fin m) (j : Fin n) => g i j / Real.sqrt (m : ℝ)))
                    (Matrix.transpose
                      (Matrix.of (fun (i : Fin m) (j : Fin n) => g i j / Real.sqrt (m : ℝ))))
                    (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)⁻¹).trace‖ ≤
              z.im⁻¹) := by
  /- @proof-region region.target-node.session.b223158b4b584452 begin -/
  intro m n hm hn p hp z hz Ω hΩ μ hμ Xi Mask hXi_meas hMask_meas
  have hprob : IsProbabilityMeasure (stdNormalMatrixMeasure m n) := by
    unfold stdNormalMatrixMeasure
    infer_instance
  have p1 : ∀ (A : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ), IsUnit A ↔ IsUnit A.det :=
    fun A => Matrix.isUnit_iff_isUnit_det A
  have p2 : ∀ (A : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ), IsUnit A.det → A⁻¹ * A = 1 :=
    fun A h => Matrix.nonsing_inv_mul A h
  have p3 : ∀ (A : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ), IsUnit A.det → A * A⁻¹ = 1 :=
    fun A h => Matrix.mul_nonsing_inv A h
  have p4 : ∀ (A : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ),
      (-A).det = (-1) ^ (Fintype.card (Fin m ⊕ Fin n)) * A.det :=
    fun A => Matrix.det_neg A
  have p7 : ∀ a : ℂ, Ring.inverse a = a⁻¹ := fun a => Ring.inverse_eq_inv a
  have p9 : Measurable (fun ω : Ω => maskedScaled p (Xi ω) (Mask ω)) := by
    unfold maskedScaled
    exact measurable_pi_iff.2 (fun i => measurable_pi_iff.2 (fun j =>
      ((hMask_meas i j).mul (hXi_meas i j)).div_const (Real.sqrt ((m : ℝ) * p))))
  have htr : Measurable (fun M : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ => M.trace) := by
    simp only [Matrix.trace]
    exact Finset.measurable_sum _ (fun i _ => (measurable_pi_apply i).comp (measurable_pi_apply i))
  have hdet : Measurable (fun M : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ => M.det) := by
    simp only [Matrix.det_apply']
    refine Finset.measurable_sum _ (fun σ _ => ?_)
    exact Measurable.const_mul (Finset.measurable_prod _
      (fun i _ => (measurable_pi_apply i).comp (measurable_pi_apply (σ i)))) _
  have hupd : ∀ (j : Fin m ⊕ Fin n) (v : Fin m ⊕ Fin n → ℂ), Measurable
      (fun M : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ => M.updateRow j v) := by
    intro j v
    refine measurable_pi_iff.2 (fun a => measurable_pi_iff.2 (fun b => ?_))
    by_cases hab : a = j
    · have h1 : (fun M : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ =>
          (M.updateRow j v) a b) = fun _ => v b := by
        funext M
        simp [Matrix.updateRow, hab]
      rw [h1]
      exact measurable_const
    · have h1 : (fun M : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ =>
          (M.updateRow j v) a b) = fun M => M a b := by
        funext M
        simp [Matrix.updateRow, hab]
      rw [h1]
      exact (measurable_pi_apply b).comp (measurable_pi_apply a)
  have hadj : ∀ (i j : Fin m ⊕ Fin n), Measurable
      (fun M : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ => M.adjugate i j) := by
    intro i j
    have h1 : (fun M : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ => M.adjugate i j)
        = fun M => (M.updateRow j (Pi.single i (1 : ℂ))).det := by
      funext M
      exact Matrix.adjugate_apply M i j
    rw [h1]
    exact hdet.comp (hupd j (Pi.single i (1 : ℂ)))
  have hring : Measurable (fun a : ℂ => Ring.inverse a) := by
    have h1 : (fun a : ℂ => Ring.inverse a) = fun a => a⁻¹ := funext p7
    rw [h1]
    exact measurable_inv
  have hInvEntry : ∀ (i j : Fin m ⊕ Fin n), Measurable
      (fun M : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ => M⁻¹ i j) := by
    intro i j
    have h1 : (fun M : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ => M⁻¹ i j)
        = fun M => Ring.inverse M.det * M.adjugate i j := by
      funext M
      rw [Matrix.inv_def]
      simp
    rw [h1]
    exact (hring.comp hdet).mul (hadj i j)
  have hMinvTr : Measurable (fun M : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ => (M⁻¹).trace) := by
    simp only [Matrix.trace]
    exact Finset.measurable_sum _ (fun i _ => hInvEntry i i)
  have hnegInv : ∀ (N : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ), IsUnit N → (-N)⁻¹ = -(N⁻¹) := by
    intro N hN
    have hdn : IsUnit N.det := (p1 N).1 hN
    have h1 : N⁻¹ * N = 1 := p2 N hdn
    have hUn : IsUnit (-N) := hN.neg
    have hdn' : IsUnit ((-N).det) := (p1 (-N)).1 hUn
    have h2 : (-N)⁻¹ * (-N) = 1 := p2 (-N) hdn'
    exact (Matrix.left_inv_eq_left_inv (show (-(N⁻¹)) * (-N) = 1 by rw [neg_mul_neg, h1]) h2).symm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (m : ℝ) + (n : ℝ) := by linarith
  have hermBlocks : ∀ (A : Matrix (Fin m) (Fin n) ℝ),
      ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) A (Matrix.transpose A)
        (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal).IsHermitian := by
    intro A
    have hmap : ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) A (Matrix.transpose A)
        (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)
        = Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) (A.map Complex.ofReal)
          ((Matrix.transpose A).map Complex.ofReal) (0 : Matrix (Fin n) (Fin n) ℂ) := by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.fromBlocks]
    rw [hmap]
    refine Matrix.IsHermitian.fromBlocks ?_ ?_ ?_
    · simp [Matrix.IsHermitian]
    · ext i j
      simp [Matrix.conjTranspose_apply, Complex.conj_ofReal]
    · simp [Matrix.IsHermitian]
  have hbound : ∀ (B : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ),
      (B.map Complex.ofReal).IsHermitian →
      ‖(((m : ℝ) + (n : ℝ))⁻¹ : ℂ) *
        ((((z : ℂ) • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) -
          (B.map Complex.ofReal))⁻¹).trace)‖ ≤ z.im⁻¹ := by
    intro B hH
    have hUm : IsUnit ((B.map Complex.ofReal) - z • 1) :=
      Matrix.IsHermitian.isUnit_sub_smul_one (B.map Complex.ofReal) hH z hz.ne'
    have hentry : ∀ (i j : Fin m ⊕ Fin n),
        ‖(((B.map Complex.ofReal) - z • 1)⁻¹) i j‖ ≤ 1 / z.im := by
      intro i j
      exact Statlib.RandomMatrix.leaveOneOut_resolvent_entry_bound B z hH hz hUm i j
    have hneg : (((z : ℂ) • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) -
        (B.map Complex.ofReal))⁻¹) = -(((B.map Complex.ofReal) - z • 1)⁻¹) := by
      have h1 : (z : ℂ) • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) - (B.map Complex.ofReal)
          = -((B.map Complex.ofReal) - z • 1) := by rw [neg_sub]
      rw [h1]
      exact hnegInv _ hUm
    have htraceM : ‖(((B.map Complex.ofReal) - z • 1)⁻¹).trace‖ ≤
        ((m : ℝ) + (n : ℝ)) * z.im⁻¹ := by
      simp only [Matrix.trace]
      calc ‖∑ i : Fin m ⊕ Fin n, (((B.map Complex.ofReal) - z • 1)⁻¹) i i‖
          ≤ ∑ i : Fin m ⊕ Fin n, ‖(((B.map Complex.ofReal) - z • 1)⁻¹) i i‖ := norm_sum_le _ _
        _ ≤ ∑ _i : Fin m ⊕ Fin n, (1 / z.im) := Finset.sum_le_sum (fun i _ => hentry i i)
        _ = ((m : ℝ) + (n : ℝ)) * z.im⁻¹ := by
            have hcard : ((Fintype.card (Fin m ⊕ Fin n) : ℕ) : ℝ) = (m : ℝ) + (n : ℝ) := by
              simp [Fintype.card_sum]
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            rw [hcard]
            simp
    have hsum_cast : (((m : ℝ) : ℂ) + ((n : ℝ) : ℂ)) = ((↑((m : ℝ) + (n : ℝ))) : ℂ) := by
      push_cast
      ring
    have harg_norm : ‖(((m : ℝ) : ℂ) + ((n : ℝ) : ℂ))‖ = ((m : ℝ) + (n : ℝ)) := by
      rw [hsum_cast]
      simpa [abs_of_pos hpos] using Complex.norm_real ((m : ℝ) + (n : ℝ))
    have hcnorm : ‖(((m : ℝ) + (n : ℝ))⁻¹ : ℂ)‖ = ((m : ℝ) + (n : ℝ))⁻¹ := by
      rw [norm_inv, harg_norm]
    rw [hneg]
    calc ‖(((m : ℝ) + (n : ℝ))⁻¹ : ℂ) * (-(((B.map Complex.ofReal) - z • 1)⁻¹)).trace‖
        = ‖(((m : ℝ) + (n : ℝ))⁻¹ : ℂ)‖ *
          ‖(-(((B.map Complex.ofReal) - z • 1)⁻¹)).trace‖ := norm_mul _ _
      _ = ((m : ℝ) + (n : ℝ))⁻¹ * ‖(((B.map Complex.ofReal) - z • 1)⁻¹).trace‖ := by
          have htrneg : (-(((B.map Complex.ofReal) - z • 1)⁻¹)).trace
              = -(((B.map Complex.ofReal) - z • 1)⁻¹).trace := by
            simp [Matrix.trace]
          rw [hcnorm, htrneg, norm_neg]
      _ ≤ ((m : ℝ) + (n : ℝ))⁻¹ * (((m : ℝ) + (n : ℝ)) * z.im⁻¹) :=
          mul_le_mul_of_nonneg_left htraceM (le_of_lt (inv_pos.2 hpos))
      _ = z.im⁻¹ := by
          have hne : ((m : ℝ) + (n : ℝ)) ≠ 0 := ne_of_gt hpos
          have hzne : z.im ≠ 0 := hz.ne'
          field_simp
  have hCM : Measurable (fun A : Matrix (Fin m) (Fin n) ℝ =>
      (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) A (Matrix.transpose A)
        (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal) := by
    refine measurable_pi_iff.2 (fun a => measurable_pi_iff.2 (fun b => ?_))
    rcases a with a | a <;> rcases b with b | b
    · have h1 : (fun A : Matrix (Fin m) (Fin n) ℝ =>
          ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) A (Matrix.transpose A)
            (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal) (Sum.inl a) (Sum.inl b))
          = fun _ => (0 : ℂ) := by
        funext A
        simp [Matrix.map, Matrix.fromBlocks]
      rw [h1]
      exact measurable_const
    · have h1 : (fun A : Matrix (Fin m) (Fin n) ℝ =>
          ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) A (Matrix.transpose A)
            (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal) (Sum.inl a) (Sum.inr b))
          = fun A => Complex.ofReal (A a b) := by
        funext A
        simp [Matrix.map, Matrix.fromBlocks]
      rw [h1]
      exact Complex.measurable_ofReal.comp ((measurable_pi_apply b).comp (measurable_pi_apply a))
    · have h1 : (fun A : Matrix (Fin m) (Fin n) ℝ =>
          ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) A (Matrix.transpose A)
            (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal) (Sum.inr a) (Sum.inl b))
          = fun A => Complex.ofReal (A b a) := by
        funext A
        simp [Matrix.map, Matrix.fromBlocks]
      rw [h1]
      exact Complex.measurable_ofReal.comp ((measurable_pi_apply a).comp (measurable_pi_apply b))
    · have h1 : (fun A : Matrix (Fin m) (Fin n) ℝ =>
          ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) A (Matrix.transpose A)
            (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal) (Sum.inr a) (Sum.inr b))
          = fun _ => (0 : ℂ) := by
        funext A
        simp [Matrix.map, Matrix.fromBlocks]
      rw [h1]
      exact measurable_const
  have hsub : Measurable (fun M : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ =>
      (z : ℂ) • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) - M) := by
    refine measurable_pi_iff.2 (fun a => measurable_pi_iff.2 (fun b => ?_))
    have h1 : (fun M : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ =>
        ((z : ℂ) • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) - M) a b)
        = fun M => ((z : ℂ) • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) a b - M a b := by
      funext M
      simp
    rw [h1]
    exact measurable_const.sub ((measurable_pi_apply b).comp (measurable_pi_apply a))
  have hPhi : Measurable (fun A : Matrix (Fin m) (Fin n) ℝ =>
      ((((z : ℂ) • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) -
        (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) A (Matrix.transpose A)
          (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)⁻¹).trace)) :=
    hMinvTr.comp (hsub.comp hCM)
  have hB : Measurable (fun g : Fin m → Fin n → ℝ =>
      Matrix.of (fun (i : Fin m) (j : Fin n) => g i j / Real.sqrt (m : ℝ))) := by
    refine measurable_pi_iff.2 (fun i => measurable_pi_iff.2 (fun j => ?_))
    have h1 : (fun g : Fin m → Fin n → ℝ =>
        (Matrix.of (fun (i : Fin m) (j : Fin n) => g i j / Real.sqrt (m : ℝ))) i j)
        = fun g => g i j / Real.sqrt (m : ℝ) := by
      funext g
      rfl
    rw [h1]
    exact ((measurable_pi_apply j).comp (measurable_pi_apply i)).div_const _
  refine ⟨hprob, ?_, ?_, ?_, ?_⟩
  · have hmeas : Measurable (fun ω : Ω =>
        (((m : ℝ) + (n : ℝ))⁻¹ : ℂ) *
          ((((z : ℂ) • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) -
            (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (maskedScaled p (Xi ω) (Mask ω))
              (Matrix.transpose (maskedScaled p (Xi ω) (Mask ω)))
              (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)⁻¹).trace)) :=
      measurable_const.mul (hPhi.comp p9)
    refine MeasureTheory.Integrable.of_bound hmeas.aestronglyMeasurable (z.im)⁻¹ ?_
    filter_upwards with ω
    exact hbound _ (hermBlocks (maskedScaled p (Xi ω) (Mask ω)))
  · intro ω
    exact hbound _ (hermBlocks (maskedScaled p (Xi ω) (Mask ω)))
  · haveI : IsProbabilityMeasure (stdNormalMatrixMeasure m n) := hprob
    have hmeas : Measurable (fun g : Fin m → Fin n → ℝ =>
        (((m : ℝ) + (n : ℝ))⁻¹ : ℂ) *
          ((((z : ℂ) • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) -
            (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
              (Matrix.of (fun (i : Fin m) (j : Fin n) => g i j / Real.sqrt (m : ℝ)))
              (Matrix.transpose (Matrix.of (fun (i : Fin m) (j : Fin n) => g i j / Real.sqrt (m : ℝ))))
              (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)⁻¹).trace)) :=
      measurable_const.mul (hPhi.comp hB)
    refine MeasureTheory.Integrable.of_bound hmeas.aestronglyMeasurable (z.im)⁻¹ ?_
    filter_upwards with g
    exact hbound _ (hermBlocks (Matrix.of (fun (i : Fin m) (j : Fin n) => g i j / Real.sqrt (m : ℝ))))
  · intro g
    exact hbound _
      (hermBlocks (Matrix.of (fun (i : Fin m) (j : Fin n) => g i j / Real.sqrt (m : ℝ))))
  /- @proof-region region.target-node.session.b223158b4b584452 end -/

end Statlib.Imported

