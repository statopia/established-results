import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_b481c8ef6498b350fab6

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
theorem statopia_math_node_980150596_3d7bf283 : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (p : ℝ) (hp0 : 0 < p)
    (Xi Mask : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hXi_meas : ∀ i j, Measurable fun ω => Xi ω i j)
    (hXi_int : ∀ i j, Integrable (fun ω => Xi ω i j) μ)
    (hXi_sq_int : ∀ i j, Integrable (fun ω => (Xi ω i j) ^ 2) μ)
    (hXi_indep : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Xi ω ij.1 ij.2) μ)
    (hXi_mean : ∀ i j, ∫ ω, Xi ω i j ∂μ = 0)
    (hXi_var : ∀ i j, ∫ ω, (Xi ω i j) ^ 2 ∂μ = 1)
    (hMask_meas : ∀ i j, Measurable fun ω => Mask ω i j)
    (hMask_val : ∀ i j (ω : Ω), Mask ω i j = 0 ∨ Mask ω i j = 1)
    (hMask_law : ∀ i j, μ {ω | Mask ω i j = 1} = ENNReal.ofReal p)
    (hMask_indep : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Mask ω ij.1 ij.2) μ)
    (hIndep : IndepFun (fun ω (ij : Fin m × Fin n) => Xi ω ij.1 ij.2)
      (fun ω (ij : Fin m × Fin n) => Mask ω ij.1 ij.2) μ),
    let e1 : Fin m ⊕ Fin n ≃ Fin (m + n) := finSumFinEquiv
      let e2 : Fin m × Fin n ≃ Fin (m * n) := finProdFinEquiv
      let F : Fin (m * n) → Ω × (Fin m → Fin n → ℝ) → Matrix (Fin m) (Fin n) ℝ :=
        fun k x i j =>
          if (i, j) = e2.symm k then maskedScaled p (Xi x.1) (Mask x.1) i j else 0
      let Z : Fin (m * n) → Ω × (Fin m → Fin n → ℝ) →
          Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
        fun k x =>
          (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (F k x) (Matrix.transpose (F k x))
              (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal
      let G : Ω × (Fin m → Fin n → ℝ) → Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
        fun x =>
          (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
              (Matrix.of fun i j => x.2 i j / Real.sqrt ((m : ℝ)))
              (Matrix.transpose (Matrix.of fun i j => x.2 i j / Real.sqrt ((m : ℝ))))
              (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal
      (∀ a b : Fin (m + n),
          ∫ x : Ω × (Fin m → Fin n → ℝ), G x (e1.symm a) (e1.symm b)
              ∂(μ.prod (stdNormalMatrixMeasure m n))
            = ∫ x : Ω × (Fin m → Fin n → ℝ),
                ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) + ∑ k : Fin (m * n), Z k x)
                  (e1.symm a) (e1.symm b) ∂(μ.prod (stdNormalMatrixMeasure m n)))
        ∧ (∀ a b c e : Fin (m + n),
            ∫ x : Ω × (Fin m → Fin n → ℝ),
                (G x (e1.symm a) (e1.symm b)
                    - ∫ x' : Ω × (Fin m → Fin n → ℝ), G x' (e1.symm a) (e1.symm b)
                        ∂(μ.prod (stdNormalMatrixMeasure m n)))
                  * (starRingEnd ℂ)
                    (G x (e1.symm c) (e1.symm e)
                      - ∫ x' : Ω × (Fin m → Fin n → ℝ), G x' (e1.symm c) (e1.symm e)
                          ∂(μ.prod (stdNormalMatrixMeasure m n)))
                ∂(μ.prod (stdNormalMatrixMeasure m n))
              = ∫ x : Ω × (Fin m → Fin n → ℝ),
                  (((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) + ∑ k : Fin (m * n), Z k x)
                      (e1.symm a) (e1.symm b)
                    - ∫ x' : Ω × (Fin m → Fin n → ℝ),
                        ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) + ∑ k : Fin (m * n), Z k x')
                          (e1.symm a) (e1.symm b) ∂(μ.prod (stdNormalMatrixMeasure m n)))
                    * (starRingEnd ℂ)
                      (((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) + ∑ k : Fin (m * n), Z k x)
                          (e1.symm c) (e1.symm e)
                        - ∫ x' : Ω × (Fin m → Fin n → ℝ),
                            ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) + ∑ k : Fin (m * n), Z k x')
                              (e1.symm c) (e1.symm e) ∂(μ.prod (stdNormalMatrixMeasure m n)))
                  ∂(μ.prod (stdNormalMatrixMeasure m n))) := by
  /- @proof-region region.target-node.session.b9fa206612ce89d8 begin -/
  intro Ω instΩ μ instμ m n hm hn p hp0 Xi Mask hXi_meas hXi_int hXi_sq_int hXi_indep
    hXi_mean hXi_var hMask_meas hMask_val hMask_law hMask_indep hIndep e1 e2 F Z G
  haveI hν : IsProbabilityMeasure (stdNormalMatrixMeasure m n) := by
    unfold stdNormalMatrixMeasure
    infer_instance
  have hcoord : ∀ (i : Fin m) (j : Fin n),
      ∫ z : Fin m → Fin n → ℝ, z i j ∂(stdNormalMatrixMeasure m n) = 0 := by
    intro i j
    have h1 : MeasurePreserving (fun z : Fin m → Fin n → ℝ => z i)
        (stdNormalMatrixMeasure m n)
        (Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1) := by
      have h := MeasureTheory.measurePreserving_eval
        (fun _ : Fin m => Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1) i
      simpa only [stdNormalMatrixMeasure] using h
    have h2 : MeasurePreserving (fun z : Fin n → ℝ => z j)
        (Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)
        (ProbabilityTheory.gaussianReal 0 1) :=
      MeasureTheory.measurePreserving_eval (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1) j
    have h3 : MeasurePreserving (fun z : Fin m → Fin n → ℝ => z i j)
        (stdNormalMatrixMeasure m n) (ProbabilityTheory.gaussianReal 0 1) := h2.comp h1
    have h4 : ∫ z : Fin m → Fin n → ℝ, z i j ∂(stdNormalMatrixMeasure m n)
        = ∫ y : ℝ, y ∂(ProbabilityTheory.gaussianReal 0 1) := by
      have hmap : Measure.map (fun z : Fin m → Fin n → ℝ => z i j)
          (stdNormalMatrixMeasure m n) = ProbabilityTheory.gaussianReal 0 1 := h3.map_eq
      rw [← hmap]
      exact (MeasureTheory.integral_map h3.measurable.aemeasurable
        continuous_id.aestronglyMeasurable).symm
    simpa [ProbabilityTheory.integral_id_gaussianReal] using h4
  have hmul : ∀ (i : Fin m) (j : Fin n),
      ∫ z : Fin m → Fin n → ℝ, z i j * (Real.sqrt ((m : ℝ)))⁻¹
        ∂(stdNormalMatrixMeasure m n) = 0 := by
    intro i j
    have hsplit : ∫ z : Fin m → Fin n → ℝ, z i j * (Real.sqrt ((m : ℝ)))⁻¹
        ∂(stdNormalMatrixMeasure m n)
        = (∫ z : Fin m → Fin n → ℝ, z i j ∂(stdNormalMatrixMeasure m n))
          * (Real.sqrt ((m : ℝ)))⁻¹ :=
      MeasureTheory.integral_mul_const _ _
    rw [hsplit, hcoord i j, zero_mul]
  have hcoordC : ∀ (i : Fin m) (j : Fin n),
      ∫ z : Fin m → Fin n → ℝ, Complex.ofReal (z i j / Real.sqrt ((m : ℝ)))
        ∂(stdNormalMatrixMeasure m n) = 0 := by
    intro i j
    have hrew : (fun z : Fin m → Fin n → ℝ => Complex.ofReal (z i j / Real.sqrt ((m : ℝ))))
        = fun z : Fin m → Fin n → ℝ => (z i j * (Real.sqrt ((m : ℝ)))⁻¹ : ℝ) • (1 : ℂ) := by
      funext z
      simp [div_eq_mul_inv]
    rw [hrew, integral_smul_const]
    simp [hmul i j]
  have hprod_l : ∀ (f : Ω → ℂ),
      ∫ x : Ω × (Fin m → Fin n → ℝ), f x.1 ∂(μ.prod (stdNormalMatrixMeasure m n))
        = ∫ ω, f ω ∂μ := by
    intro f
    have h := MeasureTheory.integral_prod_mul (μ := μ) (ν := stdNormalMatrixMeasure m n)
      (f := f) (g := fun _ : Fin m → Fin n → ℝ => (1 : ℂ))
    simpa using h
  have hprod_r : ∀ (f : (Fin m → Fin n → ℝ) → ℂ),
      ∫ x : Ω × (Fin m → Fin n → ℝ), f x.2 ∂(μ.prod (stdNormalMatrixMeasure m n))
        = ∫ z, f z ∂(stdNormalMatrixMeasure m n) := by
    intro f
    have h := MeasureTheory.integral_prod_mul (μ := μ) (ν := stdNormalMatrixMeasure m n)
      (f := fun _ : Ω => (1 : ℂ)) (g := f)
    simpa using h
  have hmaskXi : ∀ (i : Fin m) (j : Fin n),
      ∫ ω, Mask ω i j * Xi ω i j ∂μ = 0 := by
    intro i j
    have hXm : Measurable fun ω (ij : Fin m × Fin n) => Xi ω ij.1 ij.2 :=
      measurable_pi_iff.mpr fun ij => hXi_meas ij.1 ij.2
    have hYm : Measurable fun ω (ij : Fin m × Fin n) => Mask ω ij.1 ij.2 :=
      measurable_pi_iff.mpr fun ij => hMask_meas ij.1 ij.2
    have hev : Measurable fun v : Fin m × Fin n → ℝ => v (i, j) := measurable_pi_apply (i, j)
    have h := ProbabilityTheory.IndepFun.integral_comp_mul_comp (μ := μ) hIndep
      hXm.aemeasurable hYm.aemeasurable hev.aestronglyMeasurable hev.aestronglyMeasurable
      (f := fun v : Fin m × Fin n → ℝ => v (i, j))
      (g := fun v : Fin m × Fin n → ℝ => v (i, j))
    have hflip : (fun ω : Ω => Mask ω i j * Xi ω i j) = fun ω : Ω => Xi ω i j * Mask ω i j := by
      funext ω
      exact mul_comm _ _
    rw [hflip]
    have key : (∫ x, ((fun v : Fin m × Fin n → ℝ => v (i, j))
          ∘ (fun ω (ij : Fin m × Fin n) => Xi ω ij.1 ij.2)
          * (fun v : Fin m × Fin n → ℝ => v (i, j))
          ∘ (fun ω (ij : Fin m × Fin n) => Mask ω ij.1 ij.2)) x ∂μ) = 0 := by
      rw [h]
      simp [hXi_mean i j]
    exact key
  have hZi : ∀ (i : Fin m) (j : Fin n),
      ∫ ω, Complex.ofReal (maskedScaled p (Xi ω) (Mask ω) i j) ∂μ = 0 := by
    intro i j
    have hrew : (fun ω : Ω => Complex.ofReal (maskedScaled p (Xi ω) (Mask ω) i j))
        = fun ω : Ω => (Mask ω i j * Xi ω i j / Real.sqrt ((m : ℝ) * p)) • (1 : ℂ) := by
      funext ω
      simp [maskedScaled, div_eq_mul_inv]
    rw [hrew, integral_smul_const]
    have hsplit : ∫ ω, Mask ω i j * Xi ω i j / Real.sqrt ((m : ℝ) * p) ∂μ
        = (∫ ω, Mask ω i j * Xi ω i j ∂μ) * (Real.sqrt ((m : ℝ) * p))⁻¹ := by
      simp only [div_eq_mul_inv]
      exact MeasureTheory.integral_mul_const _ _
    rw [hsplit, hmaskXi i j, zero_mul, zero_smul]

  have h5 : ∀ a b : Fin (m + n),
      (∫ x : Ω × (Fin m → Fin n → ℝ), G x (e1.symm a) (e1.symm b)
          ∂(μ.prod (stdNormalMatrixMeasure m n)) = 0)
        ∧ ∫ x : Ω × (Fin m → Fin n → ℝ),
            ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) + ∑ k : Fin (m * n), Z k x)
              (e1.symm a) (e1.symm b) ∂(μ.prod (stdNormalMatrixMeasure m n)) = 0 := by
    intro a b
    cases h1 : e1.symm a with
    | inl i =>
      cases h2 : e1.symm b with
      | inl i' =>
        have hL : ∫ x : Ω × (Fin m → Fin n → ℝ), G x (Sum.inl i) (Sum.inl i')
            ∂(μ.prod (stdNormalMatrixMeasure m n)) = 0 := by
          have hfun : (fun x : Ω × (Fin m → Fin n → ℝ) => G x (Sum.inl i) (Sum.inl i'))
              = fun _ => (0 : ℂ) := by
            funext x
            simp [G]
          rw [hfun]
          simp
        have hR : ∫ x : Ω × (Fin m → Fin n → ℝ),
            ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) + ∑ k : Fin (m * n), Z k x)
              (Sum.inl i) (Sum.inl i') ∂(μ.prod (stdNormalMatrixMeasure m n)) = 0 := by
          have hfun : (fun x : Ω × (Fin m → Fin n → ℝ) =>
              ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) + ∑ k : Fin (m * n), Z k x)
                (Sum.inl i) (Sum.inl i')) = fun _ => (0 : ℂ) := by
            funext x
            simp only [Matrix.add_apply, Matrix.zero_apply, zero_add, Matrix.sum_apply]
            simp [Z, F]
          rw [hfun]
          simp
        exact ⟨hL, hR⟩
      | inr j =>
        have hL : ∫ x : Ω × (Fin m → Fin n → ℝ), G x (Sum.inl i) (Sum.inr j)
            ∂(μ.prod (stdNormalMatrixMeasure m n)) = 0 := by
          have hfun : (fun x : Ω × (Fin m → Fin n → ℝ) => G x (Sum.inl i) (Sum.inr j))
              = fun x => Complex.ofReal (x.2 i j / Real.sqrt ((m : ℝ))) := by
            funext x
            simp [G]
          rw [hfun,
            hprod_r (fun z : Fin m → Fin n → ℝ => Complex.ofReal (z i j / Real.sqrt ((m : ℝ))))]
          exact hcoordC i j
        have hR : ∫ x : Ω × (Fin m → Fin n → ℝ),
            ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) + ∑ k : Fin (m * n), Z k x)
              (Sum.inl i) (Sum.inr j) ∂(μ.prod (stdNormalMatrixMeasure m n)) = 0 := by
          have hfun : (fun x : Ω × (Fin m → Fin n → ℝ) =>
              ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) + ∑ k : Fin (m * n), Z k x)
                (Sum.inl i) (Sum.inr j))
              = fun x => Complex.ofReal (maskedScaled p (Xi x.1) (Mask x.1) i j) := by
            funext x
            have hstep : ∀ k : Fin (m * n), Z k x (Sum.inl i) (Sum.inr j)
                = Complex.ofReal (if (i, j) = e2.symm k then
                    maskedScaled p (Xi x.1) (Mask x.1) i j else 0) := by
              intro k
              simp [Z, F]
            have hsum : (∑ k : Fin (m * n), Complex.ofReal (if (i, j) = e2.symm k then
                  maskedScaled p (Xi x.1) (Mask x.1) i j else 0))
                = Complex.ofReal (maskedScaled p (Xi x.1) (Mask x.1) i j) := by
              rw [Finset.sum_eq_single (e2 (i, j))
                (by
                  intro k _ hk
                  have hne : ¬((i, j) = e2.symm k) :=
                    fun h => hk (by simpa using (congrArg e2 h).symm)
                  rw [if_neg hne]
                  simp)
                (by
                  intro h
                  exact absurd (Finset.mem_univ _) h)]
              rw [Equiv.symm_apply_apply]
              simp
            simp only [Matrix.add_apply, Matrix.zero_apply, zero_add]
            simp only [Matrix.sum_apply, hstep]
            exact hsum
          rw [hfun,
            hprod_l (fun ω => Complex.ofReal (maskedScaled p (Xi ω) (Mask ω) i j))]
          exact hZi i j
        exact ⟨hL, hR⟩
    | inr j =>
      cases h2 : e1.symm b with
      | inl i' =>
        have hL : ∫ x : Ω × (Fin m → Fin n → ℝ), G x (Sum.inr j) (Sum.inl i')
            ∂(μ.prod (stdNormalMatrixMeasure m n)) = 0 := by
          have hfun : (fun x : Ω × (Fin m → Fin n → ℝ) => G x (Sum.inr j) (Sum.inl i'))
              = fun x => Complex.ofReal (x.2 i' j / Real.sqrt ((m : ℝ))) := by
            funext x
            simp [G]
          rw [hfun,
            hprod_r (fun z : Fin m → Fin n → ℝ => Complex.ofReal (z i' j / Real.sqrt ((m : ℝ))))]
          exact hcoordC i' j
        have hR : ∫ x : Ω × (Fin m → Fin n → ℝ),
            ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) + ∑ k : Fin (m * n), Z k x)
              (Sum.inr j) (Sum.inl i') ∂(μ.prod (stdNormalMatrixMeasure m n)) = 0 := by
          have hfun : (fun x : Ω × (Fin m → Fin n → ℝ) =>
              ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) + ∑ k : Fin (m * n), Z k x)
                (Sum.inr j) (Sum.inl i'))
              = fun x => Complex.ofReal (maskedScaled p (Xi x.1) (Mask x.1) i' j) := by
            funext x
            have hstep : ∀ k : Fin (m * n), Z k x (Sum.inr j) (Sum.inl i')
                = Complex.ofReal (if (i', j) = e2.symm k then
                    maskedScaled p (Xi x.1) (Mask x.1) i' j else 0) := by
              intro k
              simp [Z, F]
            have hsum : (∑ k : Fin (m * n), Complex.ofReal (if (i', j) = e2.symm k then
                  maskedScaled p (Xi x.1) (Mask x.1) i' j else 0))
                = Complex.ofReal (maskedScaled p (Xi x.1) (Mask x.1) i' j) := by
              rw [Finset.sum_eq_single (e2 (i', j))
                (by
                  intro k _ hk
                  have hne : ¬((i', j) = e2.symm k) :=
                    fun h => hk (by simpa using (congrArg e2 h).symm)
                  rw [if_neg hne]
                  simp)
                (by
                  intro h
                  exact absurd (Finset.mem_univ _) h)]
              rw [Equiv.symm_apply_apply]
              simp
            simp only [Matrix.add_apply, Matrix.zero_apply, zero_add]
            simp only [Matrix.sum_apply, hstep]
            exact hsum
          rw [hfun,
            hprod_l (fun ω => Complex.ofReal (maskedScaled p (Xi ω) (Mask ω) i' j))]
          exact hZi i' j
        exact ⟨hL, hR⟩
      | inr j' =>
        have hL : ∫ x : Ω × (Fin m → Fin n → ℝ), G x (Sum.inr j) (Sum.inr j')
            ∂(μ.prod (stdNormalMatrixMeasure m n)) = 0 := by
          have hfun : (fun x : Ω × (Fin m → Fin n → ℝ) => G x (Sum.inr j) (Sum.inr j'))
              = fun _ => (0 : ℂ) := by
            funext x
            simp [G]
          rw [hfun]
          simp
        have hR : ∫ x : Ω × (Fin m → Fin n → ℝ),
            ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) + ∑ k : Fin (m * n), Z k x)
              (Sum.inr j) (Sum.inr j') ∂(μ.prod (stdNormalMatrixMeasure m n)) = 0 := by
          have hfun : (fun x : Ω × (Fin m → Fin n → ℝ) =>
              ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) + ∑ k : Fin (m * n), Z k x)
                (Sum.inr j) (Sum.inr j')) = fun _ => (0 : ℂ) := by
            funext x
            simp only [Matrix.add_apply, Matrix.zero_apply, zero_add, Matrix.sum_apply]
            simp [Z, F]
          rw [hfun]
          simp
        exact ⟨hL, hR⟩
  have hstarR : ∀ r : ℝ, starRingEnd ℂ (Complex.ofReal r) = Complex.ofReal r := by
    intro r
    simp
  have hGstar : ∀ (u v : Fin m ⊕ Fin n) (x : Ω × (Fin m → Fin n → ℝ)),
      starRingEnd ℂ (G x u v) = G x u v := by
    intro u v x
    cases u with
    | inl i =>
      cases v with
      | inl i' => simpa [G] using hstarR 0
      | inr j => simpa [G] using hstarR (x.2 i j / Real.sqrt ((m : ℝ)))
    | inr j =>
      cases v with
      | inl i' => simpa [G] using hstarR (x.2 i' j / Real.sqrt ((m : ℝ)))
      | inr j' => simpa [G] using hstarR 0
  have hZstar : ∀ (k : Fin (m * n)) (u v : Fin m ⊕ Fin n)
      (x : Ω × (Fin m → Fin n → ℝ)), starRingEnd ℂ (Z k x u v) = Z k x u v := by
    intro k u v x
    cases u with
    | inl i =>
      cases v with
      | inl i' => simpa [Z, F] using hstarR 0
      | inr j =>
        by_cases hc : (i, j) = e2.symm k
        · simpa [Z, F, hc] using hstarR (maskedScaled p (Xi x.1) (Mask x.1) i j)
        · simpa [Z, F, hc] using hstarR 0
    | inr j =>
      cases v with
      | inl i' =>
        by_cases hc : (i', j) = e2.symm k
        · simpa [Z, F, hc] using hstarR (maskedScaled p (Xi x.1) (Mask x.1) i' j)
        · simpa [Z, F, hc] using hstarR 0
      | inr j' => simpa [Z, F] using hstarR 0
  have hSstar : ∀ (u v : Fin m ⊕ Fin n) (x : Ω × (Fin m → Fin n → ℝ)),
      starRingEnd ℂ (((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)
        + ∑ k : Fin (m * n), Z k x) u v)
        = ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)
        + ∑ k : Fin (m * n), Z k x) u v := by
    intro u v x
    simp only [Matrix.add_apply, Matrix.zero_apply, zero_add, Matrix.sum_apply]
    rw [map_sum]
    simp only [hZstar]
  refine ⟨fun a b => (h5 a b).1.trans (h5 a b).2.symm, ?_⟩
  · intro a b c e
    rw [(h5 a b).1, (h5 c e).1, (h5 a b).2, (h5 c e).2]
    simp only [sub_zero, hGstar, hSstar]
    let Gmat : (Fin m → Fin n → ℝ) → Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
      fun z => (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
          (Matrix.of fun i j => z i j / Real.sqrt ((m : ℝ)))
          (Matrix.transpose (Matrix.of fun i j => z i j / Real.sqrt ((m : ℝ))))
          (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal
    have hGfun : ∀ (u v : Fin m ⊕ Fin n) (x : Ω × (Fin m → Fin n → ℝ)),
        G x u v = Gmat x.2 u v := by
      intro u v x
      rfl
    have hSfun : ∀ (u v : Fin m ⊕ Fin n) (x : Ω × (Fin m → Fin n → ℝ)),
        ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) + ∑ k : Fin (m * n), Z k x) u v
          = ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)
              + ∑ k : Fin (m * n), Z k (x.1, fun _ _ => (0 : ℝ))) u v := by
      intro u v x
      rfl
    have hGr : ∫ x : Ω × (Fin m → Fin n → ℝ),
          G x (e1.symm a) (e1.symm b) * G x (e1.symm c) (e1.symm e)
            ∂(μ.prod (stdNormalMatrixMeasure m n))
        = ∫ z : Fin m → Fin n → ℝ,
          Gmat z (e1.symm a) (e1.symm b) * Gmat z (e1.symm c) (e1.symm e)
            ∂(stdNormalMatrixMeasure m n) := by
      rw [show (fun x : Ω × (Fin m → Fin n → ℝ) =>
            G x (e1.symm a) (e1.symm b) * G x (e1.symm c) (e1.symm e))
          = fun x => Gmat x.2 (e1.symm a) (e1.symm b)
              * Gmat x.2 (e1.symm c) (e1.symm e) from by
        funext x
        simp only [hGfun]]
      exact hprod_r
        (fun z => Gmat z (e1.symm a) (e1.symm b) * Gmat z (e1.symm c) (e1.symm e))
    have hSr : ∫ x : Ω × (Fin m → Fin n → ℝ),
          ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) + ∑ k : Fin (m * n), Z k x)
            (e1.symm a) (e1.symm b)
          * ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) + ∑ k : Fin (m * n), Z k x)
            (e1.symm c) (e1.symm e)
            ∂(μ.prod (stdNormalMatrixMeasure m n))
        = ∫ ω : Ω,
          ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)
              + ∑ k : Fin (m * n), Z k (ω, fun _ _ => (0 : ℝ))) (e1.symm a) (e1.symm b)
          * ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)
              + ∑ k : Fin (m * n), Z k (ω, fun _ _ => (0 : ℝ))) (e1.symm c) (e1.symm e)
            ∂μ := by
      rw [show (fun x : Ω × (Fin m → Fin n → ℝ) =>
            ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) + ∑ k : Fin (m * n), Z k x)
              (e1.symm a) (e1.symm b)
            * ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) + ∑ k : Fin (m * n), Z k x)
              (e1.symm c) (e1.symm e))
          = fun x => (fun ω : Ω =>
              ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)
                  + ∑ k : Fin (m * n), Z k (ω, fun _ _ => (0 : ℝ))) (e1.symm a) (e1.symm b)
              * ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)
                  + ∑ k : Fin (m * n), Z k (ω, fun _ _ => (0 : ℝ))) (e1.symm c)
                (e1.symm e)) x.1 from by
        funext x
        simp only [hSfun]]
      exact hprod_l (fun ω =>
        ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)
            + ∑ k : Fin (m * n), Z k (ω, fun _ _ => (0 : ℝ))) (e1.symm a) (e1.symm b)
        * ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)
            + ∑ k : Fin (m * n), Z k (ω, fun _ _ => (0 : ℝ))) (e1.symm c) (e1.symm e))
    have hGG : ∀ (i i' : Fin m) (j j' : Fin n),
        ∫ z : Fin m → Fin n → ℝ,
            (Complex.ofReal (z i j / Real.sqrt ((m : ℝ)))
              * Complex.ofReal (z i' j' / Real.sqrt ((m : ℝ))))
              ∂(stdNormalMatrixMeasure m n)
          = if (i, j) = (i', j') then (Complex.ofReal ((m : ℝ)⁻¹)) else 0 := by
      intro i i' j j'
      have hmpos : (0 : ℝ) ≤ (m : ℝ) := by positivity
      have hreal : ∫ z : Fin m → Fin n → ℝ,
          ((z i j / Real.sqrt ((m : ℝ))) * (z i' j' / Real.sqrt ((m : ℝ))))
            ∂(stdNormalMatrixMeasure m n)
          = if (i, j) = (i', j') then ((m : ℝ))⁻¹ else 0 := by
        have hsplit : ∫ z : Fin m → Fin n → ℝ,
            ((z i j * z i' j') * ((Real.sqrt ((m : ℝ)))⁻¹ * (Real.sqrt ((m : ℝ)))⁻¹))
              ∂(stdNormalMatrixMeasure m n)
            = (∫ z : Fin m → Fin n → ℝ, z i j * z i' j' ∂(stdNormalMatrixMeasure m n))
              * ((Real.sqrt ((m : ℝ)))⁻¹ * (Real.sqrt ((m : ℝ)))⁻¹) :=
          MeasureTheory.integral_mul_const _ _
        have hrew : (fun z : Fin m → Fin n → ℝ =>
            (z i j / Real.sqrt ((m : ℝ))) * (z i' j' / Real.sqrt ((m : ℝ))))
            = fun z => (z i j * z i' j')
              * ((Real.sqrt ((m : ℝ)))⁻¹ * (Real.sqrt ((m : ℝ)))⁻¹) := by
          funext z
          simp only [div_eq_mul_inv]
          ring
        rw [hrew, hsplit, (statopia_math_node_1096857301_d7b64af8 m n i i' j j').2]
        by_cases hc : (i, j) = (i', j')
        · rw [if_pos hc, if_pos hc, one_mul, ← pow_two, inv_pow, Real.sq_sqrt hmpos]
        · rw [if_neg hc, if_neg hc, zero_mul]
      have hconv : (fun z : Fin m → Fin n → ℝ =>
            (Complex.ofReal (z i j / Real.sqrt ((m : ℝ)))
              * Complex.ofReal (z i' j' / Real.sqrt ((m : ℝ)))))
          = fun z => ((z i j / Real.sqrt ((m : ℝ)))
              * (z i' j' / Real.sqrt ((m : ℝ)))) • (1 : ℂ) := by
        funext z
        simp
      rw [hconv, integral_smul_const, hreal]
      by_cases hc : (i, j) = (i', j')
      · simp [if_pos hc]
      · simp [if_neg hc]
    have hGGpair : ∀ (x y : Fin m × Fin n),
        ∫ z : Fin m → Fin n → ℝ,
            (Complex.ofReal (z x.1 x.2 / Real.sqrt ((m : ℝ)))
              * Complex.ofReal (z y.1 y.2 / Real.sqrt ((m : ℝ))))
              ∂(stdNormalMatrixMeasure m n)
          = if x = y then (Complex.ofReal ((m : ℝ)⁻¹)) else 0 := by
      intro x y
      simpa using hGG x.1 y.1 x.2 y.2
    let pr : Fin m ⊕ Fin n → Fin m ⊕ Fin n → Option (Fin m × Fin n) := fun u v =>
      match u, v with
      | Sum.inl i, Sum.inr j => some (i, j)
      | Sum.inr j, Sum.inl i => some (i, j)
      | _, _ => none
    have hGmat : ∀ (u v : Fin m ⊕ Fin n) (z : Fin m → Fin n → ℝ),
        Gmat z u v = match pr u v with
          | some x => Complex.ofReal (z x.1 x.2 / Real.sqrt ((m : ℝ)))
          | none => 0 := by
      intro u v z
      cases u with
      | inl i =>
        cases v with
        | inl i' => simp [Gmat, pr]
        | inr j => simp [Gmat, pr]
      | inr j =>
        cases v with
        | inl i' => simp [Gmat, pr]
        | inr j' => simp [Gmat, pr]
    have hGmom : ∀ (u v u' v' : Fin m ⊕ Fin n),
        ∫ z : Fin m → Fin n → ℝ, Gmat z u v * Gmat z u' v'
            ∂(stdNormalMatrixMeasure m n)
          = match pr u v, pr u' v' with
            | some x, some y => if x = y then (Complex.ofReal ((m : ℝ)⁻¹)) else 0
            | _, _ => 0 := by
      intro u v u' v'
      cases h1 : pr u v with
      | none =>
        cases h2 : pr u' v' with
        | none =>
          have hfun : (fun z : Fin m → Fin n → ℝ => Gmat z u v * Gmat z u' v')
              = fun _ => (0 : ℂ) := by
            funext z
            rw [hGmat u v, hGmat u' v']
            simp [h1, h2]
          rw [hfun]
          simp [h1, h2]
        | some y =>
          have hfun : (fun z : Fin m → Fin n → ℝ => Gmat z u v * Gmat z u' v')
              = fun _ => (0 : ℂ) := by
            funext z
            rw [hGmat u v, hGmat u' v']
            simp [h1, h2]
          rw [hfun]
          simp [h1, h2]
      | some x =>
        cases h2 : pr u' v' with
        | none =>
          have hfun : (fun z : Fin m → Fin n → ℝ => Gmat z u v * Gmat z u' v')
              = fun _ => (0 : ℂ) := by
            funext z
            rw [hGmat u v, hGmat u' v']
            simp [h1, h2]
          rw [hfun]
          simp [h1, h2]
        | some y =>
          have hfun : (fun z : Fin m → Fin n → ℝ => Gmat z u v * Gmat z u' v')
              = fun z => (Complex.ofReal (z x.1 x.2 / Real.sqrt ((m : ℝ)))
                * Complex.ofReal (z y.1 y.2 / Real.sqrt ((m : ℝ)))) := by
            funext z
            rw [hGmat u v, hGmat u' v']
            simp only [h1, h2]
          rw [hfun, hGGpair x y]
    have hMInt : ∀ (i : Fin m) (j : Fin n), ∫ ω, Mask ω i j ∂μ = p := by
      intro i j
      have hset : MeasurableSet {ω : Ω | Mask ω i j = 1} :=
        (hMask_meas i j) (measurableSet_singleton 1)
      have hpt : ∀ ω : Ω, Mask ω i j
          = ({ω : Ω | Mask ω i j = 1}.indicator (fun _ => (1 : ℝ))) ω := by
        intro ω
        by_cases h : Mask ω i j = 1
        · simp [h]
        · have h0 : Mask ω i j = 0 := (hMask_val i j ω).resolve_right h
          simp [h, h0]
      have hfun : (fun ω : Ω => Mask ω i j)
          = {ω : Ω | Mask ω i j = 1}.indicator (fun _ => (1 : ℝ)) := by
        funext ω
        exact hpt ω
      rw [hfun, MeasureTheory.integral_indicator_const (1 : ℝ) hset]
      have h2 : (μ {ω : Ω | Mask ω i j = 1}).toReal = p := by
        rw [hMask_law i j]
        exact ENNReal.toReal_ofReal (le_of_lt hp0)
      have h3 : μ.real {ω : Ω | Mask ω i j = 1} • (1 : ℝ)
          = μ.real {ω : Ω | Mask ω i j = 1} := by
        rw [smul_eq_mul, mul_one]
      rw [h3]
      exact h2
    have hXm : Measurable fun ω (ij : Fin m × Fin n) => Xi ω ij.1 ij.2 :=
      measurable_pi_iff.mpr fun ij => hXi_meas ij.1 ij.2
    have hYm : Measurable fun ω (ij : Fin m × Fin n) => Mask ω ij.1 ij.2 :=
      measurable_pi_iff.mpr fun ij => hMask_meas ij.1 ij.2
    have hMXdiag : ∀ (x : Fin m × Fin n),
        ∫ ω, (Mask ω x.1 x.2 * Xi ω x.1 x.2) * (Mask ω x.1 x.2 * Xi ω x.1 x.2) ∂μ = p := by
      intro x
      have hpt : (fun ω => (Mask ω x.1 x.2 * Xi ω x.1 x.2)
            * (Mask ω x.1 x.2 * Xi ω x.1 x.2))
          = fun ω => (Xi ω x.1 x.2 * Xi ω x.1 x.2) * Mask ω x.1 x.2 := by
        funext ω
        have hm : Mask ω x.1 x.2 * Mask ω x.1 x.2 = Mask ω x.1 x.2 := by
          rcases hMask_val x.1 x.2 ω with h | h <;> simp [h]
        calc (Mask ω x.1 x.2 * Xi ω x.1 x.2) * (Mask ω x.1 x.2 * Xi ω x.1 x.2)
            = (Mask ω x.1 x.2 * Mask ω x.1 x.2) * (Xi ω x.1 x.2 * Xi ω x.1 x.2) := by
              ring
          _ = (Xi ω x.1 x.2 * Xi ω x.1 x.2) * Mask ω x.1 x.2 := by rw [hm]; ring
      rw [hpt]
      have h := ProbabilityTheory.IndepFun.integral_comp_mul_comp (μ := μ) hIndep
        hXm.aemeasurable hYm.aemeasurable
        ((measurable_pi_apply (x.1, x.2)).mul (measurable_pi_apply (x.1, x.2))).aestronglyMeasurable
        (measurable_pi_apply (x.1, x.2)).aestronglyMeasurable
        (f := fun v : Fin m × Fin n → ℝ => v (x.1, x.2) * v (x.1, x.2))
        (g := fun v : Fin m × Fin n → ℝ => v (x.1, x.2))
      refine h.trans ?_
      have hXi2 : ∫ ω, Xi ω x.1 x.2 * Xi ω x.1 x.2 ∂μ = 1 := by
        have hfun : (fun ω : Ω => Xi ω x.1 x.2 * Xi ω x.1 x.2)
            = fun ω : Ω => Xi ω x.1 x.2 ^ 2 := by
          funext ω
          rw [pow_two]
        rw [hfun]
        exact hXi_var x.1 x.2
      show (∫ ω, Xi ω x.1 x.2 * Xi ω x.1 x.2 ∂μ)
          * (∫ ω, Mask ω x.1 x.2 ∂μ) = p
      rw [hXi2, hMInt x.1 x.2, one_mul]
    have hMXoff : ∀ (x y : Fin m × Fin n), x ≠ y →
        ∫ ω, (Mask ω x.1 x.2 * Xi ω x.1 x.2) * (Mask ω y.1 y.2 * Xi ω y.1 y.2) ∂μ = 0 := by
      intro x y hxy
      have hpt : (fun ω => (Mask ω x.1 x.2 * Xi ω x.1 x.2)
            * (Mask ω y.1 y.2 * Xi ω y.1 y.2))
          = fun ω => (Xi ω x.1 x.2 * Xi ω y.1 y.2)
            * (Mask ω x.1 x.2 * Mask ω y.1 y.2) := by
        funext ω
        ring
      rw [hpt]
      have h := ProbabilityTheory.IndepFun.integral_comp_mul_comp (μ := μ) hIndep
        hXm.aemeasurable hYm.aemeasurable
        ((measurable_pi_apply (x.1, x.2)).mul (measurable_pi_apply (y.1, y.2))).aestronglyMeasurable
        ((measurable_pi_apply (x.1, x.2)).mul (measurable_pi_apply (y.1, y.2))).aestronglyMeasurable
        (f := fun v : Fin m × Fin n → ℝ => v (x.1, x.2) * v (y.1, y.2))
        (g := fun v : Fin m × Fin n → ℝ => v (x.1, x.2) * v (y.1, y.2))
      refine h.trans ?_
      have hXxy : ∫ ω, Xi ω x.1 x.2 * Xi ω y.1 y.2 ∂μ = 0 := by
        have hind : (fun ω => Xi ω x.1 x.2) ⟂ᵢ[μ] (fun ω => Xi ω y.1 y.2) :=
          ProbabilityTheory.iIndepFun.indepFun hXi_indep hxy
        have h1 := ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral (μ := μ) hind
          (hXi_meas x.1 x.2).aestronglyMeasurable (hXi_meas y.1 y.2).aestronglyMeasurable
        rw [h1, hXi_mean x.1 x.2, hXi_mean y.1 y.2, mul_zero]
      show (∫ ω, Xi ω x.1 x.2 * Xi ω y.1 y.2 ∂μ)
          * (∫ ω, Mask ω x.1 x.2 * Mask ω y.1 y.2 ∂μ) = 0
      rw [hXxy, zero_mul]
    have hSmat : ∀ (u v : Fin m ⊕ Fin n) (ω : Ω),
        ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)
          + ∑ k : Fin (m * n), Z k (ω, fun _ _ => (0 : ℝ))) u v
          = match pr u v with
            | some x => Complex.ofReal (maskedScaled p (Xi ω) (Mask ω) x.1 x.2)
            | none => 0 := by
      intro u v ω
      cases u with
      | inl i =>
        cases v with
        | inl i' =>
          simp only [Matrix.add_apply, Matrix.zero_apply, zero_add, Matrix.sum_apply]
          simp [pr, Z, F]
        | inr j =>
          have hstep : ∀ k : Fin (m * n), Z k (ω, fun _ _ => (0 : ℝ)) (Sum.inl i) (Sum.inr j)
              = Complex.ofReal (if (i, j) = e2.symm k then
                  maskedScaled p (Xi ω) (Mask ω) i j else 0) := by
            intro k
            simp [Z, F]
          have hsum : (∑ k : Fin (m * n), Complex.ofReal
                (if (i, j) = e2.symm k then maskedScaled p (Xi ω) (Mask ω) i j else 0))
              = Complex.ofReal (maskedScaled p (Xi ω) (Mask ω) i j) := by
            rw [Finset.sum_eq_single (e2 (i, j))
              (by
                intro k _ hk
                have hne : ¬((i, j) = e2.symm k) :=
                  fun h => hk (by simpa using (congrArg e2 h).symm)
                rw [if_neg hne]
                simp)
              (by
                intro h
                exact absurd (Finset.mem_univ _) h)]
            rw [Equiv.symm_apply_apply]
            simp
          simp only [Matrix.add_apply, Matrix.zero_apply, zero_add]
          simp only [Matrix.sum_apply, hstep]
          simp only [hsum]
          simp [pr]
      | inr j =>
        cases v with
        | inl i' =>
          have hstep : ∀ k : Fin (m * n), Z k (ω, fun _ _ => (0 : ℝ)) (Sum.inr j) (Sum.inl i')
              = Complex.ofReal (if (i', j) = e2.symm k then
                  maskedScaled p (Xi ω) (Mask ω) i' j else 0) := by
            intro k
            simp [Z, F]
          have hsum : (∑ k : Fin (m * n), Complex.ofReal
                (if (i', j) = e2.symm k then maskedScaled p (Xi ω) (Mask ω) i' j else 0))
              = Complex.ofReal (maskedScaled p (Xi ω) (Mask ω) i' j) := by
            rw [Finset.sum_eq_single (e2 (i', j))
              (by
                intro k _ hk
                have hne : ¬((i', j) = e2.symm k) :=
                  fun h => hk (by simpa using (congrArg e2 h).symm)
                rw [if_neg hne]
                simp)
              (by
                intro h
                exact absurd (Finset.mem_univ _) h)]
            rw [Equiv.symm_apply_apply]
            simp
          simp only [Matrix.add_apply, Matrix.zero_apply, zero_add]
          simp only [Matrix.sum_apply, hstep]
          simp only [hsum]
          simp [pr]
        | inr j' =>
          simp only [Matrix.add_apply, Matrix.zero_apply, zero_add, Matrix.sum_apply]
          simp [pr, Z, F]
    have hscaled : ∀ (x y : Fin m × Fin n),
        (∫ ω : Ω, (Complex.ofReal (maskedScaled p (Xi ω) (Mask ω) x.1 x.2)
          * Complex.ofReal (maskedScaled p (Xi ω) (Mask ω) y.1 y.2)) ∂μ)
        = if x = y then (Complex.ofReal ((m : ℝ)⁻¹)) else 0 := by
      intro x y
      have hmpos : (0 : ℝ) < (m : ℝ) := by
        have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        linarith
      have hmppos : (0 : ℝ) < (m : ℝ) * p := mul_pos hmpos hp0
      have hs : Real.sqrt ((m : ℝ) * p) * Real.sqrt ((m : ℝ) * p) = (m : ℝ) * p := by
        simpa [pow_two] using Real.sq_sqrt (le_of_lt hmppos)
      have hpt : (fun ω : Ω => Complex.ofReal (maskedScaled p (Xi ω) (Mask ω) x.1 x.2)
          * Complex.ofReal (maskedScaled p (Xi ω) (Mask ω) y.1 y.2))
          = fun ω => (maskedScaled p (Xi ω) (Mask ω) x.1 x.2
              * maskedScaled p (Xi ω) (Mask ω) y.1 y.2) • (1 : ℂ) := by
        funext ω
        simp
      rw [hpt, integral_smul_const]
      have hreal : (∫ ω : Ω, maskedScaled p (Xi ω) (Mask ω) x.1 x.2
            * maskedScaled p (Xi ω) (Mask ω) y.1 y.2 ∂μ)
          = (if x = y then (1 : ℝ) else 0) * ((m : ℝ))⁻¹ := by
        have hstep : (fun ω : Ω => maskedScaled p (Xi ω) (Mask ω) x.1 x.2
              * maskedScaled p (Xi ω) (Mask ω) y.1 y.2)
            = fun ω => ((Mask ω x.1 x.2 * Xi ω x.1 x.2)
                * (Mask ω y.1 y.2 * Xi ω y.1 y.2))
              * ((Real.sqrt ((m : ℝ) * p))⁻¹ * (Real.sqrt ((m : ℝ) * p))⁻¹) := by
          funext ω
          simp only [maskedScaled, div_eq_mul_inv]
          ring
        rw [hstep, MeasureTheory.integral_mul_const]
        have hsinv : (Real.sqrt ((m : ℝ) * p))⁻¹ * (Real.sqrt ((m : ℝ) * p))⁻¹
            = ((m : ℝ) * p)⁻¹ := by
          rw [← mul_inv, hs]
        rw [hsinv]
        by_cases hxy : x = y
        · subst hxy
          rw [if_pos rfl, hMXdiag x]
          have hmn : (m : ℝ) ≠ 0 := ne_of_gt hmpos
          have hpn : p ≠ 0 := ne_of_gt hp0
          field_simp
        · rw [if_neg hxy, hMXoff x y hxy]
          simp
      rw [hreal]
      by_cases hxy : x = y
      · simp [if_pos hxy]
      · simp [if_neg hxy]
    have hSmom : ∀ (u v u' v' : Fin m ⊕ Fin n),
        (∫ ω : Ω, ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)
            + ∑ k : Fin (m * n), Z k (ω, fun _ _ => (0 : ℝ))) u v
          * ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)
            + ∑ k : Fin (m * n), Z k (ω, fun _ _ => (0 : ℝ))) u' v' ∂μ)
        = match pr u v, pr u' v' with
          | some x, some y => if x = y then (Complex.ofReal ((m : ℝ)⁻¹)) else 0
          | _, _ => 0 := by
      intro u v u' v'
      cases h1 : pr u v with
      | none =>
        cases h2 : pr u' v' with
        | none =>
          have hfun : (fun ω : Ω =>
              ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)
                + ∑ k : Fin (m * n), Z k (ω, fun _ _ => (0 : ℝ))) u v
              * ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)
                + ∑ k : Fin (m * n), Z k (ω, fun _ _ => (0 : ℝ))) u' v')
              = fun _ => (0 : ℂ) := by
            funext ω
            rw [hSmat u v ω, hSmat u' v' ω]
            simp [h1, h2]
          rw [hfun]
          simp
        | some y =>
          have hfun : (fun ω : Ω =>
              ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)
                + ∑ k : Fin (m * n), Z k (ω, fun _ _ => (0 : ℝ))) u v
              * ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)
                + ∑ k : Fin (m * n), Z k (ω, fun _ _ => (0 : ℝ))) u' v')
              = fun _ => (0 : ℂ) := by
            funext ω
            rw [hSmat u v ω, hSmat u' v' ω]
            simp [h1, h2]
          rw [hfun]
          simp
      | some x =>
        cases h2 : pr u' v' with
        | none =>
          have hfun : (fun ω : Ω =>
              ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)
                + ∑ k : Fin (m * n), Z k (ω, fun _ _ => (0 : ℝ))) u v
              * ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)
                + ∑ k : Fin (m * n), Z k (ω, fun _ _ => (0 : ℝ))) u' v')
              = fun _ => (0 : ℂ) := by
            funext ω
            rw [hSmat u v ω, hSmat u' v' ω]
            simp [h1, h2]
          rw [hfun]
          simp
        | some y =>
          have hfun : (fun ω : Ω =>
              ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)
                + ∑ k : Fin (m * n), Z k (ω, fun _ _ => (0 : ℝ))) u v
              * ((0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)
                + ∑ k : Fin (m * n), Z k (ω, fun _ _ => (0 : ℝ))) u' v')
              = fun ω => (Complex.ofReal (maskedScaled p (Xi ω) (Mask ω) x.1 x.2)
                * Complex.ofReal (maskedScaled p (Xi ω) (Mask ω) y.1 y.2)) := by
            funext ω
            rw [hSmat u v ω, hSmat u' v' ω]
            simp only [h1, h2]
          rw [hfun, hscaled x y]
    rw [hGr, hSr, hGmom (e1.symm a) (e1.symm b) (e1.symm c) (e1.symm e)]
    exact (hSmom (e1.symm a) (e1.symm b) (e1.symm c) (e1.symm e)).symm
  /- @proof-region region.target-node.session.b9fa206612ce89d8 end -/

end Statlib.Imported

