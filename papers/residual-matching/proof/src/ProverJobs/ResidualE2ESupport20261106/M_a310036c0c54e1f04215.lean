import Lean
import ProverJobs.ResidualE2ESupport20261106.M_41404a657eb68a6e78b5
import ProverJobs.ResidualE2ESupport20261106.M_30e3ebd8c0ecef26f046
import ProverJobs.ResidualE2ESupport20261106.M_35bed150fbe6905c6172

namespace PaperProofTasks.ResidualE2ESupport20261106

run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported

namespace ResidualMaskRepair20261106.Assembly

theorem product_gaussian_specNorm_mean_le_two (m n : ℕ) (hm : 0 < m) (hnm : n ≤ m)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] :
    let γ := Measure.pi (fun _ : Fin m × Fin n => gaussianReal 0 ((1-p)/(m:ℝ)).toNNReal)
    (∫ y : Ω × ((Fin m × Fin n) → ℝ), specNorm (fun i j => y.2 (i,j)) ∂(P.prod γ)) ≤ 2 := by
  classical
  intro γ
  let v : ℝ := (1 - p) / (m : ℝ)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hv : 0 < v := div_pos (sub_pos.mpr hp1) hm0
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  let F : Ω × ((Fin m × Fin n) → ℝ) → ((Fin m × Fin n) → ℝ) :=
    fun x ij => x.2 ij / Real.sqrt v
  let φ : ((Fin m × Fin n) → ℝ) → ℝ := fun g => specNorm (fun i j => g (i,j))
  obtain ⟨hcoord, hindep, hlaw⟩ :=
    ResidualMaskRepair20261106.normalized_product_gaussian (I := Fin m × Fin n) P v hv
  have hF : Measurable F := measurable_pi_iff.2 hcoord
  have hmap : Measure.map F (P.prod γ) =
      Measure.pi (fun _ : Fin m × Fin n => gaussianReal 0 1) := by
    have hh := (iIndepFun_iff_map_fun_eq_pi_map (fun ij => (hcoord ij).aemeasurable)).1 hindep
    simpa only [hlaw] using hh
  have hφ : Continuous φ := by
    dsimp only [φ, specNorm]
    apply Continuous.norm
    let L : Matrix (Fin m) (Fin n) ℝ ≃ₗ[ℝ]
        ((EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin m))) :=
      Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap
    have hc : Continuous L := L.toLinearMap.continuous_of_finiteDimensional
    apply hc.comp
    fun_prop
  have htrans : (∫ x, φ (F x) ∂(P.prod γ)) =
      ∫ g, φ g ∂Measure.pi (fun _ : Fin m × Fin n => gaussianReal 0 1) := by
    rw [← integral_map hF.aemeasurable hφ.measurable.aestronglyMeasurable, hmap]
  have hpoint (x : Ω × ((Fin m × Fin n) → ℝ)) :
      specNorm (fun i j => x.2 (i,j)) = Real.sqrt v * φ (F x) := by
    have heq : (fun i j => x.2 (i,j)) =
        Real.sqrt v • (fun i j => x.2 (i,j) / Real.sqrt v) := by
      ext i j
      change x.2 (i,j) = Real.sqrt v * (x.2 (i,j) / Real.sqrt v)
      field_simp
    rw [heq]
    simp only [specNorm, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    rfl
  have hsharp : (∫ g, φ g ∂Measure.pi (fun _ : Fin m × Fin n => gaussianReal 0 1)) ≤
      Real.sqrt (m : ℝ) + Real.sqrt (n : ℝ) := by
    exact statopia_math_node_3041891103_ca9d76ef m n
  have hsprod : Real.sqrt v * Real.sqrt (m : ℝ) ≤ 1 := by
    rw [← Real.sqrt_mul hv.le]
    have heq : v * (m : ℝ) = 1 - p := by dsimp [v]; field_simp
    rw [heq]
    exact (Real.sqrt_le_iff).2 ⟨by norm_num, by linarith⟩
  have hsn : Real.sqrt (n : ℝ) ≤ Real.sqrt (m : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hnm)
  calc
    _ = ∫ x, Real.sqrt v * φ (F x) ∂(P.prod γ) := integral_congr_ae (ae_of_all _ hpoint)
    _ = Real.sqrt v * (∫ x, φ (F x) ∂(P.prod γ)) := integral_const_mul _ _
    _ = Real.sqrt v * (∫ g, φ g ∂Measure.pi (fun _ : Fin m × Fin n => gaussianReal 0 1)) := by rw [htrans]
    _ ≤ Real.sqrt v * (Real.sqrt (m : ℝ) + Real.sqrt (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hsharp hs.le
    _ ≤ 2 := by nlinarith [mul_le_mul_of_nonneg_left hsn hs.le]

end ResidualMaskRepair20261106.Assembly

#print axioms ResidualMaskRepair20261106.Assembly.product_gaussian_specNorm_mean_le_two

