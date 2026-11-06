import Lean
import ProverJobs.ResidualE2ESupport20261106.ExternalNodes.Node_556e505598fbe6bfd0d0

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
namespace ResidualMaskRepair20261106

lemma normalized_gaussian_law (v : ℝ) (hv : 0 < v) :
    Measure.map (fun y : ℝ => y / Real.sqrt v) (gaussianReal 0 (Real.toNNReal v)) =
      gaussianReal 0 1 := by
  simp_rw [div_eq_mul_inv]
  rw [gaussianReal_map_mul_const, mul_zero]
  congr 1
  apply NNReal.eq
  change (Real.sqrt v)⁻¹ ^ 2 * (Real.toNNReal v : ℝ) = 1
  rw [Real.coe_toNNReal _ hv.le, inv_pow, Real.sq_sqrt hv.le, inv_mul_cancel₀ hv.ne']

lemma independent_comp_snd {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure (I → ℝ)) [IsProbabilityMeasure ν]
    (f : I → (I → ℝ) → ℝ) (hf : ∀ i, Measurable (f i))
    (hi : iIndepFun f ν) :
    iIndepFun (fun i => fun x : Ω × (I → ℝ) => f i x.2) (P.prod ν) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => ((hf i).comp measurable_snd).aemeasurable)).2
  have hmap : Measure.map (Prod.snd : Ω × (I → ℝ) → (I → ℝ)) (P.prod ν) = ν :=
    (measurePreserving_snd (μ := P) (ν := ν)).map_eq
  have htuple : Measurable (fun x => fun i => f i x) := measurable_pi_iff.2 hf
  have h := (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hf i).aemeasurable)).1 hi
  change Measure.map ((fun x => fun i => f i x) ∘ Prod.snd) (P.prod ν) = _
  rw [← Measure.map_map htuple measurable_snd, hmap, h]
  congr 1
  funext i
  change Measure.map (f i) ν = Measure.map ((f i) ∘ Prod.snd) (P.prod ν)
  rw [← Measure.map_map (hf i) measurable_snd, hmap]

lemma normalized_product_gaussian {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) [IsProbabilityMeasure P] (v : ℝ) (hv : 0 < v) :
    let γ := Measure.pi (fun _ : I => gaussianReal 0 (Real.toNNReal v));
    (∀ i : I, Measurable (fun x : Ω × (I → ℝ) => x.2 i / Real.sqrt v)) ∧
    iIndepFun (fun i : I => fun x : Ω × (I → ℝ) => x.2 i / Real.sqrt v) (P.prod γ) ∧
    (∀ i : I, Measure.map (fun x : Ω × (I → ℝ) => x.2 i / Real.sqrt v) (P.prod γ) =
      gaussianReal 0 1) := by
  intro γ
  have hm : ∀ i : I, Measurable (fun x : I → ℝ => x i / Real.sqrt v) := fun i =>
    (measurable_pi_apply i).div_const _
  have hi : iIndepFun (fun i : I => fun x : I → ℝ => x i / Real.sqrt v) γ :=
    (iIndepFun_pi (fun _ => measurable_id.aemeasurable)).comp
      (fun _ y => y / Real.sqrt v) (fun _ => measurable_id.div_const _)
  refine ⟨fun i => (hm i).comp measurable_snd, independent_comp_snd P γ _ hm hi, ?_⟩
  intro i
  have hmap : Measure.map (fun x : Ω × (I → ℝ) => x.2 i) (P.prod γ) =
      gaussianReal 0 (Real.toNNReal v) := by
    rw [show (fun x : Ω × (I → ℝ) => x.2 i) = (fun x : I → ℝ => x i) ∘ Prod.snd by rfl,
      ← Measure.map_map (measurable_pi_apply i) measurable_snd,
      (measurePreserving_snd (μ := P) (ν := γ)).map_eq]
    exact (measurePreserving_eval (fun _ : I => gaussianReal 0 (Real.toNNReal v)) i).map_eq
  rw [show (fun x : Ω × (I → ℝ) => x.2 i / Real.sqrt v) =
      (fun y : ℝ => y / Real.sqrt v) ∘ (fun x : Ω × (I → ℝ) => x.2 i) by rfl,
    ← Measure.map_map
      (show Measurable (fun y : ℝ => y / Real.sqrt v) by fun_prop)
      (show Measurable (fun x : Ω × (I → ℝ) => x.2 i) by fun_prop), hmap]
  exact normalized_gaussian_law v hv

#print axioms normalized_product_gaussian
end ResidualMaskRepair20261106

