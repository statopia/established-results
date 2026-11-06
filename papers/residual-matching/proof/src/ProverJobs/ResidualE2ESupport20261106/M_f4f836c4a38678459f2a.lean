import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_7891104de187776f35de
import ProverJobs.ResidualE2ESupport20261106.M_f563494b66a5583a8f7d
import ProverJobs.ResidualE2ESupport20261106.M_a713af28bbcfff9718cd

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
theorem statopia_math_node_3824140247_e6348683 : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (p Kt : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (hKt : 0 < Kt)
    (Xi Mask : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hXi_meas : ∀ i j, Measurable fun ω => Xi ω i j)
    (hXi_int : ∀ i j, Integrable (fun ω => Xi ω i j) μ)
    (hXi_sq_int : ∀ i j, Integrable (fun ω => (Xi ω i j) ^ 2) μ)
    (hXi_indep : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Xi ω ij.1 ij.2) μ)
    (hXi_mean : ∀ i j, ∫ ω, Xi ω i j ∂μ = 0)
    (hXi_var : ∀ i j, ∫ ω, (Xi ω i j) ^ 2 ∂μ = 1)
    (hXi_tail : ∀ i j (t : ℝ), 0 < t →
      μ {ω | t < |Xi ω i j|} ≤ ENNReal.ofReal (2 * Real.exp (-t / Kt)))
    (hMask_meas : ∀ i j, Measurable fun ω => Mask ω i j)
    (hMask_val : ∀ i j ω, Mask ω i j = 0 ∨ Mask ω i j = 1)
    (hMask_law : ∀ i j, μ {ω | Mask ω i j = 1} = ENNReal.ofReal p)
    (hMask_indep : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Mask ω ij.1 ij.2) μ)
    (hIndep : IndepFun (fun ω (ij : Fin m × Fin n) => Xi ω ij.1 ij.2)
      (fun ω (ij : Fin m × Fin n) => Mask ω ij.1 ij.2) μ),
    let e1 : Fin m ⊕ Fin n ≃ Fin (m + n) := finSumFinEquiv
    let e2 : Fin m × Fin n ≃ Fin (m * n) := finProdFinEquiv
    let ν : Measure (Fin m → Fin n → ℝ) := stdNormalMatrixMeasure m n
    let G : (Ω × (Fin m → Fin n → ℝ)) → Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
      fun x u v =>
        (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
            (Matrix.of fun i j => x.2 i j / Real.sqrt ((m : ℝ)))
            (Matrix.transpose (Matrix.of fun i j => x.2 i j / Real.sqrt ((m : ℝ))))
            (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal (e1.symm u) (e1.symm v)
    let F : Fin (m * n) → (Ω × (Fin m → Fin n → ℝ)) → Matrix (Fin m) (Fin n) ℝ :=
      fun k x i j =>
        if (i, j) = e2.symm k then maskedScaled p (Xi x.1) (Mask x.1) i j else 0
    let Z : Fin (m * n) → (Ω × (Fin m → Fin n → ℝ)) →
        Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
      fun k x u v =>
        (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
            (F k x)
            (Matrix.transpose (F k x))
            (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal (e1.symm u) (e1.symm v)

    (∀ x : Ω × (Fin m → Fin n → ℝ), (G x).IsHermitian) ∧
    (∀ a b : Fin (m + n), Measurable fun x : Ω × (Fin m → Fin n → ℝ) => G x a b) ∧
    (∀ a b : Fin (m + n),
      Integrable (fun x : Ω × (Fin m → Fin n → ℝ) => G x a b) (μ.prod ν)) ∧
    IsGaussian ((μ.prod ν).map fun x (q : Fin (m + n) × Fin (m + n)) => G x q.1 q.2) ∧
    (∀ a b : Fin (m + n),
      ∫ x, G x a b ∂(μ.prod ν) =
        ∫ x, ((0 : Matrix (Fin (m + n)) (Fin (m + n)) ℂ) +
          ∑ k : Fin (m * n), Z k x) a b ∂(μ.prod ν)) ∧
    (∀ a b c e : Fin (m + n),
      ∫ x, (G x a b - ∫ x', G x' a b ∂(μ.prod ν)) *
          (starRingEnd ℂ) (G x c e - ∫ x', G x' c e ∂(μ.prod ν)) ∂(μ.prod ν) =
        ∫ x, (((0 : Matrix (Fin (m + n)) (Fin (m + n)) ℂ) +
              ∑ k : Fin (m * n), Z k x) a b -
            ∫ x', ((0 : Matrix (Fin (m + n)) (Fin (m + n)) ℂ) +
              ∑ k : Fin (m * n), Z k x') a b ∂(μ.prod ν)) *
          (starRingEnd ℂ) (((0 : Matrix (Fin (m + n)) (Fin (m + n)) ℂ) +
              ∑ k : Fin (m * n), Z k x) c e -
            ∫ x', ((0 : Matrix (Fin (m + n)) (Fin (m + n)) ℂ) +
              ∑ k : Fin (m * n), Z k x') c e ∂(μ.prod ν)) ∂(μ.prod ν)) := by
  /- @proof-region region.target-node.session.7913af7571c18964 begin -/
  intro Ω _ μ _ m n hm hn p Kt hp0 hp1 hKt Xi Mask hXi_meas hXi_int hXi_sq_int hXi_indep
    hXi_mean hXi_var hXi_tail hMask_meas hMask_val hMask_law hMask_indep hIndep
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    let B : Matrix (Fin m) (Fin n) ℝ := Matrix.of fun i j => x.2 i j / Real.sqrt ((m : ℝ))
    let M : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ :=
      Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) B (Matrix.transpose B)
        (0 : Matrix (Fin n) (Fin n) ℝ)
    have hsym : Matrix.transpose M = M := by
      ext u v
      rcases u with i | i <;> rcases v with j | j <;>
        simp [M, B, Matrix.transpose, Matrix.fromBlocks]
    have hsym2 : ∀ u v : Fin m ⊕ Fin n, M v u = M u v := by
      intro u v
      have h3 := congrFun (congrFun hsym v) u
      simpa [Matrix.transpose] using h3.symm
    have hherm : (M.map Complex.ofReal).IsHermitian := by
      simp only [Matrix.IsHermitian]
      ext u v
      rw [Matrix.conjTranspose_apply]
      show star (((M v u : ℝ)) : ℂ) = (((M u v : ℝ)) : ℂ)
      rw [hsym2 u v]
      simp
    exact (Matrix.isHermitian_submatrix_equiv (A := M.map Complex.ofReal)
      finSumFinEquiv.symm).2 hherm
  · intro a b
    dsimp only
    have hcoord : ∀ (i : Fin m) (j : Fin n),
        Measurable fun x : Ω × (Fin m → Fin n → ℝ) => x.2 i j := by
      intro i j
      have h1 : Measurable fun f : Fin m → Fin n → ℝ => f i := measurable_pi_apply i
      have h2 : Measurable fun g : Fin n → ℝ => g j := measurable_pi_apply j
      exact h2.comp (h1.comp measurable_snd)
    have hof : Measurable fun r : ℝ => (r : ℂ) := Complex.continuous_ofReal.measurable
    cases h₁ : finSumFinEquiv.symm a with
    | inl i =>
      cases h₂ : finSumFinEquiv.symm b with
      | inl j => exact (measurable_const : Measurable fun _ : Ω × (Fin m → Fin n → ℝ) => (0 : ℂ))
      | inr j => exact hof.comp ((hcoord i j).div_const (Real.sqrt ((m : ℝ))))
    | inr i =>
      cases h₂ : finSumFinEquiv.symm b with
      | inl j => exact hof.comp ((hcoord j i).div_const (Real.sqrt ((m : ℝ))))
      | inr j => exact (measurable_const : Measurable fun _ : Ω × (Fin m → Fin n → ℝ) => (0 : ℂ))
  · intro a b
    have hkey : Integrable (fun g : Fin m → Fin n → ℝ =>
        (fun u v =>
          (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
              (Matrix.of fun i j => g i j / Real.sqrt ((m : ℝ)))
              (Matrix.transpose (Matrix.of fun i j => g i j / Real.sqrt ((m : ℝ))))
              (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal
            (finSumFinEquiv.symm u) (finSumFinEquiv.symm v)) a b)
        (Measure.pi (fun _ : Fin m => Measure.pi (fun _ : Fin n => gaussianReal 0 1))) := by
      have hmarg : ∀ (i : Fin m) (j : Fin n),
          Measure.map (fun g : Fin m → Fin n → ℝ => g i j)
            (Measure.pi (fun _ : Fin m =>
              Measure.pi (fun _ : Fin n => gaussianReal 0 1)))
            = gaussianReal 0 1 := by
        intro i j
        have h₁ := measurePreserving_eval
          (fun _ : Fin m => Measure.pi (fun _ : Fin n => gaussianReal 0 1)) i
        have h₂ := measurePreserving_eval
          (fun _ : Fin n => (gaussianReal 0 1 : Measure ℝ)) j
        have hc : MeasurePreserving
            ((fun h : Fin n → ℝ => h j) ∘ (Function.eval i))
            (Measure.pi (fun _ : Fin m =>
              Measure.pi (fun _ : Fin n => gaussianReal 0 1)))
            (gaussianReal 0 1) := h₂.comp h₁
        simpa [Function.comp] using hc.map_eq
      have hψ : MemLp (fun x : ℝ => x) 1 (gaussianReal 0 1) :=
        ProbabilityTheory.memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := 1) 1 (by simp)
      have hcoord : ∀ (i : Fin m) (j : Fin n),
          Integrable (fun g : Fin m → Fin n → ℝ => g i j)
            (Measure.pi (fun _ : Fin m => Measure.pi (fun _ : Fin n => gaussianReal 0 1))) := by
        intro i j
        have h1 : Measurable fun f : Fin m → Fin n → ℝ => f i := measurable_pi_apply i
        have h2 : Measurable fun g : Fin n → ℝ => g j := measurable_pi_apply j
        have hψ' : MemLp (fun x : ℝ => x) 1
            (Measure.map (fun g : Fin m → Fin n → ℝ => g i j)
              (Measure.pi (fun _ : Fin m =>
                Measure.pi (fun _ : Fin n => gaussianReal 0 1)))) :=
          (hmarg i j).symm ▸ hψ
        have hmem : MemLp (fun g : Fin m → Fin n → ℝ => g i j) 1
            (Measure.pi (fun _ : Fin m =>
              Measure.pi (fun _ : Fin n => gaussianReal 0 1))) :=
          MeasureTheory.MemLp.comp_of_map hψ' (h2.comp h1).aemeasurable
        exact MeasureTheory.memLp_one_iff_integrable.mp hmem
      have hL : MemLp (fun x : ℝ => ((x : ℝ) : ℂ)) 1 (gaussianReal 0 1) := by
        have h := MeasureTheory.MemLp.continuousLinearMap_comp hψ Complex.ofRealCLM
        simpa using h
      dsimp only
      cases h₁ : finSumFinEquiv.symm a with
      | inl i =>
        cases h₂ : finSumFinEquiv.symm b with
        | inl j => simp
        | inr j =>
          have h1 : Measurable fun f : Fin m → Fin n → ℝ => f i := measurable_pi_apply i
          have h2 : Measurable fun g : Fin n → ℝ => g j := measurable_pi_apply j
          have hmem0 : MemLp (fun x : ℝ => ((x : ℝ) : ℂ)) 1
              (Measure.map (fun g : Fin m → Fin n → ℝ => g i j)
                (Measure.pi (fun _ : Fin m =>
                  Measure.pi (fun _ : Fin n => gaussianReal 0 1)))) :=
            (hmarg i j).symm ▸ hL
          have hmem : MemLp (fun g : Fin m → Fin n → ℝ => ((g i j : ℝ) : ℂ)) 1
              (Measure.pi (fun _ : Fin m =>
                Measure.pi (fun _ : Fin n => gaussianReal 0 1))) :=
            MeasureTheory.MemLp.comp_of_map
              (μ := Measure.pi (fun _ : Fin m => Measure.pi (fun _ : Fin n => gaussianReal 0 1)))
              (f := fun g : Fin m → Fin n → ℝ => g i j) (g := fun x : ℝ => ((x : ℝ) : ℂ))
              hmem0 (h2.comp h1).aemeasurable
          have hint : Integrable (fun g : Fin m → Fin n → ℝ => ((g i j : ℝ) : ℂ))
              (Measure.pi (fun _ : Fin m =>
                Measure.pi (fun _ : Fin n => gaussianReal 0 1))) :=
            MeasureTheory.memLp_one_iff_integrable.mp hmem
          simpa using hint.div_const ((Real.sqrt ((m : ℝ)) : ℂ))
      | inr i =>
        cases h₂ : finSumFinEquiv.symm b with
        | inl j =>
          have h1 : Measurable fun f : Fin m → Fin n → ℝ => f j := measurable_pi_apply j
          have h2 : Measurable fun g : Fin n → ℝ => g i := measurable_pi_apply i
          have hmem0 : MemLp (fun x : ℝ => ((x : ℝ) : ℂ)) 1
              (Measure.map (fun g : Fin m → Fin n → ℝ => g j i)
                (Measure.pi (fun _ : Fin m =>
                  Measure.pi (fun _ : Fin n => gaussianReal 0 1)))) :=
            (hmarg j i).symm ▸ hL
          have hmem : MemLp (fun g : Fin m → Fin n → ℝ => ((g j i : ℝ) : ℂ)) 1
              (Measure.pi (fun _ : Fin m =>
                Measure.pi (fun _ : Fin n => gaussianReal 0 1))) :=
            MeasureTheory.MemLp.comp_of_map
              (μ := Measure.pi (fun _ : Fin m => Measure.pi (fun _ : Fin n => gaussianReal 0 1)))
              (f := fun g : Fin m → Fin n → ℝ => g j i) (g := fun x : ℝ => ((x : ℝ) : ℂ))
              hmem0 (h2.comp h1).aemeasurable
          have hint : Integrable (fun g : Fin m → Fin n → ℝ => ((g j i : ℝ) : ℂ))
              (Measure.pi (fun _ : Fin m =>
                Measure.pi (fun _ : Fin n => gaussianReal 0 1))) :=
            MeasureTheory.memLp_one_iff_integrable.mp hmem
          simpa using hint.div_const ((Real.sqrt ((m : ℝ)) : ℂ))
        | inr j => simp
    exact hkey.comp_snd μ
  · exact statopia_math_node_2461078433_535c54cf μ m n hm hn
  · intro a b
    simpa [Matrix.sum_apply, Finset.sum_apply] using
      (statopia_math_node_980150596_3d7bf283 μ m n hm hn p hp0 Xi Mask hXi_meas hXi_int
        hXi_sq_int hXi_indep hXi_mean hXi_var hMask_meas hMask_val hMask_law hMask_indep hIndep).1 a b
  · intro a b c e
    simpa [Matrix.sum_apply, Finset.sum_apply] using
      (statopia_math_node_980150596_3d7bf283 μ m n hm hn p hp0 Xi Mask hXi_meas hXi_int
        hXi_sq_int hXi_indep hXi_mean hXi_var hMask_meas hMask_val hMask_law hMask_indep hIndep).2 a b c e
  /- @proof-region region.target-node.session.7913af7571c18964 end -/

end Statlib.Imported

