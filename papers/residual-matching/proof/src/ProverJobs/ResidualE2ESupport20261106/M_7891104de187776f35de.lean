import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_c82e50886360881a53f5
import ProverJobs.ResidualE2ESupport20261106.M_f563494b66a5583a8f7d

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
theorem statopia_math_node_2461078433_535c54cf : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n),
    IsGaussian ((μ.prod (stdNormalMatrixMeasure m n)).map
      (fun x (q : Fin (m + n) × Fin (m + n)) =>
        ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
            (Matrix.of (fun i j => x.2 i j / Real.sqrt ((m : ℝ))))
            (Matrix.transpose (Matrix.of (fun i j => x.2 i j / Real.sqrt ((m : ℝ)))))
            (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)
          (finSumFinEquiv.symm q.1) (finSumFinEquiv.symm q.2))) := by
  /- @proof-region region.target-node.session.abfe756df65ebbc4 begin -/
  intro Ω inst μ hμ m n hm hn
  have hν : IsGaussian (stdNormalMatrixMeasure m n) :=
    statopia_math_node_3733483906_a137eb95 m n

  have hΦex : ∃ (Φ : (Fin m → Fin n → ℝ) →L[ℝ] (Fin (m + n) × Fin (m + n) → ℂ)),
      ∀ g : Fin m → Fin n → ℝ, (Φ g : Fin (m + n) × Fin (m + n) → ℂ) =
        fun q : Fin (m + n) × Fin (m + n) =>
          ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
              (Matrix.of (fun i j => g i j / Real.sqrt ((m : ℝ))))
              (Matrix.transpose (Matrix.of (fun i j => g i j / Real.sqrt ((m : ℝ)))))
              (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)
            (finSumFinEquiv.symm q.1) (finSumFinEquiv.symm q.2) := by
    let F : (Fin m → Fin n → ℝ) → (Fin (m + n) × Fin (m + n) → ℂ) :=
      fun g q =>
        match finSumFinEquiv.symm q.1, finSumFinEquiv.symm q.2 with
        | Sum.inl _, Sum.inl _ => 0
        | Sum.inl i, Sum.inr j => ((g i j / Real.sqrt ((m : ℝ)) : ℝ) : ℂ)
        | Sum.inr i, Sum.inl j => ((g j i / Real.sqrt ((m : ℝ)) : ℝ) : ℂ)
        | Sum.inr _, Sum.inr _ => 0
    have hFadd : ∀ x y : Fin m → Fin n → ℝ, F (x + y) = F x + F y := by
      intro x y
      funext q
      rcases h1 : finSumFinEquiv.symm q.1 with i | i <;>
        rcases h2 : finSumFinEquiv.symm q.2 with j | j <;>
        simp [F, h1, h2, add_div, Complex.ofReal_add]
    have hFsmul : ∀ (c : ℝ) (x : Fin m → Fin n → ℝ), F (c • x) = c • F x := by
      intro c x
      funext q
      rcases h1 : finSumFinEquiv.symm q.1 with i | i <;>
        rcases h2 : finSumFinEquiv.symm q.2 with j | j <;>
        simp [F, h1, h2, div_eq_mul_inv, smul_eq_mul, Algebra.smul_def,
          Complex.ofReal_mul, mul_assoc, mul_comm, mul_left_comm]
    let f : (Fin m → Fin n → ℝ) →ₗ[ℝ] ((Fin (m + n) × Fin (m + n)) → ℂ) :=
      { toFun := F, map_add' := hFadd, map_smul' := hFsmul }
    have hfco : ⇑f = F := rfl
    have hform : ∀ g : Fin m → Fin n → ℝ, F g =
        fun q : Fin (m + n) × Fin (m + n) =>
          ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
              (Matrix.of (fun i j => g i j / Real.sqrt ((m : ℝ))))
              (Matrix.transpose (Matrix.of (fun i j => g i j / Real.sqrt ((m : ℝ)))))
              (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)
            (finSumFinEquiv.symm q.1) (finSumFinEquiv.symm q.2) := by
      intro g
      funext q
      rcases h1 : finSumFinEquiv.symm q.1 with i | i <;>
        rcases h2 : finSumFinEquiv.symm q.2 with j | j <;>
        simp only [F, h1, h2]
      all_goals rfl
    refine ⟨LinearMap.toContinuousLinearMap f, ?_⟩
    intro g
    rw [LinearMap.coe_toContinuousLinearMap', hfco]
    exact hform g





  obtain ⟨Φ, hΦ⟩ := hΦex
  have hmain : (μ.prod (stdNormalMatrixMeasure m n)).map
      (fun x (q : Fin (m + n) × Fin (m + n)) =>
        ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
            (Matrix.of (fun i j => x.2 i j / Real.sqrt ((m : ℝ))))
            (Matrix.transpose (Matrix.of (fun i j => x.2 i j / Real.sqrt ((m : ℝ)))))
            (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)
          (finSumFinEquiv.symm q.1) (finSumFinEquiv.symm q.2)) =
      Measure.map Φ (stdNormalMatrixMeasure m n) := by
    have hfun : ((fun x (q : Fin (m + n) × Fin (m + n)) =>
        ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
            (Matrix.of (fun i j => x.2 i j / Real.sqrt ((m : ℝ))))
            (Matrix.transpose (Matrix.of (fun i j => x.2 i j / Real.sqrt ((m : ℝ)))))
            (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)
          (finSumFinEquiv.symm q.1) (finSumFinEquiv.symm q.2)) :
        Ω × (Fin m → Fin n → ℝ) → (Fin (m + n) × Fin (m + n) → ℂ)) =
        fun x => Φ x.2 := by
      funext x
      exact (hΦ x.2).symm
    rw [hfun]
    rw [show (fun x : Ω × (Fin m → Fin n → ℝ) => Φ x.2) = ⇑Φ ∘ Prod.snd from rfl]
    rw [← Measure.map_map Φ.continuous.measurable measurable_snd]

    rw [Measure.map_snd_prod, measure_univ, one_smul]

  rw [hmain]
  haveI := hν
  exact isGaussian_map Φ

  /- @proof-region region.target-node.session.abfe756df65ebbc4 end -/

end Statlib.Imported

