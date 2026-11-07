import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Statlib.StatFoundation.RandomVariable.Gaussian.Standard
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
theorem statopia_math_node_2419531658_cacaaf43 : ∀ (p : ℕ) (hp : 1 ≤ p) (ι : Type*) [Fintype ι]
    (Lam : ι → Matrix (Fin p) (Fin p) ℝ) (hLam : ∀ i : ι, (Lam i).PosSemidef)
    (c : ι → ℝ),
    Measure.map
        (fun (w : ι → Fin p → ℝ) => fun j : Fin p => ∑ i : ι, c i * w i j)
        (Measure.pi (fun i : ι =>
          Measure.map (Slepian.canonicalGaussianVector (Lam i)) (standardPi p)))
      = Measure.map
          (Slepian.canonicalGaussianVector
            (fun j k : Fin p => ∑ i : ι, (c i) ^ 2 * Lam i j k))
          (standardPi p) := by
  /- @proof-region region.target-node.session.26ea887537b57d75 begin -/
  intro p hp ι _ Lam hLam c
  have hp0 : 0 < p := lt_of_lt_of_le Nat.zero_lt_one hp
  have hSigma : Matrix.PosSemidef (fun j k : Fin p => ∑ i : ι, (c i) ^ 2 * Lam i j k) := by
    have hmat : (fun j k : Fin p => ∑ i : ι, (c i) ^ 2 * Lam i j k)
        = ∑ i : ι, (c i) ^ 2 • Lam i := by
      ext j k
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hmat]
    exact Matrix.posSemidef_sum Finset.univ
      (fun i _ => Matrix.PosSemidef.smul (hLam i) (sq_nonneg (c i)))
  haveI : IsProbabilityMeasure (standardPi p) := Slepian.standardPi_probability_softLimit p
  have hmeas_cgv : ∀ i : ι, Measurable (Slepian.canonicalGaussianVector (Lam i)) := fun i =>
    (Slepian.canonicalGaussianVector_isCenteredGaussianVector hp0 (Lam i) (hLam i)).measurable
  haveI hnu : ∀ i : ι,
      IsProbabilityMeasure (Measure.map (Slepian.canonicalGaussianVector (Lam i)) (standardPi p)) :=
    fun i => MeasureTheory.Measure.isProbabilityMeasure_map (hmeas_cgv i).aemeasurable
  have hsum :
      IsCenteredGaussianVector
        (Measure.pi (fun i : ι => Measure.map (Slepian.canonicalGaussianVector (Lam i)) (standardPi p)))
        (fun (w : ι → Fin p → ℝ) => fun j : Fin p => ∑ i : ι, c i * w i j)
        (fun j k : Fin p => ∑ i : ι, (c i) ^ 2 * Lam i j k) := by
    have hlin : ∀ (u : Fin p → ℝ) (ω : ι → Fin p → ℝ),
        (∑ j, u j * ∑ i, c i * ω i j) = ∑ i, c i * ∑ j, u j * ω i j := by
      intro u ω
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    have hexp : ∀ (u : Fin p → ℝ) (ω : ι → Fin p → ℝ),
        Real.exp (∑ j, u j * ∑ i, c i * ω i j) = ∏ i, Real.exp (c i * ∑ j, u j * ω i j) := by
      intro u ω
      rw [hlin u ω, Real.exp_sum]
    have hfuneq : ∀ u : Fin p → ℝ,
        (fun ω : ι → Fin p → ℝ => Real.exp (∑ j, u j * ∑ i, c i * ω i j))
          = fun ω => ∏ i, Real.exp (c i * ∑ j, u j * ω i j) := by
      intro u
      funext ω
      exact hexp u ω
    refine ⟨?_, ?_, ?_⟩
    · exact measurable_pi_iff.mpr (fun j => by fun_prop)
    · intro u
      have hInt : ∀ i : ι,
          Integrable (fun x : Fin p → ℝ => Real.exp (c i * ∑ j, u j * x j))
            (Measure.map (Slepian.canonicalGaussianVector (Lam i)) (standardPi p)) := by
        intro i
        have hmp : MeasurePreserving (Slepian.canonicalGaussianVector (Lam i)) (standardPi p)
            (Measure.map (Slepian.canonicalGaussianVector (Lam i)) (standardPi p)) :=
          ⟨hmeas_cgv i, rfl⟩
        refine (hmp.integrable_comp ?_).mp ?_
        · exact (by fun_prop : Measurable (fun x : Fin p → ℝ => Real.exp (c i * ∑ j, u j * x j))).aestronglyMeasurable
        · have hb := (Slepian.canonicalGaussianVector_isCenteredGaussianVector hp0 (Lam i)
              (hLam i)).integrable_exp (fun j => c i * u j)
          simpa only [Finset.mul_sum, mul_assoc] using hb
      rw [hfuneq u]
      exact MeasureTheory.Integrable.fintype_prod_dep hInt
    · intro u
      have hsingle : ∀ i : ι,
          ∫ x, Real.exp (c i * ∑ j, u j * x j)
              ∂(Measure.map (Slepian.canonicalGaussianVector (Lam i)) (standardPi p))
            = Real.exp ((∑ a, ∑ b, ((c i * u a) * Lam i a b) * (c i * u b)) / 2) := by
        intro i
        have hmap : ∫ x, Real.exp (c i * ∑ j, u j * x j)
              ∂(Measure.map (Slepian.canonicalGaussianVector (Lam i)) (standardPi p))
            = ∫ z, Real.exp (c i * ∑ j, u j * Slepian.canonicalGaussianVector (Lam i) z j)
              ∂(standardPi p) :=
          MeasureTheory.integral_map (hmeas_cgv i).aemeasurable
            ((by fun_prop : Measurable (fun z : Fin p → ℝ => Real.exp (c i * ∑ j, u j * z j))).aestronglyMeasurable)
        rw [hmap]
        have hb := (Slepian.canonicalGaussianVector_isCenteredGaussianVector hp0 (Lam i)
              (hLam i)).mgf_eq (fun j => c i * u j)
        simpa only [Finset.mul_sum, mul_assoc] using hb
      have halg : (∑ i : ι, ∑ a : Fin p, ∑ b : Fin p, ((c i * u a) * Lam i a b) * (c i * u b))
          = ∑ a : Fin p, ∑ b : Fin p, (u a * (∑ k : ι, (c k) ^ 2 * Lam k a b)) * u b := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [hfuneq u]
      rw [MeasureTheory.integral_fintype_prod_eq_prod
        (fun i : ι => fun x : Fin p → ℝ => Real.exp (c i * ∑ j, u j * x j))]
      simp only [hsingle]
      rw [← Real.exp_sum, ← Finset.sum_div, halg]
  exact map_eq_map_of_centeredGaussianVector
    (Measure.pi (fun i : ι => Measure.map (Slepian.canonicalGaussianVector (Lam i)) (standardPi p)))
    (standardPi p)
    (fun (w : ι → Fin p → ℝ) => fun j : Fin p => ∑ i : ι, c i * w i j)
    (Slepian.canonicalGaussianVector (fun j k : Fin p => ∑ i : ι, (c i) ^ 2 * Lam i j k))
    (fun j k : Fin p => ∑ i : ι, (c i) ^ 2 * Lam i j k)
    hsum
    (Slepian.canonicalGaussianVector_isCenteredGaussianVector hp0 _ hSigma)
    hSigma
  /- @proof-region region.target-node.session.26ea887537b57d75 end -/

end

end Statlib.Imported

