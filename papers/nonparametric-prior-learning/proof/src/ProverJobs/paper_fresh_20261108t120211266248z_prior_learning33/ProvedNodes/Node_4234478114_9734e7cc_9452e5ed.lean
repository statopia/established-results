import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_454462448_6086eebe_8546ee4b

namespace PaperProofTasks.paper_fresh_20261108t120211266248z_prior_learning33

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261108t120211266248z_prior_learning33.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_4234478114_9734e7cc : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [MeasurableSpace U] [BorelSpace U]
    (e : HilbertBasis ℕ ℝ U) (c : ℕ → ℝ) (hc : ∀ k : ℕ, 0 < c k)
    (μ : Measure U) [IsProbabilityMeasure μ]
    (ν : Measure U) [IsProbabilityMeasure ν]
    (mUM mNU : U) (F : Finset ℕ)
    (hmap_mu :
      Measure.map (fun u : U => fun k : {k : ℕ // k ∈ F} => inner ℝ (e k) u) μ
        = Measure.pi (fun k : {k : ℕ // k ∈ F} =>
            ProbabilityTheory.gaussianReal (inner ℝ (e k) mUM) (Real.toNNReal (c k))))
    (hmap_nu :
      Measure.map (fun u : U => fun k : {k : ℕ // k ∈ F} => inner ℝ (e k) u) ν
        = Measure.pi (fun k : {k : ℕ // k ∈ F} =>
            ProbabilityTheory.gaussianReal (inner ℝ (e k) mNU) (Real.toNNReal (c k))))
    (B : Set ({k : ℕ // k ∈ F} → ℝ)) (hB : MeasurableSet B),
    ν {u : U | (fun k : {k : ℕ // k ∈ F} => inner ℝ (e k) u) ∈ B}
      = ∫⁻ x in {u : U | (fun k : {k : ℕ // k ∈ F} => inner ℝ (e k) u) ∈ B},
          ENNReal.ofReal
            (Real.exp ((∑ k ∈ F, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (x - mUM))
              - (2 : ℝ)⁻¹ * ∑ k ∈ F, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)) ∂μ := by
  /- @proof-region region.target-node.session.b67e813b4d975a28 begin -/
  intro U _ _ _ _ _ _ e c hc μ _ ν _ mUM mNU F hmap_mu hmap_nu B hB
  classical
  set ι : U → ({k : ℕ // k ∈ F} → ℝ) := fun u k => inner ℝ (e k) u with hι
  set Pmu : Measure ({k : ℕ // k ∈ F} → ℝ) :=
    Measure.pi (fun k : {k : ℕ // k ∈ F} =>
      ProbabilityTheory.gaussianReal (inner ℝ (e k) mUM) (Real.toNNReal (c k))) with hPmu
  set Pnu : Measure ({k : ℕ // k ∈ F} → ℝ) :=
    Measure.pi (fun k : {k : ℕ // k ∈ F} =>
      ProbabilityTheory.gaussianReal (inner ℝ (e k) mNU) (Real.toNNReal (c k))) with hPnu
  have hmu : Measure.map ι μ = Pmu := by rw [hι, hPmu]; exact hmap_mu
  have hnu : Measure.map ι ν = Pnu := by rw [hι, hPnu]; exact hmap_nu
  have hι_meas : Measurable ι := by
    rw [hι]
    exact measurable_pi_iff.mpr
      (fun k => (continuous_inner.comp (continuous_const.prodMk continuous_id)).measurable)
  have hchild := statopia_math_node_454462448_6086eebe ({k : ℕ // k ∈ F}) (fun k => c k)
    (fun k => inner ℝ (e k) mUM) (fun k => inner ℝ (e k) mNU) (fun k => hc k)
  have hchild2 := hchild.2.1
  have hLHS : ν {u : U | ι u ∈ B} = Pnu B := by
    rw [show {u : U | ι u ∈ B} = ι ⁻¹' B from rfl, ← hnu, Measure.map_apply hι_meas hB]
  set Φ : ({k : ℕ // k ∈ F} → ℝ) → ENNReal := fun y =>
    ENNReal.ofReal (∏ k : {k : ℕ // k ∈ F}, Real.exp ((c k)⁻¹ * (inner ℝ (e k) mNU - inner ℝ (e k) mUM) * (y k - inner ℝ (e k) mUM) - (2 : ℝ)⁻¹ * ((c k)⁻¹ * (inner ℝ (e k) mNU - inner ℝ (e k) mUM)) * (inner ℝ (e k) mNU - inner ℝ (e k) mUM))) with hΦ
  have hchildΦ : Pnu B = ∫⁻ y in B, Φ y ∂Pmu := by rw [hΦ]; exact hchild2 B hB
  have hΦmeas : Measurable Φ := by
    rw [hΦ]
    apply Measurable.ennreal_ofReal
    have hswap : (fun y : ({k : ℕ // k ∈ F} → ℝ) => ∏ k : {k : ℕ // k ∈ F}, Real.exp ((c k)⁻¹ * (inner ℝ (e k) mNU - inner ℝ (e k) mUM) * (y k - inner ℝ (e k) mUM) - (2 : ℝ)⁻¹ * ((c k)⁻¹ * (inner ℝ (e k) mNU - inner ℝ (e k) mUM)) * (inner ℝ (e k) mNU - inner ℝ (e k) mUM))) = (fun y : ({k : ℕ // k ∈ F} → ℝ) => Real.exp (∑ k : {k : ℕ // k ∈ F}, ((c k)⁻¹ * (inner ℝ (e k) mNU - inner ℝ (e k) mUM) * (y k - inner ℝ (e k) mUM) - (2 : ℝ)⁻¹ * ((c k)⁻¹ * (inner ℝ (e k) mNU - inner ℝ (e k) mUM)) * (inner ℝ (e k) mNU - inner ℝ (e k) mUM)))) := by
      funext y
      rw [Real.exp_sum]
    rw [hswap]
    fun_prop
  have hpt : ∀ x : U, ENNReal.ofReal (Real.exp ((∑ k ∈ F, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (x - mUM)) - (2 : ℝ)⁻¹ * ∑ k ∈ F, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)) = Φ (ι x) := by
    intro x
    have hprod : (∏ k : {k : ℕ // k ∈ F}, Real.exp ((c k)⁻¹ * (inner ℝ (e k) mNU - inner ℝ (e k) mUM) * ((ι x) k - inner ℝ (e k) mUM) - (2 : ℝ)⁻¹ * ((c k)⁻¹ * (inner ℝ (e k) mNU - inner ℝ (e k) mUM)) * (inner ℝ (e k) mNU - inner ℝ (e k) mUM))) = Real.exp ((∑ k ∈ F, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (x - mUM)) - (2 : ℝ)⁻¹ * ∑ k ∈ F, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) := by
      set f : ℕ → ℝ := fun k => (c k)⁻¹ * (inner ℝ (e k) mNU - inner ℝ (e k) mUM) * (inner ℝ (e k) x - inner ℝ (e k) mUM) - (2 : ℝ)⁻¹ * ((c k)⁻¹ * (inner ℝ (e k) mNU - inner ℝ (e k) mUM)) * (inner ℝ (e k) mNU - inner ℝ (e k) mUM) with hf
      rw [← Real.exp_sum]
      congr 1
      simp only [hι]
      rw [show (∑ k : {k : ℕ // k ∈ F}, ((c k)⁻¹ * (inner ℝ (e k) mNU - inner ℝ (e k) mUM) * (inner ℝ (e k) x - inner ℝ (e k) mUM) - (2 : ℝ)⁻¹ * ((c k)⁻¹ * (inner ℝ (e k) mNU - inner ℝ (e k) mUM)) * (inner ℝ (e k) mNU - inner ℝ (e k) mUM))) = ∑ k ∈ F, f k from Finset.sum_coe_sort F f]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [hf, inner_sub_right]
      ring
    simp only [hΦ, hprod]
  have hRHS : ∫⁻ x in {u : U | ι u ∈ B}, ENNReal.ofReal (Real.exp ((∑ k ∈ F, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (x - mUM)) - (2 : ℝ)⁻¹ * ∑ k ∈ F, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)) ∂μ = Pnu B := by
    rw [hchildΦ]
    rw [show {u : U | ι u ∈ B} = ι ⁻¹' B from rfl]
    rw [← hmu]
    rw [setLIntegral_map (μ := μ) (f := Φ) (g := ι) (s := B) hB hΦmeas hι_meas]
    apply lintegral_congr
    intro x
    exact hpt x
  rw [hLHS]
  exact hRHS.symm
  /- @proof-region region.target-node.session.b67e813b4d975a28 end -/

end Statlib.Imported
end

