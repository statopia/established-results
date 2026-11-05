import ProverJobs.jobea4701a9720de21f681f2da3.Vocabulary
import ProverJobs.jobea4701a9720de21f681f2da3.Base
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_4000542074_30367f47_51acbb0f

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
open Statlib.Imported
open Statlib.Imported.T24
open T24

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
namespace Statlib.Imported
noncomputable section
open T24

set_option autoImplicit false in
theorem statopia_math_node_1040909254_bc7c3bc1 : ∀ {Ω : Type*} [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    (mu nu : ProbabilityMeasure Ω) (zeta : ℝ) (hzeta : 0 < zeta)
    (psi : Ω → ℝ) (hpsi : Measurable psi) (hpsi0 : ∀ x : Ω, 0 ≤ psi x)
    (hExp : Integrable (fun x : Ω => Real.exp (zeta * psi x)) (mu : Measure Ω))
    (A B : EReal) (hA : A ≠ ⊤) (hB : B ≠ ⊤)
    (hKL : ENNReal.toEReal (InformationTheory.klDiv (nu : Measure Ω) (mu : Measure Ω)) = A + B),
    (∫⁻ x, ENNReal.ofReal (psi x) ∂(nu : Measure Ω)) ≠ ⊤ := by
  /- @proof-region region.target-node.session.5485d18274668780 begin -/
  intro Ω _ _ _ _ mu nu zeta hzeta psi hpsi hpsi0 hExp A B hA hB hKL
  have h0top : (0 : EReal) ≠ ⊤ := by intro h; cases h
  have hadd : ∀ (x y : EReal), x ≠ ⊤ → y ≠ ⊤ → x + y ≠ ⊤ := by
    intro x y hx hy
    rcases x with _ | a
    · rcases y with _ | b
      · intro h; cases h
      · rcases b with _ | b
        · exact fun _ => hy rfl
        · intro h; cases h
    · rcases a with _ | a
      · exact fun _ => hx rfl
      · rcases y with _ | b
        · intro h; cases h
        · rcases b with _ | b
          · exact fun _ => hy rfl
          · intro h; cases h
  have hmul : ∀ (r : ℝ) (y : EReal), 0 < r → y ≠ ⊤ → ((r : ℝ) : EReal) * y ≠ ⊤ := by
    intro r y hr hy
    rcases y with _ | b
    · intro h
      have h' : (if 0 < r then (⊥ : EReal) else if r = 0 then (0 : EReal) else ⊤) = ⊤ := h
      rw [if_pos hr] at h'
      cases h'

    · rcases b with _ | b
      · exact fun _ => hy rfl
      · intro h; cases h

  have hcorr : (∫⁻ x, ENNReal.ofReal (-(psi x)) ∂(nu : Measure Ω)) = 0 := by
    have h0 : ∀ x : Ω, ENNReal.ofReal (-(psi x)) = 0 := fun x =>
      ENNReal.ofReal_of_nonpos (by linarith [hpsi0 x])
    simp [h0]

  have hmain := statopia_math_node_4000542074_30367f47 mu nu zeta hzeta psi hpsi hExp
  rw [hcorr, hKL] at hmain
  have hz0 : ENNReal.toEReal (0 : ENNReal) = (0 : EReal) := by simp
  rw [hz0] at hmain
  have hlog : ((Real.log (∫ x, Real.exp (zeta * psi x) ∂(mu : Measure Ω)) : ℝ) : EReal) ≠ ⊤ := by
    intro h; cases h
  have hzinv : (0 : ℝ) < zeta⁻¹ := by positivity
  have hAB : A + B ≠ ⊤ := hadd A B hA hB
  have hS : A + B + ((Real.log (∫ x, Real.exp (zeta * psi x) ∂(mu : Measure Ω)) : ℝ) : EReal) ≠ ⊤ :=
    hadd (A + B) _ hAB hlog
  have hfin : ((zeta⁻¹ : ℝ) : EReal) * (A + B + ((Real.log (∫ x, Real.exp (zeta * psi x) ∂(mu : Measure Ω)) : ℝ) : EReal)) + (0 : EReal) ≠ ⊤ :=
    hadd _ _ (hmul _ _ hzinv hS) h0top

  intro ha
  have htop : ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (psi x) ∂(nu : Measure Ω)) = ⊤ := by
    rw [ha]; simp
  have hXtop : ((zeta⁻¹ : ℝ) : EReal) * (A + B + ((Real.log (∫ x, Real.exp (zeta * psi x) ∂(mu : Measure Ω)) : ℝ) : EReal)) + (0 : EReal) = ⊤ := by
    rw [← top_le_iff, ← htop]
    exact hmain
  exact hfin hXtop
  /- @proof-region region.target-node.session.5485d18274668780 end -/

end
end Statlib.Imported
