import Lean
import ProverJobs.ResidualE2ESupport20261106.M_2899ebcb4b6cf51030cf
import ProverJobs.ResidualE2ESupport20261106.M_30e3ebd8c0ecef26f046

namespace PaperProofTasks.ResidualE2ESupport20261106

run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_3089955232_110a7522 : ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {A : Type*} [MeasurableSpace A] (γ : Measure A) [IsProbabilityMeasure γ]
    {ι : Type*} {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    (f : (i : ι) → Ω → β i)
    (hf : ProbabilityTheory.iIndepFun f P),
    ProbabilityTheory.iIndepFun (fun (i : ι) (x : Ω × A) => f i x.1) (Measure.prod P γ) := by
  /- @proof-region region.target-node.session.6c366f46e85287d6 begin -/
  intro Ω _ P _ A _ γ _ ι β _ f hf
  rw [ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul] at hf ⊢
  intro s sets hs
  have hkey : ∀ U : Set Ω, (P.prod γ) (U ×ˢ (Set.univ : Set A)) = P U := by
    intro U
    rw [Measure.prod_prod, measure_univ, mul_one]
  have hpre : ∀ i, (fun x : Ω × A => f i x.1) ⁻¹' sets i
      = (f i ⁻¹' sets i) ×ˢ (Set.univ : Set A) := by
    intro i
    ext x
    simp
  have hinter : (⋂ i ∈ s, (fun x : Ω × A => f i x.1) ⁻¹' sets i)
      = (⋂ i ∈ s, f i ⁻¹' sets i) ×ˢ (Set.univ : Set A) := by
    ext x
    simp [Set.mem_prod]
  show (P.prod γ) (⋂ i ∈ s, (fun x : Ω × A => f i x.1) ⁻¹' sets i)
      = ∏ i ∈ s, (P.prod γ) ((fun x : Ω × A => f i x.1) ⁻¹' sets i)
  calc (P.prod γ) (⋂ i ∈ s, (fun x : Ω × A => f i x.1) ⁻¹' sets i)
      = (P.prod γ) ((⋂ i ∈ s, f i ⁻¹' sets i) ×ˢ (Set.univ : Set A)) := by rw [hinter]
    _ = P (⋂ i ∈ s, f i ⁻¹' sets i) := hkey _
    _ = ∏ i ∈ s, P (f i ⁻¹' sets i) := hf s hs
    _ = ∏ i ∈ s, (P.prod γ) ((f i ⁻¹' sets i) ×ˢ (Set.univ : Set A)) := by
          refine Finset.prod_congr rfl (fun i _ => ?_)
          rw [hkey]
    _ = ∏ i ∈ s, (P.prod γ) ((fun x : Ω × A => f i x.1) ⁻¹' sets i) := by
          refine Finset.prod_congr rfl (fun i _ => ?_)
          rw [hpre]
  /- @proof-region region.target-node.session.6c366f46e85287d6 end -/

end

end Statlib.Imported

