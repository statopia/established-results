import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_40da605aa78ddea0b65f

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
theorem statopia_math_node_2156877478_7316b341 : ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type*} {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (f : ι → Ω → α) (g : ι → Ω → β) (Φ : α × β → γ)
    (hf_indep : iIndepFun f μ)
    (hg_indep : iIndepFun g μ)
    (hfg_indep : IndepFun (fun ω (i : ι) => f i ω) (fun ω (i : ι) => g i ω) μ)
    (hf_meas : ∀ i : ι, AEMeasurable (f i) μ)
    (hg_meas : ∀ i : ι, AEMeasurable (g i) μ)
    (hΦ : Measurable Φ),
    iIndepFun (fun (i : ι) (ω : Ω) => Φ (f i ω, g i ω)) μ := by
  /- @proof-region region.target-node.session.9ab983fb60400c12 begin -/
  intro Ω _ μ _ ι α β γ _ _ _ f g Φ hf_indep hg_indep hfg_indep hf_meas hg_meas hΦ
  have key : iIndepFun (fun (i : ι) (ω : Ω) => (f i ω, g i ω)) μ := by
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro S B hB
    have hfS : iIndepFun (fun (i : ↥S) (ω : Ω) => f ↑i ω) μ :=
      iIndepFun.precomp (g := (Subtype.val : ↥S → ι)) (fun a b h => Subtype.ext h) hf_indep
    have hgS : iIndepFun (fun (i : ↥S) (ω : Ω) => g ↑i ω) μ :=
      iIndepFun.precomp (g := (Subtype.val : ↥S → ι)) (fun a b h => Subtype.ext h) hg_indep
    have hfgS : IndepFun (fun ω (i : ↥S) => f ↑i ω) (fun ω (i : ↥S) => g ↑i ω) μ := by
      have hresα : Measurable (fun x : ι → α => fun i : ↥S => x ↑i) :=
        measurable_pi_iff.mpr (fun i => measurable_pi_apply (↑i : ι))
      have hresβ : Measurable (fun x : ι → β => fun i : ↥S => x ↑i) :=
        measurable_pi_iff.mpr (fun i => measurable_pi_apply (↑i : ι))
      exact hfg_indep.comp hresα hresβ
    have keyS : iIndepFun (fun (i : ↥S) (ω : Ω) => (f ↑i ω, g ↑i ω)) μ :=
      statopia_math_node_1948823760_a64561a6 (fun i : ↥S => f ↑i) (fun i : ↥S => g ↑i)
        hfS hgS hfgS (fun i => hf_meas ↑i) (fun i => hg_meas ↑i)
    have h := (iIndepFun_iff_measure_inter_preimage_eq_mul.mp keyS) Finset.univ
      (sets := fun (i : ↥S) => B ↑i) (fun i _ => hB ↑i i.2)
    have h2 : μ (⋂ i : ↥S, (fun ω => (f ↑i ω, g ↑i ω)) ⁻¹' B ↑i)
        = ∏ i : ↥S, μ ((fun ω => (f ↑i ω, g ↑i ω)) ⁻¹' B ↑i) := by
      simpa using h
    have eL : (⋂ i ∈ S, (fun ω => (f i ω, g i ω)) ⁻¹' B i)
        = (⋂ i : ↥S, (fun ω => (f ↑i ω, g ↑i ω)) ⁻¹' B ↑i) := by
      ext ω
      simp only [Set.mem_iInter]
      exact ⟨fun hc i => hc ↑i i.2, fun hc i hi => hc ⟨i, hi⟩⟩
    have eR : (∏ i ∈ S, μ ((fun ω => (f i ω, g i ω)) ⁻¹' B i))
        = ∏ i : ↥S, μ ((fun ω => (f ↑i ω, g ↑i ω)) ⁻¹' B ↑i) := by
      exact (Finset.prod_coe_sort (s := S)
        (f := fun j => μ ((fun ω => (f j ω, g j ω)) ⁻¹' B j))).symm
    rw [eL, eR]
    exact h2
  exact key.comp (fun _ => Φ) (fun _ => hΦ)
  /- @proof-region region.target-node.session.9ab983fb60400c12 end -/

end Statlib.Imported

