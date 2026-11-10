import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base

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
theorem statopia_math_node_1159502109_f07fd652 : ∀ (ι : Type*) [Fintype ι]
    (μ : ι → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i, ℝ → ENNReal)
    (hmeas : ∀ i, Measurable (f i))
    (hfin : ∀ i, ∀ᵐ x ∂(μ i), f i x < ⊤),
    Measurable (fun y : ι → ℝ => ∏ i, f i (y i)) ∧
      Measure.pi (fun i => (μ i).withDensity (f i)) =
        (Measure.pi μ).withDensity (fun y : ι → ℝ => ∏ i, f i (y i)) ∧
      (∫⁻ y : ι → ℝ, ∏ i, f i (y i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x : ℝ, f i x ∂μ i) := by
  /- @proof-region region.target-node.session.446df4afac19f240 begin -/
  intro ι _ μ _ f hf hfin
  haveI hS : ∀ i, SigmaFinite ((μ i).withDensity (f i)) := fun i =>
    SigmaFinite.withDensity_of_ne_top ((hfin i).mono fun x hx => ne_of_lt hx)
  have key : ∀ (ν : ι → Measure ℝ) [∀ i, SigmaFinite (ν i)] (g : ∀ i, ℝ → ENNReal),
      (∀ i, Measurable (g i)) →
      ∫⁻ y, ∏ i, g i (y i) ∂(Measure.pi ν) = ∏ i, ∫⁻ x, g i x ∂ν i := by
    refine Fintype.induction_empty_option (P := fun (α : Type _) (_ : Fintype α) =>
      ∀ (ν : α → Measure ℝ) [∀ i, SigmaFinite (ν i)] (g : ∀ i, ℝ → ENNReal),
        (∀ i, Measurable (g i)) →
        ∫⁻ y, ∏ i, g i (y i) ∂(Measure.pi ν) = ∏ i, ∫⁻ x, g i x ∂ν i) ?_ ?_ ?_ ι

    · intro α β _ e hα ν _ g hg
      classical
      letI : Fintype α := Fintype.ofEquiv β e.symm
      have hpt : ∀ a : α → ℝ,
          (∏ i : β, g i ((MeasurableEquiv.piCongrLeft (fun _ : β => ℝ) e) a i))
            = ∏ i : α, g (e i) (a i) := by
        intro a
        rw [← Equiv.prod_comp e
          (fun i : β => g i ((MeasurableEquiv.piCongrLeft (fun _ : β => ℝ) e) a i))]
        exact Finset.prod_congr rfl (fun i _ => by
          rw [MeasurableEquiv.piCongrLeft_apply_apply])
      rw [← Measure.pi_map_piCongrLeft e ν, lintegral_map_equiv, lintegral_congr hpt,
        ← Equiv.prod_comp e (fun i : β => ∫⁻ x, g i x ∂ν i),
        hα (fun i => ν (e i)) (fun i => g (e i)) (fun i => hg (e i))]
    · intro ν _ g hg
      have hB : (∏ i, ∫⁻ x, g i x ∂ν i) = (1 : ENNReal) :=
        Finset.prod_eq_one (fun i _ => isEmptyElim i)
      have hpt : ∀ y : PEmpty → ℝ, ∏ i, g i (y i) = (1 : ENNReal) :=
        fun y => Finset.prod_eq_one (fun i _ => isEmptyElim i)
      rw [hB, lintegral_congr hpt, lintegral_const, one_mul, Measure.pi_univ]
      exact Finset.prod_eq_one (fun i _ => isEmptyElim i)
    · intro α _ hα ν _ g hg
      classical
      have hG : Measurable (fun y : α → ℝ => ∏ i, g (some i) (y i)) :=
        Finset.measurable_prod (s := Finset.univ)
          (fun i _ => (hg (some i)).comp (measurable_pi_apply i))
      have hsplit : ∀ z : (α → ℝ) × ℝ,
          (∏ i : Option α,
              g i ((MeasurableEquiv.piOptionEquivProd (fun _ : Option α => ℝ)).symm z i))
            = (∏ i : α, g (some i) (z.1 i)) * g none z.2 := by
        intro z
        rw [Fintype.prod_option]
        exact mul_comm _ _
      rw [← Measure.pi_map_piOptionEquivProd ν, lintegral_map_equiv, lintegral_congr hsplit,
        lintegral_prod_mul hG.aemeasurable (hg none).aemeasurable,
        hα (fun i => ν (some i)) (fun i => g (some i)) (fun i => hg (some i)),
        Fintype.prod_option]
      exact mul_comm _ _
  have hF : Measurable (fun y : ι → ℝ => ∏ i, f i (y i)) :=
    Finset.measurable_prod (s := Finset.univ)
      (fun i _ => (hf i).comp (measurable_pi_apply i))
  have h2 : Measure.pi (fun i => (μ i).withDensity (f i))
      = (Measure.pi μ).withDensity (fun y => ∏ i, f i (y i)) := by
    classical
    refine Measure.pi_eq (fun s hs => ?_)
    have hboxm : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
    have hindic : ∀ a : ι → ℝ,
        (Set.univ.pi s).indicator (fun y => ∏ i, f i (y i)) a
          = ∏ i, (s i).indicator (f i) (a i) := by
      intro a
      simp only [Set.indicator_apply]
      by_cases ha : a ∈ Set.univ.pi s
      · have ha' : ∀ i, a i ∈ s i := by simpa [Set.mem_univ_pi] using ha
        rw [if_pos ha]
        exact Finset.prod_congr rfl (fun i _ => (if_pos (ha' i)).symm)
      · rw [if_neg ha]
        have ha'' : ¬ ∀ i, a i ∈ s i := by simpa [Set.mem_univ_pi] using ha
        obtain ⟨i, hi⟩ := not_forall.mp ha''
        exact (Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_neg hi])).symm
    have hbox : ∫⁻ y in Set.univ.pi s, ∏ i, f i (y i) ∂(Measure.pi μ)
        = ∏ i, ∫⁻ x in s i, f i x ∂μ i := by
      have h0 : ∫⁻ y in Set.univ.pi s, ∏ i, f i (y i) ∂(Measure.pi μ)
          = ∫⁻ y, ∏ i, (s i).indicator (f i) (y i) ∂(Measure.pi μ) := by
        rw [← lintegral_indicator hboxm]
        exact lintegral_congr hindic
      rw [h0, key μ (fun i => (s i).indicator (f i)) (fun i => (hf i).indicator (hs i))]
      exact Finset.prod_congr rfl (fun i _ => lintegral_indicator (hs i) (f i))
    have hL : ((Measure.pi μ).withDensity (fun y => ∏ i, f i (y i))) (Set.univ.pi s)
        = ∫⁻ y in Set.univ.pi s, ∏ i, f i (y i) ∂(Measure.pi μ) := by
      have h1 : ((Measure.pi μ).withDensity (fun y => ∏ i, f i (y i))) (Set.univ.pi s)
          = ∫⁻ y in Set.univ.pi s, (1 : ENNReal)
            ∂((Measure.pi μ).withDensity (fun y => ∏ i, f i (y i))) := by simp
      rw [h1, setLIntegral_withDensity_eq_setLIntegral_mul (Measure.pi μ)
        (f := fun y => ∏ i, f i (y i)) (g := fun _ => (1 : ENNReal))
        hF measurable_const hboxm]
      simp
    have hR : ∀ i, ((μ i).withDensity (f i)) (s i) = ∫⁻ x in s i, f i x ∂μ i := by
      intro i
      have h1 : ((μ i).withDensity (f i)) (s i)
          = ∫⁻ x in s i, (1 : ENNReal) ∂((μ i).withDensity (f i)) := by simp
      rw [h1, setLIntegral_withDensity_eq_setLIntegral_mul (μ i) (f := f i)
        (g := fun _ => (1 : ENNReal)) (hf i) measurable_const (hs i)]
      simp
    calc ((Measure.pi μ).withDensity (fun y => ∏ i, f i (y i))) (Set.univ.pi s)
        = ∫⁻ y in Set.univ.pi s, ∏ i, f i (y i) ∂(Measure.pi μ) := hL
      _ = ∏ i, ∫⁻ x in s i, f i x ∂μ i := hbox
      _ = ∏ i, ((μ i).withDensity (f i)) (s i) :=
          Finset.prod_congr rfl (fun i _ => (hR i).symm)
  exact ⟨hF, h2, key μ f hf⟩
  /- @proof-region region.target-node.session.446df4afac19f240 end -/

end Statlib.Imported
end

