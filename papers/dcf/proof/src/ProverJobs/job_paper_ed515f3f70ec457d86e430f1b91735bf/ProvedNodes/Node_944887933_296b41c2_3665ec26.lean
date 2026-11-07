import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
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
theorem statopia_math_node_944887933_296b41c2 : ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ι : Type*) (β : ι → Type*) [mβ : ∀ i, MeasurableSpace (β i)]
    (f : (i : ι) → Ω → β i) (hfm : ∀ i, Measurable (f i))
    (hf : iIndepFun (β := β) f P),
    iIndepFun (β := fun e : ι ⊕ ι => Sum.elim β β e)
      (m := fun e => match e with
        | Sum.inl i => mβ i
        | Sum.inr i => mβ i)
      (fun e => match e with
        | Sum.inl i => fun x : Ω × Ω => f i x.1
        | Sum.inr i => fun x : Ω × Ω => f i x.2)
      (P.prod P) := by
  /- @proof-region region.target-node.session.ebb42536fc073884 begin -/
  intro Ω _ P _ ι β _ f hfm hf
  refine iIndepFun_iff_measure_inter_preimage_eq_mul.mpr ?_
  intro S sets hS
  classical
  let K : (e : ι ⊕ ι) → Ω × Ω → Sum.elim β β e := fun e =>
    match e with
    | Sum.inl i => fun x => f i x.1
    | Sum.inr i => fun x => f i x.2
  let T1 : Finset ι := S.preimage Sum.inl (fun _ _ _ _ h => Sum.inl_injective h)
  let T2 : Finset ι := S.preimage Sum.inr (fun _ _ _ _ h => Sum.inr_injective h)
  have hmem1 : ∀ i, i ∈ T1 ↔ Sum.inl i ∈ S := fun i => Finset.mem_preimage
  have hmem2 : ∀ i, i ∈ T2 ↔ Sum.inr i ∈ S := fun i => Finset.mem_preimage
  change (P.prod P) (⋂ e ∈ S, K e ⁻¹' sets e) = ∏ e ∈ S, (P.prod P) (K e ⁻¹' sets e)
  have himg1 : ∀ i, (Sum.inl i : ι ⊕ ι) ∈ T1.image (Sum.inl : ι → ι ⊕ ι) ↔ i ∈ T1 := by
    intro i
    constructor
    · intro h
      obtain ⟨a, ha, hEq⟩ := Finset.mem_image.1 h
      rwa [Sum.inl_injective hEq] at ha
    · intro h
      exact Finset.mem_image.2 ⟨i, h, rfl⟩
  have himg2 : ∀ i, (Sum.inr i : ι ⊕ ι) ∈ T2.image (Sum.inr : ι → ι ⊕ ι) ↔ i ∈ T2 := by
    intro i
    constructor
    · intro h
      obtain ⟨a, ha, hEq⟩ := Finset.mem_image.1 h
      rwa [Sum.inr_injective hEq] at ha
    · intro h
      exact Finset.mem_image.2 ⟨i, h, rfl⟩
  have hno1 : ∀ i, (Sum.inl i : ι ⊕ ι) ∉ T2.image (Sum.inr : ι → ι ⊕ ι) := by
    intro i h
    obtain ⟨a, -, ha⟩ := Finset.mem_image.1 h
    cases ha
  have hno2 : ∀ i, (Sum.inr i : ι ⊕ ι) ∉ T1.image (Sum.inl : ι → ι ⊕ ι) := by
    intro i h
    obtain ⟨a, -, ha⟩ := Finset.mem_image.1 h
    cases ha
  have hA : P (⋂ i ∈ T1, f i ⁻¹' sets (Sum.inl i)) = ∏ i ∈ T1, P (f i ⁻¹' sets (Sum.inl i)) := by
    have h := (iIndepFun_iff_measure_inter_preimage_eq_mul.mp hf) T1
      (sets := fun i => sets (Sum.inl i)) (fun i hi => hS (Sum.inl i) ((hmem1 i).1 hi))
    simpa using h
  have hB : P (⋂ i ∈ T2, f i ⁻¹' sets (Sum.inr i)) = ∏ i ∈ T2, P (f i ⁻¹' sets (Sum.inr i)) := by
    have h := (iIndepFun_iff_measure_inter_preimage_eq_mul.mp hf) T2
      (sets := fun i => sets (Sum.inr i)) (fun i hi => hS (Sum.inr i) ((hmem2 i).1 hi))
    simpa using h
  have hInter : (⋂ e ∈ S, K e ⁻¹' sets e)
      = (⋂ i ∈ T1, f i ⁻¹' sets (Sum.inl i)) ×ˢ (⋂ i ∈ T2, f i ⁻¹' sets (Sum.inr i)) := by
    ext x
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_prod]
    constructor
    · intro h
      exact ⟨fun i hi => h (Sum.inl i) ((hmem1 i).1 hi),
        fun i hi => h (Sum.inr i) ((hmem2 i).1 hi)⟩
    · rintro ⟨h1, h2⟩ e he
      cases e with
      | inl i => exact h1 i ((hmem1 i).2 he)
      | inr i => exact h2 i ((hmem2 i).2 he)
  have hmarg1 : ∀ i, (P.prod P) (K (Sum.inl i) ⁻¹' sets (Sum.inl i)) = P (f i ⁻¹' sets (Sum.inl i)) := by
    intro i
    have hK : K (Sum.inl i) = fun x : Ω × Ω => f i x.1 := rfl
    have hset : K (Sum.inl i) ⁻¹' sets (Sum.inl i)
        = (f i ⁻¹' sets (Sum.inl i)) ×ˢ (Set.univ : Set Ω) := by
      rw [hK]
      ext x
      simp
    rw [hset, Measure.prod_prod, measure_univ, mul_one]
  have hmarg2 : ∀ i, (P.prod P) (K (Sum.inr i) ⁻¹' sets (Sum.inr i)) = P (f i ⁻¹' sets (Sum.inr i)) := by
    intro i
    have hK : K (Sum.inr i) = fun x : Ω × Ω => f i x.2 := rfl
    have hset : K (Sum.inr i) ⁻¹' sets (Sum.inr i)
        = (Set.univ : Set Ω) ×ˢ (f i ⁻¹' sets (Sum.inr i)) := by
      rw [hK]
      ext x
      simp
    rw [hset, Measure.prod_prod, measure_univ, one_mul]
  have hSsplit : S = T1.image Sum.inl ∪ T2.image Sum.inr := by
    ext e
    cases e with
    | inl i =>
        rw [Finset.mem_union, himg1 i, hmem1 i]
        exact ⟨fun h => Or.inl h, fun h => h.elim id (fun h2 => absurd h2 (hno1 i))⟩
    | inr i =>
        rw [Finset.mem_union, himg2 i, hmem2 i]
        exact ⟨fun h => Or.inr h, fun h => h.elim (fun h1 => absurd h1 (hno2 i)) id⟩
  have hdisj : Disjoint (T1.image Sum.inl) (T2.image Sum.inr) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    obtain ⟨a, -, ha⟩ := Finset.mem_image.1 he1
    rw [← ha] at he2
    exact hno1 a he2
  have hprod : (∏ e ∈ S, (P.prod P) (K e ⁻¹' sets e))
      = (∏ i ∈ T1, P (f i ⁻¹' sets (Sum.inl i)))
        * (∏ i ∈ T2, P (f i ⁻¹' sets (Sum.inr i))) := by
    rw [hSsplit, Finset.prod_union hdisj]
    congr 1
    · rw [Finset.prod_image (fun i _ j _ h => Sum.inl_injective h)]
      exact Finset.prod_congr rfl (fun i _ => hmarg1 i)
    · rw [Finset.prod_image (fun i _ j _ h => Sum.inr_injective h)]
      exact Finset.prod_congr rfl (fun i _ => hmarg2 i)
  calc (P.prod P) (⋂ e ∈ S, K e ⁻¹' sets e)
      = (P.prod P) ((⋂ i ∈ T1, f i ⁻¹' sets (Sum.inl i))
          ×ˢ (⋂ i ∈ T2, f i ⁻¹' sets (Sum.inr i))) := by rw [hInter]
    _ = P (⋂ i ∈ T1, f i ⁻¹' sets (Sum.inl i))
          * P (⋂ i ∈ T2, f i ⁻¹' sets (Sum.inr i)) := by rw [Measure.prod_prod]
    _ = (∏ i ∈ T1, P (f i ⁻¹' sets (Sum.inl i)))
          * (∏ i ∈ T2, P (f i ⁻¹' sets (Sum.inr i))) := by rw [hA, hB]
    _ = ∏ e ∈ S, (P.prod P) (K e ⁻¹' sets e) := by rw [hprod]
  /- @proof-region region.target-node.session.ebb42536fc073884 end -/

end

end Statlib.Imported

