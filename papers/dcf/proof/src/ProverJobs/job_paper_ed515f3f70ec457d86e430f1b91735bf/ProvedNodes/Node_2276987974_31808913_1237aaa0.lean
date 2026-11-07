import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_2024687868_9ec8273d_4e9143f4
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_2237482606_7ec44b40_bb587f1e
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_2419531658_cacaaf43_308f6840

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
theorem statopia_math_node_2276987974_31808913 : ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n m p : ℕ) (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
    (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
    (hn : 0 < n) (hm : 0 < m) (hp : 0 < p)
    (hX : ∀ i : Fin n, Measurable (X i)) (hY : ∀ i : Fin m, Measurable (Y i))
    (hF : ∀ i : Fin n, Measurable (F i)) (hG : ∀ i : Fin m, Measurable (G i))
    (hindep : iIndepFun (β := fun _ => Fin p → ℝ) (jointFam X Y F G) P)
    (hFcov : ∀ i : Fin n,
      IsCenteredGaussianVector P (fun ω j => F i ω j - muX j) (covX P muX X i))
    (hGcov : ∀ i : Fin m,
      IsCenteredGaussianVector P (fun ω j => G i ω j - muY j) (covY P muY Y i))
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1),
    Measure.map
        (fun x : Ω × Ω => fun j : Fin p =>
          Real.sqrt (t * v) *
              combVec n m (delta n m) muX muY (fun i => X i x.1) (fun i => Y i x.1) j
            + Real.sqrt (t * (1 - v)) *
              combVec n m (delta n m) muX muY (fun i => F i x.1) (fun i => G i x.1) j
            + Real.sqrt (1 - t) *
              combVec n m (delta n m) muX muY (fun i => F i x.2) (fun i => G i x.2) j)
        (P.prod P)
      = Measure.map
        (fun ω : Ω => fun j : Fin p =>
          Real.sqrt (t * v) *
              combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j
            + Real.sqrt (1 - t * v) *
              combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j)
        P := by
  /- @proof-region region.target-node.session.9bb857747e1e8725 begin -/
  intro Ω _ P _ n m p delta muX muY X Y F G hn hm hp hX hY hF hG hindep hFcov hGcov v hv0 hv1 t ht0 ht1
  set A : Ω → Fin p → ℝ := fun ω => combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) with hA
  set B : Ω → Fin p → ℝ := fun ω => combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) with hB
  have hAm : Measurable A := by
    rw [hA, measurable_pi_iff]
    intro j
    simp only [combVec, normSum]
    measurability
  have hBm : Measurable B := by
    rw [hB, measurable_pi_iff]
    intro j
    simp only [combVec, normSum]
    measurability
  have hSB : IsCenteredGaussianVector P B
      ((n : ℝ)⁻¹ • (∑ i : Fin n, covX P muX X i) +
        (delta n m) ^ 2 • ((m : ℝ)⁻¹ • (∑ i : Fin m, covY P muY Y i))) := by
    have h := statopia_math_node_2237482606_7ec44b40 P n m p hn hm hp (delta n m) muX muY X Y F G
      hF hG hindep hFcov hGcov
    rw [hB]
    exact h
  have hbc : Real.sqrt (t * (1 - v)) ^ 2 + Real.sqrt (1 - t) ^ 2 = Real.sqrt (1 - t * v) ^ 2 := by
    rw [Real.sq_sqrt (by nlinarith), Real.sq_sqrt (by linarith), Real.sq_sqrt (by nlinarith)]
    ring
  have hclos : Measure.map
      (fun q : (Fin p → ℝ) × (Fin p → ℝ) => fun j : Fin p =>
        Real.sqrt (t * (1 - v)) * q.1 j + Real.sqrt (1 - t) * q.2 j)
      ((Measure.map B P).prod (Measure.map B P))
      = Measure.map (fun g : Fin p → ℝ => fun j : Fin p => Real.sqrt (1 - t * v) * g j)
          (Measure.map B P) :=
    statopia_math_node_2024687868_9ec8273d Ω P p hp
      ((n : ℝ)⁻¹ • (∑ i : Fin n, covX P muX X i) +
        (delta n m) ^ 2 • ((m : ℝ)⁻¹ • (∑ i : Fin m, covY P muY Y i))) B hBm hSB
      (Real.sqrt (t * (1 - v))) (Real.sqrt (1 - t)) (Real.sqrt (1 - t * v))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hbc
  have hfam_meas : ∀ i : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)), Measurable (jointFam X Y F G i) := by
    rintro (i | i | i | i)
    · exact hX i
    · exact hY i
    · exact hF i
    · exact hG i
  let S : Finset (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) :=
    (Finset.univ.image (fun i : Fin n => (Sum.inl i : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))))) ∪
      (Finset.univ.image (fun i : Fin m => (Sum.inr (Sum.inl i) : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)))))
  let T : Finset (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) :=
    (Finset.univ.image (fun i : Fin n =>
        (Sum.inr (Sum.inr (Sum.inl i)) : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))))) ∪
      (Finset.univ.image (fun i : Fin m =>
        (Sum.inr (Sum.inr (Sum.inr i)) : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)))))
  have hdisj : Disjoint S T := by
    have hSval : S = (Finset.univ.image (fun i : Fin n =>
          (Sum.inl i : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))))) ∪
        (Finset.univ.image (fun i : Fin m =>
          (Sum.inr (Sum.inl i) : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))))) := rfl
    have hTval : T = (Finset.univ.image (fun i : Fin n =>
          (Sum.inr (Sum.inr (Sum.inl i)) : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))))) ∪
        (Finset.univ.image (fun i : Fin m =>
          (Sum.inr (Sum.inr (Sum.inr i)) : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))))) := rfl
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [hSval] at ha
    rw [hTval] at hb
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at ha hb
    rcases ha with ⟨i, -, rfl⟩ | ⟨i, -, rfl⟩ <;> rcases hb with ⟨j, -, h⟩ | ⟨j, -, h⟩
    all_goals simp_all
  have hTmS : Measurable (fun a => fun (i : {i // i ∈ S}) => jointFam X Y F G (↑i) a) := by
    rw [measurable_pi_iff]
    intro i
    exact hfam_meas ↑i
  have hTmT : Measurable (fun a => fun (j : {j // j ∈ T}) => jointFam X Y F G (↑j) a) := by
    rw [measurable_pi_iff]
    intro j
    exact hfam_meas ↑j
  let gS : ({i // i ∈ S} → Fin p → ℝ) → Fin p → ℝ := fun v =>
    combVec n m (delta n m) muX muY
      (fun i : Fin n => v ⟨Sum.inl i,
        Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))⟩)
      (fun i : Fin m => v ⟨Sum.inr (Sum.inl i),
        Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))⟩)
  let gT : ({j // j ∈ T} → Fin p → ℝ) → Fin p → ℝ := fun v =>
    combVec n m (delta n m) muX muY
      (fun i : Fin n => v ⟨Sum.inr (Sum.inr (Sum.inl i)),
        Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))⟩)
      (fun i : Fin m => v ⟨Sum.inr (Sum.inr (Sum.inr i)),
        Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))⟩)
  have hgSm : Measurable gS := by
    rw [measurable_pi_iff]
    intro j
    show Measurable (fun v : {i // i ∈ S} → Fin p → ℝ => (combVec n m (delta n m) muX muY
      (fun i : Fin n => v ⟨Sum.inl i,
        Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))⟩)
      (fun i : Fin m => v ⟨Sum.inr (Sum.inl i),
        Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))⟩)) j)
    simp only [combVec, normSum]
    fun_prop
  have hgTm : Measurable gT := by
    rw [measurable_pi_iff]
    intro j
    show Measurable (fun v : {j // j ∈ T} → Fin p → ℝ => (combVec n m (delta n m) muX muY
      (fun i : Fin n => v ⟨Sum.inr (Sum.inr (Sum.inl i)),
        Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))⟩)
      (fun i : Fin m => v ⟨Sum.inr (Sum.inr (Sum.inr i)),
        Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))⟩)) j)
    simp only [combVec, normSum]
    fun_prop
  have hST : (fun a => fun (i : {i // i ∈ S}) => jointFam X Y F G (↑i) a) ⟂ᵢ[P]
      (fun a => fun (j : {j // j ∈ T}) => jointFam X Y F G (↑j) a) :=
    ProbabilityTheory.iIndepFun.indepFun_finset S T hdisj hindep hfam_meas
  have hSTpair : Measure.map (fun a => ((fun (i : {i // i ∈ S}) => jointFam X Y F G (↑i) a),
        (fun (j : {j // j ∈ T}) => jointFam X Y F G (↑j) a))) P
      = (Measure.map (fun a => fun (i : {i // i ∈ S}) => jointFam X Y F G (↑i) a) P).prod
        (Measure.map (fun a => fun (j : {j // j ∈ T}) => jointFam X Y F G (↑j) a) P) :=
    (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map hTmS.aemeasurable hTmT.aemeasurable).mp hST
  have hpullS : Measure.map gS
      (Measure.map (fun a => fun (i : {i // i ∈ S}) => jointFam X Y F G (↑i) a) P) = Measure.map A P := by
    rw [Measure.map_map]
    all_goals first
      | rfl
      | exact hgSm
      | exact hTmS
  have hpullT : Measure.map gT
      (Measure.map (fun a => fun (j : {j // j ∈ T}) => jointFam X Y F G (↑j) a) P) = Measure.map B P := by
    rw [Measure.map_map]
    all_goals first
      | rfl
      | exact hgTm
      | exact hTmT
  have hcomp : Measure.map (fun ω : Ω => (A ω, B ω)) P
      = Measure.map (Prod.map gS gT) (Measure.map (fun a => ((fun (i : {i // i ∈ S}) => jointFam X Y F G (↑i) a),
          (fun (j : {j // j ∈ T}) => jointFam X Y F G (↑j) a))) P) := by
    rw [Measure.map_map]
    · rfl
    · fun_prop
    · fun_prop
  have hpair : Measure.map (fun ω : Ω => (A ω, B ω)) P
      = (Measure.map A P).prod (Measure.map B P) := by
    rw [hcomp, hSTpair,
      ← Measure.map_prod_map
        (μa := Measure.map (fun a => fun (i : {i // i ∈ S}) => jointFam X Y F G (↑i) a) P)
        (μc := Measure.map (fun a => fun (j : {j // j ∈ T}) => jointFam X Y F G (↑j) a) P)
        (f := gS) (g := gT) hgSm hgTm,
      hpullS, hpullT]
  have hpairm : Measurable (fun ω : Ω => (A ω, B ω)) := by fun_prop
  have htriple : Measure.map (fun x : Ω × Ω => ((A x.1, B x.1), B x.2)) (P.prod P)
      = ((Measure.map A P).prod (Measure.map B P)).prod (Measure.map B P) := by
    rw [← hpair]
    exact (Measure.map_prod_map (μa := P) (μc := P)
      (f := fun ω : Ω => (A ω, B ω)) (g := B) hpairm hBm).symm
  have hmTM : Measurable (fun x : Ω × Ω => ((A x.1, B x.1), B x.2)) := by fun_prop
  have hmF0 : Measurable (fun x : Ω × Ω => fun j : Fin p =>
      Real.sqrt (t * v) * A x.1 j + (Real.sqrt (t * (1 - v)) * B x.1 j + Real.sqrt (1 - t) * B x.2 j)) := by
    rw [measurable_pi_iff]
    intro j
    fun_prop
  have hmG1 : Measurable (fun z : ((Fin p → ℝ) × (Fin p → ℝ)) × (Fin p → ℝ) => fun j : Fin p =>
      Real.sqrt (t * v) * z.1.1 j + (Real.sqrt (t * (1 - v)) * z.1.2 j + Real.sqrt (1 - t) * z.2 j)) := by
    rw [measurable_pi_iff]
    intro j
    fun_prop
  have S1 : Measure.map (fun x : Ω × Ω => fun j : Fin p =>
        Real.sqrt (t * v) * A x.1 j + (Real.sqrt (t * (1 - v)) * B x.1 j + Real.sqrt (1 - t) * B x.2 j))
      (P.prod P)
      = Measure.map (fun z : ((Fin p → ℝ) × (Fin p → ℝ)) × (Fin p → ℝ) => fun j : Fin p =>
        Real.sqrt (t * v) * z.1.1 j + (Real.sqrt (t * (1 - v)) * z.1.2 j + Real.sqrt (1 - t) * z.2 j))
        (((Measure.map A P).prod (Measure.map B P)).prod (Measure.map B P)) := by
    rw [← htriple, Measure.map_map]
    all_goals first
      | rfl
      | exact hmF0
      | exact hmG1
      | exact hmTM
  have hmG2 : Measurable (fun z : (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) => fun j : Fin p =>
      Real.sqrt (t * v) * z.1 j + (Real.sqrt (t * (1 - v)) * z.2.1 j + Real.sqrt (1 - t) * z.2.2 j)) := by
    rw [measurable_pi_iff]
    intro j
    fun_prop
  have hmPA : Measurable (⇑(MeasurableEquiv.prodAssoc (α := Fin p → ℝ) (β := Fin p → ℝ)
      (γ := Fin p → ℝ))) := MeasurableEquiv.measurable _
  have S2 : Measure.map (fun z : ((Fin p → ℝ) × (Fin p → ℝ)) × (Fin p → ℝ) => fun j : Fin p =>
        Real.sqrt (t * v) * z.1.1 j + (Real.sqrt (t * (1 - v)) * z.1.2 j + Real.sqrt (1 - t) * z.2 j))
        (((Measure.map A P).prod (Measure.map B P)).prod (Measure.map B P))
      = Measure.map (fun z : (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) => fun j : Fin p =>
        Real.sqrt (t * v) * z.1 j + (Real.sqrt (t * (1 - v)) * z.2.1 j + Real.sqrt (1 - t) * z.2.2 j))
        ((Measure.map A P).prod ((Measure.map B P).prod (Measure.map B P))) := by
    rw [← Measure.prodAssoc_prod (μ := Measure.map A P) (ν := Measure.map B P) (τ := Measure.map B P),
      Measure.map_map]
    all_goals first
      | rfl
      | exact hmG1
      | exact hmG2
      | exact hmPA
  have hmW : Measurable (fun q : (Fin p → ℝ) × (Fin p → ℝ) => fun j : Fin p =>
      Real.sqrt (t * (1 - v)) * q.1 j + Real.sqrt (1 - t) * q.2 j) := by
    rw [measurable_pi_iff]
    intro j
    fun_prop
  have hmDg : Measurable (fun g : Fin p → ℝ => fun j : Fin p => Real.sqrt (1 - t * v) * g j) := by
    rw [measurable_pi_iff]
    intro j
    fun_prop
  have hmH2 : Measurable (fun z : (Fin p → ℝ) × (Fin p → ℝ) => fun j : Fin p =>
      Real.sqrt (t * v) * z.1 j + z.2 j) := by
    rw [measurable_pi_iff]
    intro j
    fun_prop
  have hmHfin : Measurable (fun z : (Fin p → ℝ) × (Fin p → ℝ) => fun j : Fin p =>
      Real.sqrt (t * v) * z.1 j + Real.sqrt (1 - t * v) * z.2 j) := by
    rw [measurable_pi_iff]
    intro j
    fun_prop
  have hmPW : Measurable (Prod.map (id : (Fin p → ℝ) → (Fin p → ℝ))
      (fun q : (Fin p → ℝ) × (Fin p → ℝ) => fun j : Fin p =>
      Real.sqrt (t * (1 - v)) * q.1 j + Real.sqrt (1 - t) * q.2 j)) := by fun_prop
  have hmPDg : Measurable (Prod.map (id : (Fin p → ℝ) → (Fin p → ℝ))
      (fun g : Fin p → ℝ => fun j : Fin p => Real.sqrt (1 - t * v) * g j)) := by fun_prop
  have hpmW : Measure.map (Prod.map id (fun q : (Fin p → ℝ) × (Fin p → ℝ) => fun j : Fin p =>
        Real.sqrt (t * (1 - v)) * q.1 j + Real.sqrt (1 - t) * q.2 j))
        ((Measure.map A P).prod ((Measure.map B P).prod (Measure.map B P)))
      = (Measure.map A P).prod (Measure.map (fun q : (Fin p → ℝ) × (Fin p → ℝ) => fun j : Fin p =>
        Real.sqrt (t * (1 - v)) * q.1 j + Real.sqrt (1 - t) * q.2 j)
        ((Measure.map B P).prod (Measure.map B P))) := by
    rw [← Measure.map_prod_map (μa := Measure.map A P)
      (μc := (Measure.map B P).prod (Measure.map B P))
      (f := id) (g := fun q : (Fin p → ℝ) × (Fin p → ℝ) => fun j : Fin p =>
        Real.sqrt (t * (1 - v)) * q.1 j + Real.sqrt (1 - t) * q.2 j)
      measurable_id hmW, Measure.map_id]
  have S3 : Measure.map (fun z : (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) => fun j : Fin p =>
        Real.sqrt (t * v) * z.1 j + (Real.sqrt (t * (1 - v)) * z.2.1 j + Real.sqrt (1 - t) * z.2.2 j))
        ((Measure.map A P).prod ((Measure.map B P).prod (Measure.map B P)))
      = Measure.map (fun z : (Fin p → ℝ) × (Fin p → ℝ) => fun j : Fin p =>
        Real.sqrt (t * v) * z.1 j + z.2 j)
        ((Measure.map A P).prod (Measure.map (fun q : (Fin p → ℝ) × (Fin p → ℝ) => fun j : Fin p =>
          Real.sqrt (t * (1 - v)) * q.1 j + Real.sqrt (1 - t) * q.2 j)
          ((Measure.map B P).prod (Measure.map B P)))) := by
    rw [← hpmW, Measure.map_map]
    all_goals first
      | rfl
      | exact hmG2
      | exact hmH2
      | exact hmPW
  have S4 : Measure.map (fun z : (Fin p → ℝ) × (Fin p → ℝ) => fun j : Fin p =>
        Real.sqrt (t * v) * z.1 j + z.2 j)
        ((Measure.map A P).prod (Measure.map (fun q : (Fin p → ℝ) × (Fin p → ℝ) => fun j : Fin p =>
          Real.sqrt (t * (1 - v)) * q.1 j + Real.sqrt (1 - t) * q.2 j)
          ((Measure.map B P).prod (Measure.map B P))))
      = Measure.map (fun z : (Fin p → ℝ) × (Fin p → ℝ) => fun j : Fin p =>
        Real.sqrt (t * v) * z.1 j + z.2 j)
        ((Measure.map A P).prod (Measure.map (fun g : Fin p → ℝ => fun j : Fin p =>
          Real.sqrt (1 - t * v) * g j) (Measure.map B P))) := by
    rw [hclos]
  have hpmD : Measure.map (Prod.map id (fun g : Fin p → ℝ => fun j : Fin p =>
        Real.sqrt (1 - t * v) * g j)) ((Measure.map A P).prod (Measure.map B P))
      = (Measure.map A P).prod (Measure.map (fun g : Fin p → ℝ => fun j : Fin p =>
        Real.sqrt (1 - t * v) * g j) (Measure.map B P)) := by
    rw [← Measure.map_prod_map (μa := Measure.map A P) (μc := Measure.map B P)
      (f := id) (g := fun g : Fin p → ℝ => fun j : Fin p => Real.sqrt (1 - t * v) * g j)
      measurable_id hmDg, Measure.map_id]
  have S5 : Measure.map (fun z : (Fin p → ℝ) × (Fin p → ℝ) => fun j : Fin p =>
        Real.sqrt (t * v) * z.1 j + z.2 j)
        ((Measure.map A P).prod (Measure.map (fun g : Fin p → ℝ => fun j : Fin p =>
          Real.sqrt (1 - t * v) * g j) (Measure.map B P)))
      = Measure.map (fun z : (Fin p → ℝ) × (Fin p → ℝ) => fun j : Fin p =>
        Real.sqrt (t * v) * z.1 j + Real.sqrt (1 - t * v) * z.2 j)
        ((Measure.map A P).prod (Measure.map B P)) := by
    rw [← hpmD, Measure.map_map]
    all_goals first
      | rfl
      | exact hmH2
      | exact hmHfin
      | exact hmPDg
  have SR : Measure.map (fun z : (Fin p → ℝ) × (Fin p → ℝ) => fun j : Fin p =>
        Real.sqrt (t * v) * z.1 j + Real.sqrt (1 - t * v) * z.2 j)
        ((Measure.map A P).prod (Measure.map B P))
      = Measure.map (fun ω : Ω => fun j : Fin p =>
        Real.sqrt (t * v) * A ω j + Real.sqrt (1 - t * v) * B ω j) P := by
    rw [← hpair, Measure.map_map]
    all_goals first
      | rfl
      | exact hmHfin
      | exact hpairm
  have goal_eq : Measure.map (fun x : Ω × Ω => fun j : Fin p =>
        Real.sqrt (t * v) * A x.1 j + Real.sqrt (t * (1 - v)) * B x.1 j + Real.sqrt (1 - t) * B x.2 j)
        (P.prod P)
      = Measure.map (fun x : Ω × Ω => fun j : Fin p =>
        Real.sqrt (t * v) * A x.1 j + (Real.sqrt (t * (1 - v)) * B x.1 j + Real.sqrt (1 - t) * B x.2 j))
        (P.prod P) := by
    congr 1
    funext x j
    ring
  change Measure.map (fun x : Ω × Ω => fun j : Fin p =>
      Real.sqrt (t * v) * A x.1 j + Real.sqrt (t * (1 - v)) * B x.1 j + Real.sqrt (1 - t) * B x.2 j)
      (P.prod P)
    = Measure.map (fun ω : Ω => fun j : Fin p =>
      Real.sqrt (t * v) * A ω j + Real.sqrt (1 - t * v) * B ω j) P
  rw [goal_eq]
  exact (((S1.trans S2).trans S3).trans S4).trans (S5.trans SR)
  /- @proof-region region.target-node.session.9bb857747e1e8725 end -/

end

end Statlib.Imported

