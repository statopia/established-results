import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_944887933_296b41c2_3665ec26

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
theorem statopia_math_node_3430447628_ae1e147f : ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n m p : ℕ) (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
    (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
    (hXm : ∀ i, Measurable (X i)) (hYm : ∀ i, Measurable (Y i))
    (hFm : ∀ i, Measurable (F i)) (hGm : ∀ i, Measurable (G i))
    (hindep : iIndepFun (β := fun _ => Fin p → ℝ) (jointFam X Y F G) P)
    (kap : (Fin p → ℝ) → ℝ) (hkap : ContDiff ℝ 1 kap)
    (v t : ℝ) (i : Fin m) (j : Fin p),
    (let Zrest : Ω × Ω → Fin p → ℝ := fun x k =>
      (∑ i' : Fin n, (Real.sqrt (n : ℝ))⁻¹ *
          (Real.sqrt t * (Real.sqrt v * (X i' x.1 k - muX k) +
              Real.sqrt (1 - v) * (F i' x.1 k - muX k)) +
            Real.sqrt (1 - t) * (F i' x.2 k - muX k)))
        + (∑ i' : Fin m, if i' = i then 0 else
            (Real.sqrt (m : ℝ))⁻¹ * delta n m *
              (Real.sqrt t * (Real.sqrt v * (Y i' x.1 k - muY k) +
                  Real.sqrt (1 - v) * (G i' x.1 k - muY k)) +
                Real.sqrt (1 - t) * (G i' x.2 k - muY k)))
     let Psi : Ω × Ω → ℝ := fun x =>
       (fderiv ℝ kap (Zrest x)) (Pi.single j (1 : ℝ))
     IndepFun Psi (fun x : Ω × Ω => (Y i x.1, (G i x.1, G i x.2))) (P.prod P)) := by
  /- @proof-region region.target-node.session.13bbbcebf71a4ef9 begin -/
  classical
  intro Ω _ P _ n m p delta muX muY X Y F G hXm hYm hFm hGm hindep kap hkap v t i j
  dsimp only
  let ι := Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))
  let J : ι → Ω → (Fin p → ℝ) := jointFam X Y F G
  have hJmeas : ∀ s, Measurable (J s) := by
    intro s
    match s with
    | Sum.inl i' => exact hXm i'
    | Sum.inr (Sum.inl i') => exact hYm i'
    | Sum.inr (Sum.inr (Sum.inl i')) => exact hFm i'
    | Sum.inr (Sum.inr (Sum.inr i')) => exact hGm i'
  let γ : (ι ⊕ ι) → Type := Sum.elim (fun _ : ι => (Fin p → ℝ)) (fun _ : ι => (Fin p → ℝ))
  let mγ : (e : ι ⊕ ι) → MeasurableSpace (γ e) := fun e => match e with
    | Sum.inl _ => (inferInstance : MeasurableSpace (Fin p → ℝ))
    | Sum.inr _ => (inferInstance : MeasurableSpace (Fin p → ℝ))
  let K : (e : ι ⊕ ι) → Ω × Ω → γ e := fun e => match e with
      | Sum.inl s => fun x => J s x.1
      | Sum.inr s => fun x => J s x.2
  have hK : iIndepFun (β := γ) (m := mγ) K (P.prod P) :=
    statopia_math_node_944887933_296b41c2 Ω P ι (fun _ : ι => (Fin p → ℝ)) J hJmeas hindep
  have hKmeas : ∀ e, @Measurable (Ω × Ω) (γ e) _ (mγ e) (K e) := by
    intro e
    match e with
    | Sum.inl s => exact (hJmeas s).comp measurable_fst
    | Sum.inr s => exact (hJmeas s).comp measurable_snd
  let g : (e : ι ⊕ ι) → γ e → (Fin p → ℝ) := fun e => match e with
    | Sum.inl _ => (fun z => z)
    | Sum.inr _ => (fun z => z)
  have hg : ∀ e, @Measurable (γ e) (Fin p → ℝ) (mγ e) _ (g e) := by
    intro e
    match e with
    | Sum.inl _ => exact measurable_id
    | Sum.inr _ => exact measurable_id
  let K' : (e : ι ⊕ ι) → Ω × Ω → (Fin p → ℝ) := fun e => g e ∘ K e
  have hK' : iIndepFun (β := fun _ : ι ⊕ ι => (Fin p → ℝ)) K' (P.prod P) :=
    hK.comp (γ := fun _ : ι ⊕ ι => (Fin p → ℝ)) g hg
  have hK'meas : ∀ e, Measurable (K' e) := by
    intro e
    exact (hg e).comp (hKmeas e)
  let a : ι := Sum.inr (Sum.inl i)
  let b : ι := Sum.inr (Sum.inr (Sum.inr i))
  let S : Finset ι := Finset.univ \ {a, b}
  let T : Finset ι := {a, b}
  let SK : Finset (ι ⊕ ι) := S.image Sum.inl ∪ S.image Sum.inr
  let TK : Finset (ι ⊕ ι) := T.image Sum.inl ∪ T.image Sum.inr
  have hdisj : Disjoint SK TK := by
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy hxy
    simp only [SK, TK, S, T, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
      Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, true_and] at hx hy
    rcases hx with ⟨s, hsS, hsx⟩ | ⟨s, hsS, hsx⟩ <;>
      rcases hy with ⟨t, htT, hty⟩ | ⟨t, htT, hty⟩
    · have hst : s = t := Sum.inl_injective (hsx.trans (hxy.trans hty.symm))
      rcases htT with h | h
      · exact hsS (Or.inl (hst.trans h))
      · exact hsS (Or.inr (hst.trans h))
    · exact Sum.inl_ne_inr (hsx.trans (hxy.trans hty.symm))
    · exact Sum.inr_ne_inl (hsx.trans (hxy.trans hty.symm))
    · have hst : s = t := Sum.inr_injective (hsx.trans (hxy.trans hty.symm))
      rcases htT with h | h
      · exact hsS (Or.inl (hst.trans h))
      · exact hsS (Or.inr (hst.trans h))
  have hind : (fun a (i : ↥SK) => K' (↑i) a) ⟂ᵢ[P.prod P] (fun a (i : ↥TK) => K' (↑i) a) :=
    ProbabilityTheory.iIndepFun.indepFun_finset SK TK hdisj hK' hK'meas
  have mem_inl : ∀ e : ι, e ∈ S → Sum.inl e ∈ SK :=
    fun e he => Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨e, he, rfl⟩))
  have mem_inr : ∀ e : ι, e ∈ S → Sum.inr e ∈ SK :=
    fun e he => Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨e, he, rfl⟩))
  have memSx : ∀ i' : Fin n, Sum.inl i' ∈ S :=
    fun i' => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp [a, b]⟩
  have memSf : ∀ i' : Fin n, Sum.inr (Sum.inr (Sum.inl i')) ∈ S :=
    fun i' => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp [a, b]⟩
  have memSy : ∀ (i' : Fin m), i' ≠ i → Sum.inr (Sum.inl i') ∈ S :=
    fun i' h => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp [a, b, h]⟩
  have memSg : ∀ (i' : Fin m), i' ≠ i → Sum.inr (Sum.inr (Sum.inr i')) ∈ S :=
    fun i' h => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp [a, b, h]⟩
  let US : Ω × Ω → (e : ↥SK) → (Fin p → ℝ) := fun x e => K' (↑e) x
  let ZrestOf : ((e : ↥SK) → (Fin p → ℝ)) → (Fin p → ℝ) := fun u k =>
    (∑ i' : Fin n, (Real.sqrt (n : ℝ))⁻¹ *
        (Real.sqrt t * (Real.sqrt v * ((u ⟨Sum.inl (Sum.inl i'), mem_inl (Sum.inl i') (memSx i')⟩) k - muX k) +
            Real.sqrt (1 - v) * ((u ⟨Sum.inl (Sum.inr (Sum.inr (Sum.inl i'))),
              mem_inl (Sum.inr (Sum.inr (Sum.inl i'))) (memSf i')⟩) k - muX k)) +
          Real.sqrt (1 - t) * ((u ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inl i'))),
            mem_inr (Sum.inr (Sum.inr (Sum.inl i'))) (memSf i')⟩) k - muX k)))
      + (∑ i' : Fin m, if hii : i' = i then 0 else
          (Real.sqrt (m : ℝ))⁻¹ * delta n m *
            (Real.sqrt t * (Real.sqrt v * ((u ⟨Sum.inl (Sum.inr (Sum.inl i')),
                mem_inl (Sum.inr (Sum.inl i')) (memSy i' hii)⟩) k - muY k) +
                Real.sqrt (1 - v) * ((u ⟨Sum.inl (Sum.inr (Sum.inr (Sum.inr i'))),
                  mem_inl (Sum.inr (Sum.inr (Sum.inr i'))) (memSg i' hii)⟩) k - muY k)) +
              Real.sqrt (1 - t) * ((u ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inr i'))),
                mem_inr (Sum.inr (Sum.inr (Sum.inr i'))) (memSg i' hii)⟩) k - muY k)))
  have hZrestOf : Measurable ZrestOf := by
    rw [measurable_pi_iff]
    intro k
    dsimp only [ZrestOf]
    refine Measurable.add ?_ ?_
    · exact Finset.measurable_sum _ (fun i' _ => by fun_prop)
    · exact Finset.measurable_sum _ (fun i' _ => by
        by_cases hii : i' = i
        · simp only [dif_pos hii]
          exact measurable_const
        · simp only [dif_neg hii]
          fun_prop)
  let UT : Ω × Ω → (e : ↥TK) → (Fin p → ℝ) := fun x e => K' (↑e) x
  let Ψ : ((e : ↥TK) → (Fin p → ℝ)) → (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) := fun u =>
    (u ⟨Sum.inl a, Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨a, by simp [T], rfl⟩))⟩,
      (u ⟨Sum.inl b, Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨b, by simp [T], rfl⟩))⟩,
        u ⟨Sum.inr b, Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨b, by simp [T], rfl⟩))⟩))
  have hΨ : Measurable Ψ := by fun_prop
  let φ : (Fin p → ℝ) → ℝ := fun z => (fderiv ℝ kap z) (Pi.single j 1)
  have hφ : Measurable φ := measurable_fderiv_apply_const ℝ kap (Pi.single j 1)
  have hff : (fun x : Ω × Ω => φ (ZrestOf (US x))) ⟂ᵢ[P.prod P] (fun x : Ω × Ω => Ψ (UT x)) :=
    hind.comp (hφ.comp hZrestOf) hΨ
  let ZrestFn : Ω × Ω → (Fin p → ℝ) := fun x k =>
    (∑ i' : Fin n, (Real.sqrt (n : ℝ))⁻¹ *
        (Real.sqrt t * (Real.sqrt v * (X i' x.1 k - muX k) +
            Real.sqrt (1 - v) * (F i' x.1 k - muX k)) +
          Real.sqrt (1 - t) * (F i' x.2 k - muX k)))
      + (∑ i' : Fin m, if i' = i then 0 else
          (Real.sqrt (m : ℝ))⁻¹ * delta n m *
            (Real.sqrt t * (Real.sqrt v * (Y i' x.1 k - muY k) +
                Real.sqrt (1 - v) * (G i' x.1 k - muY k)) +
              Real.sqrt (1 - t) * (G i' x.2 k - muY k)))
  have cx : ∀ (i' : Fin n) (x : Ω × Ω) (k : Fin p),
      (US x ⟨Sum.inl (Sum.inl i'), mem_inl (Sum.inl i') (memSx i')⟩) k = X i' x.1 k := by
    intro i' x k
    simp only [US, K', Function.comp_apply, K, J, jointFam, g]
  have cf1 : ∀ (i' : Fin n) (x : Ω × Ω) (k : Fin p),
      (US x ⟨Sum.inl (Sum.inr (Sum.inr (Sum.inl i'))), mem_inl (Sum.inr (Sum.inr (Sum.inl i'))) (memSf i')⟩) k = F i' x.1 k := by
    intro i' x k
    simp only [US, K', Function.comp_apply, K, J, jointFam, g]
  have cf2 : ∀ (i' : Fin n) (x : Ω × Ω) (k : Fin p),
      (US x ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inl i'))), mem_inr (Sum.inr (Sum.inr (Sum.inl i'))) (memSf i')⟩) k = F i' x.2 k := by
    intro i' x k
    simp only [US, K', Function.comp_apply, K, J, jointFam, g]
  have cy : ∀ (i' : Fin m) (hh : i' ≠ i) (x : Ω × Ω) (k : Fin p),
      (US x ⟨Sum.inl (Sum.inr (Sum.inl i')), mem_inl (Sum.inr (Sum.inl i')) (memSy i' hh)⟩) k = Y i' x.1 k := by
    intro i' hh x k
    simp only [US, K', Function.comp_apply, K, J, jointFam, g]
  have cg1 : ∀ (i' : Fin m) (hh : i' ≠ i) (x : Ω × Ω) (k : Fin p),
      (US x ⟨Sum.inl (Sum.inr (Sum.inr (Sum.inr i'))), mem_inl (Sum.inr (Sum.inr (Sum.inr i'))) (memSg i' hh)⟩) k = G i' x.1 k := by
    intro i' hh x k
    simp only [US, K', Function.comp_apply, K, J, jointFam, g]
  have cg2 : ∀ (i' : Fin m) (hh : i' ≠ i) (x : Ω × Ω) (k : Fin p),
      (US x ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inr i'))), mem_inr (Sum.inr (Sum.inr (Sum.inr i'))) (memSg i' hh)⟩) k = G i' x.2 k := by
    intro i' hh x k
    simp only [US, K', Function.comp_apply, K, J, jointFam, g]
  have hZeq : ∀ x : Ω × Ω, ZrestOf (US x) = ZrestFn x := by
    intro x
    funext k
    have hX : (∑ i' : Fin n, (Real.sqrt (n : ℝ))⁻¹ * (Real.sqrt t * (Real.sqrt v * ((US x ⟨Sum.inl (Sum.inl i'), mem_inl (Sum.inl i') (memSx i')⟩) k - muX k) + Real.sqrt (1 - v) * ((US x ⟨Sum.inl (Sum.inr (Sum.inr (Sum.inl i'))), mem_inl (Sum.inr (Sum.inr (Sum.inl i'))) (memSf i')⟩) k - muX k)) + Real.sqrt (1 - t) * ((US x ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inl i'))), mem_inr (Sum.inr (Sum.inr (Sum.inl i'))) (memSf i')⟩) k - muX k))) = (∑ i' : Fin n, (Real.sqrt (n : ℝ))⁻¹ * (Real.sqrt t * (Real.sqrt v * (X i' x.1 k - muX k) + Real.sqrt (1 - v) * (F i' x.1 k - muX k)) + Real.sqrt (1 - t) * (F i' x.2 k - muX k))) := by
      apply Finset.sum_congr rfl
      intro i' _
      simp only [cx i' x k, cf1 i' x k, cf2 i' x k]
    have hY : (∑ i' : Fin m, if hii : i' = i then 0 else (Real.sqrt (m : ℝ))⁻¹ * delta n m * (Real.sqrt t * (Real.sqrt v * ((US x ⟨Sum.inl (Sum.inr (Sum.inl i')), mem_inl (Sum.inr (Sum.inl i')) (memSy i' hii)⟩) k - muY k) + Real.sqrt (1 - v) * ((US x ⟨Sum.inl (Sum.inr (Sum.inr (Sum.inr i'))), mem_inl (Sum.inr (Sum.inr (Sum.inr i'))) (memSg i' hii)⟩) k - muY k)) + Real.sqrt (1 - t) * ((US x ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inr i'))), mem_inr (Sum.inr (Sum.inr (Sum.inr i'))) (memSg i' hii)⟩) k - muY k))) = (∑ i' : Fin m, if i' = i then 0 else (Real.sqrt (m : ℝ))⁻¹ * delta n m * (Real.sqrt t * (Real.sqrt v * (Y i' x.1 k - muY k) + Real.sqrt (1 - v) * (G i' x.1 k - muY k)) + Real.sqrt (1 - t) * (G i' x.2 k - muY k))) := by
      apply Finset.sum_congr rfl
      intro i' _
      by_cases h : i' = i
      · simp only [dif_pos h, if_pos h]
      · simp only [dif_neg h, if_neg h, cy i' h x k, cg1 i' h x k, cg2 i' h x k]
    simp only [ZrestOf, ZrestFn, hX, hY]
  have hBeq : ∀ x : Ω × Ω, Ψ (UT x) = (Y i x.1, (G i x.1, G i x.2)) := by
    intro x
    simp only [Ψ, UT, K', Function.comp_apply, K, J, jointFam, g, a, b]
  have hA : (fun x : Ω × Ω => φ (ZrestOf (US x))) =
      (fun x : Ω × Ω => (fderiv ℝ kap (ZrestFn x)) (Pi.single j 1)) := by
    funext x
    simp only [φ, hZeq x]
  have hB : (fun x : Ω × Ω => Ψ (UT x)) =
      (fun x : Ω × Ω => (Y i x.1, (G i x.1, G i x.2))) := by
    funext x
    exact hBeq x
  rw [hA, hB] at hff
  exact hff
  /- @proof-region region.target-node.session.13bbbcebf71a4ef9 end -/

end

end Statlib.Imported

