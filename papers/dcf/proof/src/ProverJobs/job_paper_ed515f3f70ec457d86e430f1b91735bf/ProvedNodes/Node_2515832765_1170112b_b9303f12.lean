import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_2237482606_7ec44b40_bb587f1e
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_3058610448_3f0d893f_7e436c3d

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
theorem statopia_math_node_2515832765_1170112b : ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n m p : ℕ) (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
    (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
    (hn : 0 < n) (hm : 0 < m) (hp : 0 < p)
    (hXm : ∀ i : Fin n, Measurable (X i)) (hYm : ∀ i : Fin m, Measurable (Y i))
    (hFm : ∀ i : Fin n, Measurable (F i)) (hGm : ∀ i : Fin m, Measurable (G i))
    (hindep : iIndepFun (β := fun _ => Fin p → ℝ) (jointFam X Y F G) P)
    (hX2 : ∀ (i : Fin n) (j : Fin p), MemLp (fun ω => X i ω j) 2 P)
    (hY2 : ∀ (i : Fin m) (j : Fin p), MemLp (fun ω => Y i ω j) 2 P)
    (hXint : ∀ (i : Fin n) (j : Fin p), ∫ ω, X i ω j ∂P = muX j)
    (hYint : ∀ (i : Fin m) (j : Fin p), ∫ ω, Y i ω j ∂P = muY j)
    (hFgauss : ∀ i : Fin n,
      IsCenteredGaussianVector P (fun ω j => F i ω j - muX j) (covX P muX X i))
    (hGgauss : ∀ i : Fin m,
      IsCenteredGaussianVector P (fun ω j => G i ω j - muY j) (covY P muY Y i))
    (v t : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (z : Fin p → ℝ),
    (P.prod P) {x : Ω × Ω | ∀ j : Fin p,
        Real.sqrt (t * v) * combVec n m (delta n m) muX muY (fun i => X i x.1) (fun i => Y i x.1) j
      + Real.sqrt (t * (1 - v)) * combVec n m (delta n m) muX muY (fun i => F i x.1) (fun i => G i x.1) j
      + Real.sqrt (1 - t) * combVec n m (delta n m) muX muY (fun i => F i x.2) (fun i => G i x.2) j
        ≤ z j}
      = P {ω : Ω | ∀ j : Fin p,
        Real.sqrt (t * v) * combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j
      + Real.sqrt (1 - t * v) * combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j
        ≤ z j} := by
  /- @proof-region region.target-node.session.0ca6026b8e454eb0 begin -/
  intro Ω _ P _ n m p delta muX muY X Y F G hn hm hp hXm hYm hFm hGm hindep hX2 hY2 hXint hYint
    hFgauss hGgauss v t hv0 hv1 ht0 ht1 z
  set Udata : Ω → Fin p → ℝ :=
    fun ω => combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) with hUdata
  set UG : Ω → Fin p → ℝ :=
    fun ω => combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) with hUG
  set FL : Ω × Ω → Fin p → ℝ := fun x j =>
    Real.sqrt (t * v) * Udata x.1 j + Real.sqrt (t * (1 - v)) * UG x.1 j
      + Real.sqrt (1 - t) * UG x.2 j with hFL
  set FR : Ω → Fin p → ℝ := fun ω j =>
    Real.sqrt (t * v) * Udata ω j + Real.sqrt (1 - t * v) * UG ω j with hFR
  have hUdata_meas : Measurable Udata := by
    rw [hUdata]
    refine measurable_pi_iff.mpr (fun j => ?_)
    have hXj : Measurable (fun ω => ∑ i : Fin n, X i ω j) :=
      Finset.measurable_sum _ (fun i _ => (measurable_pi_apply j).comp (hXm i))
    have hYj : Measurable (fun ω => ∑ i : Fin m, Y i ω j) :=
      Finset.measurable_sum _ (fun i _ => (measurable_pi_apply j).comp (hYm i))
    simp only [combVec, normSum]
    fun_prop
  have hUG_meas : Measurable UG := by
    rw [hUG]
    refine measurable_pi_iff.mpr (fun j => ?_)
    have hFj : Measurable (fun ω => ∑ i : Fin n, F i ω j) :=
      Finset.measurable_sum _ (fun i _ => (measurable_pi_apply j).comp (hFm i))
    have hGj : Measurable (fun ω => ∑ i : Fin m, G i ω j) :=
      Finset.measurable_sum _ (fun i _ => (measurable_pi_apply j).comp (hGm i))
    simp only [combVec, normSum]
    fun_prop
  have hLmeas : Measurable FL := by
    rw [hFL]
    refine measurable_pi_iff.mpr (fun j => ?_)
    have h1 : Measurable (fun x : Ω × Ω => Udata x.1 j) :=
      (measurable_pi_apply j).comp (hUdata_meas.comp measurable_fst)
    have h2 : Measurable (fun x : Ω × Ω => UG x.1 j) :=
      (measurable_pi_apply j).comp (hUG_meas.comp measurable_fst)
    have h3 : Measurable (fun x : Ω × Ω => UG x.2 j) :=
      (measurable_pi_apply j).comp (hUG_meas.comp measurable_snd)
    fun_prop
  have hRmeas : Measurable FR := by
    rw [hFR]
    refine measurable_pi_iff.mpr (fun j => ?_)
    have h1 : Measurable (fun ω => Udata ω j) := (measurable_pi_apply j).comp hUdata_meas
    have h2 : Measurable (fun ω => UG ω j) := (measurable_pi_apply j).comp hUG_meas
    fun_prop
  have hUGgauss : IsCenteredGaussianVector P UG
      ((n : ℝ)⁻¹ • (∑ i : Fin n, covX P muX X i)
        + (delta n m) ^ 2 • ((m : ℝ)⁻¹ • (∑ i : Fin m, covY P muY Y i))) :=
    statopia_math_node_2237482606_7ec44b40 P n m p hn hm hp (delta n m) muX muY X Y F G
      hFm hGm hindep hFgauss hGgauss
  have hlaw : Measure.map FL (P.prod P) = Measure.map FR P := by
    have hWU : IndepFun Udata UG P := by
      set S : Finset (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) :=
        Finset.univ.image (fun k : Fin n ⊕ Fin m =>
          Sum.elim (fun i : Fin n => (Sum.inl i : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))))
            (fun i : Fin m => (Sum.inr (Sum.inl i) : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)))) k) with hSdef
      set T : Finset (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) :=
        Finset.univ.image (fun k : Fin n ⊕ Fin m =>
          Sum.elim
            (fun i : Fin n => (Sum.inr (Sum.inr (Sum.inl i)) : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))))
            (fun i : Fin m => (Sum.inr (Sum.inr (Sum.inr i)) : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))))
            k) with hTdef
      have hx : ∀ i : Fin n, (Sum.inl i : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) ∈ S :=
        fun i => Finset.mem_image.mpr ⟨Sum.inl i, Finset.mem_univ _, rfl⟩
      have hy : ∀ i : Fin m, (Sum.inr (Sum.inl i) : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) ∈ S :=
        fun i => Finset.mem_image.mpr ⟨Sum.inr i, Finset.mem_univ _, rfl⟩
      have hFx : ∀ i : Fin n,
          (Sum.inr (Sum.inr (Sum.inl i)) : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) ∈ T :=
        fun i => Finset.mem_image.mpr ⟨Sum.inl i, Finset.mem_univ _, rfl⟩
      have hGx : ∀ i : Fin m,
          (Sum.inr (Sum.inr (Sum.inr i)) : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) ∈ T :=
        fun i => Finset.mem_image.mpr ⟨Sum.inr i, Finset.mem_univ _, rfl⟩
      have hdisj : Disjoint S T := by
        rw [Finset.disjoint_left]
        intro a ha hb
        simp only [hSdef, hTdef, Finset.mem_image, Finset.mem_univ, true_and] at ha hb
        obtain ⟨k, hk⟩ := ha
        obtain ⟨k', hk'⟩ := hb
        have hEq := hk.trans hk'.symm
        rcases k with i | i
        · rcases k' with j | j
          · cases hEq
          · cases hEq
        · rcases k' with j | j
          · injection hEq with hc
            cases hc
          · injection hEq with hc
            cases hc
      have hmeas : ∀ i : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)),
          Measurable (jointFam X Y F G i) := by
        intro i
        cases i with
        | inl i => exact hXm i
        | inr i =>
          cases i with
          | inl i => exact hYm i
          | inr i =>
            cases i with
            | inl i => exact hFm i
            | inr i => exact hGm i
      have hblocks := ProbabilityTheory.iIndepFun.indepFun_finset S T hdisj hindep hmeas
      set phi : ((i : ↥S) → Fin p → ℝ) → Fin p → ℝ := fun v =>
        combVec n m (delta n m) muX muY (fun i : Fin n => v ⟨Sum.inl i, hx i⟩)
          (fun i : Fin m => v ⟨Sum.inr (Sum.inl i), hy i⟩) with hphidef
      set psi : ((i : ↥T) → Fin p → ℝ) → Fin p → ℝ := fun v =>
        combVec n m (delta n m) muX muY
          (fun i : Fin n => v ⟨Sum.inr (Sum.inr (Sum.inl i)), hFx i⟩)
          (fun i : Fin m => v ⟨Sum.inr (Sum.inr (Sum.inr i)), hGx i⟩) with hpsidef
      have hphi : Measurable phi := by
        rw [hphidef]
        refine measurable_pi_iff.mpr (fun j => ?_)
        have hs1 : Measurable (fun v : (i : ↥S) → Fin p → ℝ =>
            ∑ i : Fin n, v ⟨Sum.inl i, hx i⟩ j) :=
          Finset.measurable_sum _ (fun i _ =>
            (measurable_pi_apply j).comp (measurable_pi_apply (⟨Sum.inl i, hx i⟩ : ↥S)))
        have hs2 : Measurable (fun v : (i : ↥S) → Fin p → ℝ =>
            ∑ i : Fin m, v ⟨Sum.inr (Sum.inl i), hy i⟩ j) :=
          Finset.measurable_sum _ (fun i _ =>
            (measurable_pi_apply j).comp (measurable_pi_apply (⟨Sum.inr (Sum.inl i), hy i⟩ : ↥S)))
        simp only [combVec, normSum]
        fun_prop
      have hpsi : Measurable psi := by
        rw [hpsidef]
        refine measurable_pi_iff.mpr (fun j => ?_)
        have hs1 : Measurable (fun v : (i : ↥T) → Fin p → ℝ =>
            ∑ i : Fin n, v ⟨Sum.inr (Sum.inr (Sum.inl i)), hFx i⟩ j) :=
          Finset.measurable_sum _ (fun i _ =>
            (measurable_pi_apply j).comp
              (measurable_pi_apply (⟨Sum.inr (Sum.inr (Sum.inl i)), hFx i⟩ : ↥T)))
        have hs2 : Measurable (fun v : (i : ↥T) → Fin p → ℝ =>
            ∑ i : Fin m, v ⟨Sum.inr (Sum.inr (Sum.inr i)), hGx i⟩ j) :=
          Finset.measurable_sum _ (fun i _ =>
            (measurable_pi_apply j).comp
              (measurable_pi_apply (⟨Sum.inr (Sum.inr (Sum.inr i)), hGx i⟩ : ↥T)))
        simp only [combVec, normSum]
        fun_prop
      exact ProbabilityTheory.IndepFun.comp hblocks hphi hpsi
    have h1 : 0 ≤ t * (1 - v) := mul_nonneg ht0 (by linarith)
    have h2 : 0 ≤ 1 - t := by linarith
    have h3 : 0 ≤ 1 - t * v := by nlinarith [mul_le_mul ht1 hv1 hv0 zero_le_one]
    have hb : 0 ≤ Real.sqrt (t * (1 - v)) := Real.sqrt_nonneg _
    have hc : 0 ≤ Real.sqrt (1 - t) := Real.sqrt_nonneg _
    have hd : 0 ≤ Real.sqrt (1 - t * v) := Real.sqrt_nonneg _
    have hbc : Real.sqrt (t * (1 - v)) ^ 2 + Real.sqrt (1 - t) ^ 2
        = Real.sqrt (1 - t * v) ^ 2 := by
      rw [Real.sq_sqrt h1, Real.sq_sqrt h2, Real.sq_sqrt h3]
      ring
    exact statopia_math_node_3058610448_3f0d893f Ω P p (by omega)
      ((n : ℝ)⁻¹ • (∑ i : Fin n, covX P muX X i)
        + (delta n m) ^ 2 • ((m : ℝ)⁻¹ • (∑ i : Fin m, covY P muY Y i)))
      Udata UG hUdata_meas hUG_meas hUGgauss hWU
      (Real.sqrt (t * v)) (Real.sqrt (t * (1 - v))) (Real.sqrt (1 - t))
      (Real.sqrt (1 - t * v)) hb hc hd hbc
  have hset : MeasurableSet {y : Fin p → ℝ | ∀ j : Fin p, y j ≤ z j} := by
    have hEq : {y : Fin p → ℝ | ∀ j : Fin p, y j ≤ z j}
        = ⋂ j : Fin p, {y : Fin p → ℝ | y j ≤ z j} := by
      ext y
      simp
    rw [hEq]
    exact MeasurableSet.iInter (fun j => measurableSet_le (measurable_pi_apply j) measurable_const)
  have hgoal : (P.prod P) {x : Ω × Ω | ∀ j : Fin p,
      Real.sqrt (t * v) * Udata x.1 j + Real.sqrt (t * (1 - v)) * UG x.1 j
        + Real.sqrt (1 - t) * UG x.2 j ≤ z j}
      = P {ω : Ω | ∀ j : Fin p,
      Real.sqrt (t * v) * Udata ω j + Real.sqrt (1 - t * v) * UG ω j ≤ z j} := by
    have e1 : {x : Ω × Ω | ∀ j : Fin p,
        Real.sqrt (t * v) * Udata x.1 j + Real.sqrt (t * (1 - v)) * UG x.1 j
          + Real.sqrt (1 - t) * UG x.2 j ≤ z j}
        = FL ⁻¹' {y : Fin p → ℝ | ∀ j : Fin p, y j ≤ z j} := rfl
    have e2 : {ω : Ω | ∀ j : Fin p,
        Real.sqrt (t * v) * Udata ω j + Real.sqrt (1 - t * v) * UG ω j ≤ z j}
        = FR ⁻¹' {y : Fin p → ℝ | ∀ j : Fin p, y j ≤ z j} := rfl
    calc (P.prod P) {x : Ω × Ω | ∀ j : Fin p,
        Real.sqrt (t * v) * Udata x.1 j + Real.sqrt (t * (1 - v)) * UG x.1 j
          + Real.sqrt (1 - t) * UG x.2 j ≤ z j}
        = (Measure.map FL (P.prod P)) {y : Fin p → ℝ | ∀ j : Fin p, y j ≤ z j} := by
          rw [e1, Measure.map_apply hLmeas hset]
      _ = (Measure.map FR P) {y : Fin p → ℝ | ∀ j : Fin p, y j ≤ z j} := by
          rw [hlaw]
      _ = P {ω : Ω | ∀ j : Fin p,
        Real.sqrt (t * v) * Udata ω j + Real.sqrt (1 - t * v) * UG ω j ≤ z j} := by
          rw [Measure.map_apply hRmeas hset, e2]
  exact hgoal
  /- @proof-region region.target-node.session.0ca6026b8e454eb0 end -/

end

end Statlib.Imported

