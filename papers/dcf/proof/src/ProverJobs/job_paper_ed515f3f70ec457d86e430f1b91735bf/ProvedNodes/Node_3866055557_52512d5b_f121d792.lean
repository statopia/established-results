import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_1649031325_12d7295c_13e7bff5
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_219120413_99b9d052_0aa6365d
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_2194576110_d2ad0cef_60d45604
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_3430447628_ae1e147f_4d81461a

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
theorem statopia_math_node_3866055557_52512d5b : ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n m p : ℕ) (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
    (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
    (hn : 0 < n) (hm : 0 < m) (hp : 0 < p) (hlogp : 0 < Real.log (p : ℝ))
    (hdelta : delta n m ≠ 0)
    (hXm : ∀ i : Fin n, Measurable (X i))
    (hYm : ∀ i : Fin m, Measurable (Y i))
    (hFm : ∀ i : Fin n, Measurable (F i))
    (hGm : ∀ i : Fin m, Measurable (G i))
    (hindep : iIndepFun (β := fun _ => Fin p → ℝ) (jointFam X Y F G) P)
    (hXmean : ∀ (i : Fin n) (j : Fin p), ∫ ω, X i ω j ∂P = muX j)
    (hYmean : ∀ (i : Fin m) (j : Fin p), ∫ ω, Y i ω j ∂P = muY j)
    (hXL2 : ∀ (i : Fin n) (j : Fin p), MemLp (fun ω => X i ω j) 2 P)
    (hYL2 : ∀ (i : Fin m) (j : Fin p), MemLp (fun ω => Y i ω j) 2 P)
    (hX3 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |X i ω j - muX j| ^ 3) P)
    (hY3 : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => |Y i ω j - muY j| ^ 3) P)
    (hF3 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |F i ω j - muX j| ^ 3) P)
    (hG3 : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => |G i ω j - muY j| ^ 3) P)
    (hFcov : ∀ i : Fin n,
      IsCenteredGaussianVector P (fun ω j => F i ω j - muX j) (covX P muX X i))
    (hGcov : ∀ i : Fin m,
      IsCenteredGaussianVector P (fun ω j => G i ω j - muY j) (covY P muY Y i))
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (phi1 phi2 : ℝ) (hphi1 : 1 ≤ phi1) (hphi2 : 1 ≤ phi2)
    (y : Fin p → ℝ) (phi0 : ℝ → ℝ) (hphi0_cont : ContDiff ℝ 3 phi0)
    (hphi0_left : ∀ z : ℝ, z ≤ 0 → phi0 z = 1)
    (hphi0_right : ∀ z : ℝ, 1 ≤ z → phi0 z = 0)
    (hphi0_range : ∀ z : ℝ, phi0 z ∈ Set.Icc (0 : ℝ) 1)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (i : Fin m) (j : Fin p),
    (let phi : ℝ := min phi1 phi2
     let beta : ℝ := phi * Real.log (p : ℝ)
     let KAP : (Fin p → ℝ) → ℝ := fun w =>
       phi0 (phi * (beta⁻¹ * Real.log (∑ q : Fin p, Real.exp (beta * (w q - y q)))))
     let Zss : Ω × Ω → Fin p → ℝ := fun x k =>
       (Real.sqrt (m : ℝ))⁻¹ * delta n m *
         (Real.sqrt t * (Real.sqrt v * (Y i x.1 k - muY k) + Real.sqrt (1 - v) * (G i x.1 k - muY k))
           + Real.sqrt (1 - t) * (G i x.2 k - muY k))
     let Zrest : Ω × Ω → Fin p → ℝ := fun x k =>
       (∑ i2 : Fin n,
          (Real.sqrt (n : ℝ))⁻¹ *
            (Real.sqrt t * (Real.sqrt v * (X i2 x.1 k - muX k) + Real.sqrt (1 - v) * (F i2 x.1 k - muX k))
              + Real.sqrt (1 - t) * (F i2 x.2 k - muX k)))
       + (∑ i2 : Fin m, if i2 = i then 0 else
          (Real.sqrt (m : ℝ))⁻¹ * delta n m *
            (Real.sqrt t * (Real.sqrt v * (Y i2 x.1 k - muY k) + Real.sqrt (1 - v) * (G i2 x.1 k - muY k))
              + Real.sqrt (1 - t) * (G i2 x.2 k - muY k)))
     let Zd : Ω × Ω → ℝ := fun x =>
       (Real.sqrt (m : ℝ))⁻¹ * delta n m *
         ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))
           - (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j))
     ∫ x, (∑ k : Fin p,
         (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ KAP z) (Pi.single j (1 : ℝ))) (Zrest x))
           (Pi.single k (1 : ℝ)) * Zss x k) * Zd x ∂(P.prod P) = 0) := by
  /- @proof-region region.target-node.session.8eb969c766dc9096 begin -/
  intro Ω _ P _ n m p delta muX muY X Y F G hn hm hp hlogp hdelta hXm hYm hFm hGm hindep
    hXmean hYmean hXL2 hYL2 hX3 hY3 hF3 hG3 hFcov hGcov v hv0 hv1 phi1 phi2 hphi1 hphi2
    y phi0 hphi0_cont hphi0_left hphi0_right hphi0_range t ht0 ht1 i j
  intro phi beta KAP Zss Zrest Zd
  have hp2 : 2 ≤ p := by
    rcases lt_or_ge p 2 with h | h
    · have hp1 : p = 1 := by omega
      subst hp1
      have h0 : Real.log ((1 : ℕ) : ℝ) = 0 := by simp
      rw [h0] at hlogp
      exact absurd hlogp (lt_irrefl (0 : ℝ))
    · exact h
  have hphi_ge : 1 ≤ phi := le_min hphi1 hphi2
  have hkappa :=
    statopia_math_node_2194576110_d2ad0cef p hp2 phi hphi_ge phi0 hphi0_cont hphi0_left
      hphi0_right hphi0_range y
  have hKAPcont : ContDiff ℝ 3 KAP := hkappa.1
  have hKAP01 : ∀ w : Fin p → ℝ, 0 ≤ KAP w ∧ KAP w ≤ 1 := hkappa.2.1
  have hdep :=
    statopia_math_node_1649031325_12d7295c Ω P n m p delta muX muY X Y F G hn hm hp
      hXm hYm hFm hGm hindep hXmean hYmean hXL2 hYL2 hX3 hY3 hF3 hG3 hFcov hGcov v hv0 hv1
      t ht0 ht1 i j
  have hgi : ∀ k : Fin p, Integrable (fun x : Ω × Ω => Zss x k * Zd x) (P.prod P) := by
    intro k
    exact (hdep k).1
  have hg0 : ∀ k : Fin p, ∫ x : Ω × Ω, Zss x k * Zd x ∂(P.prod P) = 0 := by
    intro k
    exact (hdep k).2
  have hcoordS : ∀ (Z : Ω → Fin p → ℝ), Measurable Z → ∀ k : Fin p,
      Measurable (fun x : Ω × Ω => Z x.1 k) := by
    intro Z hZ k
    exact ((continuous_apply k).measurable).comp (hZ.comp measurable_fst)
  have hcoordT : ∀ (Z : Ω → Fin p → ℝ), Measurable Z → ∀ k : Fin p,
      Measurable (fun x : Ω × Ω => Z x.2 k) := by
    intro Z hZ k
    exact ((continuous_apply k).measurable).comp (hZ.comp measurable_snd)
  have hblk : ∀ (A B : Ω → Fin p → ℝ) (mu : Fin p → ℝ), Measurable A → Measurable B →
      ∀ k : Fin p, Measurable (fun x : Ω × Ω =>
        Real.sqrt t * (Real.sqrt v * (A x.1 k - mu k) + Real.sqrt (1 - v) * (B x.1 k - mu k))) := by
    intro A B mu hA hB k
    exact ((((hcoordS A hA k).sub measurable_const).const_mul (Real.sqrt v)).add
      (((hcoordS B hB k).sub measurable_const).const_mul (Real.sqrt (1 - v)))).const_mul (Real.sqrt t)
  have hZrest_meas : ∀ k : Fin p, Measurable (fun x : Ω × Ω => Zrest x k) := by
    intro k
    have h1 : Measurable (fun x : Ω × Ω => ∑ i2 : Fin n,
        (Real.sqrt (n : ℝ))⁻¹ *
          (Real.sqrt t * (Real.sqrt v * (X i2 x.1 k - muX k) + Real.sqrt (1 - v) * (F i2 x.1 k - muX k))
            + Real.sqrt (1 - t) * (F i2 x.2 k - muX k))) := by
      apply Finset.measurable_sum
      intro i2 _
      exact ((hblk (X i2) (F i2) muX (hXm i2) (hFm i2) k).add
        (((hcoordT (F i2) (hFm i2) k).sub measurable_const).const_mul (Real.sqrt (1 - t)))).const_mul
        ((Real.sqrt (n : ℝ))⁻¹)
    have h2 : Measurable (fun x : Ω × Ω => ∑ i2 : Fin m, if i2 = i then 0 else
        (Real.sqrt (m : ℝ))⁻¹ * delta n m *
          (Real.sqrt t * (Real.sqrt v * (Y i2 x.1 k - muY k) + Real.sqrt (1 - v) * (G i2 x.1 k - muY k))
            + Real.sqrt (1 - t) * (G i2 x.2 k - muY k))) := by
      apply Finset.measurable_sum
      intro i2 _
      by_cases hii : i2 = i
      · simp only [if_pos hii]
        exact measurable_const
      · simp only [if_neg hii]
        exact ((hblk (Y i2) (G i2) muY (hYm i2) (hGm i2) k).add
          (((hcoordT (G i2) (hGm i2) k).sub measurable_const).const_mul (Real.sqrt (1 - t)))).const_mul
          ((Real.sqrt (m : ℝ))⁻¹ * delta n m)
    exact h1.add h2
  have hZrest_meas' : Measurable Zrest := measurable_pi_iff.mpr hZrest_meas
  have hZss_meas : ∀ k : Fin p, Measurable (fun x : Ω × Ω => Zss x k) := by
    intro k
    exact ((hblk (Y i) (G i) muY (hYm i) (hGm i) k).add
      (((hcoordT (G i) (hGm i) k).sub measurable_const).const_mul (Real.sqrt (1 - t)))).const_mul
      ((Real.sqrt (m : ℝ))⁻¹ * delta n m)
  have hZd_meas : Measurable Zd := by
    have hA : Measurable (fun x : Ω × Ω => (2 * Real.sqrt t)⁻¹ *
        (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))) :=
      ((((hcoordS (Y i) (hYm i) j).sub measurable_const).const_mul (Real.sqrt v)).add
        (((hcoordS (G i) (hGm i) j).sub measurable_const).const_mul (Real.sqrt (1 - v)))).const_mul
        ((2 * Real.sqrt t)⁻¹)
    have hB : Measurable (fun x : Ω × Ω => (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j)) :=
      ((hcoordT (G i) (hGm i) j).sub measurable_const).const_mul ((2 * Real.sqrt (1 - t))⁻¹)
    exact (hA.sub hB).const_mul ((Real.sqrt (m : ℝ))⁻¹ * delta n m)
  have hfmeas : ∀ k : Fin p, Measurable (fun x : Ω × Ω => Zss x k * Zd x) := fun k =>
    (hZss_meas k).mul hZd_meas
  have hJ : ContDiff ℝ 1
      (fun p : (Fin p → ℝ) × (Fin p → ℝ) => (fderiv ℝ KAP p.1) p.2) :=
    ContDiff.contDiff_fderiv_apply hKAPcont (by norm_num)
  have hsec : ContDiff ℝ 1 (fun z : Fin p → ℝ => (z, (Pi.single j (1 : ℝ) : Fin p → ℝ))) := by
    fun_prop
  have hGdiff : ContDiff ℝ 1
      (fun z : Fin p → ℝ => (fderiv ℝ KAP z) (Pi.single j (1 : ℝ))) :=
    ContDiff.comp hJ hsec
  have hGcont : Continuous (fun z : Fin p → ℝ =>
      fderiv ℝ (fun z' : Fin p → ℝ => (fderiv ℝ KAP z') (Pi.single j (1 : ℝ))) z) :=
    ContDiff.continuous_fderiv hGdiff (by norm_num)
  have hΦcont : ∀ k : Fin p, Continuous (fun z : Fin p → ℝ =>
      (fderiv ℝ (fun z' : Fin p → ℝ => (fderiv ℝ KAP z') (Pi.single j (1 : ℝ))) z)
        (Pi.single k (1 : ℝ))) := by
    intro k
    exact hGcont.clm_apply continuous_const
  have hΦmeas : ∀ k : Fin p, Measurable (fun x : Ω × Ω =>
      (fderiv ℝ (fun z' : Fin p → ℝ => (fderiv ℝ KAP z') (Pi.single j (1 : ℝ))) (Zrest x))
        (Pi.single k (1 : ℝ))) := fun k =>
    (hΦcont k).measurable.comp hZrest_meas'
  have hJmeas : ∀ a : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)),
      Measurable (jointFam X Y F G a) := by
    intro a
    rcases a with i' | (i' | (i' | i'))
    · exact hXm i'
    · exact hYm i'
    · exact hFm i'
    · exact hGm i'
  have hpull : ∀ (π : Ω × Ω → Ω), (∀ s : Set Ω, MeasurableSet s → (P.prod P) (π ⁻¹' s) = P s) →
      iIndepFun (β := fun _ => Fin p → ℝ) (fun a => jointFam X Y F G a ∘ π) (P.prod P) := by
    intro π hπ
    refine iIndepFun_iff_measure_inter_preimage_eq_mul.mpr ?_
    intro S sets hsets
    have hM : MeasurableSet (⋂ i ∈ S, jointFam X Y F G i ⁻¹' sets i) := by
      refine MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun hi => ?_))
      exact hJmeas i (hsets i hi)
    have hL : (⋂ i ∈ S, (fun a => jointFam X Y F G a ∘ π) i ⁻¹' sets i)
        = π ⁻¹' (⋂ i ∈ S, jointFam X Y F G i ⁻¹' sets i) := by
      simp only [Set.preimage_iInter, Set.preimage_comp, Function.comp_apply]
    rw [hL, hπ _ hM, iIndepFun_iff_measure_inter_preimage_eq_mul.mp hindep S hsets]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    exact (hπ _ (hJmeas i (hsets i hi))).symm
  have hpullF := hpull Prod.fst (fun s _ => by
    rw [← Set.prod_univ, Measure.prod_prod, measure_univ, mul_one])
  have hpullS := hpull Prod.snd (fun s _ => by
    rw [← Set.univ_prod, Measure.prod_prod, measure_univ, one_mul])
  have hJFmeas : ∀ a : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)),
      Measurable (fun x : Ω × Ω => jointFam X Y F G a x.1) := fun a =>
    (hJmeas a).comp measurable_fst
  have hJSmeas : ∀ a : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)),
      Measurable (fun x : Ω × Ω => jointFam X Y F G a x.2) := fun a =>
    (hJmeas a).comp measurable_snd
  classical
  let Texcl : Finset (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) :=
    {Sum.inr (Sum.inl i), Sum.inr (Sum.inr (Sum.inr i))}
  let Srest : Finset (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) := Finset.univ \ Texcl
  have hdisj : Disjoint Srest Texcl := by
    refine Finset.disjoint_left.mpr ?_
    intro x hx hxT
    exact (Finset.mem_sdiff.mp hx).2 hxT
  have hR1E1 := iIndepFun.indepFun_finset Srest Texcl hdisj hpullF hJFmeas
  have hR2E2 := iIndepFun.indepFun_finset Srest Texcl hdisj hpullS hJSmeas
  have hTupMeas : Measurable (fun ω : Ω => fun a : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)) =>
      jointFam X Y F G a ω) := measurable_pi_iff.mpr hJmeas
  have hcopy : (fun x : Ω × Ω => fun a : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)) =>
        jointFam X Y F G a x.1) ⟂ᵢ[P.prod P]
      (fun x : Ω × Ω => fun a : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)) =>
        jointFam X Y F G a x.2) :=
    indepFun_prod hTupMeas hTupMeas
  have hprojR : Measurable (fun t : (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) → Fin p → ℝ =>
      fun a : ↥Srest => t ↑a) :=
    measurable_pi_iff.mpr
      (fun a => (continuous_apply (↑a : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)))).measurable)
  have hRR : (fun x : Ω × Ω => fun a : ↥Srest => jointFam X Y F G ↑a x.1) ⟂ᵢ[P.prod P]
      (fun x : Ω × Ω => fun a : ↥Srest => jointFam X Y F G ↑a x.2) :=
    IndepFun.comp hcopy hprojR hprojR
  have hprojE : Measurable (fun t : (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) → Fin p → ℝ =>
      fun a : ↥Texcl => t ↑a) :=
    measurable_pi_iff.mpr
      (fun a => (continuous_apply (↑a : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)))).measurable)
  have hEE : (fun x : Ω × Ω => fun a : ↥Texcl => jointFam X Y F G ↑a x.1) ⟂ᵢ[P.prod P]
      (fun x : Ω × Ω => fun a : ↥Texcl => jointFam X Y F G ↑a x.2) :=
    IndepFun.comp hcopy hprojE hprojE
  have hbdd : ∀ k : Fin p, ∃ C : ℝ, ∀ x : Ω × Ω,
      ‖(fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ KAP z) (Pi.single j (1 : ℝ))) (Zrest x))
        (Pi.single k (1 : ℝ))‖ ≤ C := by
    obtain ⟨C, hC⟩ :=
      statopia_math_node_219120413_99b9d052 p hp2 phi hphi_ge phi0 hphi0_cont hphi0_left
        hphi0_right hphi0_range y j
    exact fun k => ⟨C, fun x => hC k (Zrest x)⟩
  have hInt : ∀ k : Fin p, Integrable (fun x : Ω × Ω =>
      (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ KAP z) (Pi.single j (1 : ℝ))) (Zrest x))
        (Pi.single k (1 : ℝ)) * (Zss x k * Zd x)) (P.prod P) := by
    intro k
    obtain ⟨C, hC⟩ := hbdd k
    exact MeasureTheory.Integrable.bdd_mul (hgi k) (hΦmeas k).aestronglyMeasurable
      (Filter.Eventually.of_forall hC)
  have hIndep : ∀ k : Fin p,
      (fun x : Ω × Ω =>
        (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ KAP z) (Pi.single j (1 : ℝ))) (Zrest x))
          (Pi.single k (1 : ℝ))) ⟂ᵢ[P.prod P] (fun x : Ω × Ω => Zss x k * Zd x) := by
    intro k
    have hZR :=
      statopia_math_node_3430447628_ae1e147f Ω P n m p delta muX muY X Y F G hXm hYm hFm hGm
        hindep (fun z : Fin p → ℝ => (fderiv ℝ KAP z) (Pi.single j (1 : ℝ))) hGdiff v t i k
    have hFm : Measurable (fun u : (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) =>
        ((Real.sqrt (m : ℝ))⁻¹ * delta n m *
          (Real.sqrt t * (Real.sqrt v * (u.1 k - muY k) + Real.sqrt (1 - v) * (u.2.1 k - muY k))
            + Real.sqrt (1 - t) * (u.2.2 k - muY k)))
        * ((Real.sqrt (m : ℝ))⁻¹ * delta n m *
          ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (u.1 j - muY j) + Real.sqrt (1 - v) * (u.2.1 j - muY j))
            - (2 * Real.sqrt (1 - t))⁻¹ * (u.2.2 j - muY j)))) := by
      fun_prop
    exact IndepFun.comp hZR measurable_id hFm
  have hterm : ∀ k : Fin p, ∫ x : Ω × Ω,
      (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ KAP z) (Pi.single j (1 : ℝ))) (Zrest x))
        (Pi.single k (1 : ℝ)) * (Zss x k * Zd x) ∂(P.prod P) = 0 := by
    intro k
    calc ∫ x : Ω × Ω,
        (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ KAP z) (Pi.single j (1 : ℝ))) (Zrest x))
          (Pi.single k (1 : ℝ)) * (Zss x k * Zd x) ∂(P.prod P)
        = (∫ x : Ω × Ω,
            (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ KAP z) (Pi.single j (1 : ℝ))) (Zrest x))
              (Pi.single k (1 : ℝ)) ∂(P.prod P)) * ∫ x : Ω × Ω, Zss x k * Zd x ∂(P.prod P) :=
          IndepFun.integral_fun_mul_eq_mul_integral (hIndep k)
            (hΦmeas k).aestronglyMeasurable (hfmeas k).aestronglyMeasurable
      _ = 0 := by rw [hg0 k, mul_zero]
  have hstep1 : ∫ x : Ω × Ω, (∑ k : Fin p,
        (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ KAP z) (Pi.single j (1 : ℝ))) (Zrest x))
          (Pi.single k (1 : ℝ)) * Zss x k) * Zd x ∂(P.prod P)
      = ∫ x : Ω × Ω, ∑ k : Fin p,
        (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ KAP z) (Pi.single j (1 : ℝ))) (Zrest x))
          (Pi.single k (1 : ℝ)) * (Zss x k * Zd x) ∂(P.prod P) := by
    apply integral_congr_ae
    filter_upwards with x
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun k _ => mul_assoc _ _ _)
  have hstep2 : ∫ x : Ω × Ω, ∑ k : Fin p,
        (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ KAP z) (Pi.single j (1 : ℝ))) (Zrest x))
          (Pi.single k (1 : ℝ)) * (Zss x k * Zd x) ∂(P.prod P)
      = ∑ k : Fin p, ∫ x : Ω × Ω,
        (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ KAP z) (Pi.single j (1 : ℝ))) (Zrest x))
          (Pi.single k (1 : ℝ)) * (Zss x k * Zd x) ∂(P.prod P) := by
    rw [integral_finset_sum]
    intro k _
    exact hInt k
  rw [hstep1, hstep2]
  exact Finset.sum_eq_zero (fun k _ => hterm k)

  /- @proof-region region.target-node.session.8eb969c766dc9096 end -/

end

end Statlib.Imported

