import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_1649031325_12d7295c_13e7bff5
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_219120413_99b9d052_0aa6365d
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_2194576110_d2ad0cef_60d45604
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_3430447628_ae1e147f_4d81461a
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_4002104850_4380db1f_47e2833e

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
theorem statopia_math_node_3406556126_a8c6e89f : ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n m p : ℕ) (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
    (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
    (phi1 phi2 : ℝ) (hphi1 : 1 ≤ phi1) (hphi2 : 1 ≤ phi2)
    (phi0 : ℝ → ℝ) (hphi0_cont : ContDiff ℝ 3 phi0)
    (hphi0_left : ∀ z : ℝ, z ≤ 0 → phi0 z = 1)
    (hphi0_right : ∀ z : ℝ, 1 ≤ z → phi0 z = 0)
    (hphi0_range : ∀ z : ℝ, phi0 z ∈ Set.Icc (0 : ℝ) 1)
    (y : Fin p → ℝ) (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hn : 0 < n) (hm : 0 < m) (hp : 0 < p) (hlogp : 0 < Real.log (p : ℝ))
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
      IsCenteredGaussianVector P (fun ω j => G i ω j - muY j) (covY P muY Y i)),
    let KAP : (Fin p → ℝ) → ℝ := fun w =>
      phi0 (min phi1 phi2 * (((min phi1 phi2) * Real.log (p : ℝ))⁻¹ *
        Real.log (∑ r : Fin p, Real.exp (((min phi1 phi2) * Real.log (p : ℝ)) * (w r - y r)))))
    let ZST : ℝ → Ω × Ω → Fin n → Fin p → ℝ := fun t x i j =>
      (Real.sqrt (n : ℝ))⁻¹ *
        (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)) +
          Real.sqrt (1 - t) * (F i x.2 j - muX j))
    let ZSS : ℝ → Ω × Ω → Fin m → Fin p → ℝ := fun t x i j =>
      (Real.sqrt (m : ℝ))⁻¹ * delta n m *
        (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j)) +
          Real.sqrt (1 - t) * (G i x.2 j - muY j))
    let ZC : ℝ → Ω × Ω → Fin p → ℝ := fun t x j =>
      (∑ i : Fin n, ZST t x i j) + (∑ i : Fin m, ZSS t x i j)
    let ZD : ℝ → Ω × Ω → Fin m → Fin p → ℝ := fun t x i j =>
      (Real.sqrt (m : ℝ))⁻¹ * delta n m *
        ((2 * Real.sqrt t)⁻¹ *
            (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j)) -
          (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j))
    let Zrest : ℝ → Fin m → Ω × Ω → Fin p → ℝ := fun t i x j => ZC t x j - ZSS t x i j
    ∀ t : ℝ, 0 < t → t < 1 → ∀ (i : Fin m) (j k : Fin p),
      Integrable (fun x : Ω × Ω =>
        (fderiv ℝ (fun z : Fin p → ℝ =>
            (fderiv ℝ KAP z) (Pi.single j (1 : ℝ) : Fin p → ℝ)) (Zrest t i x))
          (Pi.single k (1 : ℝ) : Fin p → ℝ) * ZSS t x i k * ZD t x i j) (P.prod P) ∧
      ∫ x, (fderiv ℝ (fun z : Fin p → ℝ =>
            (fderiv ℝ KAP z) (Pi.single j (1 : ℝ) : Fin p → ℝ)) (Zrest t i x))
          (Pi.single k (1 : ℝ) : Fin p → ℝ) * ZSS t x i k * ZD t x i j ∂(P.prod P) = 0 := by
  /- @proof-region region.target-node.session.2718be0106388ce9 begin -/
  classical
  dsimp only
  intro Ω instΩ P instP n m p delta muX muY X Y F G phi1 phi2 hphi1 hphi2
    phi0 hphi0_cont hphi0_left hphi0_right hphi0_range y v hv0 hv1 hn hm hp hlogp
    hXm hYm hFm hGm hindep hXmean hYmean hXL2 hYL2 hX3 hY3 hF3 hG3 hFcov hGcov
    t ht0 ht1 i j k
  let KAP : (Fin p → ℝ) → ℝ := fun w =>
    phi0 (min phi1 phi2 * (((min phi1 phi2) * Real.log (p : ℝ))⁻¹ *
      Real.log (∑ r : Fin p, Real.exp (((min phi1 phi2) * Real.log (p : ℝ)) * (w r - y r)))))
  let ZST : ℝ → Ω × Ω → Fin n → Fin p → ℝ := fun t x i j =>
    (Real.sqrt (n : ℝ))⁻¹ *
      (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)) +
        Real.sqrt (1 - t) * (F i x.2 j - muX j))
  let ZSS : ℝ → Ω × Ω → Fin m → Fin p → ℝ := fun t x i j =>
    (Real.sqrt (m : ℝ))⁻¹ * delta n m *
      (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j)) +
        Real.sqrt (1 - t) * (G i x.2 j - muY j))
  let ZC : ℝ → Ω × Ω → Fin p → ℝ := fun t x j =>
    (∑ i : Fin n, ZST t x i j) + (∑ i : Fin m, ZSS t x i j)
  let ZD : ℝ → Ω × Ω → Fin m → Fin p → ℝ := fun t x i j =>
    (Real.sqrt (m : ℝ))⁻¹ * delta n m *
      ((2 * Real.sqrt t)⁻¹ *
          (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j)) -
        (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j))
  let Zrest : ℝ → Fin m → Ω × Ω → Fin p → ℝ := fun t i x j => ZC t x j - ZSS t x i j
  have hUW : Integrable (fun x : Ω × Ω => ZSS t x i k * ZD t x i j) (P.prod P) ∧
      ∫ x, ZSS t x i k * ZD t x i j ∂(P.prod P) = 0 := by
    have h := statopia_math_node_1649031325_12d7295c Ω P n m p delta muX muY X Y F G
      hn hm hp hXm hYm hFm hGm hindep hXmean hYmean hXL2 hYL2 hX3 hY3 hF3 hG3 hFcov hGcov
      v hv0 hv1 t ht0 ht1 i j k
    simpa only [ZSS, ZD] using h
  obtain ⟨hUWint, hUWzero⟩ := hUW
  have hp2 : 2 ≤ p := by
    have hlt : (1 : ℝ) < (p : ℝ) := by
      rcases lt_or_ge (1 : ℝ) (p : ℝ) with h | h
      · exact h
      · exfalso
        have hpos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
        have hle : Real.log (p : ℝ) ≤ Real.log 1 := Real.log_le_log hpos h
        rw [Real.log_one] at hle
        linarith
    have h1p : 1 < p := by exact_mod_cast hlt
    omega
  have hKAPcd : ContDiff ℝ 3 KAP := by
    have hkp := statopia_math_node_2194576110_d2ad0cef p hp2 (min phi1 phi2) (le_min hphi1 hphi2)
      phi0 hphi0_cont hphi0_left hphi0_right hphi0_range y
    exact hkp.1
  have hpair1 : ContDiff ℝ 1 (fun q : (Fin p → ℝ) × (Fin p → ℝ) => (fderiv ℝ KAP q.1) q.2) :=
    hKAPcd.contDiff_fderiv_apply (m := 1) (by norm_num)
  have hid : ContDiff ℝ 1 (fun w : Fin p → ℝ => w) := contDiff_id
  have hinner : ContDiff ℝ 1 (fun w : Fin p → ℝ => (w, (Pi.single j (1 : ℝ) : Fin p → ℝ))) := by
    fun_prop
  have hg1cd : ContDiff ℝ 1 (fun z : Fin p → ℝ => (fderiv ℝ KAP z) (Pi.single j (1 : ℝ))) :=
    hpair1.comp hinner
  have hpair0cont : Continuous (fun q : (Fin p → ℝ) × (Fin p → ℝ) =>
      (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ KAP z) (Pi.single j (1 : ℝ))) q.1) q.2) :=
    (hg1cd.contDiff_fderiv_apply (m := 0) (by norm_num)).continuous
  have hTk : Continuous (fun w : Fin p → ℝ => (w, (Pi.single k (1 : ℝ) : Fin p → ℝ))) := by
    fun_prop
  have hcont2 : Continuous (fun w : Fin p → ℝ =>
      (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ KAP z) (Pi.single j (1 : ℝ))) w)
        (Pi.single k (1 : ℝ))) :=
    hpair0cont.comp hTk
  have hmeasX1 : ∀ (i : Fin n) (j : Fin p), Measurable (fun x : Ω × Ω => X i x.1 j) := by
    intro i j; fun_prop
  have hmeasY1 : ∀ (i : Fin m) (j : Fin p), Measurable (fun x : Ω × Ω => Y i x.1 j) := by
    intro i j; fun_prop
  have hmeasF1 : ∀ (i : Fin n) (j : Fin p), Measurable (fun x : Ω × Ω => F i x.1 j) := by
    intro i j; fun_prop
  have hmeasF2 : ∀ (i : Fin n) (j : Fin p), Measurable (fun x : Ω × Ω => F i x.2 j) := by
    intro i j; fun_prop
  have hmeasG1 : ∀ (i : Fin m) (j : Fin p), Measurable (fun x : Ω × Ω => G i x.1 j) := by
    intro i j; fun_prop
  have hmeasG2 : ∀ (i : Fin m) (j : Fin p), Measurable (fun x : Ω × Ω => G i x.2 j) := by
    intro i j; fun_prop
  have hmeasU : Measurable (fun x : Ω × Ω => ZSS t x i k) := by
    simp only [ZSS]; fun_prop
  have hmeasW : Measurable (fun x : Ω × Ω => ZD t x i j) := by
    simp only [ZD]; fun_prop
  have hbdd : ∃ B : ℝ, ∀ w : Fin p → ℝ,
      |(fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ KAP z) (Pi.single j (1 : ℝ))) w)
        (Pi.single k (1 : ℝ))| ≤ B := by
    obtain ⟨C, hC⟩ := statopia_math_node_219120413_99b9d052 p hp2 (min phi1 phi2)
      (le_min hphi1 hphi2) phi0 hphi0_cont hphi0_left hphi0_right hphi0_range y j
    exact ⟨C, fun w => by simpa [KAP] using hC k w⟩
  have hmeasZST : ∀ (i : Fin n) (j : Fin p), Measurable (fun x : Ω × Ω => ZST t x i j) := by
    intro i j; simp only [ZST]; fun_prop
  have hmeasZSS : ∀ (i : Fin m) (j : Fin p), Measurable (fun x : Ω × Ω => ZSS t x i j) := by
    intro i j; simp only [ZSS]; fun_prop
  have hmeasZD : ∀ (i : Fin m) (j : Fin p), Measurable (fun x : Ω × Ω => ZD t x i j) := by
    intro i j; simp only [ZD]; fun_prop
  have hmeasZ : Measurable (fun x : Ω × Ω => Zrest t i x) := by
    simp only [Zrest, ZC]
    fun_prop
  have hmeasA : AEStronglyMeasurable (fun x : Ω × Ω =>
      (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ KAP z) (Pi.single j (1 : ℝ))) (Zrest t i x))
        (Pi.single k (1 : ℝ))) (P.prod P) :=
    (hcont2.measurable.comp hmeasZ).aestronglyMeasurable
  have hindepAU : IndepFun (fun x : Ω × Ω =>
      (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ KAP z) (Pi.single j (1 : ℝ))) (Zrest t i x))
        (Pi.single k (1 : ℝ)))
      (fun x : Ω × Ω => ZSS t x i k * ZD t x i j) (P.prod P) := by
    let kap : (Fin p → ℝ) → ℝ := fun w => (fderiv ℝ KAP w) (Pi.single j (1 : ℝ))
    let ZRC : Ω × Ω → Fin p → ℝ := fun x k' =>
      (∑ i' : Fin n, ZST t x i' k') + (∑ i' : Fin m, if i' = i then (0 : ℝ) else ZSS t x i' k')
    let Φ : (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) → ℝ := fun T =>
      ((Real.sqrt (m : ℝ))⁻¹ * delta n m *
          (Real.sqrt t * (Real.sqrt v * (T.1 k - muY k) + Real.sqrt (1 - v) * (T.2.1 k - muY k)) +
            Real.sqrt (1 - t) * (T.2.2 k - muY k))) *
        ((Real.sqrt (m : ℝ))⁻¹ * delta n m *
          ((2 * Real.sqrt t)⁻¹ *
              (Real.sqrt v * (T.1 j - muY j) + Real.sqrt (1 - v) * (T.2.1 j - muY j)) -
            (2 * Real.sqrt (1 - t))⁻¹ * (T.2.2 j - muY j)))
    have hkap : ContDiff ℝ 1 kap := hg1cd
    have hZrest_eq : ∀ x : Ω × Ω, Zrest t i x = ZRC x := by
      intro x
      funext k'
      have hsplit : (∑ i' : Fin m, ZSS t x i' k') - ZSS t x i k'
          = ∑ i' : Fin m, (if i' = i then (0 : ℝ) else ZSS t x i' k') := by
        have hpt : ∀ i' : Fin m,
            ZSS t x i' k' - (if i' = i then ZSS t x i' k' else 0)
              = (if i' = i then (0 : ℝ) else ZSS t x i' k') := by
          intro i'
          by_cases h : i' = i <;> simp [h]
        calc (∑ i' : Fin m, ZSS t x i' k') - ZSS t x i k'
            = (∑ i' : Fin m, ZSS t x i' k')
                - (∑ i' : Fin m, (if i' = i then ZSS t x i' k' else 0)) := by
              rw [Finset.sum_ite_eq']
              simp
          _ = ∑ i' : Fin m, (ZSS t x i' k' - (if i' = i then ZSS t x i' k' else 0)) := by
              rw [Finset.sum_sub_distrib]
          _ = ∑ i' : Fin m, (if i' = i then (0 : ℝ) else ZSS t x i' k') :=
              Finset.sum_congr rfl (fun i' _ => hpt i')
      simp only [Zrest, ZRC, ZC]
      rw [← hsplit]
      ring
    have hchildRaw := statopia_math_node_3430447628_ae1e147f Ω P n m p delta muX muY X Y F G
      hXm hYm hFm hGm hindep kap hkap v t i k
    have hchild : IndepFun (fun x : Ω × Ω => (fderiv ℝ kap (ZRC x)) (Pi.single k (1 : ℝ)))
        (fun x : Ω × Ω => (Y i x.1, (G i x.1, G i x.2))) (P.prod P) := by
      simpa only [ZRC, ZST, ZSS, kap] using hchildRaw
    have hΦmeas : Measurable Φ := by
      simp only [Φ]
      fun_prop
    have hUWΦ : (fun x : Ω × Ω => ZSS t x i k * ZD t x i j)
        = fun x => Φ (Y i x.1, (G i x.1, G i x.2)) := by
      funext x
      simp only [Φ, ZSS, ZD]
    simp only [kap, hZrest_eq]
    rw [hUWΦ]
    rw [indepFun_iff_measure_inter_preimage_eq_mul] at hchild ⊢
    intro s t' hs ht'
    exact hchild s (Φ ⁻¹' t') hs (hΦmeas ht')
  have hAEM : AEMeasurable (fun x : Ω × Ω =>
      (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ KAP z) (Pi.single j (1 : ℝ))) (Zrest t i x))
        (Pi.single k (1 : ℝ))) (P.prod P) :=
    hmeasA.aemeasurable
  have hUWAEM : AEMeasurable (fun x : Ω × Ω => ZSS t x i k * ZD t x i j) (P.prod P) :=
    (hmeasU.mul hmeasW).aemeasurable
  have hAEid : ∀ ν : Measure ℝ, AEStronglyMeasurable (fun r : ℝ => r) ν := by
    intro ν
    fun_prop
  obtain ⟨B, hB⟩ := hbdd
  have hIntA : Integrable (fun x : Ω × Ω =>
      (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ KAP z) (Pi.single j (1 : ℝ))) (Zrest t i x))
        (Pi.single k (1 : ℝ))) (P.prod P) := by
    refine MeasureTheory.Integrable.of_bound hmeasA B ?_
    filter_upwards with x
    simpa using hB (Zrest t i x)
  have h1 : Integrable (fun x : Ω × Ω =>
      (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ KAP z) (Pi.single j (1 : ℝ))) (Zrest t i x))
        (Pi.single k (1 : ℝ)) * (ZSS t x i k * ZD t x i j)) (P.prod P) :=
    MeasureTheory.Integrable.bdd_mul hUWint hmeasA (by
      filter_upwards with x
      simpa using hB (Zrest t i x))
  have hassoc : (fun x : Ω × Ω =>
      (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ KAP z) (Pi.single j (1 : ℝ))) (Zrest t i x))
        (Pi.single k (1 : ℝ)) * (ZSS t x i k * ZD t x i j))
      = fun x : Ω × Ω =>
      (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ KAP z) (Pi.single j (1 : ℝ))) (Zrest t i x))
        (Pi.single k (1 : ℝ)) * ZSS t x i k * ZD t x i j := by
    funext x
    ring
  constructor
  · rw [hassoc] at h1
    exact h1
  · rw [← hassoc]
    set Afun : Ω × Ω → ℝ := fun x =>
      (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ KAP z) (Pi.single j (1 : ℝ))) (Zrest t i x))
        (Pi.single k (1 : ℝ)) with hAfun
    set UWfun : Ω × Ω → ℝ := fun x => ZSS t x i k * ZD t x i j with hUWfun
    have hAEM' : AEMeasurable Afun (P.prod P) := hAEM
    have hUWAEM' : AEMeasurable UWfun (P.prod P) := hUWAEM
    have hmap : Measure.map (fun x : Ω × Ω => (Afun x, UWfun x)) (P.prod P)
        = (Measure.map Afun (P.prod P)).prod (Measure.map UWfun (P.prod P)) :=
      (indepFun_iff_map_prod_eq_prod_map_map hAEM' hUWAEM').mp hindepAU
    have hpairmeas : AEMeasurable (fun x : Ω × Ω => (Afun x, UWfun x)) (P.prod P) := by
      fun_prop
    have hsm : AEStronglyMeasurable (fun z : ℝ × ℝ => z.1 * z.2)
        (Measure.map (fun x : Ω × Ω => (Afun x, UWfun x)) (P.prod P)) := by
      fun_prop
    have h4 : ∫ x : Ω × Ω, Afun x * UWfun x ∂(P.prod P)
        = ∫ z : ℝ × ℝ, z.1 * z.2
            ∂(Measure.map (fun x : Ω × Ω => (Afun x, UWfun x)) (P.prod P)) :=
      (MeasureTheory.integral_map hpairmeas hsm).symm
    have h1 : ∫ z : ℝ × ℝ, z.1 * z.2
          ∂(Measure.map (fun x : Ω × Ω => (Afun x, UWfun x)) (P.prod P))
        = (∫ z : ℝ, z ∂(Measure.map Afun (P.prod P))) *
            ∫ z : ℝ, z ∂(Measure.map UWfun (P.prod P)) := by
      rw [hmap]
      exact MeasureTheory.integral_prod_mul (fun z : ℝ => z) (fun z : ℝ => z)
    have h2 : ∫ z : ℝ, z ∂(Measure.map Afun (P.prod P)) = ∫ x : Ω × Ω, Afun x ∂(P.prod P) :=
      MeasureTheory.integral_map hAEM' (hAEid _)
    have h3 : ∫ z : ℝ, z ∂(Measure.map UWfun (P.prod P)) = ∫ x : Ω × Ω, UWfun x ∂(P.prod P) :=
      MeasureTheory.integral_map hUWAEM' (hAEid _)
    have hUWzero' : ∫ x : Ω × Ω, UWfun x ∂(P.prod P) = 0 := hUWzero
    calc ∫ x : Ω × Ω, Afun x * UWfun x ∂(P.prod P)
        = ∫ z : ℝ × ℝ, z.1 * z.2
            ∂(Measure.map (fun x : Ω × Ω => (Afun x, UWfun x)) (P.prod P)) := h4
      _ = (∫ z : ℝ, z ∂(Measure.map Afun (P.prod P))) *
            ∫ z : ℝ, z ∂(Measure.map UWfun (P.prod P)) := h1
      _ = (∫ x : Ω × Ω, Afun x ∂(P.prod P)) * ∫ x : Ω × Ω, UWfun x ∂(P.prod P) := by
            rw [h2, h3]
      _ = 0 := by rw [hUWzero', mul_zero]


  /- @proof-region region.target-node.session.2718be0106388ce9 end -/

end

end Statlib.Imported

