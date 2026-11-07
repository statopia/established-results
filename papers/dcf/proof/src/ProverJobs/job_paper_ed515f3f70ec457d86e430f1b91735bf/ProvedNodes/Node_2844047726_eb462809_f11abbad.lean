import Statlib.HypothesisTesting.Nonparametric.MannWhitney
import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_2194576110_d2ad0cef_60d45604
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_2984263438_339ceff3_bd31fda9
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_3412747228_aa4ab764_0e900670
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
theorem statopia_math_node_2844047726_eb462809 : ∀ (b : ℝ) (hb : 0 < b),
    ∃ Cb : ℝ, 0 < Cb ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (n m p : ℕ) (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
        (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
        (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
        (phi1 phi2 : ℝ) (y : Fin p → ℝ) (v : ℝ),
        0 < n → 0 < m → 0 < p → 0 < Real.log (p : ℝ) → delta n m ≠ 0 →
        (∀ i : Fin n, Measurable (X i)) → (∀ i : Fin m, Measurable (Y i)) →
        (∀ i : Fin n, Measurable (F i)) → (∀ i : Fin m, Measurable (G i)) →
        iIndepFun (β := fun _ => Fin p → ℝ) (jointFam X Y F G) P →
        (∀ (i : Fin n) (j : Fin p), MemLp (fun ω => X i ω j) 2 P) →
        (∀ (i : Fin m) (j : Fin p), MemLp (fun ω => Y i ω j) 2 P) →
        (∀ (i : Fin n) (j : Fin p), ∫ ω, X i ω j ∂P = muX j) →
        (∀ (i : Fin m) (j : Fin p), ∫ ω, Y i ω j ∂P = muY j) →
        (∀ i : Fin n,
          IsCenteredGaussianVector P (fun ω j => F i ω j - muX j) (covX P muX X i)) →
        (∀ i : Fin m,
          IsCenteredGaussianVector P (fun ω j => G i ω j - muY j) (covY P muY Y i)) →
        (∀ j : Fin p, Integrable (fun ω =>
          (combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j) ^ 2) P) →
        (∀ j : Fin p, b ≤ ∫ ω,
          (combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j) ^ 2 ∂P) →
        1 ≤ phi1 → 1 ≤ phi2 → 0 ≤ v → v ≤ 1 →
              (let phi : ℝ := min phi1 phi2
               let beta : ℝ := phi * Real.log (p : ℝ)
               let kappa0 : ℝ := phi⁻¹ + 2 * beta⁻¹
               let Uprime : Ω → Fin p → ℝ := fun ω j =>
                 combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j
               let Zstar : ℝ → Ω × Ω → Fin n → Fin p → ℝ := fun t x i j =>
                 (Real.sqrt (n : ℝ))⁻¹ *
                   (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) +
                       Real.sqrt (1 - v) * (F i x.1 j - muX j)) +
                     Real.sqrt (1 - t) * (F i x.2 j - muX j))
               let Zstarstar : ℝ → Ω × Ω → Fin m → Fin p → ℝ := fun t x i j =>
                 (Real.sqrt (m : ℝ))⁻¹ * delta n m *
                   (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) +
                       Real.sqrt (1 - v) * (G i x.1 j - muY j)) +
                     Real.sqrt (1 - t) * (G i x.2 j - muY j))
               let Z : ℝ → Ω × Ω → Fin p → ℝ := fun t x j =>
                 (∑ i : Fin n, Zstar t x i j) + (∑ i : Fin m, Zstarstar t x i j)
               let hloc : (Fin p → ℝ) → ℝ := fun w =>
                 Set.indicator {w : Fin p → ℝ |
                     -phi⁻¹ - 2 * beta⁻¹ < (⨆ j : Fin p, (w j - y j)) ∧
                       (⨆ j : Fin p, (w j - y j)) ≤ phi⁻¹ + 2 * beta⁻¹}
                   (fun _ => (1 : ℝ)) w
               let rhoVal : ℝ := rho P n m p (delta n m) muX muY X Y F G
               let PrPlus : ℝ := (P {ω : Ω | ∀ j : Fin p, Uprime ω j ≤ y j + kappa0}).toReal
               let PrMinus : ℝ := (P {ω : Ω | ∀ j : Fin p, Uprime ω j ≤ y j - kappa0}).toReal
               (∀ w : Fin p → ℝ,
                 Set.indicator {w : Fin p → ℝ |
                     -phi⁻¹ ≤ (⨆ j : Fin p, (w j - y j)) ∧
                       (⨆ j : Fin p, (w j - y j)) ≤ phi⁻¹}
                   (fun _ => (1 : ℝ)) w ≤ hloc w) ∧
               ∀ t ∈ Set.Icc (0 : ℝ) 1,
                 (∫ x, hloc (Z t x) ∂(P.prod P) ≤ 2 * rhoVal + (PrPlus - PrMinus)) ∧
                   (2 * rhoVal + (PrPlus - PrMinus) ≤
                     2 * rhoVal + Cb * kappa0 * Real.sqrt (Real.log (p : ℝ)))) := by
  /- @proof-region region.target-node.session.f1c96118b12c0dec begin -/
  intro b hb
  obtain ⟨Cb0, hCb0pos, hCb0⟩ := statopia_math_node_3412747228_aa4ab764 b hb
  refine ⟨2 * Cb0, by linarith [hCb0pos], by
    intro Ω _ P _ n m p delta muX muY X Y F G phi1 phi2 y v
    intro hn hm hp hlogp hδ hXm hYm hFm hGm hind hX2 hY2 hXmu hYmu hFcov hGcov hInt hb_lb hphi1 hphi2 hv0 hv1
    intro phi beta kappa0 Uprime Zstar Zstarstar Z hloc rhoVal PrPlus PrMinus
    have hphi_ge : 1 ≤ phi := by simp only [phi]; exact le_min hphi1 hphi2
    have hphi_pos : 0 < phi := lt_of_lt_of_le one_pos hphi_ge
    have hbeta_pos : 0 < beta := mul_pos hphi_pos hlogp
    have h2beta : 0 < 2 * beta⁻¹ := by positivity
    constructor
    · intro w
      simp only [hloc]
      by_cases h : w ∈ {w : Fin p → ℝ | -phi⁻¹ ≤ (⨆ j : Fin p, (w j - y j)) ∧ (⨆ j : Fin p, (w j - y j)) ≤ phi⁻¹}
      · have hwide : w ∈ {w : Fin p → ℝ | -phi⁻¹ - 2 * beta⁻¹ < (⨆ j : Fin p, (w j - y j)) ∧ (⨆ j : Fin p, (w j - y j)) ≤ phi⁻¹ + 2 * beta⁻¹} := by
          have h' : -phi⁻¹ ≤ (⨆ j : Fin p, (w j - y j)) ∧ (⨆ j : Fin p, (w j - y j)) ≤ phi⁻¹ := h
          exact ⟨by linarith [h'.1, h2beta], by linarith [h'.2, h2beta]⟩
        rw [Set.indicator_of_mem h, Set.indicator_of_mem hwide]
      · have hz : Set.indicator {w : Fin p → ℝ | -phi⁻¹ ≤ (⨆ j : Fin p, (w j - y j)) ∧ (⨆ j : Fin p, (w j - y j)) ≤ phi⁻¹} (fun _ => (1 : ℝ)) w = 0 := by simp [h]
        rw [hz]
        by_cases hw : w ∈ {w : Fin p → ℝ | -phi⁻¹ - 2 * beta⁻¹ < (⨆ j : Fin p, (w j - y j)) ∧ (⨆ j : Fin p, (w j - y j)) ≤ phi⁻¹ + 2 * beta⁻¹}
        · rw [Set.indicator_of_mem hw]; norm_num
        · simp [hw]
    · intro t ht
      constructor
      · have hkey : ∀ z : Fin p → ℝ, |((P.prod P) {x : Ω × Ω | ∀ j : Fin p, Z t x j ≤ z j}).toReal - (P {ω : Ω | ∀ j : Fin p, Uprime ω j ≤ z j}).toReal| ≤ rhoVal :=
          fun z => statopia_math_node_2984263438_339ceff3 Ω P n m p delta muX muY X Y F G phi1 phi2 y v t hn hm hp hlogp hδ hphi1 hphi2 hv0 hv1 ht hXm hYm hFm hGm hind hX2 hY2 hXmu hYmu hFcov hGcov z
        have h1 := abs_le.mp (hkey (fun j => y j + kappa0))
        have h2 := abs_le.mp (hkey (fun j => y j - kappa0))
        have hint : (∫ x, hloc (Z t x) ∂(P.prod P)) = ((P.prod P) {x : Ω × Ω | ∀ j : Fin p, Z t x j ≤ y j + kappa0}).toReal - ((P.prod P) {x : Ω × Ω | ∀ j : Fin p, Z t x j ≤ y j - kappa0}).toReal := by
          haveI : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
          have hκ0pos : 0 < kappa0 := add_pos (inv_pos.mpr hphi_pos) h2beta
          have hneg : -phi⁻¹ - 2 * beta⁻¹ = -kappa0 := by simp only [kappa0]; ring
          have hhi : phi⁻¹ + 2 * beta⁻¹ = kappa0 := by simp only [kappa0]
          have hsup_le : ∀ (w : Fin p → ℝ) (a : ℝ), (⨆ j : Fin p, (w j - y j)) ≤ a ↔ ∀ j, w j - y j ≤ a := by
            intro w a
            rw [← Finset.sup'_univ_eq_ciSup (fun j : Fin p => w j - y j)]
            rw [Finset.sup'_le_iff]
            simp
          have hZj : ∀ j : Fin p, Measurable (fun x : Ω × Ω => Z t x j) := by
            intro j
            have hXi : ∀ i : Fin n, Measurable (fun x : Ω × Ω => Zstar t x i j) := by
              intro i
              have hXa : Measurable (fun x : Ω × Ω => X i x.1 j) := (measurable_pi_apply j).comp ((hXm i).comp measurable_fst)
              have hFa : Measurable (fun x : Ω × Ω => F i x.1 j) := (measurable_pi_apply j).comp ((hFm i).comp measurable_fst)
              have hFb : Measurable (fun x : Ω × Ω => F i x.2 j) := (measurable_pi_apply j).comp ((hFm i).comp measurable_snd)
              have p1 := hXa.sub (measurable_const : Measurable (fun _ : Ω × Ω => muX j))
              have p2 := hFa.sub (measurable_const : Measurable (fun _ : Ω × Ω => muX j))
              have p3 := hFb.sub (measurable_const : Measurable (fun _ : Ω × Ω => muX j))
              have q1 := (measurable_const : Measurable (fun _ : Ω × Ω => Real.sqrt v)).mul p1
              have q2 := (measurable_const : Measurable (fun _ : Ω × Ω => Real.sqrt (1 - v))).mul p2
              have r1 := q1.add q2
              have r2 := ((measurable_const : Measurable (fun _ : Ω × Ω => Real.sqrt t)).mul r1).add ((measurable_const : Measurable (fun _ : Ω × Ω => Real.sqrt (1 - t))).mul p3)
              exact ((measurable_const : Measurable (fun _ : Ω × Ω => (Real.sqrt (n : ℝ))⁻¹)).mul r2)
            have hYi : ∀ i : Fin m, Measurable (fun x : Ω × Ω => Zstarstar t x i j) := by
              intro i
              have gYa : Measurable (fun x : Ω × Ω => Y i x.1 j) := (measurable_pi_apply j).comp ((hYm i).comp measurable_fst)
              have gGa : Measurable (fun x : Ω × Ω => G i x.1 j) := (measurable_pi_apply j).comp ((hGm i).comp measurable_fst)
              have gGb : Measurable (fun x : Ω × Ω => G i x.2 j) := (measurable_pi_apply j).comp ((hGm i).comp measurable_snd)
              have p1 := gYa.sub (measurable_const : Measurable (fun _ : Ω × Ω => muY j))
              have p2 := gGa.sub (measurable_const : Measurable (fun _ : Ω × Ω => muY j))
              have p3 := gGb.sub (measurable_const : Measurable (fun _ : Ω × Ω => muY j))
              have q1 := (measurable_const : Measurable (fun _ : Ω × Ω => Real.sqrt v)).mul p1
              have q2 := (measurable_const : Measurable (fun _ : Ω × Ω => Real.sqrt (1 - v))).mul p2
              have r1 := q1.add q2
              have r2 := ((measurable_const : Measurable (fun _ : Ω × Ω => Real.sqrt t)).mul r1).add ((measurable_const : Measurable (fun _ : Ω × Ω => Real.sqrt (1 - t))).mul p3)
              exact ((measurable_const : Measurable (fun _ : Ω × Ω => (Real.sqrt (m : ℝ))⁻¹ * delta n m)).mul r2)
            have s1 : Measurable (fun x : Ω × Ω => ∑ i : Fin n, Zstar t x i j) := Finset.measurable_sum Finset.univ (fun i _ => hXi i)
            have s2 : Measurable (fun x : Ω × Ω => ∑ i : Fin m, Zstarstar t x i j) := Finset.measurable_sum Finset.univ (fun i _ => hYi i)
            have hsum : Measurable (fun x : Ω × Ω => (∑ i : Fin n, Zstar t x i j) + (∑ i : Fin m, Zstarstar t x i j)) := s1.add s2
            exact hsum
          have hmA : MeasurableSet {x : Ω × Ω | ∀ j : Fin p, Z t x j ≤ y j + kappa0} := by
            have hset : {x : Ω × Ω | ∀ j : Fin p, Z t x j ≤ y j + kappa0} = ⋂ j : Fin p, {x : Ω × Ω | Z t x j ≤ y j + kappa0} := by
              ext x; simp only [Set.mem_setOf_eq, Set.mem_iInter]
            rw [hset]
            exact MeasurableSet.iInter (fun j => measurableSet_le (hZj j) measurable_const)
          have hmB : MeasurableSet {x : Ω × Ω | ∀ j : Fin p, Z t x j ≤ y j - kappa0} := by
            have hset : {x : Ω × Ω | ∀ j : Fin p, Z t x j ≤ y j - kappa0} = ⋂ j : Fin p, {x : Ω × Ω | Z t x j ≤ y j - kappa0} := by
              ext x; simp only [Set.mem_setOf_eq, Set.mem_iInter]
            rw [hset]
            exact MeasurableSet.iInter (fun j => measurableSet_le (hZj j) measurable_const)
          have hpt : ∀ x : Ω × Ω, hloc (Z t x) = Set.indicator {x : Ω × Ω | ∀ j : Fin p, Z t x j ≤ y j + kappa0} (fun _ => (1:ℝ)) x - Set.indicator {x : Ω × Ω | ∀ j : Fin p, Z t x j ≤ y j - kappa0} (fun _ => (1:ℝ)) x := by
            intro x
            set s : ℝ := ⨆ j : Fin p, (Z t x j - y j) with hs
            have hAs : (x ∈ {x : Ω × Ω | ∀ j : Fin p, Z t x j ≤ y j + kappa0}) ↔ s ≤ kappa0 := by
              rw [Set.mem_setOf_eq, hs, hsup_le]
              constructor <;> intro h j <;> linarith [h j]
            have hBs : (x ∈ {x : Ω × Ω | ∀ j : Fin p, Z t x j ≤ y j - kappa0}) ↔ s ≤ -kappa0 := by
              rw [Set.mem_setOf_eq, hs, hsup_le]
              constructor <;> intro h j <;> linarith [h j]
            have hSs : (Z t x ∈ {w : Fin p → ℝ | -phi⁻¹ - 2 * beta⁻¹ < (⨆ j : Fin p, (w j - y j)) ∧ (⨆ j : Fin p, (w j - y j)) ≤ phi⁻¹ + 2 * beta⁻¹}) ↔ (-kappa0 < s ∧ s ≤ kappa0) := by
              rw [Set.mem_setOf_eq, hneg, hhi, hs]
            simp only [hloc]
            by_cases h1 : s ≤ -kappa0
            · have hSn : Z t x ∉ {w : Fin p → ℝ | -phi⁻¹ - 2 * beta⁻¹ < (⨆ j : Fin p, (w j - y j)) ∧ (⨆ j : Fin p, (w j - y j)) ≤ phi⁻¹ + 2 * beta⁻¹} := by
                intro hmem; have hh := hSs.mp hmem; linarith [hh.1, h1]
              have hAm : x ∈ {x : Ω × Ω | ∀ j : Fin p, Z t x j ≤ y j + kappa0} := hAs.mpr (by linarith [h1, hκ0pos])
              have hBm : x ∈ {x : Ω × Ω | ∀ j : Fin p, Z t x j ≤ y j - kappa0} := hBs.mpr h1
              rw [Set.indicator_of_mem hAm, Set.indicator_of_mem hBm]
              simp [hSn]
            · have hgn : -kappa0 < s := not_le.mp h1
              by_cases h2 : s ≤ kappa0
              · have hSm : Z t x ∈ {w : Fin p → ℝ | -phi⁻¹ - 2 * beta⁻¹ < (⨆ j : Fin p, (w j - y j)) ∧ (⨆ j : Fin p, (w j - y j)) ≤ phi⁻¹ + 2 * beta⁻¹} := hSs.mpr ⟨hgn, h2⟩
                have hAm : x ∈ {x : Ω × Ω | ∀ j : Fin p, Z t x j ≤ y j + kappa0} := hAs.mpr h2
                have hBn : x ∉ {x : Ω × Ω | ∀ j : Fin p, Z t x j ≤ y j - kappa0} := by
                  intro hmem; have hh := hBs.mp hmem; linarith [hh, hgn]
                rw [Set.indicator_of_mem hSm, Set.indicator_of_mem hAm]
                simp [hBn]
              · have hκs : kappa0 < s := not_le.mp h2
                have hSn : Z t x ∉ {w : Fin p → ℝ | -phi⁻¹ - 2 * beta⁻¹ < (⨆ j : Fin p, (w j - y j)) ∧ (⨆ j : Fin p, (w j - y j)) ≤ phi⁻¹ + 2 * beta⁻¹} := by
                  intro hmem; have hh := (hSs.mp hmem).2; linarith [hh, hκs]
                have hAn : x ∉ {x : Ω × Ω | ∀ j : Fin p, Z t x j ≤ y j + kappa0} := by
                  intro hmem; have hh := hAs.mp hmem; linarith [hh, hκs]
                have hBn : x ∉ {x : Ω × Ω | ∀ j : Fin p, Z t x j ≤ y j - kappa0} := by
                  intro hmem; have hh := hBs.mp hmem; linarith [hh, hgn]
                simp [hSn, hAn, hBn]
          have hIA : Integrable (Set.indicator {x : Ω × Ω | ∀ j : Fin p, Z t x j ≤ y j + kappa0} (fun _ => (1:ℝ))) (P.prod P) :=
            MeasureTheory.Integrable.indicator (MeasureTheory.integrable_const (1:ℝ)) hmA
          have hIB : Integrable (Set.indicator {x : Ω × Ω | ∀ j : Fin p, Z t x j ≤ y j - kappa0} (fun _ => (1:ℝ))) (P.prod P) :=
            MeasureTheory.Integrable.indicator (MeasureTheory.integrable_const (1:ℝ)) hmB
          rw [show (fun x : Ω × Ω => hloc (Z t x)) = (fun x : Ω × Ω => Set.indicator {x : Ω × Ω | ∀ j : Fin p, Z t x j ≤ y j + kappa0} (fun _ => (1:ℝ)) x - Set.indicator {x : Ω × Ω | ∀ j : Fin p, Z t x j ≤ y j - kappa0} (fun _ => (1:ℝ)) x) from funext hpt]
          rw [MeasureTheory.integral_sub hIA hIB]
          rw [Statlib.HypothesisTesting.measure_eq_integral_indicator hmA, Statlib.HypothesisTesting.measure_eq_integral_indicator hmB]
        rw [hint]
        linarith [h1.1, h1.2, h2.1, h2.2]
      · have hkey2 : PrPlus - PrMinus ≤ 2 * Cb0 * kappa0 * Real.sqrt (Real.log (p : ℝ)) := by
          simp only [PrPlus, PrMinus, Uprime]
          have hκ0pos : 0 < kappa0 := add_pos (inv_pos.mpr hphi_pos) h2beta
          have hbound := (hCb0 Ω P n m p delta muX muY X Y F G hn hm hp hlogp hδ hFm hGm hind hX2 hY2 hXmu hYmu hFcov hGcov hInt hb_lb).2
          have e1 := hbound y kappa0 hκ0pos
          have e2 : (P {ω : Ω | ∀ j : Fin p, combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤ (y j - kappa0) + kappa0}).toReal - (P {ω : Ω | ∀ j : Fin p, combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤ y j - kappa0}).toReal ≤ Cb0 * kappa0 * Real.sqrt (Real.log (p : ℝ)) := hbound (fun j => y j - kappa0) kappa0 hκ0pos
          have hB : (P {ω : Ω | ∀ j : Fin p, combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤ (y j - kappa0) + kappa0}).toReal = (P {ω : Ω | ∀ j : Fin p, combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤ y j}).toReal := by
            have hset : {ω : Ω | ∀ j : Fin p, combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤ (y j - kappa0) + kappa0} = {ω : Ω | ∀ j : Fin p, combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤ y j} := by
              ext ω
              simp only [Set.mem_setOf_eq]
              constructor <;> intro hh j
              · linarith [hh j]
              · linarith [hh j]
            rw [hset]
          linarith [e1, e2, hB]
        linarith [hkey2]⟩
  /- @proof-region region.target-node.session.f1c96118b12c0dec end -/

end

end Statlib.Imported

