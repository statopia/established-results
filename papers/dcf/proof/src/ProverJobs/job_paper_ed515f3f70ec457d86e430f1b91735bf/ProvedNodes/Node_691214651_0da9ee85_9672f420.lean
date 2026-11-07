import Statlib.HypothesisTesting.Nonparametric.MannWhitney
import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_2276987974_31808913_1237aaa0

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
theorem statopia_math_node_691214651_0da9ee85 : ∀ (b : ℝ) (hb : 0 < b) (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n m p : ℕ) (hn : 0 < n) (hm : 0 < m) (hp : 0 < p)
    (hlogp : 0 < Real.log (p : ℝ)) (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
    (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
    (hXm : ∀ i : Fin n, Measurable (X i))
    (hYm : ∀ i : Fin m, Measurable (Y i))
    (hFm : ∀ i : Fin n, Measurable (F i))
    (hGm : ∀ i : Fin m, Measurable (G i))
    (hindep : iIndepFun (β := fun _ => Fin p → ℝ) (jointFam X Y F G) P)
    (hXL2 : ∀ (i : Fin n) (j : Fin p), MemLp (fun ω => X i ω j) 2 P)
    (hYL2 : ∀ (i : Fin m) (j : Fin p), MemLp (fun ω => Y i ω j) 2 P)
    (hX3 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |X i ω j - muX j| ^ 3) P)
    (hY3 : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => |Y i ω j - muY j| ^ 3) P)
    (hF3 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |F i ω j - muX j| ^ 3) P)
    (hG3 : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => |G i ω j - muY j| ^ 3) P)
    (hXmean : ∀ (i : Fin n) (j : Fin p), ∫ ω, X i ω j ∂P = muX j)
    (hYmean : ∀ (i : Fin m) (j : Fin p), ∫ ω, Y i ω j ∂P = muY j)
    (hFcov : ∀ i : Fin n,
      Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector P
        (fun ω j => F i ω j - muX j) (covX P muX X i))
    (hGcov : ∀ i : Fin m,
      Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector P
        (fun ω j => G i ω j - muY j) (covY P muY Y i))
    (hcomb2 : ∀ j : Fin p, Integrable (fun ω =>
      (combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j) ^ 2) P)
    (hbvar : ∀ j : Fin p, b ≤ ∫ ω,
      (combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j) ^ 2 ∂P)
    (phi1 phi2 : ℝ) (hphi1 : 1 ≤ phi1) (hphi2 : 1 ≤ phi2)
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (y : Fin p → ℝ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (w : ℝ) (hw : 0 ≤ w),
    (∫ x, Set.indicator
        {u : Fin p → ℝ | -w < (⨆ j : Fin p, (u j - y j)) ∧ (⨆ j : Fin p, (u j - y j)) ≤ w}
        (fun _ : Fin p → ℝ => (1 : ℝ))
        (fun j : Fin p =>
          (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ *
            (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))
              + Real.sqrt (1 - t) * (F i x.2 j - muX j)))
          + (∑ i' : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m *
            (Real.sqrt t * (Real.sqrt v * (Y i' x.1 j - muY j) + Real.sqrt (1 - v) * (G i' x.1 j - muY j))
              + Real.sqrt (1 - t) * (G i' x.2 j - muY j))))
        ∂(P.prod P))
      ≤ 2 * rho P n m p (delta n m) muX muY X Y F G +
        (P {ω : Ω | -w < (⨆ j : Fin p, (combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j - y j)) ∧
          (⨆ j : Fin p, (combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j - y j)) ≤ w}).toReal := by
  /- @proof-region region.target-node.session.351c63bd2f89385f begin -/
  intro b hb Ω _ P _ n m p hn hm hp hlogp delta muX muY X Y F G
    hXm hYm hFm hGm hindep hXL2 hYL2 hX3 hY3 hF3 hG3 hXmean hYmean hFcov hGcov hcomb2 hbvar
    phi1 phi2 hphi1 hphi2 v hv0 hv1 y t ht w hw
  haveI : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  have hsup_iff : ∀ (u : Fin p → ℝ) (c : ℝ),
      (⨆ j : Fin p, (u j - y j)) ≤ c ↔ ∀ j : Fin p, u j - y j ≤ c := by
    intro u c
    refine ⟨fun h j => ?_, fun h => ciSup_le h⟩
    exact le_trans (le_ciSup (Finite.bddAbove_range (fun j : Fin p => u j - y j)) j) h
  set S : Set (Fin p → ℝ) :=
    {u : Fin p → ℝ | -w < (⨆ j : Fin p, (u j - y j)) ∧ (⨆ j : Fin p, (u j - y j)) ≤ w} with hS
  have hSmeas : MeasurableSet S := by
    have heq : S = (⋂ j : Fin p, {u : Fin p → ℝ | u j - y j ≤ w}) ∩
        (⋂ j : Fin p, {u : Fin p → ℝ | u j - y j ≤ -w})ᶜ := by
      ext u
      rw [hS]
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨fun j => (hsup_iff u w).1 h2 j,
          fun hj => (not_le.2 h1) ((hsup_iff u (-w)).2 hj)⟩
      · rintro ⟨h1, h2⟩
        exact ⟨not_le.1 (fun hs => h2 ((hsup_iff u (-w)).1 hs)), (hsup_iff u w).2 h1⟩
    rw [heq]
    refine MeasurableSet.inter (MeasurableSet.iInter fun j => ?_)
      (MeasurableSet.iInter fun j => ?_).compl
    · exact measurableSet_le ((measurable_pi_apply j).sub measurable_const) measurable_const
    · exact measurableSet_le ((measurable_pi_apply j).sub measurable_const) measurable_const
  let Zf : Ω × Ω → Fin p → ℝ := fun x j =>
    (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ *
      (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))
        + Real.sqrt (1 - t) * (F i x.2 j - muX j)))
    + (∑ i' : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m *
      (Real.sqrt t * (Real.sqrt v * (Y i' x.1 j - muY j) + Real.sqrt (1 - v) * (G i' x.1 j - muY j))
        + Real.sqrt (1 - t) * (G i' x.2 j - muY j)))
  have hZmeas : Measurable Zf := by
    refine measurable_pi_iff.mpr (fun j => ?_)
    fun_prop
  have hInt : (∫ x, Set.indicator S (fun _ : Fin p → ℝ => (1 : ℝ)) (Zf x) ∂(P.prod P))
      = ((P.prod P) (Zf ⁻¹' S)).toReal := by
    rw [Statlib.HypothesisTesting.measure_eq_integral_indicator (hSmeas.preimage hZmeas)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : Zf x ∈ S
    · simp [hx]
    · simp [hx]
  let Df : Ω → Fin p → ℝ := fun ω => combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω)
  let Gf : Ω → Fin p → ℝ := fun ω => combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω)
  have htv0 : 0 ≤ t * v := mul_nonneg ht.1 hv0
  have htv1 : t * v ≤ 1 := by
    have h := mul_le_mul ht.2 hv1 hv0 (by norm_num : (0 : ℝ) ≤ 1)
    simpa using h
  let M : Ω → Fin p → ℝ := fun ω j =>
    Real.sqrt (t * v) * Df ω j + Real.sqrt (1 - t * v) * Gf ω j
  have hDf_meas : Measurable Df := by
    change Measurable (fun ω : Ω =>
      combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω))
    refine measurable_pi_iff.mpr (fun j => ?_)
    change Measurable (fun ω : Ω =>
      (Real.sqrt (n : ℝ))⁻¹ * (∑ i : Fin n, X i ω j) - Real.sqrt (n : ℝ) * muX j
        + delta n m * ((Real.sqrt (m : ℝ))⁻¹ * (∑ i' : Fin m, Y i' ω j))
        - delta n m * Real.sqrt (m : ℝ) * muY j)
    have hsumX : Measurable (fun ω : Ω => ∑ i : Fin n, X i ω j) := by
      have h := Finset.measurable_sum (Finset.univ : Finset (Fin n))
        (fun i _ => (measurable_pi_apply j).comp (hXm i))
      simpa using h
    have hsumY : Measurable (fun ω : Ω => ∑ i' : Fin m, Y i' ω j) := by
      have h := Finset.measurable_sum (Finset.univ : Finset (Fin m))
        (fun i _ => (measurable_pi_apply j).comp (hYm i))
      simpa using h
    exact (((hsumX.const_mul _).sub measurable_const).add
      (measurable_const.mul (hsumY.const_mul _))).sub measurable_const
  have hGf_meas : Measurable Gf := by
    change Measurable (fun ω : Ω =>
      combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω))
    refine measurable_pi_iff.mpr (fun j => ?_)
    change Measurable (fun ω : Ω =>
      (Real.sqrt (n : ℝ))⁻¹ * (∑ i : Fin n, F i ω j) - Real.sqrt (n : ℝ) * muX j
        + delta n m * ((Real.sqrt (m : ℝ))⁻¹ * (∑ i' : Fin m, G i' ω j))
        - delta n m * Real.sqrt (m : ℝ) * muY j)
    have hsumF : Measurable (fun ω : Ω => ∑ i : Fin n, F i ω j) := by
      have h := Finset.measurable_sum (Finset.univ : Finset (Fin n))
        (fun i _ => (measurable_pi_apply j).comp (hFm i))
      simpa using h
    have hsumG : Measurable (fun ω : Ω => ∑ i' : Fin m, G i' ω j) := by
      have h := Finset.measurable_sum (Finset.univ : Finset (Fin m))
        (fun i _ => (measurable_pi_apply j).comp (hGm i))
      simpa using h
    exact (((hsumF.const_mul _).sub measurable_const).add
      (measurable_const.mul (hsumG.const_mul _))).sub measurable_const
  have hmM : Measurable M := by
    refine measurable_pi_iff.mpr (fun j => ?_)
    change Measurable (fun ω : Ω =>
      Real.sqrt (t * v) * Df ω j + Real.sqrt (1 - t * v) * Gf ω j)
    have h1 : Measurable (fun ω : Ω => Df ω j) := (measurable_pi_apply j).comp hDf_meas
    have h2 : Measurable (fun ω : Ω => Gf ω j) := (measurable_pi_apply j).comp hGf_meas
    exact (h1.const_mul _).add (h2.const_mul _)
  have hZW : Zf = fun x : Ω × Ω => fun j : Fin p =>
      Real.sqrt (t * v) * combVec n m (delta n m) muX muY (fun i => X i x.1) (fun i => Y i x.1) j
        + Real.sqrt (t * (1 - v)) * combVec n m (delta n m) muX muY (fun i => F i x.1) (fun i => G i x.1) j
        + Real.sqrt (1 - t) * combVec n m (delta n m) muX muY (fun i => F i x.2) (fun i => G i x.2) j := by
    have hblk : ∀ (N : ℕ), 0 < N → ∀ (Z : Fin N → ℝ) (μ : ℝ),
        ∑ i : Fin N, (Real.sqrt (N : ℝ))⁻¹ * (Z i - μ)
          = (Real.sqrt (N : ℝ))⁻¹ * (∑ i : Fin N, Z i) - Real.sqrt (N : ℝ) * μ := by
      intro N hN Z μ
      have hcast : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      have hsq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) :=
        Real.mul_self_sqrt (le_of_lt hcast)
      have hconst : (Real.sqrt (N : ℝ))⁻¹ * (N : ℝ) = Real.sqrt (N : ℝ) := by
        set s : ℝ := Real.sqrt (N : ℝ) with hs
        have hss : s * s = (N : ℝ) := by rw [hs]; exact hsq
        have hsne : s ≠ 0 := by rw [hs]; exact ne_of_gt (Real.sqrt_pos.mpr hcast)
        rw [← hss]
        field_simp
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_sub, ← mul_assoc, hconst]
    have hblk3 : ∀ (N : ℕ), 0 < N → ∀ (Z1 Z2 Z3 : Fin N → ℝ) (μ : ℝ),
        ∑ i : Fin N, (Real.sqrt (N : ℝ))⁻¹ *
            (Real.sqrt t * (Real.sqrt v * (Z1 i - μ) + Real.sqrt (1 - v) * (Z2 i - μ))
              + Real.sqrt (1 - t) * (Z3 i - μ))
          = Real.sqrt t * Real.sqrt v *
              ((Real.sqrt (N : ℝ))⁻¹ * (∑ i : Fin N, Z1 i) - Real.sqrt (N : ℝ) * μ)
            + Real.sqrt t * Real.sqrt (1 - v) *
              ((Real.sqrt (N : ℝ))⁻¹ * (∑ i : Fin N, Z2 i) - Real.sqrt (N : ℝ) * μ)
            + Real.sqrt (1 - t) *
              ((Real.sqrt (N : ℝ))⁻¹ * (∑ i : Fin N, Z3 i) - Real.sqrt (N : ℝ) * μ) := by
      intro N hN Z1 Z2 Z3 μ
      have hQ1 : ∑ i : Fin N, Real.sqrt t * Real.sqrt v * ((Real.sqrt (N : ℝ))⁻¹ * (Z1 i - μ))
          = Real.sqrt t * Real.sqrt v *
            ((Real.sqrt (N : ℝ))⁻¹ * (∑ i : Fin N, Z1 i) - Real.sqrt (N : ℝ) * μ) := by
        rw [← Finset.mul_sum, hblk N hN]
      have hQ2 : ∑ i : Fin N, Real.sqrt t * Real.sqrt (1 - v) *
            ((Real.sqrt (N : ℝ))⁻¹ * (Z2 i - μ))
          = Real.sqrt t * Real.sqrt (1 - v) *
            ((Real.sqrt (N : ℝ))⁻¹ * (∑ i : Fin N, Z2 i) - Real.sqrt (N : ℝ) * μ) := by
        rw [← Finset.mul_sum, hblk N hN]
      have hQ3 : ∑ i : Fin N, Real.sqrt (1 - t) * ((Real.sqrt (N : ℝ))⁻¹ * (Z3 i - μ))
          = Real.sqrt (1 - t) *
            ((Real.sqrt (N : ℝ))⁻¹ * (∑ i : Fin N, Z3 i) - Real.sqrt (N : ℝ) * μ) := by
        rw [← Finset.mul_sum, hblk N hN]
      have h1 : ∑ i : Fin N, (Real.sqrt (N : ℝ))⁻¹ *
            (Real.sqrt t * (Real.sqrt v * (Z1 i - μ) + Real.sqrt (1 - v) * (Z2 i - μ))
              + Real.sqrt (1 - t) * (Z3 i - μ))
          = ∑ i : Fin N, (Real.sqrt t * Real.sqrt v * ((Real.sqrt (N : ℝ))⁻¹ * (Z1 i - μ))
              + Real.sqrt t * Real.sqrt (1 - v) * ((Real.sqrt (N : ℝ))⁻¹ * (Z2 i - μ))
              + Real.sqrt (1 - t) * ((Real.sqrt (N : ℝ))⁻¹ * (Z3 i - μ))) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
      rw [h1, Finset.sum_add_distrib, Finset.sum_add_distrib, hQ1, hQ2, hQ3]
    funext x j
    dsimp only [Zf]
    simp only [combVec, normSum]
    rw [Real.sqrt_mul ht.1, Real.sqrt_mul ht.1]
    have hn_eq := hblk3 n hn (fun i => X i x.1 j) (fun i => F i x.1 j) (fun i => F i x.2 j) (muX j)
    have hdm : ∑ i' : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m *
          (Real.sqrt t * (Real.sqrt v * (Y i' x.1 j - muY j) + Real.sqrt (1 - v) * (G i' x.1 j - muY j))
            + Real.sqrt (1 - t) * (G i' x.2 j - muY j))
        = delta n m * ∑ i' : Fin m, (Real.sqrt (m : ℝ))⁻¹ *
          (Real.sqrt t * (Real.sqrt v * (Y i' x.1 j - muY j) + Real.sqrt (1 - v) * (G i' x.1 j - muY j))
            + Real.sqrt (1 - t) * (G i' x.2 j - muY j)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i' _ => ?_)
      ring
    have hm_eq := hblk3 m hm (fun i => Y i x.1 j) (fun i => G i x.1 j) (fun i => G i x.2 j) (muY j)
    rw [hn_eq, hdm, hm_eq]
    ring
  have hlaw : (P.prod P).map Zf = P.map M := by
    have ht01 : t = 0 ∨ t = 1 ∨ (0 < t ∧ t < 1) := by
      rcases lt_or_eq_of_le ht.2 with hlt | heq
      · rcases eq_or_lt_of_le ht.1 with heq0 | hpos
        · exact Or.inl heq0.symm
        · exact Or.inr (Or.inr ⟨hpos, hlt⟩)
      · exact Or.inr (Or.inl heq)
    rcases ht01 with rfl | rfl | ⟨ht0, ht1⟩
    · have hZ0 : Zf = Gf ∘ Prod.snd := by
        rw [hZW]
        funext x j
        dsimp only [Gf]
        simp
      have hM0 : M = Gf := by
        funext ω j
        dsimp only [M, Gf]
        simp
      rw [hZ0, hM0, ← Measure.map_map hGf_meas measurable_snd,
        (measurePreserving_snd : MeasurePreserving Prod.snd (P.prod P) P).map_eq]
    · have hZ1 : Zf = M ∘ Prod.fst := by
        rw [hZW]
        funext x j
        dsimp only [M, Df, Gf]
        simp
      rw [hZ1, ← Measure.map_map hmM measurable_fst,
        (measurePreserving_fst : MeasurePreserving Prod.fst (P.prod P) P).map_eq]
    · rw [hZW]
      exact statopia_math_node_2276987974_31808913 Ω P n m p delta muX muY X Y F G
        hn hm hp hXm hYm hFm hGm hindep hFcov hGcov v hv0 hv1 t ht0 ht1
  set Sp : Set (Fin p → ℝ) := {u : Fin p → ℝ | ∀ j : Fin p, u j - y j ≤ w} with hSp
  set Sm : Set (Fin p → ℝ) := {u : Fin p → ℝ | ∀ j : Fin p, u j - y j ≤ -w} with hSm
  have hSpmeas : MeasurableSet Sp := by
    have he : Sp = ⋂ j : Fin p, {u : Fin p → ℝ | u j - y j ≤ w} := by
      ext u
      simp only [hSp, Set.mem_setOf_eq, Set.mem_iInter]
    rw [he]
    exact MeasurableSet.iInter fun j =>
      measurableSet_le ((measurable_pi_apply j).sub measurable_const) measurable_const
  have hSmmeas : MeasurableSet Sm := by
    have he : Sm = ⋂ j : Fin p, {u : Fin p → ℝ | u j - y j ≤ -w} := by
      ext u
      simp only [hSm, Set.mem_setOf_eq, Set.mem_iInter]
    rw [he]
    exact MeasurableSet.iInter fun j =>
      measurableSet_le ((measurable_pi_apply j).sub measurable_const) measurable_const
  have hSsplit : S = Sp \ Sm := by
    ext u
    rw [hS, hSp, hSm]
    simp only [Set.mem_setOf_eq, Set.mem_diff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(hsup_iff u w).1 h2,
        fun hj => (not_le.2 h1) ((hsup_iff u (-w)).2 hj)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨not_le.1 (fun hs => h2 ((hsup_iff u (-w)).1 hs)), (hsup_iff u w).2 h1⟩
  have hmain : (P (M ⁻¹' S)).toReal
      ≤ 2 * rho P n m p (delta n m) muX muY X Y F G + (P (Gf ⁻¹' S)).toReal := by
    have hle_one : ∀ s : Set Ω, P s ≤ 1 := by
      intro s
      have h : P s ≤ P Set.univ := measure_mono (Set.subset_univ s)
      simpa using h
    have hne_top : ∀ s t : Set Ω, P s + P t ≠ ⊤ := by
      intro s t
      have h2 : P s + P t ≤ 2 := by
        calc P s + P t ≤ 1 + 1 := add_le_add (hle_one s) (hle_one t)
          _ = 2 := by norm_num
      exact ne_top_of_le_ne_top (by simp) h2
    have hMval : ∀ (ω : Ω) (j : Fin p),
        M ω j = Real.sqrt (t * v) * Df ω j + Real.sqrt (1 - t * v) * Gf ω j := fun ω j => rfl
    have hvv : ((⟨t * v, htv0, htv1⟩ : Set.Icc (0 : ℝ) 1) : ℝ) = t * v := rfl
    have hMpre : M ⁻¹' S = M ⁻¹' Sp \ M ⁻¹' Sm := by rw [hSsplit, Set.preimage_diff]
    have hGpre : Gf ⁻¹' S = Gf ⁻¹' Sp \ Gf ⁻¹' Sm := by rw [hSsplit, Set.preimage_diff]
    have hMSp : MeasurableSet (M ⁻¹' Sp) := hSpmeas.preimage hmM
    have hMSm : MeasurableSet (M ⁻¹' Sm) := hSmmeas.preimage hmM
    have hMsub : M ⁻¹' Sm ⊆ M ⁻¹' Sp := by
      intro ω hω
      simp only [Set.mem_preimage, hSp, hSm, Set.mem_setOf_eq] at hω ⊢
      intro j
      linarith [hω j]
    have hGsub : Gf ⁻¹' Sm ⊆ Gf ⁻¹' Sp := by
      intro ω hω
      simp only [Set.mem_preimage, hSp, hSm, Set.mem_setOf_eq] at hω ⊢
      intro j
      linarith [hω j]
    have hMsplit : (P (M ⁻¹' Sp)).toReal = (P (M ⁻¹' Sm)).toReal + (P (M ⁻¹' S)).toReal := by
      have hun : P (M ⁻¹' Sm ∪ (M ⁻¹' Sp \ M ⁻¹' Sm)) =
          P (M ⁻¹' Sm) + P (M ⁻¹' Sp \ M ⁻¹' Sm) :=
        measure_union disjoint_sdiff_self_right (hMSp.diff hMSm)
      rw [Set.union_diff_cancel hMsub] at hun
      have h2 : P (M ⁻¹' Sp \ M ⁻¹' Sm) = P (M ⁻¹' S) := by rw [← hMpre]
      rw [h2] at hun
      rw [hun]
      exact ENNReal.toReal_add (ne_top_of_le_ne_top (by simp) (hle_one _))
        (ne_top_of_le_ne_top (by simp) (hle_one _))
    have hGineq : (P (Gf ⁻¹' Sp)).toReal ≤ (P (Gf ⁻¹' Sm)).toReal + (P (Gf ⁻¹' S)).toReal := by
      have hun : P (Gf ⁻¹' Sm ∪ (Gf ⁻¹' Sp \ Gf ⁻¹' Sm)) ≤
          P (Gf ⁻¹' Sm) + P (Gf ⁻¹' Sp \ Gf ⁻¹' Sm) :=
        measure_union_le _ _
      rw [Set.union_diff_cancel hGsub] at hun
      have h2 : P (Gf ⁻¹' Sp \ Gf ⁻¹' Sm) = P (Gf ⁻¹' S) := by rw [← hGpre]
      rw [h2] at hun
      have h3 : (P (Gf ⁻¹' Sp)).toReal ≤ (P (Gf ⁻¹' Sm) + P (Gf ⁻¹' S)).toReal :=
        ENNReal.toReal_mono (hne_top _ _) hun
      exact le_trans h3 (le_of_eq (ENNReal.toReal_add (ne_top_of_le_ne_top (by simp) (hle_one _))
        (ne_top_of_le_ne_top (by simp) (hle_one _))))
    have hthm : ∀ (v' : Set.Icc (0 : ℝ) 1) (z : Fin p → ℝ),
        |(P {ω : Ω | ∀ j : Fin p, Real.sqrt (v' : ℝ) * Df ω j
              + Real.sqrt (1 - (v' : ℝ)) * Gf ω j ≤ z j}).toReal
          - (P {ω : Ω | ∀ j : Fin p, Gf ω j ≤ z j}).toReal| ≤ 1 := by
      intro v' z
      have ha : (P {ω : Ω | ∀ j : Fin p, Real.sqrt (v' : ℝ) * Df ω j
            + Real.sqrt (1 - (v' : ℝ)) * Gf ω j ≤ z j}).toReal ≤ 1 := by
        calc (P {ω : Ω | ∀ j : Fin p, Real.sqrt (v' : ℝ) * Df ω j
              + Real.sqrt (1 - (v' : ℝ)) * Gf ω j ≤ z j}).toReal
            ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono (by simp) (hle_one _)
          _ = 1 := by simp
      have hb : (P {ω : Ω | ∀ j : Fin p, Gf ω j ≤ z j}).toReal ≤ 1 := by
        calc (P {ω : Ω | ∀ j : Fin p, Gf ω j ≤ z j}).toReal
            ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono (by simp) (hle_one _)
          _ = 1 := by simp
      have ha0 : 0 ≤ (P {ω : Ω | ∀ j : Fin p, Real.sqrt (v' : ℝ) * Df ω j
            + Real.sqrt (1 - (v' : ℝ)) * Gf ω j ≤ z j}).toReal := ENNReal.toReal_nonneg
      have hb0 : 0 ≤ (P {ω : Ω | ∀ j : Fin p, Gf ω j ≤ z j}).toReal := ENNReal.toReal_nonneg
      refine abs_le.mpr ⟨by linarith, by linarith⟩
    have hbdd_y : ∀ v' : Set.Icc (0 : ℝ) 1, BddAbove (Set.range fun z : Fin p → ℝ =>
        |(P {ω : Ω | ∀ j : Fin p, Real.sqrt (v' : ℝ) * Df ω j
              + Real.sqrt (1 - (v' : ℝ)) * Gf ω j ≤ z j}).toReal
          - (P {ω : Ω | ∀ j : Fin p, Gf ω j ≤ z j}).toReal|) := by
      intro v'
      refine ⟨1, ?_⟩
      rintro _ ⟨z, rfl⟩
      exact hthm v' z
    have hbdd_v : BddAbove (Set.range fun v' : Set.Icc (0 : ℝ) 1 => ⨆ z : Fin p → ℝ,
        |(P {ω : Ω | ∀ j : Fin p, Real.sqrt (v' : ℝ) * Df ω j
              + Real.sqrt (1 - (v' : ℝ)) * Gf ω j ≤ z j}).toReal
          - (P {ω : Ω | ∀ j : Fin p, Gf ω j ≤ z j}).toReal|) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨v', rfl⟩
      exact Real.iSup_le (fun z => hthm v' z) zero_le_one
    have hAplus : {ω : Ω | ∀ j : Fin p,
        Real.sqrt ((⟨t * v, htv0, htv1⟩ : Set.Icc (0 : ℝ) 1) : ℝ) * Df ω j
          + Real.sqrt (1 - ((⟨t * v, htv0, htv1⟩ : Set.Icc (0 : ℝ) 1) : ℝ)) * Gf ω j
          ≤ (fun j : Fin p => y j + w) j} = M ⁻¹' Sp := by
      ext ω
      simp only [Set.mem_preimage, hSp, Set.mem_setOf_eq, hMval, hvv]
      constructor
      · intro h j
        linarith [h j]
      · intro h j
        linarith [h j]
    have hBplus : {ω : Ω | ∀ j : Fin p, Gf ω j ≤ (fun j : Fin p => y j + w) j} = Gf ⁻¹' Sp := by
      ext ω
      simp only [Set.mem_preimage, hSp, Set.mem_setOf_eq]
      constructor
      · intro h j
        linarith [h j]
      · intro h j
        linarith [h j]
    have hrho_plus : |(P (M ⁻¹' Sp)).toReal - (P (Gf ⁻¹' Sp)).toReal|
        ≤ rho P n m p (delta n m) muX muY X Y F G := by
      have h1 : (P (M ⁻¹' Sp)) = P {ω : Ω | ∀ j : Fin p,
          Real.sqrt ((⟨t * v, htv0, htv1⟩ : Set.Icc (0 : ℝ) 1) : ℝ) * Df ω j
            + Real.sqrt (1 - ((⟨t * v, htv0, htv1⟩ : Set.Icc (0 : ℝ) 1) : ℝ)) * Gf ω j
            ≤ (fun j : Fin p => y j + w) j} := by rw [← hAplus]
      have h2 : (P (Gf ⁻¹' Sp)) =
          P {ω : Ω | ∀ j : Fin p, Gf ω j ≤ (fun j : Fin p => y j + w) j} := by rw [← hBplus]
      rw [h1, h2]
      exact le_trans (le_ciSup (hbdd_y ⟨t * v, htv0, htv1⟩) (fun j : Fin p => y j + w))
        (le_ciSup hbdd_v ⟨t * v, htv0, htv1⟩)
    have hAminus : {ω : Ω | ∀ j : Fin p,
        Real.sqrt ((⟨t * v, htv0, htv1⟩ : Set.Icc (0 : ℝ) 1) : ℝ) * Df ω j
          + Real.sqrt (1 - ((⟨t * v, htv0, htv1⟩ : Set.Icc (0 : ℝ) 1) : ℝ)) * Gf ω j
          ≤ (fun j : Fin p => y j - w) j} = M ⁻¹' Sm := by
      ext ω
      simp only [Set.mem_preimage, hSm, Set.mem_setOf_eq, hMval, hvv]
      constructor
      · intro h j
        linarith [h j]
      · intro h j
        linarith [h j]
    have hBminus : {ω : Ω | ∀ j : Fin p, Gf ω j ≤ (fun j : Fin p => y j - w) j} = Gf ⁻¹' Sm := by
      ext ω
      simp only [Set.mem_preimage, hSm, Set.mem_setOf_eq]
      constructor
      · intro h j
        linarith [h j]
      · intro h j
        linarith [h j]
    have hrho_minus : |(P (M ⁻¹' Sm)).toReal - (P (Gf ⁻¹' Sm)).toReal|
        ≤ rho P n m p (delta n m) muX muY X Y F G := by
      have h1 : (P (M ⁻¹' Sm)) = P {ω : Ω | ∀ j : Fin p,
          Real.sqrt ((⟨t * v, htv0, htv1⟩ : Set.Icc (0 : ℝ) 1) : ℝ) * Df ω j
            + Real.sqrt (1 - ((⟨t * v, htv0, htv1⟩ : Set.Icc (0 : ℝ) 1) : ℝ)) * Gf ω j
            ≤ (fun j : Fin p => y j - w) j} := by rw [← hAminus]
      have h2 : (P (Gf ⁻¹' Sm)) =
          P {ω : Ω | ∀ j : Fin p, Gf ω j ≤ (fun j : Fin p => y j - w) j} := by rw [← hBminus]
      rw [h1, h2]
      exact le_trans (le_ciSup (hbdd_y ⟨t * v, htv0, htv1⟩) (fun j : Fin p => y j - w))
        (le_ciSup hbdd_v ⟨t * v, htv0, htv1⟩)
    have hb1 : (P (M ⁻¹' Sp)).toReal
        ≤ (P (Gf ⁻¹' Sp)).toReal + rho P n m p (delta n m) muX muY X Y F G := by
      have h := (abs_le.mp hrho_plus).2
      linarith
    have hb2 : (P (Gf ⁻¹' Sm)).toReal
        ≤ (P (M ⁻¹' Sm)).toReal + rho P n m p (delta n m) muX muY X Y F G := by
      have h := (abs_le.mp hrho_minus).1
      linarith
    linarith [hMsplit, hGineq, hb1, hb2]
  have h_main : (∫ x, Set.indicator S (fun _ : Fin p → ℝ => (1 : ℝ)) (Zf x) ∂(P.prod P))
      ≤ 2 * rho P n m p (delta n m) muX muY X Y F G +
        (P {ω : Ω | -w < (⨆ j : Fin p, (combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j - y j)) ∧
          (⨆ j : Fin p, (combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j - y j)) ≤ w}).toReal := by
    rw [hInt]
    have hmapp : ((P.prod P) (Zf ⁻¹' S)) = (P (M ⁻¹' S)) := by
      have h1 : ((P.prod P) (Zf ⁻¹' S)) = ((P.prod P).map Zf S) := by
        rw [Measure.map_apply hZmeas hSmeas]
      have h2 : (P.prod P).map Zf = P.map M := hlaw
      rw [h1, h2]
      exact Measure.map_apply hmM hSmeas
    rw [hmapp]
    exact hmain
  exact h_main
  /- @proof-region region.target-node.session.351c63bd2f89385f end -/

end

end Statlib.Imported

