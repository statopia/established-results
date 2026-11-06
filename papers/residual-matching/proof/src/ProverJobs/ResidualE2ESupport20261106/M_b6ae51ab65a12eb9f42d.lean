import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Vocabulary.MaxType
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_4d45e28b5bdc9d435f78

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
theorem statopia_math_node_2689151497_94127261 : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (hN : 1 ≤ N) (X Y : Ω → Fin N → ℝ)
    (hX_meas : ∀ k : Fin N, Measurable fun ω => X ω k)
    (hY_meas : ∀ k : Fin N, Measurable fun ω => Y ω k)
    (hX_sq : ∀ k : Fin N, Integrable (fun ω => (X ω k) ^ 2) μ)
    (hY_sq : ∀ k : Fin N, Integrable (fun ω => (Y ω k) ^ 2) μ)
    (hX_gauss : ∀ a : Fin N → ℝ, ∃ v : NNReal,
      Measure.map (fun ω => ∑ k : Fin N, a k * X ω k) μ = gaussianReal 0 v)
    (hY_gauss : ∀ a : Fin N → ℝ, ∃ v : NNReal,
      Measure.map (fun ω => ∑ k : Fin N, a k * Y ω k) μ = gaussianReal 0 v)
    (hIndep : IndepFun X Y μ)
    (hincr : ∀ k l : Fin N,
      (∫ ω, X ω k * X ω k ∂μ) + (∫ ω, X ω l * X ω l ∂μ)
          - 2 * (∫ ω, X ω k * X ω l ∂μ)
        ≤ (∫ ω, Y ω k * Y ω k ∂μ) + (∫ ω, Y ω l * Y ω l ∂μ)
          - 2 * (∫ ω, Y ω k * Y ω l ∂μ))
    (beta : ℝ) (hbeta : 0 < beta),
    ContinuousOn
      (fun t : ℝ => ∫ ω, Statlib.StatFoundation.Convergence.smoothMax beta
          (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) ∂μ)
      (Set.Icc 0 1)
    ∧ (∀ t ∈ Set.Ioo 0 1,
        DifferentiableAt ℝ
          (fun t : ℝ => ∫ ω, Statlib.StatFoundation.Convergence.smoothMax beta
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) ∂μ) t)
    ∧ (∀ t ∈ Set.Ioo 0 1,
        0 ≤ deriv
          (fun t : ℝ => ∫ ω, Statlib.StatFoundation.Convergence.smoothMax beta
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) ∂μ) t) := by
  /- @proof-region region.target-node.session.f55b01846bc57219 begin -/
  intro Ω _inst μ _ N hN X Y hX_meas hY_meas hX_sq hY_sq hX_gauss hY_gauss hIndep hincr beta hbeta
  have hcont :
      ContinuousOn
        (fun t : ℝ => ∫ ω, Statlib.StatFoundation.Convergence.smoothMax beta
            (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) ∂μ)
        (Set.Icc 0 1) := by
    intro t₀ ht₀
    refine MeasureTheory.continuousWithinAt_of_dominated
      (bound := fun ω => (∑ j : Fin N, (|X ω j| + |Y ω j|)) + Real.log N / beta) ?_ ?_ ?_ ?_
    · filter_upwards with x
      have hsm : Measurable (Statlib.StatFoundation.Convergence.smoothMax beta) :=
        (Statlib.StatFoundation.Convergence.smoothMax_def_measurable_continuous
          (p := N) (β := beta) (by omega) hbeta).2
      have hZ : Measurable (fun ω : Ω =>
          WithLp.toLp 2 (fun j : Fin N => Real.sqrt x * Y ω j + Real.sqrt (1 - x) * X ω j)) :=
        (WithLp.measurable_toLp 2 (Fin N → ℝ)).comp (by
          rw [measurable_pi_iff]
          intro j
          exact ((hY_meas j).const_mul (Real.sqrt x)).add
            ((hX_meas j).const_mul (Real.sqrt (1 - x))))
      exact (hsm.comp hZ).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with x hx
      haveI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
      have hbdd : ∀ z : EuclideanSpace ℝ (Fin N),
          BddAbove (Set.range fun j : Fin N => |z.ofLp j|) := fun z =>
        (Set.finite_range (fun j : Fin N => |z.ofLp j|)).bddAbove
      have hA : ∀ z : EuclideanSpace ℝ (Fin N),
          Statlib.StatFoundation.Vocabulary.maxCoord z
            ≤ Statlib.StatFoundation.Vocabulary.maxAbsCoord z := by
        intro z
        simp only [Statlib.StatFoundation.Vocabulary.maxCoord,
          Statlib.StatFoundation.Vocabulary.maxAbsCoord]
        refine ciSup_le fun i => ?_
        exact (le_abs_self _).trans (le_ciSup (hbdd z) i)
      have hB : ∀ z : EuclideanSpace ℝ (Fin N),
          -Statlib.StatFoundation.Vocabulary.maxAbsCoord z
            ≤ Statlib.StatFoundation.Vocabulary.maxCoord z := by
        intro z
        simp only [Statlib.StatFoundation.Vocabulary.maxCoord,
          Statlib.StatFoundation.Vocabulary.maxAbsCoord]
        exact le_trans
          ((neg_le_neg (le_ciSup (hbdd z) ⟨0, by omega⟩)).trans
            (neg_abs_le (z.ofLp ⟨0, by omega⟩)))
          (le_ciSup (Set.finite_range (fun j : Fin N => z.ofLp j)).bddAbove ⟨0, by omega⟩)
      have hc0 : 0 ≤ Real.log (N : ℝ) / beta :=
        div_nonneg (Real.log_nonneg (by exact_mod_cast hN)) hbeta.le
      have hsm_bound : ∀ z : EuclideanSpace ℝ (Fin N),
          |Statlib.StatFoundation.Convergence.smoothMax beta z|
            ≤ Statlib.StatFoundation.Vocabulary.maxAbsCoord z + Real.log (N : ℝ) / beta := by
        intro z
        obtain ⟨h1, h2⟩ :=
          Statlib.StatFoundation.Convergence.smoothMax_bounds_max_log_card N (by omega) beta hbeta z
        refine abs_le.mpr ⟨?_, ?_⟩
        · linarith [hB z]
        · linarith [hA z]
      have hcoord : ∀ a : Ω,
          Statlib.StatFoundation.Vocabulary.maxAbsCoord
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt x * Y a j + Real.sqrt (1 - x) * X a j))
            ≤ ∑ j : Fin N, (|X a j| + |Y a j|) := by
        intro a
        simp only [Statlib.StatFoundation.Vocabulary.maxAbsCoord, PiLp.toLp_apply]
        refine ciSup_le fun i => ?_
        have h1 : Real.sqrt x ≤ 1 := Real.sqrt_le_one.mpr hx.2
        have h2 : Real.sqrt (1 - x) ≤ 1 := Real.sqrt_le_one.mpr (by linarith [hx.1])
        have h3 : |Real.sqrt x * Y a i + Real.sqrt (1 - x) * X a i| ≤ |Y a i| + |X a i| := by
          calc |Real.sqrt x * Y a i + Real.sqrt (1 - x) * X a i|
              ≤ |Real.sqrt x * Y a i| + |Real.sqrt (1 - x) * X a i| := abs_add_le _ _
            _ = Real.sqrt x * |Y a i| + Real.sqrt (1 - x) * |X a i| := by
                rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg x),
                  abs_of_nonneg (Real.sqrt_nonneg (1 - x))]
            _ ≤ |Y a i| + |X a i| := by
                nlinarith [abs_nonneg (Y a i), abs_nonneg (X a i), Real.sqrt_nonneg x,
                  Real.sqrt_nonneg (1 - x)]
        have h4 : |X a i| + |Y a i| ≤ ∑ j : Fin N, (|X a j| + |Y a j|) := by
          have hsum := Finset.single_le_sum (s := Finset.univ)
            (f := fun j : Fin N => |X a j| + |Y a j|) (fun j _ => by positivity)
            (Finset.mem_univ i)
          simpa using hsum
        linarith
      filter_upwards with a
      have h1 := hsm_bound
        (WithLp.toLp 2 (fun j : Fin N => Real.sqrt x * Y a j + Real.sqrt (1 - x) * X a j))
      have h2 := hcoord a
      rw [Real.norm_eq_abs]
      linarith
    · have hX_L2 : ∀ k : Fin N, MemLp (fun ω => X ω k) 2 μ := fun k =>
        (MeasureTheory.memLp_two_iff_integrable_sq (hX_meas k).aestronglyMeasurable).mpr (hX_sq k)
      have hY_L2 : ∀ k : Fin N, MemLp (fun ω => Y ω k) 2 μ := fun k =>
        (MeasureTheory.memLp_two_iff_integrable_sq (hY_meas k).aestronglyMeasurable).mpr (hY_sq k)
      have hX_int : ∀ k : Fin N, Integrable (fun ω => X ω k) μ := fun k =>
        MeasureTheory.MemLp.integrable (q := 2) (by norm_num) (hX_L2 k)
      have hY_int : ∀ k : Fin N, Integrable (fun ω => Y ω k) μ := fun k =>
        MeasureTheory.MemLp.integrable (q := 2) (by norm_num) (hY_L2 k)
      have hXabs : ∀ j : Fin N, Integrable (fun ω => |X ω j|) μ := fun j => by
        simpa [Real.norm_eq_abs] using (hX_int j).norm
      have hYabs : ∀ j : Fin N, Integrable (fun ω => |Y ω j|) μ := fun j => by
        simpa [Real.norm_eq_abs] using (hY_int j).norm
      have hsum_int : Integrable (fun ω => ∑ j : Fin N, (|X ω j| + |Y ω j|)) μ := by
        refine integrable_finset_sum (s := Finset.univ)
          (f := fun j ω => |X ω j| + |Y ω j|) ?_
        intro j _
        exact (hXabs j).add (hYabs j)
      exact hsum_int.add (integrable_const _)
    · filter_upwards with ω
      have hsmc : Continuous (Statlib.StatFoundation.Convergence.smoothMax beta) :=
        (Statlib.StatFoundation.Convergence.smoothMax_def_measurable_continuous
          (p := N) (β := beta) (by omega) hbeta).1
      have hZsmul : ∀ x : ℝ,
          WithLp.toLp 2 (fun j : Fin N => Real.sqrt x * Y ω j + Real.sqrt (1 - x) * X ω j)
            = Real.sqrt x • (WithLp.toLp 2 (fun j : Fin N => Y ω j))
              + Real.sqrt (1 - x) • (WithLp.toLp 2 (fun j : Fin N => X ω j)) := by
        intro x
        rw [show (fun j : Fin N => Real.sqrt x * Y ω j + Real.sqrt (1 - x) * X ω j)
              = Real.sqrt x • (fun j : Fin N => Y ω j)
                + Real.sqrt (1 - x) • (fun j : Fin N => X ω j) from rfl]
        rw [WithLp.toLp_add, WithLp.toLp_smul, WithLp.toLp_smul]
      have hc : Continuous (fun x : ℝ =>
          Real.sqrt x • (WithLp.toLp 2 (fun j : Fin N => Y ω j))
            + Real.sqrt (1 - x) • (WithLp.toLp 2 (fun j : Fin N => X ω j))) :=
        (Real.continuous_sqrt.smul continuous_const).add
          ((Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).smul continuous_const)
      simp only [hZsmul]
      exact (hsmc.comp hc).continuousWithinAt
  haveI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  have hZsmul : ∀ (x : ℝ) (ω : Ω),
      WithLp.toLp 2 (fun j : Fin N => Real.sqrt x * Y ω j + Real.sqrt (1 - x) * X ω j)
        = Real.sqrt x • (WithLp.toLp 2 (fun j : Fin N => Y ω j))
          + Real.sqrt (1 - x) • (WithLp.toLp 2 (fun j : Fin N => X ω j)) := by
    intro x ω
    rw [show (fun j : Fin N => Real.sqrt x * Y ω j + Real.sqrt (1 - x) * X ω j)
          = Real.sqrt x • (fun j : Fin N => Y ω j)
            + Real.sqrt (1 - x) • (fun j : Fin N => X ω j) from rfl]
    rw [WithLp.toLp_add, WithLp.toLp_smul, WithLp.toLp_smul]
  have hZ_meas : ∀ x : ℝ, Measurable (fun ω : Ω =>
      WithLp.toLp 2 (fun j : Fin N => Real.sqrt x * Y ω j + Real.sqrt (1 - x) * X ω j)) := by
    intro x
    exact (WithLp.measurable_toLp 2 (Fin N → ℝ)).comp (by
      rw [measurable_pi_iff]
      intro j
      exact ((hY_meas j).const_mul (Real.sqrt x)).add
        ((hX_meas j).const_mul (Real.sqrt (1 - x))))
  have hZ_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ ω : Ω,
      HasDerivAt (fun t : ℝ =>
          WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j))
        (WithLp.toLp 2 (fun j : Fin N =>
          Y ω j / (2 * Real.sqrt x) - X ω j / (2 * Real.sqrt (1 - x)))) x := by
    intro x hx ω
    have hx0 : x ≠ 0 := ne_of_gt hx.1
    have hx1 : (1 - x) ≠ 0 := ne_of_gt (by linarith [hx.2])
    have hYv : HasDerivAt (fun t : ℝ => Real.sqrt t • (WithLp.toLp 2 (fun j : Fin N => Y ω j)))
        ((1 / (2 * Real.sqrt x)) • (WithLp.toLp 2 (fun j : Fin N => Y ω j))) x :=
      (Real.hasDerivAt_sqrt hx0).smul_const _
    have hXv : HasDerivAt
        (fun t : ℝ => Real.sqrt (1 - t) • (WithLp.toLp 2 (fun j : Fin N => X ω j)))
        ((-(1 / (2 * Real.sqrt (1 - x)))) • (WithLp.toLp 2 (fun j : Fin N => X ω j))) x := by
      have hinner : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
        simpa using (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub (hasDerivAt_id x)
      have hsqrt := (Real.hasDerivAt_sqrt hx1).comp x hinner
      have := hsqrt.smul_const (WithLp.toLp 2 (fun j : Fin N => X ω j))
      simpa [Function.comp_apply, mul_neg, mul_one] using this
    have hsum := hYv.add hXv
    have hfn : (fun t : ℝ =>
          WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j))
        = ((fun t : ℝ => Real.sqrt t • (WithLp.toLp 2 (fun j : Fin N => Y ω j)))
            + fun t : ℝ => Real.sqrt (1 - t) • (WithLp.toLp 2 (fun j : Fin N => X ω j))) := by
      funext t
      exact hZsmul t ω
    have hv : ((1 / (2 * Real.sqrt x)) • (WithLp.toLp 2 (fun j : Fin N => Y ω j))
          + (-(1 / (2 * Real.sqrt (1 - x)))) • (WithLp.toLp 2 (fun j : Fin N => X ω j)))
        = WithLp.toLp 2 (fun j : Fin N =>
            Y ω j / (2 * Real.sqrt x) - X ω j / (2 * Real.sqrt (1 - x))) := by
      rw [show (1 / (2 * Real.sqrt x)) • (WithLp.toLp 2 (fun j : Fin N => Y ω j))
            + (-(1 / (2 * Real.sqrt (1 - x)))) • (WithLp.toLp 2 (fun j : Fin N => X ω j))
          = WithLp.toLp 2 ((1 / (2 * Real.sqrt x)) • (fun j : Fin N => Y ω j)
              + (-(1 / (2 * Real.sqrt (1 - x)))) • (fun j : Fin N => X ω j)) from by
        rw [WithLp.toLp_add, WithLp.toLp_smul, WithLp.toLp_smul]]
      congr 1
      funext j
      show (1 / (2 * Real.sqrt x)) * Y ω j + (-(1 / (2 * Real.sqrt (1 - x)))) * X ω j
        = Y ω j / (2 * Real.sqrt x) - X ω j / (2 * Real.sqrt (1 - x))
      ring
    rw [hv, ← hfn] at hsum
    exact hsum
  have hsmw_meas : ∀ k : Fin N, Measurable
      (fun z : EuclideanSpace ℝ (Fin N) =>
        Statlib.StatFoundation.Convergence.softmaxWeight beta z k) := by
    intro k
    unfold Statlib.StatFoundation.Convergence.softmaxWeight
    measurability
  have hbdd : ∀ z : EuclideanSpace ℝ (Fin N),
      BddAbove (Set.range fun j : Fin N => |z.ofLp j|) := fun z =>
    (Set.finite_range (fun j : Fin N => |z.ofLp j|)).bddAbove
  have hmaxA : ∀ z : EuclideanSpace ℝ (Fin N),
      Statlib.StatFoundation.Vocabulary.maxCoord z
        ≤ Statlib.StatFoundation.Vocabulary.maxAbsCoord z := by
    intro z
    simp only [Statlib.StatFoundation.Vocabulary.maxCoord,
      Statlib.StatFoundation.Vocabulary.maxAbsCoord]
    refine ciSup_le fun i => ?_
    exact (le_abs_self _).trans (le_ciSup (hbdd z) i)
  have hmaxB : ∀ z : EuclideanSpace ℝ (Fin N),
      -Statlib.StatFoundation.Vocabulary.maxAbsCoord z
        ≤ Statlib.StatFoundation.Vocabulary.maxCoord z := by
    intro z
    simp only [Statlib.StatFoundation.Vocabulary.maxCoord,
      Statlib.StatFoundation.Vocabulary.maxAbsCoord]
    exact le_trans
      ((neg_le_neg (le_ciSup (hbdd z) ⟨0, by omega⟩)).trans
        (neg_abs_le (z.ofLp ⟨0, by omega⟩)))
      (le_ciSup (Set.finite_range (fun j : Fin N => z.ofLp j)).bddAbove ⟨0, by omega⟩)
  have hc0 : 0 ≤ Real.log (N : ℝ) / beta :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hN)) hbeta.le
  have hsm_bound : ∀ z : EuclideanSpace ℝ (Fin N),
      |Statlib.StatFoundation.Convergence.smoothMax beta z|
        ≤ Statlib.StatFoundation.Vocabulary.maxAbsCoord z + Real.log (N : ℝ) / beta := by
    intro z
    obtain ⟨h1, h2⟩ :=
      Statlib.StatFoundation.Convergence.smoothMax_bounds_max_log_card N (by omega) beta hbeta z
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith [hmaxB z]
    · linarith [hmaxA z]
  have hcoord : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ a : Ω,
      Statlib.StatFoundation.Vocabulary.maxAbsCoord
          (WithLp.toLp 2 (fun j : Fin N => Real.sqrt x * Y a j + Real.sqrt (1 - x) * X a j))
        ≤ ∑ j : Fin N, (|X a j| + |Y a j|) := by
    intro x hx a
    simp only [Statlib.StatFoundation.Vocabulary.maxAbsCoord, PiLp.toLp_apply]
    refine ciSup_le fun i => ?_
    have h1 : Real.sqrt x ≤ 1 := Real.sqrt_le_one.mpr hx.2
    have h2 : Real.sqrt (1 - x) ≤ 1 := Real.sqrt_le_one.mpr (by linarith [hx.1])
    have h3 : |Real.sqrt x * Y a i + Real.sqrt (1 - x) * X a i| ≤ |Y a i| + |X a i| := by
      calc |Real.sqrt x * Y a i + Real.sqrt (1 - x) * X a i|
          ≤ |Real.sqrt x * Y a i| + |Real.sqrt (1 - x) * X a i| := abs_add_le _ _
        _ = Real.sqrt x * |Y a i| + Real.sqrt (1 - x) * |X a i| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg x),
              abs_of_nonneg (Real.sqrt_nonneg (1 - x))]
        _ ≤ |Y a i| + |X a i| := by
            nlinarith [abs_nonneg (Y a i), abs_nonneg (X a i), Real.sqrt_nonneg x,
              Real.sqrt_nonneg (1 - x)]
    have h4 : |X a i| + |Y a i| ≤ ∑ j : Fin N, (|X a j| + |Y a j|) := by
      have hsum := Finset.single_le_sum (s := Finset.univ)
        (f := fun j : Fin N => |X a j| + |Y a j|) (fun j _ => by positivity)
        (Finset.mem_univ i)
      simpa using hsum
    linarith
  have hXint : ∀ k : Fin N, Integrable (fun ω => X ω k) μ := fun k =>
    MeasureTheory.MemLp.integrable (q := 2) (by norm_num)
      ((MeasureTheory.memLp_two_iff_integrable_sq (hX_meas k).aestronglyMeasurable).mpr (hX_sq k))
  have hYint : ∀ k : Fin N, Integrable (fun ω => Y ω k) μ := fun k =>
    MeasureTheory.MemLp.integrable (q := 2) (by norm_num)
      ((MeasureTheory.memLp_two_iff_integrable_sq (hY_meas k).aestronglyMeasurable).mpr (hY_sq k))
  have hXabs : ∀ j : Fin N, Integrable (fun ω => |X ω j|) μ := fun j => by
    simpa [Real.norm_eq_abs] using (hXint j).norm
  have hYabs : ∀ j : Fin N, Integrable (fun ω => |Y ω j|) μ := fun j => by
    simpa [Real.norm_eq_abs] using (hYint j).norm
  have hsum_int : Integrable (fun ω => ∑ j : Fin N, (|X ω j| + |Y ω j|)) μ := by
    refine integrable_finset_sum (s := Finset.univ)
      (f := fun j ω => |X ω j| + |Y ω j|) ?_
    intro j _
    exact (hXabs j).add (hYabs j)
  have henv : Integrable
      (fun ω => (∑ j : Fin N, (|X ω j| + |Y ω j|)) + Real.log (N : ℝ) / beta + 1) μ :=
    (hsum_int.add (integrable_const _)).add (integrable_const _)
  have hsm_meas' : Measurable (Statlib.StatFoundation.Convergence.smoothMax beta) :=
    (Statlib.StatFoundation.Convergence.smoothMax_def_measurable_continuous
      (p := N) (β := beta) (by omega) hbeta).2
  have hpoint : ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ ω : Ω,
      HasDerivAt (fun t : ℝ => Statlib.StatFoundation.Convergence.smoothMax beta
          (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)))
        (∑ k : Fin N, Statlib.StatFoundation.Convergence.softmaxWeight beta
            (WithLp.toLp 2 (fun j : Fin N => Real.sqrt x * Y ω j + Real.sqrt (1 - x) * X ω j)) k
            * (Y ω k / (2 * Real.sqrt x) - X ω k / (2 * Real.sqrt (1 - x)))) x := by
    intro x hx ω
    have hgrad := Statlib.StatFoundation.Convergence.smoothMax_gradient_eq_softmax
      (p := N) (β := beta) (by omega) hbeta
      (WithLp.toLp 2 (fun j : Fin N => Real.sqrt x * Y ω j + Real.sqrt (1 - x) * X ω j))
    have hcomp := hgrad.comp_hasDerivAt x (hZ_deriv x hx ω)
    have hval : ((innerSL ℝ) (WithLp.toLp 2 (fun j : Fin N =>
          Statlib.StatFoundation.Convergence.softmaxWeight beta
            (WithLp.toLp 2 (fun j : Fin N =>
              Real.sqrt x * Y ω j + Real.sqrt (1 - x) * X ω j)) j)))
        (WithLp.toLp 2 (fun j : Fin N =>
          Y ω j / (2 * Real.sqrt x) - X ω j / (2 * Real.sqrt (1 - x))))
        = ∑ k : Fin N, Statlib.StatFoundation.Convergence.softmaxWeight beta
            (WithLp.toLp 2 (fun j : Fin N =>
              Real.sqrt x * Y ω j + Real.sqrt (1 - x) * X ω j)) k
            * (Y ω k / (2 * Real.sqrt x) - X ω k / (2 * Real.sqrt (1 - x))) := by
      rw [innerSL_apply_apply, PiLp.inner_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [RCLike.inner_apply', mul_comm]
    rw [← hval]
    exact hcomp
  have hF'_meas : ∀ t : ℝ, AEStronglyMeasurable (fun ω : Ω => ∑ k : Fin N,
      Statlib.StatFoundation.Convergence.softmaxWeight beta
        (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
        * (Y ω k / (2 * Real.sqrt t) - X ω k / (2 * Real.sqrt (1 - t)))) μ := by
    intro t
    apply Measurable.aestronglyMeasurable
    refine Finset.measurable_sum Finset.univ (fun k _ => ?_)
    exact ((hsmw_meas k).comp (hZ_meas t)).mul
      (((hY_meas k).div measurable_const).sub ((hX_meas k).div measurable_const))
  have hw_meas : Measurable (fun ω : Ω =>
      (∑ j : Fin N, (|X ω j| + |Y ω j|)) + Real.log (N : ℝ) / beta + 1) := by
    have hsum_meas : Measurable (fun ω : Ω => ∑ j : Fin N, (|X ω j| + |Y ω j|)) :=
      Finset.measurable_sum Finset.univ (fun j _ => ((hX_meas j).abs).add ((hY_meas j).abs))
    exact (hsum_meas.add measurable_const).add measurable_const
  have hwpos : ∀ ω : Ω,
      0 < (∑ j : Fin N, (|X ω j| + |Y ω j|)) + Real.log (N : ℝ) / beta + 1 := by
    intro ω
    have h1 : 0 ≤ ∑ j : Fin N, (|X ω j| + |Y ω j|) := Finset.sum_nonneg fun j _ => by positivity
    linarith [hc0]
  have hF_int : ∀ t ∈ Set.Ioo (0 : ℝ) 1, Integrable (fun ω : Ω =>
      Statlib.StatFoundation.Convergence.smoothMax beta
        (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j))) μ := by
    intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    have hratio_meas : AEStronglyMeasurable (fun ω : Ω =>
        Statlib.StatFoundation.Convergence.smoothMax beta
          (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j))
        / ((∑ j : Fin N, (|X ω j| + |Y ω j|)) + Real.log (N : ℝ) / beta + 1)) μ :=
      ((hsm_meas'.comp (hZ_meas t)).div hw_meas).aestronglyMeasurable
    have hrbound : ∀ᵐ ω ∂μ, ‖Statlib.StatFoundation.Convergence.smoothMax beta
          (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j))
        / ((∑ j : Fin N, (|X ω j| + |Y ω j|)) + Real.log (N : ℝ) / beta + 1)‖ ≤ 1 := by
      filter_upwards with ω
      have hb := hsm_bound (WithLp.toLp 2 (fun j : Fin N =>
        Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j))
      have hc := hcoord t ⟨le_of_lt ht0, le_of_lt ht1⟩ ω
      have h1 : 0 ≤ ∑ j : Fin N, (|X ω j| + |Y ω j|) :=
        Finset.sum_nonneg fun j _ => by positivity
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (hwpos ω), div_le_one (hwpos ω)]
      linarith
    have hbm := MeasureTheory.Integrable.bdd_mul (c := 1) henv hratio_meas hrbound
    convert hbm using 1
    funext ω
    have hne : ((∑ j : Fin N, (|X ω j| + |Y ω j|)) + Real.log (N : ℝ) / beta + 1) ≠ 0 :=
      ne_of_gt (hwpos ω)
    field_simp
  have hderiv :
      ∀ t ∈ Set.Ioo 0 1,
        HasDerivAt
          (fun t : ℝ => ∫ ω, Statlib.StatFoundation.Convergence.smoothMax beta
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) ∂μ)
          (∫ ω, ∑ k : Fin N, Statlib.StatFoundation.Convergence.softmaxWeight beta
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
              * (Y ω k / (2 * Real.sqrt t) - X ω k / (2 * Real.sqrt (1 - t))) ∂μ) t := by
    intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    have ht2pos : 0 < Real.sqrt (t / 2) := Real.sqrt_pos.mpr (by linarith)
    have ht2pos' : 0 < Real.sqrt ((1 - t) / 2) := Real.sqrt_pos.mpr (by linarith)
    have hCnn : 0 ≤ 1 / (2 * Real.sqrt (t / 2)) + 1 / (2 * Real.sqrt ((1 - t) / 2)) := by
      have h1 : 0 ≤ 1 / (2 * Real.sqrt (t / 2)) := by positivity
      have h2 : 0 ≤ 1 / (2 * Real.sqrt ((1 - t) / 2)) := by positivity
      linarith
    have hs : Set.Ioo (t / 2) ((t + 1) / 2) ∈ nhds t :=
      IsOpen.mem_nhds isOpen_Ioo ⟨by linarith, by linarith⟩
    have hF_ae : ∀ᶠ x in nhds t, AEStronglyMeasurable (fun ω : Ω =>
        Statlib.StatFoundation.Convergence.smoothMax beta
          (WithLp.toLp 2 (fun j : Fin N =>
            Real.sqrt x * Y ω j + Real.sqrt (1 - x) * X ω j))) μ := by
      filter_upwards with x
      exact (hsm_meas'.comp (hZ_meas x)).aestronglyMeasurable
    have hpt : ∀ᵐ ω ∂μ, ∀ x ∈ Set.Ioo (t / 2) ((t + 1) / 2),
        HasDerivAt (fun x : ℝ => Statlib.StatFoundation.Convergence.smoothMax beta
            (WithLp.toLp 2 (fun j : Fin N =>
              Real.sqrt x * Y ω j + Real.sqrt (1 - x) * X ω j)))
          (∑ k : Fin N, Statlib.StatFoundation.Convergence.softmaxWeight beta
              (WithLp.toLp 2 (fun j : Fin N =>
                Real.sqrt x * Y ω j + Real.sqrt (1 - x) * X ω j)) k
              * (Y ω k / (2 * Real.sqrt x) - X ω k / (2 * Real.sqrt (1 - x)))) x := by
      filter_upwards with ω x hx
      exact hpoint x ⟨by linarith [hx.1], by linarith [hx.2]⟩ ω
    have hbound_int : Integrable (fun ω : Ω =>
        (1 / (2 * Real.sqrt (t / 2)) + 1 / (2 * Real.sqrt ((1 - t) / 2)))
          * ((∑ j : Fin N, (|X ω j| + |Y ω j|)) + Real.log (N : ℝ) / beta + 1)) μ :=
      henv.const_mul _
    have hbound : ∀ᵐ ω ∂μ, ∀ x ∈ Set.Ioo (t / 2) ((t + 1) / 2),
        ‖∑ k : Fin N, Statlib.StatFoundation.Convergence.softmaxWeight beta
            (WithLp.toLp 2 (fun j : Fin N =>
              Real.sqrt x * Y ω j + Real.sqrt (1 - x) * X ω j)) k
            * (Y ω k / (2 * Real.sqrt x) - X ω k / (2 * Real.sqrt (1 - x)))‖
          ≤ (1 / (2 * Real.sqrt (t / 2)) + 1 / (2 * Real.sqrt ((1 - t) / 2)))
            * ((∑ j : Fin N, (|X ω j| + |Y ω j|)) + Real.log (N : ℝ) / beta + 1) := by
      filter_upwards with ω x hx
      obtain ⟨hxA, hxB⟩ := hx
      have hxpos : 0 < x := by linarith
      have h1mx : 0 < 1 - x := by linarith
      have hsqx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
      have hsqmx : 0 < Real.sqrt (1 - x) := Real.sqrt_pos.mpr h1mx
      have hAle : 1 / (2 * Real.sqrt x) ≤ 1 / (2 * Real.sqrt (t / 2)) :=
        div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
          (by linarith : (0 : ℝ) < 2 * Real.sqrt (t / 2))
          (by
            have h := Real.sqrt_le_sqrt (show t / 2 ≤ x by linarith)
            linarith)
      have hBle : 1 / (2 * Real.sqrt (1 - x)) ≤ 1 / (2 * Real.sqrt ((1 - t) / 2)) :=
        div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
          (by linarith : (0 : ℝ) < 2 * Real.sqrt ((1 - t) / 2))
          (by
            have h := Real.sqrt_le_sqrt (show (1 - t) / 2 ≤ 1 - x by linarith)
            linarith)
      obtain ⟨hpn, hpsum⟩ :=
        Statlib.StatFoundation.Convergence.softmax_weights_sum_nonneg
          (p := N) (β := beta) (by omega)
          (WithLp.toLp 2 (fun j : Fin N => Real.sqrt x * Y ω j + Real.sqrt (1 - x) * X ω j))
      have hp1 : ∀ k : Fin N,
          Statlib.StatFoundation.Convergence.softmaxWeight beta
            (WithLp.toLp 2 (fun j : Fin N =>
              Real.sqrt x * Y ω j + Real.sqrt (1 - x) * X ω j)) k ≤ 1 := by
        intro k
        have h := Finset.single_le_sum (s := Finset.univ)
          (f := fun j : Fin N => Statlib.StatFoundation.Convergence.softmaxWeight beta
            (WithLp.toLp 2 (fun j : Fin N =>
              Real.sqrt x * Y ω j + Real.sqrt (1 - x) * X ω j)) j)
          (fun j _ => hpn j) (Finset.mem_univ k)
        rwa [hpsum] at h
      have hterm : ∀ k : Fin N,
          |Statlib.StatFoundation.Convergence.softmaxWeight beta
              (WithLp.toLp 2 (fun j : Fin N =>
                Real.sqrt x * Y ω j + Real.sqrt (1 - x) * X ω j)) k
            * (Y ω k / (2 * Real.sqrt x) - X ω k / (2 * Real.sqrt (1 - x)))|
          ≤ (1 / (2 * Real.sqrt (t / 2)) + 1 / (2 * Real.sqrt ((1 - t) / 2)))
            * (Statlib.StatFoundation.Convergence.softmaxWeight beta
                (WithLp.toLp 2 (fun j : Fin N =>
                  Real.sqrt x * Y ω j + Real.sqrt (1 - x) * X ω j)) k
              * (|X ω k| + |Y ω k|)) := by
        intro k
        have hu : |Y ω k / (2 * Real.sqrt x) - X ω k / (2 * Real.sqrt (1 - x))|
            ≤ (1 / (2 * Real.sqrt (t / 2)) + 1 / (2 * Real.sqrt ((1 - t) / 2)))
              * (|X ω k| + |Y ω k|) := by
          have hsplit : |Y ω k / (2 * Real.sqrt x) - X ω k / (2 * Real.sqrt (1 - x))|
              ≤ |Y ω k / (2 * Real.sqrt x)| + |X ω k / (2 * Real.sqrt (1 - x))| := by
            simpa [sub_eq_add_neg] using
              abs_add_le (Y ω k / (2 * Real.sqrt x))
                (-(X ω k / (2 * Real.sqrt (1 - x))))
          have h1 : |Y ω k / (2 * Real.sqrt x)|
              ≤ (1 / (2 * Real.sqrt (t / 2))) * |Y ω k| := by
            rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 * Real.sqrt x)]
            calc |Y ω k| / (2 * Real.sqrt x)
                = (1 / (2 * Real.sqrt x)) * |Y ω k| := by
                  rw [div_eq_mul_inv, one_div]
                  ring
              _ ≤ (1 / (2 * Real.sqrt (t / 2))) * |Y ω k| :=
                  mul_le_mul_of_nonneg_right hAle (abs_nonneg _)
          have h2 : |X ω k / (2 * Real.sqrt (1 - x))|
              ≤ (1 / (2 * Real.sqrt ((1 - t) / 2))) * |X ω k| := by
            rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 * Real.sqrt (1 - x))]
            calc |X ω k| / (2 * Real.sqrt (1 - x))
                = (1 / (2 * Real.sqrt (1 - x))) * |X ω k| := by
                  rw [div_eq_mul_inv, one_div]
                  ring
              _ ≤ (1 / (2 * Real.sqrt ((1 - t) / 2))) * |X ω k| :=
                  mul_le_mul_of_nonneg_right hBle (abs_nonneg _)
          have hAnn : 0 ≤ 1 / (2 * Real.sqrt (t / 2)) := by positivity
          have hBnn : 0 ≤ 1 / (2 * Real.sqrt ((1 - t) / 2)) := by positivity
          nlinarith [abs_nonneg (X ω k), abs_nonneg (Y ω k), hsplit, h1, h2, hAnn, hBnn]
        calc |Statlib.StatFoundation.Convergence.softmaxWeight beta
              (WithLp.toLp 2 (fun j : Fin N =>
                Real.sqrt x * Y ω j + Real.sqrt (1 - x) * X ω j)) k
            * (Y ω k / (2 * Real.sqrt x) - X ω k / (2 * Real.sqrt (1 - x)))|
            = Statlib.StatFoundation.Convergence.softmaxWeight beta
                (WithLp.toLp 2 (fun j : Fin N =>
                  Real.sqrt x * Y ω j + Real.sqrt (1 - x) * X ω j)) k
              * |Y ω k / (2 * Real.sqrt x) - X ω k / (2 * Real.sqrt (1 - x))| := by
              rw [abs_mul, abs_of_nonneg (hpn k)]
          _ ≤ Statlib.StatFoundation.Convergence.softmaxWeight beta
                (WithLp.toLp 2 (fun j : Fin N =>
                  Real.sqrt x * Y ω j + Real.sqrt (1 - x) * X ω j)) k
              * ((1 / (2 * Real.sqrt (t / 2)) + 1 / (2 * Real.sqrt ((1 - t) / 2)))
                * (|X ω k| + |Y ω k|)) := mul_le_mul_of_nonneg_left hu (hpn k)
          _ = (1 / (2 * Real.sqrt (t / 2)) + 1 / (2 * Real.sqrt ((1 - t) / 2)))
              * (Statlib.StatFoundation.Convergence.softmaxWeight beta
                  (WithLp.toLp 2 (fun j : Fin N =>
                    Real.sqrt x * Y ω j + Real.sqrt (1 - x) * X ω j)) k
                * (|X ω k| + |Y ω k|)) := by ring
      rw [Real.norm_eq_abs]
      calc |∑ k : Fin N, Statlib.StatFoundation.Convergence.softmaxWeight beta
              (WithLp.toLp 2 (fun j : Fin N =>
                Real.sqrt x * Y ω j + Real.sqrt (1 - x) * X ω j)) k
            * (Y ω k / (2 * Real.sqrt x) - X ω k / (2 * Real.sqrt (1 - x)))|
          ≤ ∑ k : Fin N, |Statlib.StatFoundation.Convergence.softmaxWeight beta
              (WithLp.toLp 2 (fun j : Fin N =>
                Real.sqrt x * Y ω j + Real.sqrt (1 - x) * X ω j)) k
            * (Y ω k / (2 * Real.sqrt x) - X ω k / (2 * Real.sqrt (1 - x)))| :=
            Finset.abs_sum_le_sum_abs (fun k : Fin N =>
              Statlib.StatFoundation.Convergence.softmaxWeight beta
                (WithLp.toLp 2 (fun j : Fin N =>
                  Real.sqrt x * Y ω j + Real.sqrt (1 - x) * X ω j)) k
                * (Y ω k / (2 * Real.sqrt x) - X ω k / (2 * Real.sqrt (1 - x)))) Finset.univ
        _ ≤ ∑ k : Fin N, (1 / (2 * Real.sqrt (t / 2)) + 1 / (2 * Real.sqrt ((1 - t) / 2)))
              * (Statlib.StatFoundation.Convergence.softmaxWeight beta
                  (WithLp.toLp 2 (fun j : Fin N =>
                    Real.sqrt x * Y ω j + Real.sqrt (1 - x) * X ω j)) k
                * (|X ω k| + |Y ω k|)) := Finset.sum_le_sum fun k _ => hterm k
        _ = (1 / (2 * Real.sqrt (t / 2)) + 1 / (2 * Real.sqrt ((1 - t) / 2)))
              * ∑ k : Fin N, Statlib.StatFoundation.Convergence.softmaxWeight beta
                  (WithLp.toLp 2 (fun j : Fin N =>
                    Real.sqrt x * Y ω j + Real.sqrt (1 - x) * X ω j)) k
                * (|X ω k| + |Y ω k|) := by
              rw [Finset.mul_sum]
        _ ≤ (1 / (2 * Real.sqrt (t / 2)) + 1 / (2 * Real.sqrt ((1 - t) / 2)))
              * ∑ k : Fin N, (|X ω k| + |Y ω k|) := by
              apply mul_le_mul_of_nonneg_left _ hCnn
              exact Finset.sum_le_sum fun k _ => by
                calc Statlib.StatFoundation.Convergence.softmaxWeight beta
                      (WithLp.toLp 2 (fun j : Fin N =>
                        Real.sqrt x * Y ω j + Real.sqrt (1 - x) * X ω j)) k
                    * (|X ω k| + |Y ω k|)
                    ≤ 1 * (|X ω k| + |Y ω k|) :=
                      mul_le_mul_of_nonneg_right (hp1 k) (by positivity)
                  _ = |X ω k| + |Y ω k| := one_mul _
        _ ≤ (1 / (2 * Real.sqrt (t / 2)) + 1 / (2 * Real.sqrt ((1 - t) / 2)))
              * ((∑ j : Fin N, (|X ω j| + |Y ω j|)) + Real.log (N : ℝ) / beta + 1) := by
              apply mul_le_mul_of_nonneg_left _ hCnn
              linarith [hc0]
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun ω : Ω =>
        (1 / (2 * Real.sqrt (t / 2)) + 1 / (2 * Real.sqrt ((1 - t) / 2)))
          * ((∑ j : Fin N, (|X ω j| + |Y ω j|)) + Real.log (N : ℝ) / beta + 1))
      hs hF_ae (hF_int t ⟨ht0, ht1⟩) (hF'_meas t) hbound hbound_int hpt).2
  have hnonneg :
      ∀ t ∈ Set.Ioo 0 1,
        0 ≤ ∫ ω, ∑ k : Fin N, Statlib.StatFoundation.Convergence.softmaxWeight beta
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
              * (Y ω k / (2 * Real.sqrt t) - X ω k / (2 * Real.sqrt (1 - t))) ∂μ := by
    intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    have halg : ∀ (p : Fin N → ℝ) (D : Fin N → Fin N → ℝ), (∑ k, p k = 1) →
        (∑ k, ∑ l, D k l * (p k * (if k = l then (1 : ℝ) else 0) - p k * p l))
          = (1 / 2) * ∑ k, ∑ l, p k * p l * (D k k + D l l - 2 * D k l) := by
      intro p D hp
      have hdiag : ∀ k : Fin N,
          ∑ l : Fin N, D k l * (p k * (if k = l then (1 : ℝ) else 0)) = D k k * p k := by
        intro k
        calc ∑ l : Fin N, D k l * (p k * (if k = l then (1 : ℝ) else 0))
            = ∑ l : Fin N, (if k = l then (1 : ℝ) else 0) * (D k l * p k) :=
              Finset.sum_congr rfl fun l _ => by ring
          _ = D k k * p k := by
              rw [Finset.sum_boole_mul]
              simp
      have h1 : ∑ k, ∑ l, D k l * (p k * (if k = l then (1 : ℝ) else 0) - p k * p l)
          = ∑ k, D k k * p k - ∑ k, ∑ l, D k l * (p k * p l) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        calc ∑ l : Fin N, D k l * (p k * (if k = l then (1 : ℝ) else 0) - p k * p l)
            = ∑ l : Fin N,
                (D k l * (p k * (if k = l then (1 : ℝ) else 0)) - D k l * (p k * p l)) :=
              Finset.sum_congr rfl fun l _ => by ring
          _ = D k k * p k - ∑ l : Fin N, D k l * (p k * p l) := by
              rw [Finset.sum_sub_distrib, hdiag k]
      have hP1 : ∑ k, ∑ l, p k * p l * D k k = ∑ k, D k k * p k := by
        have hs := Fintype.sum_mul_sum (fun k : Fin N => D k k * p k) (fun l : Fin N => p l)
        rw [hp, mul_one] at hs
        calc ∑ k, ∑ l, p k * p l * D k k
            = ∑ k, ∑ l, (D k k * p k) * p l :=
              Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
          _ = ∑ k, D k k * p k := hs.symm
      have hP2 : ∑ k, ∑ l, p k * p l * D l l = ∑ k, D k k * p k := by
        have hs := Fintype.sum_mul_sum (fun k : Fin N => p k) (fun l : Fin N => D l l * p l)
        rw [hp, one_mul] at hs
        calc ∑ k, ∑ l, p k * p l * D l l
            = ∑ k, ∑ l, p k * (D l l * p l) :=
              Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
          _ = ∑ l, D l l * p l := hs.symm
          _ = ∑ k, D k k * p k := rfl
      have hT : ∑ k, ∑ l, p k * p l * (D k k + D l l - 2 * D k l)
          = (∑ k, D k k * p k) + (∑ k, D k k * p k)
            - 2 * (∑ k, ∑ l, D k l * (p k * p l)) := by
        calc ∑ k, ∑ l, p k * p l * (D k k + D l l - 2 * D k l)
            = ∑ k, ∑ l,
                (p k * p l * D k k + p k * p l * D l l - 2 * (D k l * (p k * p l))) :=
              Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
          _ = ∑ k, ((∑ l, p k * p l * D k k) + (∑ l, p k * p l * D l l)
                - (∑ l, 2 * (D k l * (p k * p l)))) := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
          _ = ∑ k, ((∑ l, p k * p l * D k k) + (∑ l, p k * p l * D l l)
                - 2 * (∑ l, D k l * (p k * p l))) := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [← Finset.mul_sum]
          _ = (∑ k, ∑ l, p k * p l * D k k) + (∑ k, ∑ l, p k * p l * D l l)
                - 2 * (∑ k, ∑ l, D k l * (p k * p l)) := by
              rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
          _ = (∑ k, D k k * p k) + (∑ k, D k k * p k)
                - 2 * (∑ k, ∑ l, D k l * (p k * p l)) := by
              rw [hP1, hP2]
      rw [h1, hT]
      ring
    have hpsm : ∀ (ω : Ω) (k : Fin N),
        Statlib.StatFoundation.Convergence.softmaxWeight beta
            (WithLp.toLp 2 (fun j : Fin N =>
              Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k ≤ 1 := by
      intro ω k
      obtain ⟨h1, h2⟩ := Statlib.StatFoundation.Convergence.softmax_weights_sum_nonneg
        (p := N) (β := beta) (by omega)
        (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j))
      have hle := Finset.single_le_sum (s := Finset.univ)
        (f := fun j : Fin N => Statlib.StatFoundation.Convergence.softmaxWeight beta
          (WithLp.toLp 2 (fun j : Fin N =>
            Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) j)
        (fun j _ => h1 j) (Finset.mem_univ k)
      rwa [h2] at hle
    have hbdd_p : ∀ (ω : Ω) (k : Fin N),
        ‖Statlib.StatFoundation.Convergence.softmaxWeight beta
            (WithLp.toLp 2 (fun j : Fin N =>
              Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k‖ ≤ 1 := by
      intro ω k
      obtain ⟨h1, _⟩ := Statlib.StatFoundation.Convergence.softmax_weights_sum_nonneg
        (p := N) (β := beta) (by omega)
        (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j))
      rw [Real.norm_eq_abs, abs_of_nonneg (h1 k)]
      exact hpsm ω k
    have hAint : Integrable (fun ω : Ω => ∑ k : Fin N,
        Statlib.StatFoundation.Convergence.softmaxWeight beta
          (WithLp.toLp 2 (fun j : Fin N =>
            Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k * Y ω k) μ := by
      refine integrable_finset_sum (s := Finset.univ) (f := fun k (ω : Ω) =>
        Statlib.StatFoundation.Convergence.softmaxWeight beta
          (WithLp.toLp 2 (fun j : Fin N =>
            Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k * Y ω k) ?_
      intro k _
      exact MeasureTheory.Integrable.bdd_mul (c := 1) (hYint k)
        ((hsmw_meas k).comp (hZ_meas t)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => hbdd_p ω k)
    have hBint : Integrable (fun ω : Ω => ∑ k : Fin N,
        Statlib.StatFoundation.Convergence.softmaxWeight beta
          (WithLp.toLp 2 (fun j : Fin N =>
            Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k * X ω k) μ := by
      refine integrable_finset_sum (s := Finset.univ) (f := fun k (ω : Ω) =>
        Statlib.StatFoundation.Convergence.softmaxWeight beta
          (WithLp.toLp 2 (fun j : Fin N =>
            Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k * X ω k) ?_
      intro k _
      exact MeasureTheory.Integrable.bdd_mul (c := 1) (hXint k)
        ((hsmw_meas k).comp (hZ_meas t)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => hbdd_p ω k)
    obtain ⟨hIY, hIX⟩ :=
      statopia_math_node_1558287015_ebcf50db μ N hN X Y hX_meas hY_meas hX_gauss hY_gauss
        hIndep beta hbeta t ht0 ht1
    have hpt : ∀ ω : Ω,
        ∑ k : Fin N, Statlib.StatFoundation.Convergence.softmaxWeight beta
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
            * (Y ω k / (2 * Real.sqrt t) - X ω k / (2 * Real.sqrt (1 - t)))
          = (1 / (2 * Real.sqrt t)) * (∑ k : Fin N,
                Statlib.StatFoundation.Convergence.softmaxWeight beta
                  (WithLp.toLp 2 (fun j : Fin N =>
                    Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k * Y ω k)
            - (1 / (2 * Real.sqrt (1 - t))) * (∑ k : Fin N,
                Statlib.StatFoundation.Convergence.softmaxWeight beta
                  (WithLp.toLp 2 (fun j : Fin N =>
                    Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k * X ω k) := by
      intro ω
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hsplit : ∫ ω, ∑ k : Fin N, Statlib.StatFoundation.Convergence.softmaxWeight beta
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
              * (Y ω k / (2 * Real.sqrt t) - X ω k / (2 * Real.sqrt (1 - t))) ∂μ
          = (1 / (2 * Real.sqrt t)) * (∫ ω, ∑ k : Fin N,
                Statlib.StatFoundation.Convergence.softmaxWeight beta
                  (WithLp.toLp 2 (fun j : Fin N =>
                    Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k * Y ω k ∂μ)
            - (1 / (2 * Real.sqrt (1 - t))) * (∫ ω, ∑ k : Fin N,
                Statlib.StatFoundation.Convergence.softmaxWeight beta
                  (WithLp.toLp 2 (fun j : Fin N =>
                    Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k * X ω k ∂μ) := by
      simp only [hpt]
      rw [integral_sub (hAint.const_mul _) (hBint.const_mul _),
        integral_const_mul_of_integrable hAint, integral_const_mul_of_integrable hBint]
    have hint_gen : ∀ (Z : Ω → EuclideanSpace ℝ (Fin N)), Measurable Z →
        ∀ c : Fin N → Fin N → ℝ, Integrable (fun ω : Ω => ∑ k : Fin N, ∑ l : Fin N,
          c k l * (beta * (Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) k
            * (if k = l then (1 : ℝ) else 0)
            - Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) k
              * Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) l))) μ := by
      intro Z hZm c
      refine MeasureTheory.Integrable.of_bound ?_
        (∑ k : Fin N, ∑ l : Fin N, |c k l| * (|beta| * 2)) ?_
      · apply Measurable.aestronglyMeasurable
        refine Finset.measurable_sum Finset.univ (fun k _ =>
          Finset.measurable_sum Finset.univ (fun l _ => ?_))
        exact measurable_const.mul (measurable_const.mul
          ((((hsmw_meas k).comp hZm).mul measurable_const).sub
            (((hsmw_meas k).comp hZm).mul ((hsmw_meas l).comp hZm))))
      · filter_upwards with ω
        obtain ⟨hpn, hpsum⟩ := Statlib.StatFoundation.Convergence.softmax_weights_sum_nonneg
          (p := N) (β := beta) (by omega) (Z ω)
        have hp1 : ∀ k : Fin N,
            ‖Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) k‖ ≤ 1 := by
          intro k
          rw [Real.norm_eq_abs, abs_of_nonneg (hpn k)]
          have h := Finset.single_le_sum (s := Finset.univ)
            (f := fun j : Fin N => Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) j)
            (fun j _ => hpn j) (Finset.mem_univ k)
          rwa [hpsum] at h
        have hterm : ∀ k l : Fin N,
            ‖c k l * (beta * (Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) k
                * (if k = l then (1 : ℝ) else 0)
              - Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) k
                * Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) l))‖
              ≤ |c k l| * (|beta| * 2) := by
          intro k l
          have hk1 : |Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) k| ≤ 1 := by
            simpa [Real.norm_eq_abs] using hp1 k
          have hl1 : |Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) l| ≤ 1 := by
            simpa [Real.norm_eq_abs] using hp1 l
          have h1 : |Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) k
              * (if k = l then (1 : ℝ) else 0)| ≤ 1 := by
            rw [abs_mul]
            by_cases hkl : k = l
            · rw [if_pos hkl, abs_one, mul_one]
              exact hk1
            · rw [if_neg hkl, abs_zero, mul_zero]
              norm_num
          have h2 : |Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) k
              * Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) l| ≤ 1 := by
            rw [abs_mul]
            calc |Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) k|
                  * |Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) l|
                ≤ 1 * 1 := mul_le_mul hk1 hl1 (abs_nonneg _) (by norm_num)
              _ = 1 := by norm_num
          have h3 : |Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) k
              * (if k = l then (1 : ℝ) else 0)
              - Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) k
                * Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) l| ≤ 2 := by
            have h := abs_add_le
              (Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) k
                * (if k = l then (1 : ℝ) else 0))
              (-(Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) k
                * Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) l))
            rw [abs_neg] at h
            calc |Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) k
                  * (if k = l then (1 : ℝ) else 0)
                  - Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) k
                    * Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) l|
                = |Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) k
                    * (if k = l then (1 : ℝ) else 0)
                    + -(Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) k
                      * Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) l)| := by
                  rw [sub_eq_add_neg]
              _ ≤ |Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) k
                    * (if k = l then (1 : ℝ) else 0)|
                  + |Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) k
                    * Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) l| := h
              _ ≤ 1 + 1 := add_le_add h1 h2
              _ = 2 := by norm_num
          rw [norm_mul, norm_mul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h3 (abs_nonneg _)) (abs_nonneg _)
        calc ‖∑ k : Fin N, ∑ l : Fin N,
              c k l * (beta * (Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) k
                * (if k = l then (1 : ℝ) else 0)
              - Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) k
                * Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) l))‖
            = |∑ k : Fin N, ∑ l : Fin N,
                c k l * (beta * (Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) k
                  * (if k = l then (1 : ℝ) else 0)
                - Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) k
                  * Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) l))| :=
              Real.norm_eq_abs _
          _ ≤ ∑ k : Fin N, |∑ l : Fin N,
                c k l * (beta * (Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) k
                  * (if k = l then (1 : ℝ) else 0)
                - Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) k
                  * Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) l))| :=
              Finset.abs_sum_le_sum_abs (fun k : Fin N => ∑ l : Fin N,
                c k l * (beta * (Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) k
                  * (if k = l then (1 : ℝ) else 0)
                - Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) k
                  * Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) l))) Finset.univ
          _ ≤ ∑ k : Fin N, ∑ l : Fin N, |c k l| * (|beta| * 2) := by
              refine Finset.sum_le_sum fun k _ => ?_
              exact (Finset.abs_sum_le_sum_abs (fun l : Fin N =>
                c k l * (beta * (Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) k
                  * (if k = l then (1 : ℝ) else 0)
                - Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) k
                  * Statlib.StatFoundation.Convergence.softmaxWeight beta (Z ω) l)))
                Finset.univ).trans (Finset.sum_le_sum fun l _ => by
                  simpa only [Real.norm_eq_abs] using hterm k l)
    have hfac_gen : ∀ (D f : Fin N → Fin N → ℝ),
        (∑ k : Fin N, ∑ l : Fin N, D k l * (beta * f k l))
          = beta * ∑ k : Fin N, ∑ l : Fin N, D k l * f k l := by
      intro D f
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    have hgen : ∀ (z : EuclideanSpace ℝ (Fin N)) (A B : Fin N → Fin N → ℝ),
        (∀ k : Fin N, 0 ≤ Statlib.StatFoundation.Convergence.softmaxWeight beta z k) →
        (∑ k : Fin N, Statlib.StatFoundation.Convergence.softmaxWeight beta z k = 1) →
        (∀ k l : Fin N, 0 ≤ (A k k - B k k) + (A l l - B l l) - 2 * (A k l - B k l)) →
        0 ≤ ∑ k : Fin N, ∑ l : Fin N,
          (A k l - B k l) * (beta * (Statlib.StatFoundation.Convergence.softmaxWeight beta z k
            * (if k = l then (1 : ℝ) else 0)
            - Statlib.StatFoundation.Convergence.softmaxWeight beta z k
              * Statlib.StatFoundation.Convergence.softmaxWeight beta z l)) := by
      intro z A B hpn hpsum hAB
      rw [hfac_gen]
      have halg' := halg (fun k => Statlib.StatFoundation.Convergence.softmaxWeight beta z k)
        (fun k l => A k l - B k l) hpsum
      rw [halg']
      refine mul_nonneg hbeta.le (mul_nonneg (by norm_num) ?_)
      exact Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ =>
        mul_nonneg (mul_nonneg (hpn k) (hpn l)) (hAB k l)
    have hconv : ∀ (z : EuclideanSpace ℝ (Fin N)) (A B : Fin N → Fin N → ℝ),
        0 ≤ (∑ k : Fin N, ∑ l : Fin N,
              (A k l - B k l) * (beta * (Statlib.StatFoundation.Convergence.softmaxWeight beta z k
                * (if k = l then (1 : ℝ) else 0)
                - Statlib.StatFoundation.Convergence.softmaxWeight beta z k
                  * Statlib.StatFoundation.Convergence.softmaxWeight beta z l))) →
        (∑ k : Fin N, ∑ l : Fin N,
            B k l * (beta * (Statlib.StatFoundation.Convergence.softmaxWeight beta z k
              * (if k = l then (1 : ℝ) else 0)
              - Statlib.StatFoundation.Convergence.softmaxWeight beta z k
                * Statlib.StatFoundation.Convergence.softmaxWeight beta z l)))
          ≤ ∑ k : Fin N, ∑ l : Fin N,
              A k l * (beta * (Statlib.StatFoundation.Convergence.softmaxWeight beta z k
                * (if k = l then (1 : ℝ) else 0)
                - Statlib.StatFoundation.Convergence.softmaxWeight beta z k
                  * Statlib.StatFoundation.Convergence.softmaxWeight beta z l)) := by
      intro z A B h
      have hd : (∑ k : Fin N, ∑ l : Fin N,
              A k l * (beta * (Statlib.StatFoundation.Convergence.softmaxWeight beta z k
                * (if k = l then (1 : ℝ) else 0)
                - Statlib.StatFoundation.Convergence.softmaxWeight beta z k
                  * Statlib.StatFoundation.Convergence.softmaxWeight beta z l)))
            - (∑ k : Fin N, ∑ l : Fin N,
              B k l * (beta * (Statlib.StatFoundation.Convergence.softmaxWeight beta z k
                * (if k = l then (1 : ℝ) else 0)
                - Statlib.StatFoundation.Convergence.softmaxWeight beta z k
                  * Statlib.StatFoundation.Convergence.softmaxWeight beta z l)))
          = ∑ k : Fin N, ∑ l : Fin N,
              (A k l - B k l) * (beta * (Statlib.StatFoundation.Convergence.softmaxWeight beta z k
                * (if k = l then (1 : ℝ) else 0)
                - Statlib.StatFoundation.Convergence.softmaxWeight beta z k
                  * Statlib.StatFoundation.Convergence.softmaxWeight beta z l)) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun l _ => by ring
      rw [← sub_nonneg]
      rw [hd]
      exact h
    have hcancel : ∀ (s A : ℝ), 0 < s → (1 / (2 * s)) * (s * A) = (1 / 2) * A := by
      intro s A hs
      have h1 : (1 / (2 * s)) * s = 1 / 2 := by field_simp
      rw [← mul_assoc, h1]
    rw [hsplit, hIY, hIX, hcancel (Real.sqrt t) _ (Real.sqrt_pos.mpr ht0),
      hcancel (Real.sqrt (1 - t)) _ (Real.sqrt_pos.mpr (by linarith only [ht1]))]
    rw [sub_nonneg]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine MeasureTheory.integral_mono_ae
      (hint_gen (fun ω => WithLp.toLp 2 (fun j : Fin N =>
          Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) (hZ_meas t)
        (fun k l => ∫ ω', X ω' k * X ω' l ∂μ))
      (hint_gen (fun ω => WithLp.toLp 2 (fun j : Fin N =>
          Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) (hZ_meas t)
        (fun k l => ∫ ω', Y ω' k * Y ω' l ∂μ)) ?_
    filter_upwards with ω
    obtain ⟨hpn, hpsum⟩ := Statlib.StatFoundation.Convergence.softmax_weights_sum_nonneg
      (p := N) (β := beta) (by omega)
      (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j))
    exact hconv (WithLp.toLp 2 (fun j : Fin N =>
          Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j))
      (fun k l => ∫ ω', Y ω' k * Y ω' l ∂μ)
      (fun k l => ∫ ω', X ω' k * X ω' l ∂μ)
      (hgen (WithLp.toLp 2 (fun j : Fin N =>
            Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j))
        (fun k l => ∫ ω', Y ω' k * Y ω' l ∂μ)
        (fun k l => ∫ ω', X ω' k * X ω' l ∂μ)
        hpn hpsum (fun k l => by linarith only [hincr k l]))
  refine ⟨hcont, fun t ht => (hderiv t ht).differentiableAt, fun t ht => ?_⟩
  rw [HasDerivAt.deriv (hderiv t ht)]
  exact hnonneg t ht
  /- @proof-region region.target-node.session.f55b01846bc57219 end -/

end Statlib.Imported

