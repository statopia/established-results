import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_3956b9469d6105db3a38

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
theorem statopia_math_node_1558287015_ebcf50db : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (hN : 1 ≤ N) (X Y : Ω → Fin N → ℝ)
    (hX_meas : ∀ k : Fin N, Measurable fun ω => X ω k)
    (hY_meas : ∀ k : Fin N, Measurable fun ω => Y ω k)
    (hX_gauss : ∀ a : Fin N → ℝ, ∃ v : NNReal,
      Measure.map (fun ω => ∑ k : Fin N, a k * X ω k) μ = gaussianReal 0 v)
    (hY_gauss : ∀ a : Fin N → ℝ, ∃ v : NNReal,
      Measure.map (fun ω => ∑ k : Fin N, a k * Y ω k) μ = gaussianReal 0 v)
    (hIndep : IndepFun X Y μ)
    (β : ℝ) (hβ : 0 < β) (t : ℝ) (ht_pos : 0 < t) (ht_lt_one : t < 1),
    (∫ ω, (∑ k : Fin N,
          Statlib.StatFoundation.Convergence.softmaxWeight β
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
            * Y ω k) ∂μ
        = Real.sqrt t * ∫ ω, (∑ k : Fin N, ∑ l : Fin N,
            (∫ ω', Y ω' k * Y ω' l ∂μ)
              * (β * (Statlib.StatFoundation.Convergence.softmaxWeight β
                        (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
                      * (if k = l then (1 : ℝ) else 0)
                    - Statlib.StatFoundation.Convergence.softmaxWeight β
                        (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
                      * Statlib.StatFoundation.Convergence.softmaxWeight β
                        (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) l))) ∂μ)
      ∧ (∫ ω, (∑ k : Fin N,
          Statlib.StatFoundation.Convergence.softmaxWeight β
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
            * X ω k) ∂μ
        = Real.sqrt (1 - t) * ∫ ω, (∑ k : Fin N, ∑ l : Fin N,
            (∫ ω', X ω' k * X ω' l ∂μ)
              * (β * (Statlib.StatFoundation.Convergence.softmaxWeight β
                        (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
                      * (if k = l then (1 : ℝ) else 0)
                    - Statlib.StatFoundation.Convergence.softmaxWeight β
                        (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
                      * Statlib.StatFoundation.Convergence.softmaxWeight β
                        (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) l))) ∂μ) := by
  /- @proof-region region.target-node.session.a4869d7394f8aa28 begin -/
  intro Ω instΩ μ instμ N hN X Y hX_meas hY_meas hX_gauss hY_gauss hIndep β hβ t ht_pos ht_lt_one
  have hY_coord : ∀ k : Fin N, ∃ v : NNReal, Measure.map (fun ω => Y ω k) μ = gaussianReal 0 v := by
    intro k
    obtain ⟨v, hv⟩ := hY_gauss (fun j => if j = k then (1 : ℝ) else 0)
    refine ⟨v, ?_⟩
    have hfun : (fun ω => ∑ j : Fin N, (if j = k then (1 : ℝ) else 0) * Y ω j) = fun ω => Y ω k := by
      funext ω
      have hsum : (∑ j : Fin N, (if j = k then (1 : ℝ) else 0) * Y ω j)
          = (if k = k then (1 : ℝ) else 0) * Y ω k :=
        Finset.sum_eq_single (s := Finset.univ)
          (f := fun j : Fin N => (if j = k then (1 : ℝ) else 0) * Y ω j) k
          (fun j _ hj => by simp [hj])
          (fun h => absurd (Finset.mem_univ k) h)
      simpa using hsum
    rw [hfun] at hv
    exact hv
  have hX_coord : ∀ k : Fin N, ∃ v : NNReal, Measure.map (fun ω => X ω k) μ = gaussianReal 0 v := by
    intro k
    obtain ⟨v, hv⟩ := hX_gauss (fun j => if j = k then (1 : ℝ) else 0)
    refine ⟨v, ?_⟩
    have hfun : (fun ω => ∑ j : Fin N, (if j = k then (1 : ℝ) else 0) * X ω j) = fun ω => X ω k := by
      funext ω
      have hsum : (∑ j : Fin N, (if j = k then (1 : ℝ) else 0) * X ω j)
          = (if k = k then (1 : ℝ) else 0) * X ω k :=
        Finset.sum_eq_single (s := Finset.univ)
          (f := fun j : Fin N => (if j = k then (1 : ℝ) else 0) * X ω j) k
          (fun j _ hj => by simp [hj])
          (fun h => absurd (Finset.mem_univ k) h)
      simpa using hsum
    rw [hfun] at hv
    exact hv
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  have hproj_cont : ∀ k : Fin N, Continuous fun x : EuclideanSpace ℝ (Fin N) => x.ofLp k := by
    intro k
    fun_prop
  have hproj_cd : ∀ k : Fin N, ContDiff ℝ 1 fun x : EuclideanSpace ℝ (Fin N) => x.ofLp k := by
    intro k
    fun_prop
  have hden_pos : ∀ x : EuclideanSpace ℝ (Fin N), (0 : ℝ) < ∑ j : Fin N, Real.exp (β * x.ofLp j) := by
    intro x
    refine Finset.sum_pos (fun j _ => Real.exp_pos _) ?_
    exact ⟨⟨0, hNpos⟩, Finset.mem_univ _⟩
  have hsw_cont : ∀ k : Fin N, Continuous fun x : EuclideanSpace ℝ (Fin N) =>
      Statlib.StatFoundation.Convergence.softmaxWeight β x k := by
    intro k
    simp only [Statlib.StatFoundation.Convergence.softmaxWeight]
    refine Continuous.div ?_ ?_ (fun x => ne_of_gt (hden_pos x))
    · fun_prop
    · fun_prop
  have hsw_cd : ∀ k : Fin N, ContDiff ℝ 1 fun x : EuclideanSpace ℝ (Fin N) =>
      Statlib.StatFoundation.Convergence.softmaxWeight β x k := by
    intro k
    simp only [Statlib.StatFoundation.Convergence.softmaxWeight]
    refine ContDiff.div ?_ ?_ (fun x => ne_of_gt (hden_pos x))
    · fun_prop
    · fun_prop
  have hsw_meas : ∀ k : Fin N, Measurable fun x : EuclideanSpace ℝ (Fin N) =>
      Statlib.StatFoundation.Convergence.softmaxWeight β x k :=
    fun k => (hsw_cont k).measurable
  have hZ_cont : Continuous fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * p.1 j + Real.sqrt (1 - t) * p.2 j) : EuclideanSpace ℝ (Fin N)) := by
    fun_prop
  have hPhi_meas : ∀ k : Fin N, Measurable fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      Real.sqrt t * Statlib.StatFoundation.Convergence.softmaxWeight β
        (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * p.1 j + Real.sqrt (1 - t) * p.2 j)) k := by
    intro k
    exact (continuous_const.mul ((hsw_cont k).comp hZ_cont)).measurable
  have hZ_cd : ∀ y : Fin N → ℝ, ContDiff ℝ 1 fun x : Fin N → ℝ =>
      (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * x j + Real.sqrt (1 - t) * y j) : EuclideanSpace ℝ (Fin N)) := by
    intro y
    fun_prop
  have hPhi_cd : ∀ (k : Fin N) (y : Fin N → ℝ), ContDiff ℝ 1 fun x : Fin N → ℝ =>
      Real.sqrt t * Statlib.StatFoundation.Convergence.softmaxWeight β
        (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * x j + Real.sqrt (1 - t) * y j)) k := by
    intro k y
    exact contDiff_const.mul ((hsw_cd k).comp (hZ_cd y))
  have hp_bounds : ∀ (x y : Fin N → ℝ) (k : Fin N),
      0 ≤ Statlib.StatFoundation.Convergence.softmaxWeight β
            (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * x j + Real.sqrt (1 - t) * y j)) k
      ∧ Statlib.StatFoundation.Convergence.softmaxWeight β
            (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * x j + Real.sqrt (1 - t) * y j)) k ≤ 1 := by
    intro x y k
    obtain ⟨h1, h2⟩ := Statlib.StatFoundation.Convergence.softmax_weights_sum_nonneg hNpos
      (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * x j + Real.sqrt (1 - t) * y j))
    refine ⟨h1 k, ?_⟩
    have h3 := Finset.single_le_sum (f := fun j : Fin N =>
        Statlib.StatFoundation.Convergence.softmaxWeight β
          (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * x j + Real.sqrt (1 - t) * y j)) j)
      (fun i _ => h1 i) (Finset.mem_univ k)
    rw [h2] at h3
    simpa using h3
  have hPhi_bdd : ∃ C : ℝ, ∀ (x y : Fin N → ℝ) (k : Fin N),
      |Real.sqrt t * Statlib.StatFoundation.Convergence.softmaxWeight β
        (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * x j + Real.sqrt (1 - t) * y j)) k| ≤ C := by
    refine ⟨Real.sqrt t, fun x y k => ?_⟩
    obtain ⟨h1, h2⟩ := hp_bounds x y k
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg t), abs_of_nonneg h1]
    calc Real.sqrt t * Statlib.StatFoundation.Convergence.softmaxWeight β
          (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * x j + Real.sqrt (1 - t) * y j)) k
        ≤ Real.sqrt t * 1 := mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg t)
      _ = Real.sqrt t := by ring


  constructor
  · have hY_memLp : ∀ k : Fin N, MemLp (fun ω => Y ω k) 2 μ := by
      intro k
      obtain ⟨v, hv⟩ := hY_coord k
      have h1 : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 v) :=
        ProbabilityTheory.memLp_id_gaussianReal' 2 (by norm_num)
      have h3 : MemLp ((id : ℝ → ℝ) ∘ fun ω => Y ω k) 2 μ :=
        MeasureTheory.MemLp.comp_of_map (f := fun ω => Y ω k) (by rw [hv]; exact h1)
          (hY_meas k).aemeasurable
      simpa using h3
    have hX_memLp : ∀ k : Fin N, MemLp (fun ω => X ω k) 2 μ := by
      intro k
      obtain ⟨v, hv⟩ := hX_coord k
      have h1 : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 v) :=
        ProbabilityTheory.memLp_id_gaussianReal' 2 (by norm_num)
      have h3 : MemLp ((id : ℝ → ℝ) ∘ fun ω => X ω k) 2 μ :=
        MeasureTheory.MemLp.comp_of_map (f := fun ω => X ω k) (by rw [hv]; exact h1)
          (hX_meas k).aemeasurable
      simpa using h3
    have hY_int : ∀ k : Fin N, Integrable (fun ω => Y ω k) μ := fun k =>
      MeasureTheory.MemLp.integrable (q := 2) (by norm_num) (hY_memLp k)
    have hX_int : ∀ k : Fin N, Integrable (fun ω => X ω k) μ := fun k =>
      MeasureTheory.MemLp.integrable (q := 2) (by norm_num) (hX_memLp k)
    have hpair_meas : Measurable fun ω : Ω => (Y ω, X ω) :=
      (measurable_pi_iff.mpr hY_meas).prod (measurable_pi_iff.mpr hX_meas)
    have hPhi_meas' : ∀ k : Fin N, Measurable fun ω : Ω =>
        Real.sqrt t * Statlib.StatFoundation.Convergence.softmaxWeight β
          (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k :=
      fun k => (hPhi_meas k).comp hpair_meas
    have hPairInt : ∀ (k k' : Fin N), Integrable (fun ω => Y ω k' *
        (Real.sqrt t * Statlib.StatFoundation.Convergence.softmaxWeight β
          (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k)) μ := by
      intro k k'
      have hdom : Integrable (fun ω => Real.sqrt t * ‖Y ω k'‖) μ :=
        (hY_int k').norm.const_mul _
      refine Integrable.mono hdom ((hY_meas k').mul (hPhi_meas' k)).aestronglyMeasurable ?_
      filter_upwards with ω
      have hp := hp_bounds (Y ω) (X ω) k
      have hnorm : ‖Real.sqrt t * Statlib.StatFoundation.Convergence.softmaxWeight β
          (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k‖
          ≤ Real.sqrt t := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg t), abs_of_nonneg hp.1]
        calc Real.sqrt t * Statlib.StatFoundation.Convergence.softmaxWeight β
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
            ≤ Real.sqrt t * 1 := mul_le_mul_of_nonneg_left hp.2 (Real.sqrt_nonneg t)
          _ = Real.sqrt t := by ring
      rw [norm_mul]
      have hgn : ‖Real.sqrt t * ‖Y ω k'‖‖ = Real.sqrt t * ‖Y ω k'‖ := by
        rw [Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg t) (norm_nonneg _))]
      rw [hgn]
      calc ‖Y ω k'‖ * ‖Real.sqrt t * Statlib.StatFoundation.Convergence.softmaxWeight β
            (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k‖
          ≤ ‖Y ω k'‖ * Real.sqrt t := mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
        _ = Real.sqrt t * ‖Y ω k'‖ := by ring

    have hsw_eq_fderiv : ∀ (z : EuclideanSpace ℝ (Fin N)) (k : Fin N),
        (fderiv ℝ (Statlib.StatFoundation.Convergence.smoothMax β) z)
            (WithLp.toLp 2 (fun a : Fin N => if a = k then (1 : ℝ) else 0))
          = Statlib.StatFoundation.Convergence.softmaxWeight β z k := by
      intro z k
      rw [(Statlib.StatFoundation.Convergence.smoothMax_gradient_eq_softmax hNpos hβ z).fderiv]

      have hsum : (∑ a : Fin N, Statlib.StatFoundation.Convergence.softmaxWeight β z a
            * (if a = k then (1 : ℝ) else 0))
          = Statlib.StatFoundation.Convergence.softmaxWeight β z k
            * (if k = k then (1 : ℝ) else 0) :=
        Finset.sum_eq_single (s := Finset.univ)
          (f := fun a : Fin N => Statlib.StatFoundation.Convergence.softmaxWeight β z a
            * (if a = k then (1 : ℝ) else 0)) k
          (fun a _ ha => by simp [ha])
          (fun h => absurd (Finset.mem_univ k) h)
      simpa [PiLp.inner_apply] using hsum


    have hslice : ∀ (k l : Fin N) (x y : Fin N → ℝ),
        deriv (fun s : ℝ => Real.sqrt t * Statlib.StatFoundation.Convergence.softmaxWeight β
            (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Function.update x l s j + Real.sqrt (1 - t) * y j)) k) (x l)
          = t * (β * (Statlib.StatFoundation.Convergence.softmaxWeight β
                (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * x j + Real.sqrt (1 - t) * y j)) k
              * (if k = l then (1 : ℝ) else 0)
              - Statlib.StatFoundation.Convergence.softmaxWeight β
                (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * x j + Real.sqrt (1 - t) * y j)) k
                * Statlib.StatFoundation.Convergence.softmaxWeight β
                (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * x j + Real.sqrt (1 - t) * y j)) l)) := by
      intro k l x y
      have hHess := (Statlib.StatFoundation.Convergence.smoothMax_hessian_bounds N hNpos β hβ
        (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * x j + Real.sqrt (1 - t) * y j)) k l).2.2.1
      have hinner : HasDerivAt (fun s : ℝ => Real.sqrt t * s + Real.sqrt (1 - t) * y l)
          (Real.sqrt t) (x l) := by
        simpa using ((hasDerivAt_id (x l)).const_mul (Real.sqrt t)).const_add
          (Real.sqrt (1 - t) * y l)
      have hcomp := hHess.comp (x l) hinner
      have hfun : (fun s : ℝ => Real.sqrt t * Statlib.StatFoundation.Convergence.softmaxWeight β
            (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Function.update x l s j + Real.sqrt (1 - t) * y j)) k)
          = fun s : ℝ => Real.sqrt t * ((fderiv ℝ (Statlib.StatFoundation.Convergence.smoothMax β)
              (WithLp.toLp 2 (Function.update (fun j : Fin N => Real.sqrt t * x j + Real.sqrt (1 - t) * y j) l
                (Real.sqrt t * s + Real.sqrt (1 - t) * y l))))
              (WithLp.toLp 2 (fun a : Fin N => if a = k then (1 : ℝ) else 0))) := by
        funext s
        have hpt : (fun j : Fin N => Real.sqrt t * Function.update x l s j + Real.sqrt (1 - t) * y j)
            = Function.update (fun j : Fin N => Real.sqrt t * x j + Real.sqrt (1 - t) * y j) l
                (Real.sqrt t * s + Real.sqrt (1 - t) * y l) := by
          funext j
          by_cases hj : j = l
          · subst hj
            simp
          · simp [hj]
        rw [hpt, ← hsw_eq_fderiv]

      have hd : HasDerivAt (fun s : ℝ => Real.sqrt t * ((fderiv ℝ (Statlib.StatFoundation.Convergence.smoothMax β)
            (WithLp.toLp 2 (Function.update (fun j : Fin N => Real.sqrt t * x j + Real.sqrt (1 - t) * y j) l
              (Real.sqrt t * s + Real.sqrt (1 - t) * y l))))
            (WithLp.toLp 2 (fun a : Fin N => if a = k then (1 : ℝ) else 0))))
          (Real.sqrt t * ((β * ((Statlib.StatFoundation.Convergence.softmaxWeight β
                (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * x j + Real.sqrt (1 - t) * y j)) k
              * (if k = l then (1 : ℝ) else 0)
              - Statlib.StatFoundation.Convergence.softmaxWeight β
                (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * x j + Real.sqrt (1 - t) * y j)) k
                * Statlib.StatFoundation.Convergence.softmaxWeight β
                (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * x j + Real.sqrt (1 - t) * y j)) l))) * Real.sqrt t))
          (x l) := by
        simpa [Function.comp] using hcomp.const_mul (Real.sqrt t)
      rw [hfun, hd.deriv]

      have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt (le_of_lt ht_pos)
      have key : ∀ a b : ℝ, a * (b * a) = (a * a) * b := by
        intro a b
        ring
      rw [key, hsq]


    have hp_meas : ∀ k : Fin N, Measurable fun ω : Ω =>
        Statlib.StatFoundation.Convergence.softmaxWeight β
          (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k := by
      intro k
      have h1 : Measurable fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
          Statlib.StatFoundation.Convergence.softmaxWeight β
            (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * p.1 j + Real.sqrt (1 - t) * p.2 j)) k :=
        ((hsw_cont k).comp hZ_cont).measurable
      exact h1.comp hpair_meas
    have hPhi_deriv_int : ∀ k l : Fin N, Integrable (fun ω : Ω => deriv (fun s : ℝ =>
        Real.sqrt t * Statlib.StatFoundation.Convergence.softmaxWeight β
          (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Function.update (Y ω) l s j + Real.sqrt (1 - t) * X ω j)) k) (Y ω l)) μ := by
      intro k l
      have hmeasfun : AEStronglyMeasurable (fun ω : Ω => deriv (fun s : ℝ =>
          Real.sqrt t * Statlib.StatFoundation.Convergence.softmaxWeight β
            (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Function.update (Y ω) l s j + Real.sqrt (1 - t) * X ω j)) k) (Y ω l)) μ := by
        have hfun2 : (fun ω : Ω => deriv (fun s : ℝ =>
            Real.sqrt t * Statlib.StatFoundation.Convergence.softmaxWeight β
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Function.update (Y ω) l s j + Real.sqrt (1 - t) * X ω j)) k) (Y ω l))
            = fun ω : Ω => t * (β * (Statlib.StatFoundation.Convergence.softmaxWeight β
                  (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
                * (if k = l then (1 : ℝ) else 0)
                - Statlib.StatFoundation.Convergence.softmaxWeight β
                  (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
                  * Statlib.StatFoundation.Convergence.softmaxWeight β
                  (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) l)) := by
          funext ω
          exact hslice k l (Y ω) (X ω)
        rw [hfun2]
        exact (measurable_const.mul (measurable_const.mul
          (((hp_meas k).mul measurable_const).sub ((hp_meas k).mul (hp_meas l))))).aestronglyMeasurable
      refine MeasureTheory.Integrable.of_bound hmeasfun (t * (2 * β)) ?_
      filter_upwards with ω
      rw [hslice k l (Y ω) (X ω)]
      have h4 := (Statlib.StatFoundation.Convergence.smoothMax_hessian_bounds N hNpos β hβ
        (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k l).2.2.2
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (le_of_lt ht_pos), ← Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left h4 (le_of_lt ht_pos)
    have hV_int : ∀ k l : Fin N, Integrable (fun ω : Ω =>
        β * (Statlib.StatFoundation.Convergence.softmaxWeight β
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
            * (if k = l then (1 : ℝ) else 0)
            - Statlib.StatFoundation.Convergence.softmaxWeight β
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
              * Statlib.StatFoundation.Convergence.softmaxWeight β
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) l)) μ := by
      intro k l
      have hm : AEStronglyMeasurable (fun ω : Ω =>
          β * (Statlib.StatFoundation.Convergence.softmaxWeight β
                (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
              * (if k = l then (1 : ℝ) else 0)
              - Statlib.StatFoundation.Convergence.softmaxWeight β
                (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
                * Statlib.StatFoundation.Convergence.softmaxWeight β
                (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) l)) μ :=
        (measurable_const.mul
          (((hp_meas k).mul measurable_const).sub ((hp_meas k).mul (hp_meas l)))).aestronglyMeasurable
      refine MeasureTheory.Integrable.of_bound hm (2 * β) ?_
      filter_upwards with ω
      exact (Statlib.StatFoundation.Convergence.smoothMax_hessian_bounds N hNpos β hβ
        (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k l).2.2.2
    have hderivval : ∀ k l : Fin N, (∫ ω : Ω, deriv (fun s : ℝ =>
        Real.sqrt t * Statlib.StatFoundation.Convergence.softmaxWeight β
          (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Function.update (Y ω) l s j + Real.sqrt (1 - t) * X ω j)) k) (Y ω l) ∂μ)
        = t * ∫ ω : Ω, β * (Statlib.StatFoundation.Convergence.softmaxWeight β
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
            * (if k = l then (1 : ℝ) else 0)
            - Statlib.StatFoundation.Convergence.softmaxWeight β
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
              * Statlib.StatFoundation.Convergence.softmaxWeight β
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) l) ∂μ := by
      intro k l
      have hcongr : (fun ω : Ω => deriv (fun s : ℝ =>
          Real.sqrt t * Statlib.StatFoundation.Convergence.softmaxWeight β
            (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Function.update (Y ω) l s j + Real.sqrt (1 - t) * X ω j)) k) (Y ω l))
          = fun ω : Ω => t * (β * (Statlib.StatFoundation.Convergence.softmaxWeight β
                (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
              * (if k = l then (1 : ℝ) else 0)
              - Statlib.StatFoundation.Convergence.softmaxWeight β
                (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
                * Statlib.StatFoundation.Convergence.softmaxWeight β
                (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) l)) := by
        funext ω
        exact hslice k l (Y ω) (X ω)
      rw [hcongr, integral_const_mul_of_integrable (hV_int k l)]
    have hchild : ∀ k : Fin N, ∫ ω : Ω, Y ω k *
        (Real.sqrt t * Statlib.StatFoundation.Convergence.softmaxWeight β
          (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k) ∂μ
        = ∑ l : Fin N, (∫ ω : Ω, Y ω k * Y ω l ∂μ) *
            ∫ ω : Ω, deriv (fun s : ℝ => Real.sqrt t * Statlib.StatFoundation.Convergence.softmaxWeight β
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Function.update (Y ω) l s j + Real.sqrt (1 - t) * X ω j)) k) (Y ω l) ∂μ := by
      intro k
      exact statopia_math_node_2593933868_24c165f4 (μ := μ) (n := N) (hn := hN) (U := Y) (W := X)
        hY_meas hX_meas hY_gauss hIndep.symm
        (fun x y => Real.sqrt t * Statlib.StatFoundation.Convergence.softmaxWeight β
          (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * x j + Real.sqrt (1 - t) * y j)) k)
        (hPhi_meas k)
        (by
          obtain ⟨C, hC⟩ := hPhi_bdd
          exact ⟨C, fun x y => hC x y k⟩)
        (hPhi_cd k)
        (fun k' => hPairInt k k')
        (fun _ l => hPhi_deriv_int k l)
        k
    have hsqrt_sq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt (le_of_lt ht_pos)
    have hsqrt_ne : Real.sqrt t ≠ 0 := by
      intro h
      rw [h, mul_zero] at hsqrt_sq
      exact (ne_of_gt ht_pos) hsqrt_sq.symm
    have hcomm : ∀ (a b c : ℝ), a * a = t → c * b = a⁻¹ * (b * (a * c)) := by
      intro a b c ha
      have ha0 : a ≠ 0 := by
        intro h
        rw [h, mul_zero] at ha
        exact (ne_of_gt ht_pos) ha.symm
      have step : a⁻¹ * (b * (a * c)) = b * c := by
        rw [show b * (a * c) = a * (b * c) from by ring, inv_mul_cancel_left₀ ha0]
      rw [step, mul_comm c b]
    have hkey : ∀ (a c : ℝ), a * a = t → a⁻¹ * (t * c) = a * c := by
      intro a c ha
      have ha0 : a ≠ 0 := by
        intro h
        rw [h, mul_zero] at ha
        exact (ne_of_gt ht_pos) ha.symm
      rw [← ha, mul_assoc, inv_mul_cancel_left₀ ha0]
    let P : Ω → Fin N → ℝ := fun ω k =>
      Statlib.StatFoundation.Convergence.softmaxWeight β
        (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
    let Vf : Ω → Fin N → Fin N → ℝ := fun ω k l =>
      β * (P ω k * (if k = l then (1 : ℝ) else 0) - P ω k * P ω l)
    let Sf : Fin N → Fin N → ℝ := fun k l => ∫ ω' : Ω, Y ω' k * Y ω' l ∂μ
    have hleft : (∫ ω : Ω, ∑ k : Fin N, P ω k * Y ω k ∂μ)
        = Real.sqrt t * (∑ k : Fin N, ∑ l : Fin N, Sf k l * ∫ ω : Ω, Vf ω k l ∂μ) := by
      have hfun0 : (fun ω : Ω => ∑ k : Fin N, P ω k * Y ω k)
          = fun ω : Ω => ∑ k : Fin N, (Real.sqrt t)⁻¹ * (Y ω k * (Real.sqrt t * P ω k)) := by
        funext ω
        refine Finset.sum_congr rfl (fun k _ => ?_)
        exact hcomm (Real.sqrt t) (Y ω k) (P ω k) hsqrt_sq
      have h1 : (∫ ω : Ω, ∑ k : Fin N, P ω k * Y ω k ∂μ)
          = ∫ ω : Ω, ∑ k : Fin N, (Real.sqrt t)⁻¹ * (Y ω k * (Real.sqrt t * P ω k)) ∂μ := by
        rw [hfun0]

      have h2 : (∫ ω : Ω, ∑ k : Fin N, (Real.sqrt t)⁻¹ * (Y ω k * (Real.sqrt t * P ω k)) ∂μ)
          = ∑ k : Fin N, ∫ ω : Ω, (Real.sqrt t)⁻¹ * (Y ω k * (Real.sqrt t * P ω k)) ∂μ :=
        MeasureTheory.integral_finset_sum Finset.univ (fun k _ => (hPairInt k k).const_mul _)
      have h3 : (∑ k : Fin N, ∫ ω : Ω, (Real.sqrt t)⁻¹ * (Y ω k * (Real.sqrt t * P ω k)) ∂μ)
          = (Real.sqrt t)⁻¹ * ∑ k : Fin N, ∫ ω : Ω, Y ω k * (Real.sqrt t * P ω k) ∂μ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        exact integral_const_mul_of_integrable (hPairInt k k)
      have h4 : (∑ k : Fin N, ∫ ω : Ω, Y ω k * (Real.sqrt t * P ω k) ∂μ)
          = ∑ k : Fin N, ∑ l : Fin N, Sf k l * (t * ∫ ω : Ω, Vf ω k l ∂μ) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [hchild k]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [hderivval k l]
      have h5 : (∑ k : Fin N, ∑ l : Fin N, Sf k l * (t * ∫ ω : Ω, Vf ω k l ∂μ))
          = t * ∑ k : Fin N, ∑ l : Fin N, Sf k l * ∫ ω : Ω, Vf ω k l ∂μ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        ring
      have h6 : (Real.sqrt t)⁻¹ * (t * ∑ k : Fin N, ∑ l : Fin N, Sf k l * ∫ ω : Ω, Vf ω k l ∂μ)
          = Real.sqrt t * ∑ k : Fin N, ∑ l : Fin N, Sf k l * ∫ ω : Ω, Vf ω k l ∂μ :=
        hkey (Real.sqrt t) _ hsqrt_sq
      calc (∫ ω : Ω, ∑ k : Fin N, P ω k * Y ω k ∂μ)
          = ∫ ω : Ω, ∑ k : Fin N, (Real.sqrt t)⁻¹ * (Y ω k * (Real.sqrt t * P ω k)) ∂μ := h1
        _ = ∑ k : Fin N, ∫ ω : Ω, (Real.sqrt t)⁻¹ * (Y ω k * (Real.sqrt t * P ω k)) ∂μ := h2
        _ = (Real.sqrt t)⁻¹ * ∑ k : Fin N, ∫ ω : Ω, Y ω k * (Real.sqrt t * P ω k) ∂μ := h3
        _ = (Real.sqrt t)⁻¹ * ∑ k : Fin N, ∑ l : Fin N, Sf k l * (t * ∫ ω : Ω, Vf ω k l ∂μ) := by
              rw [h4]
        _ = (Real.sqrt t)⁻¹ * (t * ∑ k : Fin N, ∑ l : Fin N, Sf k l * ∫ ω : Ω, Vf ω k l ∂μ) := by
              rw [h5]
        _ = Real.sqrt t * ∑ k : Fin N, ∑ l : Fin N, Sf k l * ∫ ω : Ω, Vf ω k l ∂μ := h6
    have hright : (∫ ω : Ω, ∑ k : Fin N, ∑ l : Fin N, Sf k l * Vf ω k l ∂μ)
        = ∑ k : Fin N, ∑ l : Fin N, Sf k l * ∫ ω : Ω, Vf ω k l ∂μ := by
      rw [MeasureTheory.integral_finset_sum Finset.univ (fun k _ =>
        MeasureTheory.integrable_finset_sum Finset.univ (fun l _ => (hV_int k l).const_mul _))]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [MeasureTheory.integral_finset_sum Finset.univ (fun l _ => (hV_int k l).const_mul _)]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      exact integral_const_mul_of_integrable (hV_int k l)
    rw [hleft, hright]






  · have hX_memLp : ∀ k : Fin N, MemLp (fun ω => X ω k) 2 μ := by
      intro k
      obtain ⟨v, hv⟩ := hX_coord k
      have h1 : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 v) :=
        ProbabilityTheory.memLp_id_gaussianReal' 2 (by norm_num)
      have h3 : MemLp ((id : ℝ → ℝ) ∘ fun ω => X ω k) 2 μ :=
        MeasureTheory.MemLp.comp_of_map (f := fun ω => X ω k) (by rw [hv]; exact h1)
          (hX_meas k).aemeasurable
      simpa using h3
    have hX_int : ∀ k : Fin N, Integrable (fun ω => X ω k) μ := fun k =>
      MeasureTheory.MemLp.integrable (q := 2) (by norm_num) (hX_memLp k)
    have hpair : Measurable fun ω : Ω => (X ω, Y ω) :=
      (measurable_pi_iff.mpr hX_meas).prod (measurable_pi_iff.mpr hY_meas)
    have hw_cont : Continuous fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
        (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * p.1 j + Real.sqrt t * p.2 j) : EuclideanSpace ℝ (Fin N)) := by
      fun_prop
    have hPhi_meas2 : ∀ k : Fin N, Measurable fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
        Real.sqrt (1 - t) * Statlib.StatFoundation.Convergence.softmaxWeight β
          (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * p.1 j + Real.sqrt t * p.2 j)) k := by
      intro k
      exact (continuous_const.mul ((hsw_cont k).comp hw_cont)).measurable
    have hPhi_cd2 : ∀ (k : Fin N) (y : Fin N → ℝ), ContDiff ℝ 1 fun x : Fin N → ℝ =>
        Real.sqrt (1 - t) * Statlib.StatFoundation.Convergence.softmaxWeight β
          (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * x j + Real.sqrt t * y j)) k := by
      intro k y
      have h1 : ContDiff ℝ 1 fun x : Fin N → ℝ =>
          (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * x j + Real.sqrt t * y j) : EuclideanSpace ℝ (Fin N)) := by
        fun_prop
      exact contDiff_const.mul ((hsw_cd k).comp h1)
    have hp_bounds2 : ∀ (x y : Fin N → ℝ) (k : Fin N),
        0 ≤ Statlib.StatFoundation.Convergence.softmaxWeight β
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * x j + Real.sqrt t * y j)) k
        ∧ Statlib.StatFoundation.Convergence.softmaxWeight β
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * x j + Real.sqrt t * y j)) k ≤ 1 := by
      intro x y k
      obtain ⟨h1, h2⟩ := Statlib.StatFoundation.Convergence.softmax_weights_sum_nonneg hNpos
        (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * x j + Real.sqrt t * y j))
      refine ⟨h1 k, ?_⟩
      have h3 := Finset.single_le_sum (f := fun j : Fin N =>
          Statlib.StatFoundation.Convergence.softmaxWeight β
            (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * x j + Real.sqrt t * y j)) j)
        (fun i _ => h1 i) (Finset.mem_univ k)
      rw [h2] at h3
      simpa using h3
    have hPhi_bdd2 : ∃ C : ℝ, ∀ (x y : Fin N → ℝ) (k : Fin N),
        |Real.sqrt (1 - t) * Statlib.StatFoundation.Convergence.softmaxWeight β
          (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * x j + Real.sqrt t * y j)) k| ≤ C := by
      refine ⟨Real.sqrt (1 - t), fun x y k => ?_⟩
      obtain ⟨h1, h2⟩ := hp_bounds2 x y k
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg (1 - t)), abs_of_nonneg h1]
      calc Real.sqrt (1 - t) * Statlib.StatFoundation.Convergence.softmaxWeight β
            (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * x j + Real.sqrt t * y j)) k
          ≤ Real.sqrt (1 - t) * 1 := mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg (1 - t))
        _ = Real.sqrt (1 - t) := by ring
    have hperm : ∀ (x y : Fin N → ℝ),
        (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * x j + Real.sqrt t * y j) : EuclideanSpace ℝ (Fin N))
          = WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * y j + Real.sqrt (1 - t) * x j) := by
      intro x y
      rw [show (fun j : Fin N => Real.sqrt (1 - t) * x j + Real.sqrt t * y j)
          = (fun j : Fin N => Real.sqrt t * y j + Real.sqrt (1 - t) * x j) from by
        funext j
        ring]
    have hpairYX : Measurable fun ω : Ω => (Y ω, X ω) :=
      (measurable_pi_iff.mpr hY_meas).prod (measurable_pi_iff.mpr hX_meas)
    have hp_meas2 : ∀ k : Fin N, Measurable fun ω : Ω =>
        Statlib.StatFoundation.Convergence.softmaxWeight β
          (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k :=
      fun k => (hsw_meas k).comp (hZ_cont.measurable.comp hpairYX)
    have hp_measX : ∀ k : Fin N, Measurable fun ω : Ω =>
        Statlib.StatFoundation.Convergence.softmaxWeight β
          (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * X ω j + Real.sqrt t * Y ω j)) k := by
      intro k
      have hfunX : (fun ω : Ω => Statlib.StatFoundation.Convergence.softmaxWeight β
            (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * X ω j + Real.sqrt t * Y ω j)) k)
          = fun ω : Ω => Statlib.StatFoundation.Convergence.softmaxWeight β
            (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k := by
        funext ω
        rw [hperm (X ω) (Y ω)]
      rw [hfunX]
      exact hp_meas2 k
    have hPhi_meas'2 : ∀ k : Fin N, Measurable fun ω : Ω =>
        Real.sqrt (1 - t) * Statlib.StatFoundation.Convergence.softmaxWeight β
          (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * X ω j + Real.sqrt t * Y ω j)) k := by
      intro k
      have hfunX : (fun ω : Ω => Real.sqrt (1 - t) * Statlib.StatFoundation.Convergence.softmaxWeight β
            (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * X ω j + Real.sqrt t * Y ω j)) k)
          = fun ω : Ω => Real.sqrt (1 - t) * Statlib.StatFoundation.Convergence.softmaxWeight β
            (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k := by
        funext ω
        rw [hperm (X ω) (Y ω)]
      rw [hfunX]
      exact measurable_const.mul (hp_meas2 k)
    have hPairInt2 : ∀ (k k' : Fin N), Integrable (fun ω => X ω k' *
        (Real.sqrt (1 - t) * Statlib.StatFoundation.Convergence.softmaxWeight β
          (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * X ω j + Real.sqrt t * Y ω j)) k)) μ := by
      intro k k'
      have hdom : Integrable (fun ω => Real.sqrt (1 - t) * ‖X ω k'‖) μ :=
        (hX_int k').norm.const_mul _
      refine Integrable.mono hdom ((hX_meas k').mul (hPhi_meas'2 k)).aestronglyMeasurable ?_
      filter_upwards with ω
      have hp := hp_bounds2 (X ω) (Y ω) k
      have hnorm : ‖Real.sqrt (1 - t) * Statlib.StatFoundation.Convergence.softmaxWeight β
          (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * X ω j + Real.sqrt t * Y ω j)) k‖
          ≤ Real.sqrt (1 - t) := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg (1 - t)), abs_of_nonneg hp.1]
        calc Real.sqrt (1 - t) * Statlib.StatFoundation.Convergence.softmaxWeight β
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * X ω j + Real.sqrt t * Y ω j)) k
            ≤ Real.sqrt (1 - t) * 1 := mul_le_mul_of_nonneg_left hp.2 (Real.sqrt_nonneg (1 - t))
          _ = Real.sqrt (1 - t) := by ring
      rw [norm_mul]
      have hgn : ‖Real.sqrt (1 - t) * ‖X ω k'‖‖ = Real.sqrt (1 - t) * ‖X ω k'‖ := by
        rw [Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg (1 - t)) (norm_nonneg _))]
      rw [hgn]
      calc ‖X ω k'‖ * ‖Real.sqrt (1 - t) * Statlib.StatFoundation.Convergence.softmaxWeight β
            (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * X ω j + Real.sqrt t * Y ω j)) k‖
          ≤ ‖X ω k'‖ * Real.sqrt (1 - t) := mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
        _ = Real.sqrt (1 - t) * ‖X ω k'‖ := by ring

    have hsw2 : ∀ (z : EuclideanSpace ℝ (Fin N)) (k : Fin N),
        (fderiv ℝ (Statlib.StatFoundation.Convergence.smoothMax β) z)
            (WithLp.toLp 2 (fun a : Fin N => if a = k then (1 : ℝ) else 0))
          = Statlib.StatFoundation.Convergence.softmaxWeight β z k := by
      intro z k
      rw [(Statlib.StatFoundation.Convergence.smoothMax_gradient_eq_softmax hNpos hβ z).fderiv]
      have hsum : (∑ a : Fin N, Statlib.StatFoundation.Convergence.softmaxWeight β z a
            * (if a = k then (1 : ℝ) else 0))
          = Statlib.StatFoundation.Convergence.softmaxWeight β z k
            * (if k = k then (1 : ℝ) else 0) :=
        Finset.sum_eq_single (s := Finset.univ)
          (f := fun a : Fin N => Statlib.StatFoundation.Convergence.softmaxWeight β z a
            * (if a = k then (1 : ℝ) else 0)) k
          (fun a _ ha => by simp [ha])
          (fun h => absurd (Finset.mem_univ k) h)
      simpa [PiLp.inner_apply] using hsum
    have hslice2 : ∀ (k l : Fin N) (x y : Fin N → ℝ),
        deriv (fun s : ℝ => Real.sqrt (1 - t) * Statlib.StatFoundation.Convergence.softmaxWeight β
            (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * Function.update x l s j + Real.sqrt t * y j)) k) (x l)
          = (1 - t) * (β * (Statlib.StatFoundation.Convergence.softmaxWeight β
                (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * x j + Real.sqrt t * y j)) k
              * (if k = l then (1 : ℝ) else 0)
              - Statlib.StatFoundation.Convergence.softmaxWeight β
                (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * x j + Real.sqrt t * y j)) k
                * Statlib.StatFoundation.Convergence.softmaxWeight β
                (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * x j + Real.sqrt t * y j)) l)) := by
      intro k l x y
      have hHess := (Statlib.StatFoundation.Convergence.smoothMax_hessian_bounds N hNpos β hβ
        (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * x j + Real.sqrt t * y j)) k l).2.2.1
      have hinner : HasDerivAt (fun s : ℝ => Real.sqrt (1 - t) * s + Real.sqrt t * y l)
          (Real.sqrt (1 - t)) (x l) := by
        simpa using ((hasDerivAt_id (x l)).const_mul (Real.sqrt (1 - t))).const_add
          (Real.sqrt t * y l)
      have hcomp := hHess.comp (x l) hinner
      have hfun : (fun s : ℝ => Real.sqrt (1 - t) * Statlib.StatFoundation.Convergence.softmaxWeight β
            (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * Function.update x l s j + Real.sqrt t * y j)) k)
          = fun s : ℝ => Real.sqrt (1 - t) * ((fderiv ℝ (Statlib.StatFoundation.Convergence.smoothMax β)
              (WithLp.toLp 2 (Function.update (fun j : Fin N => Real.sqrt (1 - t) * x j + Real.sqrt t * y j) l
                (Real.sqrt (1 - t) * s + Real.sqrt t * y l))))
              (WithLp.toLp 2 (fun a : Fin N => if a = k then (1 : ℝ) else 0))) := by
        funext s
        have hpt : (fun j : Fin N => Real.sqrt (1 - t) * Function.update x l s j + Real.sqrt t * y j)
            = Function.update (fun j : Fin N => Real.sqrt (1 - t) * x j + Real.sqrt t * y j) l
                (Real.sqrt (1 - t) * s + Real.sqrt t * y l) := by
          funext j
          by_cases hj : j = l
          · subst hj
            simp
          · simp [hj]
        rw [hpt, ← hsw2]
      have hd : HasDerivAt (fun s : ℝ => Real.sqrt (1 - t) * ((fderiv ℝ (Statlib.StatFoundation.Convergence.smoothMax β)
            (WithLp.toLp 2 (Function.update (fun j : Fin N => Real.sqrt (1 - t) * x j + Real.sqrt t * y j) l
              (Real.sqrt (1 - t) * s + Real.sqrt t * y l))))
            (WithLp.toLp 2 (fun a : Fin N => if a = k then (1 : ℝ) else 0))))
          (Real.sqrt (1 - t) * ((β * ((Statlib.StatFoundation.Convergence.softmaxWeight β
                (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * x j + Real.sqrt t * y j)) k
              * (if k = l then (1 : ℝ) else 0)
              - Statlib.StatFoundation.Convergence.softmaxWeight β
                (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * x j + Real.sqrt t * y j)) k
                * Statlib.StatFoundation.Convergence.softmaxWeight β
                (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * x j + Real.sqrt t * y j)) l))) * Real.sqrt (1 - t)))
          (x l) := by
        simpa [Function.comp] using hcomp.const_mul (Real.sqrt (1 - t))
      rw [hfun, hd.deriv]
      have hsq : Real.sqrt (1 - t) * Real.sqrt (1 - t) = 1 - t :=
        Real.mul_self_sqrt (by linarith)
      have key : ∀ a b : ℝ, a * (b * a) = (a * a) * b := by
        intro a b
        ring
      rw [key, hsq]
    have hV_int2 : ∀ k l : Fin N, Integrable (fun ω : Ω =>
        β * (Statlib.StatFoundation.Convergence.softmaxWeight β
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
            * (if k = l then (1 : ℝ) else 0)
            - Statlib.StatFoundation.Convergence.softmaxWeight β
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
              * Statlib.StatFoundation.Convergence.softmaxWeight β
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) l)) μ := by
      intro k l
      have hm : AEStronglyMeasurable (fun ω : Ω =>
          β * (Statlib.StatFoundation.Convergence.softmaxWeight β
                (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
              * (if k = l then (1 : ℝ) else 0)
              - Statlib.StatFoundation.Convergence.softmaxWeight β
                (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
                * Statlib.StatFoundation.Convergence.softmaxWeight β
                (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) l)) μ :=
        (measurable_const.mul
          (((hp_meas2 k).mul measurable_const).sub ((hp_meas2 k).mul (hp_meas2 l)))).aestronglyMeasurable
      refine MeasureTheory.Integrable.of_bound hm (2 * β) ?_
      filter_upwards with ω
      exact (Statlib.StatFoundation.Convergence.smoothMax_hessian_bounds N hNpos β hβ
        (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k l).2.2.2
    have hderivval2 : ∀ k l : Fin N, (∫ ω : Ω, deriv (fun s : ℝ =>
        Real.sqrt (1 - t) * Statlib.StatFoundation.Convergence.softmaxWeight β
          (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * Function.update (X ω) l s j + Real.sqrt t * Y ω j)) k) (X ω l) ∂μ)
        = (1 - t) * ∫ ω : Ω, β * (Statlib.StatFoundation.Convergence.softmaxWeight β
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
            * (if k = l then (1 : ℝ) else 0)
            - Statlib.StatFoundation.Convergence.softmaxWeight β
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
              * Statlib.StatFoundation.Convergence.softmaxWeight β
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) l) ∂μ := by
      intro k l
      have hcongr : (fun ω : Ω => deriv (fun s : ℝ =>
          Real.sqrt (1 - t) * Statlib.StatFoundation.Convergence.softmaxWeight β
            (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * Function.update (X ω) l s j + Real.sqrt t * Y ω j)) k) (X ω l))
          = fun ω : Ω => (1 - t) * (β * (Statlib.StatFoundation.Convergence.softmaxWeight β
                (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
              * (if k = l then (1 : ℝ) else 0)
              - Statlib.StatFoundation.Convergence.softmaxWeight β
                (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
                * Statlib.StatFoundation.Convergence.softmaxWeight β
                (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) l)) := by
        funext ω
        rw [hslice2 k l (X ω) (Y ω), hperm (X ω) (Y ω)]
      rw [hcongr, integral_const_mul_of_integrable (hV_int2 k l)]
    have hPhi_deriv_int2 : ∀ k l : Fin N, Integrable (fun ω : Ω => deriv (fun s : ℝ =>
        Real.sqrt (1 - t) * Statlib.StatFoundation.Convergence.softmaxWeight β
          (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * Function.update (X ω) l s j + Real.sqrt t * Y ω j)) k) (X ω l)) μ := by
      intro k l
      have hmeasfun : AEStronglyMeasurable (fun ω : Ω => deriv (fun s : ℝ =>
          Real.sqrt (1 - t) * Statlib.StatFoundation.Convergence.softmaxWeight β
            (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * Function.update (X ω) l s j + Real.sqrt t * Y ω j)) k) (X ω l)) μ := by
        have hfun2 : (fun ω : Ω => deriv (fun s : ℝ =>
            Real.sqrt (1 - t) * Statlib.StatFoundation.Convergence.softmaxWeight β
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * Function.update (X ω) l s j + Real.sqrt t * Y ω j)) k) (X ω l))
            = fun ω : Ω => (1 - t) * (β * (Statlib.StatFoundation.Convergence.softmaxWeight β
                  (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
                * (if k = l then (1 : ℝ) else 0)
                - Statlib.StatFoundation.Convergence.softmaxWeight β
                  (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
                  * Statlib.StatFoundation.Convergence.softmaxWeight β
                  (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) l)) := by
          funext ω
          rw [hslice2 k l (X ω) (Y ω), hperm (X ω) (Y ω)]
        rw [hfun2]
        exact (measurable_const.mul (measurable_const.mul
          (((hp_meas2 k).mul measurable_const).sub ((hp_meas2 k).mul (hp_meas2 l))))).aestronglyMeasurable
      refine MeasureTheory.Integrable.of_bound hmeasfun ((1 - t) * (2 * β)) ?_
      filter_upwards with ω
      rw [hslice2 k l (X ω) (Y ω), hperm (X ω) (Y ω)]
      have h4 := (Statlib.StatFoundation.Convergence.smoothMax_hessian_bounds N hNpos β hβ
        (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k l).2.2.2
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - t), ← Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left h4 (by linarith : (0 : ℝ) ≤ 1 - t)
    have hchild2 : ∀ k : Fin N, ∫ ω : Ω, X ω k *
        (Real.sqrt (1 - t) * Statlib.StatFoundation.Convergence.softmaxWeight β
          (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * X ω j + Real.sqrt t * Y ω j)) k) ∂μ
        = ∑ l : Fin N, (∫ ω : Ω, X ω k * X ω l ∂μ) *
            ∫ ω : Ω, deriv (fun s : ℝ => Real.sqrt (1 - t) * Statlib.StatFoundation.Convergence.softmaxWeight β
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * Function.update (X ω) l s j + Real.sqrt t * Y ω j)) k) (X ω l) ∂μ := by
      intro k
      exact statopia_math_node_2593933868_24c165f4 (μ := μ) (n := N) (hn := hN) (U := X) (W := Y)
        hX_meas hY_meas hX_gauss hIndep
        (fun x y => Real.sqrt (1 - t) * Statlib.StatFoundation.Convergence.softmaxWeight β
          (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * x j + Real.sqrt t * y j)) k)
        (hPhi_meas2 k)
        (by
          obtain ⟨C, hC⟩ := hPhi_bdd2
          exact ⟨C, fun x y => hC x y k⟩)
        (hPhi_cd2 k)
        (fun k' => hPairInt2 k k')
        (fun _ l => hPhi_deriv_int2 k l)
        k
    have hcomm2 : ∀ (T a b c : ℝ), 0 < T → a * a = T → c * b = a⁻¹ * (b * (a * c)) := by
      intro T a b c hT ha
      have ha0 : a ≠ 0 := by
        intro h
        rw [h, mul_zero] at ha
        exact (ne_of_gt hT) ha.symm
      have step : a⁻¹ * (b * (a * c)) = b * c := by
        rw [show b * (a * c) = a * (b * c) from by ring, inv_mul_cancel_left₀ ha0]
      rw [step, mul_comm c b]
    have hkey2 : ∀ (T a c : ℝ), 0 < T → a * a = T → a⁻¹ * (T * c) = a * c := by
      intro T a c hT ha
      have ha0 : a ≠ 0 := by
        intro h
        rw [h, mul_zero] at ha
        exact (ne_of_gt hT) ha.symm
      rw [← ha, mul_assoc, inv_mul_cancel_left₀ ha0]
    have hsq2 : Real.sqrt (1 - t) * Real.sqrt (1 - t) = 1 - t :=
      Real.mul_self_sqrt (by linarith)
    have hpermw : ∀ (ω : Ω) (k : Fin N),
        Statlib.StatFoundation.Convergence.softmaxWeight β
            (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * X ω j + Real.sqrt t * Y ω j)) k
          = Statlib.StatFoundation.Convergence.softmaxWeight β
            (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k := by
      intro ω k
      rw [hperm (X ω) (Y ω)]
    have hstepA : (∫ ω : Ω, ∑ k : Fin N,
        Statlib.StatFoundation.Convergence.softmaxWeight β
            (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k * X ω k ∂μ)
        = ∫ ω : Ω, ∑ k : Fin N,
          Statlib.StatFoundation.Convergence.softmaxWeight β
            (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * X ω j + Real.sqrt t * Y ω j)) k * X ω k ∂μ := by
      rw [show (fun ω : Ω => ∑ k : Fin N,
            Statlib.StatFoundation.Convergence.softmaxWeight β
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k * X ω k)
          = (fun ω : Ω => ∑ k : Fin N,
            Statlib.StatFoundation.Convergence.softmaxWeight β
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * X ω j + Real.sqrt t * Y ω j)) k * X ω k) from by
        funext ω
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [hpermw ω k]]
    have hleft : (∫ ω : Ω, ∑ k : Fin N,
        Statlib.StatFoundation.Convergence.softmaxWeight β
            (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * X ω j + Real.sqrt t * Y ω j)) k * X ω k ∂μ)
        = Real.sqrt (1 - t) * (∑ k : Fin N, ∑ l : Fin N,
            (∫ ω' : Ω, X ω' k * X ω' l ∂μ) * ∫ ω : Ω, β * (Statlib.StatFoundation.Convergence.softmaxWeight β
                (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
              * (if k = l then (1 : ℝ) else 0)
              - Statlib.StatFoundation.Convergence.softmaxWeight β
                (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
                * Statlib.StatFoundation.Convergence.softmaxWeight β
                (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) l) ∂μ) := by
      have hfun0 : (fun ω : Ω => ∑ k : Fin N,
            Statlib.StatFoundation.Convergence.softmaxWeight β
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * X ω j + Real.sqrt t * Y ω j)) k * X ω k)
          = (fun ω : Ω => ∑ k : Fin N, (Real.sqrt (1 - t))⁻¹ *
              (X ω k * (Real.sqrt (1 - t) * Statlib.StatFoundation.Convergence.softmaxWeight β
                (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * X ω j + Real.sqrt t * Y ω j)) k))) := by
        funext ω
        refine Finset.sum_congr rfl (fun k _ => ?_)
        exact hcomm2 (1 - t) (Real.sqrt (1 - t)) (X ω k)
          (Statlib.StatFoundation.Convergence.softmaxWeight β
            (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * X ω j + Real.sqrt t * Y ω j)) k)
          (by linarith) hsq2
      have h1 : (∫ ω : Ω, ∑ k : Fin N,
            Statlib.StatFoundation.Convergence.softmaxWeight β
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * X ω j + Real.sqrt t * Y ω j)) k * X ω k ∂μ)
          = ∫ ω : Ω, ∑ k : Fin N, (Real.sqrt (1 - t))⁻¹ *
              (X ω k * (Real.sqrt (1 - t) * Statlib.StatFoundation.Convergence.softmaxWeight β
                (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * X ω j + Real.sqrt t * Y ω j)) k)) ∂μ := by
        rw [hfun0]
      have h2 : (∫ ω : Ω, ∑ k : Fin N, (Real.sqrt (1 - t))⁻¹ *
              (X ω k * (Real.sqrt (1 - t) * Statlib.StatFoundation.Convergence.softmaxWeight β
                (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * X ω j + Real.sqrt t * Y ω j)) k)) ∂μ)
          = ∑ k : Fin N, ∫ ω : Ω, (Real.sqrt (1 - t))⁻¹ *
              (X ω k * (Real.sqrt (1 - t) * Statlib.StatFoundation.Convergence.softmaxWeight β
                (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * X ω j + Real.sqrt t * Y ω j)) k)) ∂μ :=
        MeasureTheory.integral_finset_sum Finset.univ (fun k _ => (hPairInt2 k k).const_mul _)
      have h3 : (∑ k : Fin N, ∫ ω : Ω, (Real.sqrt (1 - t))⁻¹ *
              (X ω k * (Real.sqrt (1 - t) * Statlib.StatFoundation.Convergence.softmaxWeight β
                (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * X ω j + Real.sqrt t * Y ω j)) k)) ∂μ)
          = (Real.sqrt (1 - t))⁻¹ * ∑ k : Fin N, ∫ ω : Ω, X ω k *
              (Real.sqrt (1 - t) * Statlib.StatFoundation.Convergence.softmaxWeight β
                (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * X ω j + Real.sqrt t * Y ω j)) k) ∂μ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        exact integral_const_mul_of_integrable (hPairInt2 k k)
      have h4 : (∑ k : Fin N, ∫ ω : Ω, X ω k *
              (Real.sqrt (1 - t) * Statlib.StatFoundation.Convergence.softmaxWeight β
                (WithLp.toLp 2 (fun j : Fin N => Real.sqrt (1 - t) * X ω j + Real.sqrt t * Y ω j)) k) ∂μ)
          = ∑ k : Fin N, ∑ l : Fin N, (∫ ω' : Ω, X ω' k * X ω' l ∂μ) *
              ((1 - t) * ∫ ω : Ω, β * (Statlib.StatFoundation.Convergence.softmaxWeight β
                  (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
                * (if k = l then (1 : ℝ) else 0)
                - Statlib.StatFoundation.Convergence.softmaxWeight β
                  (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
                  * Statlib.StatFoundation.Convergence.softmaxWeight β
                  (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) l) ∂μ) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [hchild2 k]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [hderivval2 k l]
      have h5 : (∑ k : Fin N, ∑ l : Fin N, (∫ ω' : Ω, X ω' k * X ω' l ∂μ) *
              ((1 - t) * ∫ ω : Ω, β * (Statlib.StatFoundation.Convergence.softmaxWeight β
                  (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
                * (if k = l then (1 : ℝ) else 0)
                - Statlib.StatFoundation.Convergence.softmaxWeight β
                  (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
                  * Statlib.StatFoundation.Convergence.softmaxWeight β
                  (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) l) ∂μ))
          = (1 - t) * ∑ k : Fin N, ∑ l : Fin N, (∫ ω' : Ω, X ω' k * X ω' l ∂μ) *
              ∫ ω : Ω, β * (Statlib.StatFoundation.Convergence.softmaxWeight β
                  (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
                * (if k = l then (1 : ℝ) else 0)
                - Statlib.StatFoundation.Convergence.softmaxWeight β
                  (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
                  * Statlib.StatFoundation.Convergence.softmaxWeight β
                  (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) l) ∂μ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        ring
      have h6 : (Real.sqrt (1 - t))⁻¹ * ((1 - t) * ∑ k : Fin N, ∑ l : Fin N, (∫ ω' : Ω, X ω' k * X ω' l ∂μ) *
              ∫ ω : Ω, β * (Statlib.StatFoundation.Convergence.softmaxWeight β
                  (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
                * (if k = l then (1 : ℝ) else 0)
                - Statlib.StatFoundation.Convergence.softmaxWeight β
                  (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
                  * Statlib.StatFoundation.Convergence.softmaxWeight β
                  (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) l) ∂μ)
          = Real.sqrt (1 - t) * ∑ k : Fin N, ∑ l : Fin N, (∫ ω' : Ω, X ω' k * X ω' l ∂μ) *
              ∫ ω : Ω, β * (Statlib.StatFoundation.Convergence.softmaxWeight β
                  (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
                * (if k = l then (1 : ℝ) else 0)
                - Statlib.StatFoundation.Convergence.softmaxWeight β
                  (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
                  * Statlib.StatFoundation.Convergence.softmaxWeight β
                  (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) l) ∂μ :=
        hkey2 (1 - t) (Real.sqrt (1 - t)) _ (by linarith) hsq2
      rw [h1, h2, h3, h4, h5, h6]
    have hright : (∫ ω : Ω, ∑ k : Fin N, ∑ l : Fin N, (∫ ω' : Ω, X ω' k * X ω' l ∂μ) *
        (β * (Statlib.StatFoundation.Convergence.softmaxWeight β
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
            * (if k = l then (1 : ℝ) else 0)
            - Statlib.StatFoundation.Convergence.softmaxWeight β
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
              * Statlib.StatFoundation.Convergence.softmaxWeight β
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) l)) ∂μ)
        = ∑ k : Fin N, ∑ l : Fin N, (∫ ω' : Ω, X ω' k * X ω' l ∂μ) *
            ∫ ω : Ω, β * (Statlib.StatFoundation.Convergence.softmaxWeight β
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
            * (if k = l then (1 : ℝ) else 0)
            - Statlib.StatFoundation.Convergence.softmaxWeight β
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) k
              * Statlib.StatFoundation.Convergence.softmaxWeight β
              (WithLp.toLp 2 (fun j : Fin N => Real.sqrt t * Y ω j + Real.sqrt (1 - t) * X ω j)) l) ∂μ := by
      rw [MeasureTheory.integral_finset_sum Finset.univ (fun k _ =>
        MeasureTheory.integrable_finset_sum Finset.univ (fun l _ => (hV_int2 k l).const_mul _))]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [MeasureTheory.integral_finset_sum Finset.univ (fun l _ => (hV_int2 k l).const_mul _)]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      exact integral_const_mul_of_integrable (hV_int2 k l)
    rw [hstepA, hleft, hright]




  /- @proof-region region.target-node.session.a4869d7394f8aa28 end -/

end Statlib.Imported

