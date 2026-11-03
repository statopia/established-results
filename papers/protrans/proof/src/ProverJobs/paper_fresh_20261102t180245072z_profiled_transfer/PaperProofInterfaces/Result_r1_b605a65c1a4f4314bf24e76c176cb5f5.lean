import Lean
import ProverJobs.job_paper_4a6904a098fa4fcebf3058bbb4e15c0e.ExternalNodes.Node_cf7d724670d04d1cac6f
import ProverJobs.job_paper_4a6904a098fa4fcebf3058bbb4e15c0e.Vocabulary
import ProverJobs.job_paper_4a6904a098fa4fcebf3058bbb4e15c0e.ProvedNodes
import ProverJobs.job_paper_4a6904a098fa4fcebf3058bbb4e15c0e.Base

namespace PaperProofTasks.job_paper_4a6904a098fa4fcebf3058bbb4e15c0e

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
open MeasureTheory ProbabilityTheory

theorem paper_4a6904a098fa4fcebf3058bbb4e15c0e
    (q : ℕ) (hq : 1 ≤ q) (L : ℝ) (hL : 0 < L) (c : ℝ) (hc : 0 < c) :
    ∃ Cx : ℝ, 0 < Cx ∧ ∃ Nx : ℝ, 0 < Nx ∧
      ∀ (p : ℕ), 2 ≤ p →
      ∀ (f : (Fin q → ℝ) → (Fin p → ℝ)), Measurable f →
      ∀ (P : Measure ((Fin q → ℝ) × (Fin p → ℝ))), IsProbabilityMeasure P →
      
      (∀ i : Fin p, Integrable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => z.2 i) P) →
      (∀ j : Fin q, Integrable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => z.1 j) P) →
      (∀ k : Fin p, Integrable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => f z.1 k) P) →
      
      (∀ i : Fin p, ∫ z, z.2 i ∂P = 0) →
      (∀ j : Fin q, ∫ z, z.1 j ∂P = 0) →
      (∀ k : Fin p, ∫ z, f z.1 k ∂P = 0) →
      
      (∀ i : Fin p, HasSubgaussianMGF (fun z : (Fin q → ℝ) × (Fin p → ℝ) => z.2 i)
        (Real.toNNReal (L ^ 2)) P) →
      (∀ j : Fin q, HasSubgaussianMGF (fun z : (Fin q → ℝ) × (Fin p → ℝ) => z.1 j)
        (Real.toNNReal (L ^ 2)) P) →
      (∀ k : Fin p, HasSubgaussianMGF (fun z : (Fin q → ℝ) × (Fin p → ℝ) => f z.1 k)
        (Real.toNNReal (L ^ 2)) P) →
      
      (∀ (i : Fin p) (j : Fin q),
        Integrable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => z.2 i * z.1 j) P) →
      (∀ (i : Fin p) (j : Fin q), ∫ z, z.2 i * z.1 j ∂P = 0) →
      
      (∀ (i j : Fin p),
        Integrable (fun z : (Fin q → ℝ) × (Fin p → ℝ) =>
          (f z.1 i + z.2 i) * (f z.1 j + z.2 j)) P) →
      ∀ (N : ℕ), 0 < N → Nx * Real.log (p : ℝ) ≤ (N : ℝ) →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω), IsProbabilityMeasure μ →
      ∀ (rows : Fin N → Ω → (Fin q → ℝ) × (Fin p → ℝ)),
      (∀ l, Measurable (rows l)) → iIndepFun rows μ →
      (∀ l, Measure.map (rows l) μ = P) →
      μ.real {ω | ∀ i j : Fin p,
          |empSigma f rows ω i j - SigmaX f P i j|
            ≤ Cx * Real.sqrt (Real.log (p : ℝ) / (N : ℝ))}
        ≥ 1 - Real.rpow (p : ℝ) (-c) / 20
:= by
  /- @proof-region region.root.09b616a26d72 begin -/
  obtain ⟨V, hVpos, hVb⟩ := statopia_math_node_1884859470_ed2c3864 L hL
  obtain ⟨Cx, Nx, hCx, hNx, hunion⟩ :=
    _root_.PaperProofTasks.job_paper_8ff73b3c73e04139840b7ba5205a04c8.Statlib.Imported.paper_8ff73b3c73e04139840b7ba5205a04c8
      c V q hc hVpos (by omega)
  refine ⟨Cx, hCx, Nx, hNx, ?_⟩
  intro p hp f hf P hP hEi hHj hfk hE0 hH0 hf0 hEmgf hHmgf hfmgf hEH hEH0 hXint
  intro N hN hNlog Ω inst μ hμ rows hrows hindep hmap
  haveI : IsProbabilityMeasure μ := hμ
  let e : Fin (p * p) ≃ Fin p × Fin p := finProdFinEquiv.symm
  let gg : Fin (p * p) → ((Fin q → ℝ) × (Fin p → ℝ)) → ℝ := fun k z =>
    (f z.1 (e k).1 + z.2 (e k).1) * (f z.1 (e k).2 + z.2 (e k).2) - SigmaX f P (e k).1 (e k).2
  let U : Fin (p * p) → Fin N → Ω → ℝ := fun k l ω => gg k (rows l ω)
  have hggm : ∀ k, Measurable (gg k) := by
    intro k
    have h1 : Measurable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => f z.1 (e k).1) :=
      (measurable_pi_apply (e k).1).comp (hf.comp measurable_fst)
    have h2 : Measurable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => z.2 (e k).1) :=
      (measurable_pi_apply (e k).1).comp measurable_snd
    have h3 : Measurable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => f z.1 (e k).2) :=
      (measurable_pi_apply (e k).2).comp (hf.comp measurable_fst)
    have h4 : Measurable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => z.2 (e k).2) :=
      (measurable_pi_apply (e k).2).comp measurable_snd
    exact ((h1.add h2).mul (h3.add h4)).sub measurable_const
  have hUm : ∀ (k : Fin (p * p)) (l : Fin N), Measurable (U k l) := by
    intro k l
    exact (hggm k).comp (hrows l)
  have hkey : ∀ (k : Fin (p * p)) (ω : Ω),
      empSigma f rows ω (e k).1 (e k).2 - SigmaX f P (e k).1 (e k).2
        = (N : ℝ)⁻¹ * ∑ l : Fin N, U k l ω := by
    intro k ω
    have hN0 : (N : ℝ) ≠ 0 := by
      have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      exact ne_of_gt hNr
    have e1 : empSigma f rows ω (e k).1 (e k).2
        = (N : ℝ)⁻¹ * ∑ l : Fin N,
          (f ((rows l ω).1) (e k).1 + (rows l ω).2 (e k).1) *
            (f ((rows l ω).1) (e k).2 + (rows l ω).2 (e k).2) := rfl
    have e2 : (∑ l : Fin N, U k l ω)
        = ∑ l : Fin N,
          ((f ((rows l ω).1) (e k).1 + (rows l ω).2 (e k).1) *
              (f ((rows l ω).1) (e k).2 + (rows l ω).2 (e k).2)
            - SigmaX f P (e k).1 (e k).2) :=
      Finset.sum_congr rfl (fun l _ => rfl)
    rw [e1, e2, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hN0, one_mul]
  have hUi : ∀ k : Fin (p * p), iIndepFun (fun l => U k l) μ := by
    intro k
    exact ProbabilityTheory.iIndepFun.comp hindep (fun _ => gg k) (fun _ => hggm k)
  have hUint : ∀ (k : Fin (p * p)) (l : Fin N), Integrable (U k l) μ := by
    intro k l
    have hPint : Integrable (gg k) P := (hXint (e k).1 (e k).2).sub (integrable_const _)
    have hiff := MeasureTheory.integrable_map_measure (μ := μ) (f := rows l) (g := gg k)
      (hggm k).aestronglyMeasurable (hrows l).aemeasurable
    rw [hmap l] at hiff
    exact hiff.mp hPint
  have hU0 : ∀ (k : Fin (p * p)) (l : Fin N), ∫ ω, U k l ω ∂μ = 0 := by
    intro k l
    have hsm : StronglyMeasurable (gg k) := (hggm k).stronglyMeasurable
    have htrans : ∫ ω, U k l ω ∂μ = ∫ z, gg k z ∂P := by
      have h := MeasureTheory.integral_map_of_stronglyMeasurable (μ := μ) (φ := rows l)
        (hrows l) hsm
      rw [hmap l] at h
      exact h.symm
    rw [htrans]
    have hP1 : P.real Set.univ = 1 := by
      rw [measureReal_def, measure_univ, ENNReal.toReal_one]
    have hint : ∫ z, gg k z ∂P
        = (∫ z, (f z.1 (e k).1 + z.2 (e k).1) * (f z.1 (e k).2 + z.2 (e k).2) ∂P)
          - SigmaX f P (e k).1 (e k).2 := by
      rw [show gg k = (fun z : (Fin q → ℝ) × (Fin p → ℝ) =>
          (f z.1 (e k).1 + z.2 (e k).1) * (f z.1 (e k).2 + z.2 (e k).2)
            - SigmaX f P (e k).1 (e k).2) from rfl]
      rw [integral_sub (hXint (e k).1 (e k).2) (integrable_const _), integral_const, hP1,
        one_smul]
    rw [hint]
    have hdef : SigmaX f P (e k).1 (e k).2
        = ∫ z, (f z.1 (e k).1 + z.2 (e k).1) * (f z.1 (e k).2 + z.2 (e k).2) ∂P := rfl
    rw [hdef, sub_self]
  have hUmom : ∀ (k : Fin (p * p)) (l : Fin N) (r : ℕ), 2 ≤ r →
      ∫⁻ ω, ENNReal.ofReal (|U k l ω| ^ r) ∂μ
        ≤ ENNReal.ofReal (↑(r.factorial) * V ^ r) := by
    intro k l r hr
    have hp1 : 1 ≤ p := by omega
    have hmom : ∫ ω, |U k l ω| ^ r ∂μ ≤ (r.factorial : ℝ) * V ^ r :=
      hVb q hq p hp1 f hf P hP hEi hHj hfk hE0 hH0 hf0 hEmgf hHmgf hfmgf hXint N hN
        Ω μ hμ rows hrows hmap l (e k).1 (e k).2 r hr
    have hint : Integrable (fun ω => |U k l ω| ^ r) μ := by
      haveI hP' : IsProbabilityMeasure P := hP
      have hMXi : MemLp (fun z : (Fin q → ℝ) × (Fin p → ℝ) =>
          f z.1 (e k).1 + z.2 (e k).1) ((2 * r : ℕ) : ENNReal) P := by
        simpa using (((hfmgf (e k).1).memLp ((2 * r : ℕ) : NNReal)).add
          ((hEmgf (e k).1).memLp ((2 * r : ℕ) : NNReal)))
      have hMXj : MemLp (fun z : (Fin q → ℝ) × (Fin p → ℝ) =>
          f z.1 (e k).2 + z.2 (e k).2) ((2 * r : ℕ) : ENNReal) P := by
        simpa using (((hfmgf (e k).2).memLp ((2 * r : ℕ) : NNReal)).add
          ((hEmgf (e k).2).memLp ((2 * r : ℕ) : NNReal)))
      have hIi : Integrable (fun z : (Fin q → ℝ) × (Fin p → ℝ) =>
          |f z.1 (e k).1 + z.2 (e k).1| ^ (2 * r)) P :=
        hMXi.integrable_norm_pow (by omega)
      have hIj : Integrable (fun z : (Fin q → ℝ) × (Fin p → ℝ) =>
          |f z.1 (e k).2 + z.2 (e k).2| ^ (2 * r)) P :=
        hMXj.integrable_norm_pow (by omega)
      have hDint : Integrable (fun z : (Fin q → ℝ) × (Fin p → ℝ) =>
          (2 : ℝ) ^ r * ((|f z.1 (e k).1 + z.2 (e k).1| ^ (2 * r) +
            |f z.1 (e k).2 + z.2 (e k).2| ^ (2 * r)) +
              |SigmaX f P (e k).1 (e k).2| ^ r)) P :=
        ((hIi.add hIj).add (integrable_const (|SigmaX f P (e k).1 (e k).2| ^ r))).const_mul _
      have hpowsum : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → (u + v) ^ r ≤ 2 ^ r * (u ^ r + v ^ r) := by
        intro u v hu hv
        rcases le_total u v with h | h
        · have h2 : u + v ≤ 2 * v := by linarith
          have h3 : (u + v) ^ r ≤ (2 * v) ^ r := by gcongr <;> linarith
          calc (u + v) ^ r ≤ (2 * v) ^ r := h3
            _ = 2 ^ r * v ^ r := by rw [mul_pow]
            _ ≤ 2 ^ r * (u ^ r + v ^ r) := by
                have h4 : v ^ r ≤ u ^ r + v ^ r := le_add_of_nonneg_left (by positivity)
                exact mul_le_mul_of_nonneg_left h4 (by positivity)
        · have h2 : u + v ≤ 2 * u := by linarith
          have h3 : (u + v) ^ r ≤ (2 * u) ^ r := by gcongr <;> linarith
          calc (u + v) ^ r ≤ (2 * u) ^ r := h3
            _ = 2 ^ r * u ^ r := by rw [mul_pow]
            _ ≤ 2 ^ r * (u ^ r + v ^ r) := by
                have h4 : u ^ r ≤ u ^ r + v ^ r := le_add_of_nonneg_right (by positivity)
                exact mul_le_mul_of_nonneg_left h4 (by positivity)
      have hamgm : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a * b ≤ a ^ 2 + b ^ 2 := by
        intro a b ha hb
        nlinarith [sq_nonneg (a - b)]
      have hstep : ∀ z : (Fin q → ℝ) × (Fin p → ℝ), |gg k z| ^ r ≤
          (2 : ℝ) ^ r * ((|f z.1 (e k).1 + z.2 (e k).1| ^ (2 * r) +
            |f z.1 (e k).2 + z.2 (e k).2| ^ (2 * r)) +
              |SigmaX f P (e k).1 (e k).2| ^ r) := by
        intro z
        have h1 : |gg k z| ≤ |f z.1 (e k).1 + z.2 (e k).1| *
            |f z.1 (e k).2 + z.2 (e k).2| + |SigmaX f P (e k).1 (e k).2| := by
          have h := abs_add_le ((f z.1 (e k).1 + z.2 (e k).1) * (f z.1 (e k).2 + z.2 (e k).2))
            (-(SigmaX f P (e k).1 (e k).2))
          rw [abs_neg, abs_mul, ← sub_eq_add_neg] at h
          exact h
        have h2 : |gg k z| ^ r ≤ (|f z.1 (e k).1 + z.2 (e k).1| *
            |f z.1 (e k).2 + z.2 (e k).2| + |SigmaX f P (e k).1 (e k).2|) ^ r := by
          gcongr <;> positivity
        have h3 : (|f z.1 (e k).1 + z.2 (e k).1| * |f z.1 (e k).2 + z.2 (e k).2| +
            |SigmaX f P (e k).1 (e k).2|) ^ r
            ≤ 2 ^ r * ((|f z.1 (e k).1 + z.2 (e k).1| *
              |f z.1 (e k).2 + z.2 (e k).2|) ^ r + |SigmaX f P (e k).1 (e k).2| ^ r) :=
          hpowsum _ _ (by positivity) (by positivity)
        have hmain : (|f z.1 (e k).1 + z.2 (e k).1| *
            |f z.1 (e k).2 + z.2 (e k).2|) ^ r
            ≤ |f z.1 (e k).1 + z.2 (e k).1| ^ (2 * r) +
              |f z.1 (e k).2 + z.2 (e k).2| ^ (2 * r) := by
          calc (|f z.1 (e k).1 + z.2 (e k).1| * |f z.1 (e k).2 + z.2 (e k).2|) ^ r
              = |f z.1 (e k).1 + z.2 (e k).1| ^ r *
                |f z.1 (e k).2 + z.2 (e k).2| ^ r := by rw [mul_pow]
            _ ≤ (|f z.1 (e k).1 + z.2 (e k).1| ^ r) ^ 2 +
                (|f z.1 (e k).2 + z.2 (e k).2| ^ r) ^ 2 :=
                hamgm _ _ (by positivity) (by positivity)
            _ = |f z.1 (e k).1 + z.2 (e k).1| ^ (2 * r) +
                |f z.1 (e k).2 + z.2 (e k).2| ^ (2 * r) := by
                rw [← pow_mul, ← pow_mul, Nat.mul_comm r 2]
        refine le_trans h2 (le_trans h3 ?_)
        exact mul_le_mul_of_nonneg_left (by linarith [hmain]) (by positivity)
      have hPint : Integrable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => |gg k z| ^ r) P :=
        MeasureTheory.Integrable.mono' hDint (((hggm k).abs.pow_const r).aestronglyMeasurable)
          (Filter.Eventually.of_forall fun z => by
            simpa only [Real.norm_eq_abs,
              abs_of_nonneg (pow_nonneg (abs_nonneg (gg k z)) r)] using hstep z)
      have hiff := MeasureTheory.integrable_map_measure (μ := μ) (f := rows l)
        (g := fun z : (Fin q → ℝ) × (Fin p → ℝ) => |gg k z| ^ r)
        (((hggm k).abs.pow_const r).aestronglyMeasurable) (hrows l).aemeasurable
      rw [hmap l] at hiff
      exact hiff.mp hPint
    have hconv : ENNReal.ofReal (∫ ω, |U k l ω| ^ r ∂μ)
        = ∫⁻ ω, ENNReal.ofReal (|U k l ω| ^ r) ∂μ :=
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun ω => pow_nonneg (abs_nonneg _) r)
    rw [← hconv]
    exact ENNReal.ofReal_le_ofReal hmom
  have hmle : p * p ≤ p ^ 2 := by rw [pow_two]
  have hbad := hunion p hp N hN hNlog Ω μ (p * p) (Or.inl hmle) U hUm hUi hUint hU0 hUmom
  have hnn : (0 : ℝ) ≤ Real.rpow (↑p) (-c) / 20 :=
    div_nonneg (Real.rpow_nonneg (by positivity) (-c)) (by norm_num)
  have hbadle : μ.real {ω : Ω | ∃ k : Fin (p * p),
      Cx * Real.sqrt (Real.log (↑p) / ↑N) < |(↑N)⁻¹ * ∑ l : Fin N, U k l ω|}
      ≤ Real.rpow (↑p) (-c) / 20 := by
    have hmono := ENNReal.toReal_mono
      (a := μ {ω : Ω | ∃ k : Fin (p * p),
        Cx * Real.sqrt (Real.log (↑p) / ↑N) < |(↑N)⁻¹ * ∑ l : Fin N, U k l ω|})
      (b := ENNReal.ofReal (Real.rpow (↑p) (-c) / 20)) ENNReal.ofReal_ne_top hbad
    have h1 : (ENNReal.ofReal (Real.rpow (↑p) (-c) / 20)).toReal = Real.rpow (↑p) (-c) / 20 :=
      ENNReal.toReal_ofReal hnn
    rw [h1] at hmono
    rw [measureReal_def]
    exact hmono
  have hterm : ∀ (l : Fin N) (i j : Fin p), Measurable (fun ω : Ω =>
      (f (rows l ω).1 i + (rows l ω).2 i) * (f (rows l ω).1 j + (rows l ω).2 j)) := by
    intro l i j
    have h1 : Measurable (fun ω : Ω => f (rows l ω).1 i) :=
      (measurable_pi_apply i).comp (hf.comp (hrows l).fst)
    have h2 : Measurable (fun ω : Ω => (rows l ω).2 i) :=
      (measurable_pi_apply i).comp (hrows l).snd
    have h3 : Measurable (fun ω : Ω => f (rows l ω).1 j) :=
      (measurable_pi_apply j).comp (hf.comp (hrows l).fst)
    have h4 : Measurable (fun ω : Ω => (rows l ω).2 j) :=
      (measurable_pi_apply j).comp (hrows l).snd
    exact (h1.add h2).mul (h3.add h4)
  have hentry : ∀ (i j : Fin p), Measurable (fun ω : Ω =>
      empSigma f rows ω i j - SigmaX f P i j) := by
    intro i j
    have hsum : Measurable (fun ω : Ω => ∑ l : Fin N,
        (f (rows l ω).1 i + (rows l ω).2 i) * (f (rows l ω).1 j + (rows l ω).2 j)) :=
      Finset.measurable_sum _ (fun l _ => hterm l i j)
    exact (hsum.const_mul ((N : ℝ)⁻¹)).sub measurable_const
  have hgoodmeas : MeasurableSet {ω : Ω | ∀ i j : Fin p,
      |empSigma f rows ω i j - SigmaX f P i j| ≤ Cx * Real.sqrt (Real.log (↑p) / ↑N)} := by
    have hset : {ω : Ω | ∀ i j : Fin p,
        |empSigma f rows ω i j - SigmaX f P i j| ≤ Cx * Real.sqrt (Real.log (↑p) / ↑N)}
        = ⋂ i : Fin p, ⋂ j : Fin p,
          {ω : Ω | |empSigma f rows ω i j - SigmaX f P i j|
            ≤ Cx * Real.sqrt (Real.log (↑p) / ↑N)} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [hset]
    exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j =>
      measurableSet_Iic.preimage (hentry i j).abs))
  have hcompeq : {ω : Ω | ∀ i j : Fin p,
      |empSigma f rows ω i j - SigmaX f P i j| ≤ Cx * Real.sqrt (Real.log (↑p) / ↑N)}
      = {ω : Ω | ∃ k : Fin (p * p),
          Cx * Real.sqrt (Real.log (↑p) / ↑N) < |(↑N)⁻¹ * ∑ l : Fin N, U k l ω|}ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
    constructor
    · intro h hk
      obtain ⟨k, hk'⟩ := hk
      have h1 := h (e k).1 (e k).2
      rw [hkey k ω] at h1
      linarith
    · intro h i j
      by_contra hlt
      rw [not_le] at hlt
      refine h ⟨e.symm (i, j), ?_⟩
      have hk0 := hkey (e.symm (i, j)) ω
      rw [Equiv.apply_symm_apply] at hk0
      rw [← hk0]
      exact hlt
  have hbadmeas : MeasurableSet {ω : Ω | ∃ k : Fin (p * p),
      Cx * Real.sqrt (Real.log (↑p) / ↑N) < |(↑N)⁻¹ * ∑ l : Fin N, U k l ω|} := by
    have hb : {ω : Ω | ∃ k : Fin (p * p),
        Cx * Real.sqrt (Real.log (↑p) / ↑N) < |(↑N)⁻¹ * ∑ l : Fin N, U k l ω|}
        = {ω : Ω | ∀ i j : Fin p,
            |empSigma f rows ω i j - SigmaX f P i j|
              ≤ Cx * Real.sqrt (Real.log (↑p) / ↑N)}ᶜ := by
      rw [hcompeq]; simp
    rw [hb]
    exact hgoodmeas.compl
  have huniv : μ.real Set.univ = 1 := by
    rw [measureReal_def, measure_univ, ENNReal.toReal_one]
  calc μ.real {ω : Ω | ∀ i j : Fin p,
        |empSigma f rows ω i j - SigmaX f P i j| ≤ Cx * Real.sqrt (Real.log (↑p) / ↑N)}
      = μ.real {ω : Ω | ∃ k : Fin (p * p),
          Cx * Real.sqrt (Real.log (↑p) / ↑N) < |(↑N)⁻¹ * ∑ l : Fin N, U k l ω|}ᶜ := by
        rw [hcompeq]
    _ = μ.real Set.univ - μ.real {ω : Ω | ∃ k : Fin (p * p),
          Cx * Real.sqrt (Real.log (↑p) / ↑N) < |(↑N)⁻¹ * ∑ l : Fin N, U k l ω|} :=
        measureReal_compl hbadmeas
    _ = 1 - μ.real {ω : Ω | ∃ k : Fin (p * p),
          Cx * Real.sqrt (Real.log (↑p) / ↑N) < |(↑N)⁻¹ * ∑ l : Fin N, U k l ω|} := by
        rw [huniv]
    _ ≥ 1 - Real.rpow (↑p) (-c) / 20 := by linarith
  /- @proof-region region.root.09b616a26d72 end -/

end Statlib.Imported

-- Paper root revision 12662f51-8cf3-456d-a31c-a0603d2387ca

