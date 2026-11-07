import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_227172929_e53d1a52_97cf7d0e

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
theorem statopia_math_node_3642255598_3496c7f2 : ∀ (b : ℝ)
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n m p : ℕ) (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
    (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
    (hn : 0 < n) (hm : 0 < m) (hp : 0 < p)
    (hX : ∀ i : Fin n, Measurable (X i)) (hY : ∀ i : Fin m, Measurable (Y i))
    (hF : ∀ i : Fin n, Measurable (F i)) (hG : ∀ i : Fin m, Measurable (G i))
    (hindep : iIndepFun (β := fun _ => Fin p → ℝ) (Statlib.Imported.jointFam X Y F G) P)
    (hXmean : ∀ (i : Fin n) (j : Fin p), ∫ ω, X i ω j ∂P = muX j)
    (hYmean : ∀ (i : Fin m) (j : Fin p), ∫ ω, Y i ω j ∂P = muY j)
    (hXL2 : ∀ (i : Fin n) (j : Fin p), MemLp (fun ω => X i ω j) 2 P)
    (hYL2 : ∀ (i : Fin m) (j : Fin p), MemLp (fun ω => Y i ω j) 2 P)
    (hFcov : ∀ i : Fin n,
      IsCenteredGaussianVector P (fun ω j => F i ω j - muX j)
        (Statlib.Imported.covX P muX X i))
    (hGcov : ∀ i : Fin m,
      IsCenteredGaussianVector P (fun ω j => G i ω j - muY j)
        (Statlib.Imported.covY P muY Y i))
    (hbvar : ∀ (j : Fin p),
      b ≤ ∫ (ω : Ω),
        Statlib.Imported.combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j ^ 2 ∂P),
    IsCenteredGaussianVector P
      (fun ω j =>
        Statlib.Imported.combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j)
      ((∑ i : Fin n, (n : ℝ)⁻¹ • Statlib.Imported.covX P muX X i) +
        ∑ i : Fin m, ((delta n m) ^ 2 * (m : ℝ)⁻¹) • Statlib.Imported.covY P muY Y i) ∧
    (∀ j : Fin p,
      b ≤ ((∑ i : Fin n, (n : ℝ)⁻¹ • Statlib.Imported.covX P muX X i) +
        ∑ i : Fin m, ((delta n m) ^ 2 * (m : ℝ)⁻¹) • Statlib.Imported.covY P muY Y i) j j) := by
  /- @proof-region region.target-node.session.b6a6f878120850bf begin -/
  intro b Ω _ P _ n m p delta muX muY X Y F G hn hm hp hX hY hF hG hindep hXmean hYmean
    hXL2 hYL2 hFcov hGcov hbvar
  have hBpt : ∀ (ω : Ω) (j : Fin p),
      combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j
        = ∑ i : Fin n, (Real.sqrt (n:ℝ))⁻¹ * (F i ω j - muX j)
          + ∑ i : Fin m, ((delta n m) * (Real.sqrt (m:ℝ))⁻¹) * (G i ω j - muY j) := by
    intro ω j
    have hnpos : (0:ℝ) ≤ (n:ℝ) := by positivity
    have hmpos : (0:ℝ) ≤ (m:ℝ) := by positivity
    have hnne : Real.sqrt (n:ℝ) ≠ 0 := by positivity
    have hmne : Real.sqrt (m:ℝ) ≠ 0 := by positivity
    have hn' : Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ) = (n:ℝ) := by
      rw [← pow_two, Real.sq_sqrt hnpos]
    have hm' : Real.sqrt (m:ℝ) * Real.sqrt (m:ℝ) = (m:ℝ) := by
      rw [← pow_two, Real.sq_sqrt hmpos]
    have hc1 : (Real.sqrt (n:ℝ))⁻¹ * (n:ℝ) = Real.sqrt (n:ℝ) := by
      set a := Real.sqrt (n:ℝ) with ha
      have haa : a * a = (n:ℝ) := by rw [ha]; exact hn'
      have hane : a ≠ 0 := by rw [ha]; exact hnne
      rw [← haa, ← mul_assoc, inv_mul_cancel₀ hane, one_mul]
    have hc2 : (m:ℝ) * (Real.sqrt (m:ℝ))⁻¹ = Real.sqrt (m:ℝ) := by
      set b := Real.sqrt (m:ℝ) with hb
      have hbb : b * b = (m:ℝ) := by rw [hb]; exact hm'
      have hbne : b ≠ 0 := by rw [hb]; exact hmne
      rw [← hbb, mul_assoc, mul_inv_cancel₀ hbne, mul_one]
    have h1 : (∑ i : Fin n, (Real.sqrt (n:ℝ))⁻¹ * (F i ω j - muX j))
        = (Real.sqrt (n:ℝ))⁻¹ * (∑ i : Fin n, F i ω j) - Real.sqrt (n:ℝ) * muX j := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      rw [mul_sub, ← mul_assoc, hc1]
    have h2 : (∑ i : Fin m, ((delta n m) * (Real.sqrt (m:ℝ))⁻¹) * (G i ω j - muY j))
        = (delta n m) * ((Real.sqrt (m:ℝ))⁻¹ * (∑ i : Fin m, G i ω j))
          - delta n m * Real.sqrt (m:ℝ) * muY j := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      rw [mul_sub]
      rw [show ((delta n m) * (Real.sqrt (m:ℝ))⁻¹) * ((m:ℝ) * muY j)
            = (delta n m) * ((m:ℝ) * (Real.sqrt (m:ℝ))⁻¹) * muY j from by ring]
      rw [hc2]
      ring
    simp only [combVec, normSum, h1, h2]
    ring
  have hmeas :
      Measurable (fun ω (j : Fin p) =>
        combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j) := by
    unfold combVec normSum
    measurability
  have hBsum : ∀ (u : Fin p → ℝ) (ω : Ω),
      ∑ j, u j * combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j
        = (∑ i : Fin n, ∑ j, ((Real.sqrt (n:ℝ))⁻¹ * u j) * (F i ω j - muX j))
          + ∑ i : Fin m, ∑ j, (((delta n m) * (Real.sqrt (m:ℝ))⁻¹) * u j) * (G i ω j - muY j) := by
    intro u ω
    have step1 : ∑ j, u j * combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j
        = ∑ j, (u j * (∑ i : Fin n, (Real.sqrt (n:ℝ))⁻¹ * (F i ω j - muX j))
            + u j * ∑ i : Fin m, ((delta n m) * (Real.sqrt (m:ℝ))⁻¹) * (G i ω j - muY j)) := by
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [hBpt ω j, mul_add]
    have step2 : ∑ j, (u j * (∑ i : Fin n, (Real.sqrt (n:ℝ))⁻¹ * (F i ω j - muX j))
            + u j * ∑ i : Fin m, ((delta n m) * (Real.sqrt (m:ℝ))⁻¹) * (G i ω j - muY j))
        = (∑ j, ∑ i : Fin n, u j * ((Real.sqrt (n:ℝ))⁻¹ * (F i ω j - muX j)))
          + ∑ j, ∑ i : Fin m, u j * (((delta n m) * (Real.sqrt (m:ℝ))⁻¹) * (G i ω j - muY j)) := by
      rw [Finset.sum_add_distrib]
      congr 1
      · refine Finset.sum_congr rfl ?_
        intro j _
        rw [Finset.mul_sum]
      · refine Finset.sum_congr rfl ?_
        intro j _
        rw [Finset.mul_sum]
    rw [step1, step2]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      ring

  have hsummeas : ∀ (s : Finset (Fin p)) (c m0 : Fin p → ℝ),
      Measurable (fun v : Fin p → ℝ => ∑ j ∈ s, c j * (v j - m0 j)) := by
    intro s
    induction s using Finset.induction with
    | empty =>
        intro c m0
        simp only [Finset.sum_empty]
        exact measurable_const
    | insert x s hx ih =>
        intro c m0
        have h3 : (fun v : Fin p → ℝ => ∑ j ∈ insert x s, c j * (v j - m0 j))
            = fun v => c x * (v x - m0 x) + ∑ j ∈ s, c j * (v j - m0 j) := by
          funext v
          rw [Finset.sum_insert hx]
        rw [h3]
        have ht : Measurable (fun v : Fin p → ℝ => c x * (v x - m0 x)) := by
          have h1 : Measurable (fun v : Fin p → ℝ => v x - m0 x) :=
            (measurable_pi_apply x).sub
              (measurable_const : Measurable (fun _ : Fin p → ℝ => m0 x))
          have h2 : Measurable (fun _ : Fin p → ℝ => c x) := measurable_const
          exact h2.mul h1
        exact ht.add (ih c m0)
  set Gfun : (Fin p → ℝ) → (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) → (Fin p → ℝ) → ℝ :=
    fun u t v => match t with
      | Sum.inl _ => 0
      | Sum.inr (Sum.inl _) => 0
      | Sum.inr (Sum.inr (Sum.inl i)) => ∑ j, ((Real.sqrt (n:ℝ))⁻¹ * u j) * (v j - muX j)
      | Sum.inr (Sum.inr (Sum.inr i)) =>
          ∑ j, (((delta n m) * (Real.sqrt (m:ℝ))⁻¹) * u j) * (v j - muY j)
    with hGfun
  have hGmeas : ∀ (u : Fin p → ℝ) (t : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))),
      Measurable (Gfun u t) := by
    intro u t
    cases t with
    | inl i =>
        show Measurable (fun _ : Fin p → ℝ => (0:ℝ))
        exact measurable_const
    | inr r =>
        cases r with
        | inl i =>
            show Measurable (fun _ : Fin p → ℝ => (0:ℝ))
            exact measurable_const
        | inr r2 =>
            cases r2 with
            | inl i =>
                show Measurable (fun v : Fin p → ℝ =>
                  ∑ j, ((Real.sqrt (n:ℝ))⁻¹ * u j) * (v j - muX j))
                exact hsummeas Finset.univ (fun j => (Real.sqrt (n:ℝ))⁻¹ * u j) muX
            | inr i =>
                show Measurable (fun v : Fin p → ℝ =>
                  ∑ j, (((delta n m) * (Real.sqrt (m:ℝ))⁻¹) * u j) * (v j - muY j))
                exact hsummeas Finset.univ
                  (fun j => ((delta n m) * (Real.sqrt (m:ℝ))⁻¹) * u j) muY
  have hjfmeas : ∀ t : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)),
      Measurable (jointFam X Y F G t) := by
    intro t
    cases t with
    | inl i => exact hX i
    | inr r =>
        cases r with
        | inl i => exact hY i
        | inr r2 =>
            cases r2 with
            | inl i => exact hF i
            | inr i => exact hG i
  have hXmeas : ∀ (u : Fin p → ℝ) (t : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))),
      Measurable (fun ω : Ω => Gfun u t (jointFam X Y F G t ω)) := by
    intro u t
    exact (hGmeas u t).comp (hjfmeas t)
  have hXfam : ∀ u : Fin p → ℝ,
      iIndepFun (fun t (ω : Ω) => Gfun u t (jointFam X Y F G t ω)) P := by
    intro u
    exact hindep.comp (Gfun u) (fun t => hGmeas u t)
  have hint : ∀ (u : Fin p → ℝ) (t : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))),
      t ∈ (Finset.univ : Finset (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)))) →
      Integrable (fun ω : Ω => Real.exp (1 * Gfun u t (jointFam X Y F G t ω))) P := by
    intro u t _
    cases t with
    | inl i =>
        have hc : (fun ω : Ω => Real.exp (1 * Gfun u (Sum.inl i) (jointFam X Y F G (Sum.inl i) ω)))
            = fun _ => (1:ℝ) := by
          funext ω
          show Real.exp (1 * 0) = 1
          simp
        rw [hc]; exact integrable_const 1
    | inr r =>
        cases r with
        | inl i =>
            have hc : (fun ω : Ω =>
                Real.exp (1 * Gfun u (Sum.inr (Sum.inl i)) (jointFam X Y F G (Sum.inr (Sum.inl i)) ω)))
                = fun _ => (1:ℝ) := by
              funext ω
              show Real.exp (1 * 0) = 1
              simp
            rw [hc]; exact integrable_const 1
        | inr r2 =>
            cases r2 with
            | inl i =>
                have hc : (fun ω : Ω =>
                    Real.exp (1 * Gfun u (Sum.inr (Sum.inr (Sum.inl i)))
                      (jointFam X Y F G (Sum.inr (Sum.inr (Sum.inl i))) ω)))
                    = fun ω => Real.exp (∑ j, ((Real.sqrt (n:ℝ))⁻¹ * u j) * (F i ω j - muX j)) := by
                  funext ω
                  show Real.exp (1 * ∑ j, ((Real.sqrt (n:ℝ))⁻¹ * u j) * (F i ω j - muX j))
                    = Real.exp (∑ j, ((Real.sqrt (n:ℝ))⁻¹ * u j) * (F i ω j - muX j))
                  rw [one_mul]
                rw [hc]
                exact (hFcov i).integrable_exp (fun j => (Real.sqrt (n:ℝ))⁻¹ * u j)
            | inr i =>
                have hc : (fun ω : Ω =>
                    Real.exp (1 * Gfun u (Sum.inr (Sum.inr (Sum.inr i)))
                      (jointFam X Y F G (Sum.inr (Sum.inr (Sum.inr i))) ω)))
                    = fun ω => Real.exp
                        (∑ j, (((delta n m) * (Real.sqrt (m:ℝ))⁻¹) * u j) * (G i ω j - muY j)) := by
                  funext ω
                  show Real.exp
                      (1 * ∑ j, (((delta n m) * (Real.sqrt (m:ℝ))⁻¹) * u j) * (G i ω j - muY j))
                    = Real.exp
                      (∑ j, (((delta n m) * (Real.sqrt (m:ℝ))⁻¹) * u j) * (G i ω j - muY j))
                  rw [one_mul]
                rw [hc]
                exact (hGcov i).integrable_exp (fun j => ((delta n m) * (Real.sqrt (m:ℝ))⁻¹) * u j)
  have hexp_sum : ∀ {ι : Type} (s : Finset ι) (a : ι → ℝ),
      Real.exp (∑ i ∈ s, a i) = ∏ i ∈ s, Real.exp (a i) := by
    intro ι s a
    classical
    induction s using Finset.induction with
    | empty => simp
    | insert x s hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, Real.exp_add, ih]
  have hsum_split : ∀ {α β : Type} [Fintype α] [Fintype β] (f : α ⊕ β → ℝ),
      ∑ t, f t = (∑ i : α, f (Sum.inl i)) + ∑ i : β, f (Sum.inr i) := by
    intro α β _ _ f
    have h1 : Real.exp (∑ t, f t) = ∏ t, Real.exp (f t) := hexp_sum Finset.univ f
    have h3 : (∏ t, Real.exp (f t))
        = (∏ i : α, Real.exp (f (Sum.inl i))) * ∏ i : β, Real.exp (f (Sum.inr i)) :=
      Fintype.prod_sum_type (fun t => Real.exp (f t))
    have h2 : Real.exp ((∑ i : α, f (Sum.inl i)) + ∑ i : β, f (Sum.inr i))
        = (∏ i : α, Real.exp (f (Sum.inl i))) * ∏ i : β, Real.exp (f (Sum.inr i)) := by
      rw [Real.exp_add, hexp_sum Finset.univ (fun i => f (Sum.inl i)),
        hexp_sum Finset.univ (fun i => f (Sum.inr i))]
    exact Real.exp_injective (h1.trans (h3.trans h2.symm))
  have hR : ∀ (u : Fin p → ℝ) (ω : Ω),
      (∑ i, Gfun u i (jointFam X Y F G i ω))
        = (∑ i : Fin n, ∑ j, ((Real.sqrt (n:ℝ))⁻¹ * u j) * (F i ω j - muX j))
          + ∑ i : Fin m, ∑ j, (((delta n m) * (Real.sqrt (m:ℝ))⁻¹) * u j) * (G i ω j - muY j) := by
    intro u ω
    rw [hsum_split, hsum_split, hsum_split]
    simp only [hGfun, jointFam, Finset.sum_const_zero, zero_add]

  refine ⟨?_, ?_⟩
  · constructor
    · exact hmeas
    · intro u
      have hmain := (hXfam u).integrable_exp_mul_sum (hXmeas u) (hint u)
      have hswap : (fun ω : Ω =>
            Real.exp (1 * (∑ i, fun ω' : Ω => Gfun u i (jointFam X Y F G i ω')) ω))
          = fun ω : Ω => Real.exp (1 * ∑ i, Gfun u i (jointFam X Y F G i ω)) := by
        funext ω
        rw [Finset.sum_apply]
      rw [hswap] at hmain
      have hfun : (fun ω : Ω =>
            Real.exp (∑ j, u j * combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j))
          = fun ω : Ω => Real.exp (1 * ∑ i, Gfun u i (jointFam X Y F G i ω)) := by
        funext ω
        rw [hBsum u ω, hR u ω, one_mul]
      rw [hfun]
      exact hmain
    · intro u
      set Sigma : Matrix (Fin p) (Fin p) ℝ :=
        ((∑ i : Fin n, (n : ℝ)⁻¹ • covX P muX X i) +
          ∑ i : Fin m, ((delta n m) ^ 2 * (m : ℝ)⁻¹) • covY P muY Y i) with hSigma
      have hEmeas : ∀ t : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)),
          Measurable (fun ω : Ω => Real.exp (Gfun u t (jointFam X Y F G t ω))) :=
        fun t => Real.measurable_exp.comp (hXmeas u t)
      have hEfam : iIndepFun (fun t (ω : Ω) => Real.exp (Gfun u t (jointFam X Y F G t ω))) P :=
        (hXfam u).comp (fun _ => Real.exp) (fun _ => Real.measurable_exp)
      have hInt : (∫ ω, ∏ t, Real.exp (Gfun u t (jointFam X Y F G t ω)) ∂P)
          = ∏ t, ∫ ω, Real.exp (Gfun u t (jointFam X Y F G t ω)) ∂P :=
        hEfam.integral_fun_prod_eq_prod_integral (fun t => (hEmeas t).aestronglyMeasurable)
      have hfun : (fun ω : Ω =>
            Real.exp (∑ j, u j * combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j))
          = fun ω : Ω => ∏ t, Real.exp (Gfun u t (jointFam X Y F G t ω)) := by
        funext ω
        rw [hBsum u ω, ← hR u ω, hexp_sum]
      have hone1 : ∀ i : Fin n,
          (∫ ω, Real.exp (Gfun u (Sum.inl i) (jointFam X Y F G (Sum.inl i) ω)) ∂P) = 1 := by
        intro i
        show (∫ _ : Ω, Real.exp (0:ℝ) ∂P) = 1
        simp
      have hone2 : ∀ i : Fin m,
          (∫ ω, Real.exp (Gfun u (Sum.inr (Sum.inl i))
            (jointFam X Y F G (Sum.inr (Sum.inl i)) ω)) ∂P) = 1 := by
        intro i
        show (∫ _ : Ω, Real.exp (0:ℝ) ∂P) = 1
        simp
      have hFX : ∀ i : Fin n,
          (∫ ω, Real.exp (Gfun u (Sum.inr (Sum.inr (Sum.inl i)))
              (jointFam X Y F G (Sum.inr (Sum.inr (Sum.inl i))) ω)) ∂P)
            = Real.exp ((∑ a, ∑ b,
                ((Real.sqrt (n:ℝ))⁻¹ * u a) * covX P muX X i a b * ((Real.sqrt (n:ℝ))⁻¹ * u b)) / 2) := by
        intro i
        show (∫ ω, Real.exp (∑ j, ((Real.sqrt (n:ℝ))⁻¹ * u j) * (F i ω j - muX j)) ∂P)
            = Real.exp ((∑ a, ∑ b,
                ((Real.sqrt (n:ℝ))⁻¹ * u a) * covX P muX X i a b * ((Real.sqrt (n:ℝ))⁻¹ * u b)) / 2)
        exact (hFcov i).mgf_eq (fun j => (Real.sqrt (n:ℝ))⁻¹ * u j)
      have hGY : ∀ i : Fin m,
          (∫ ω, Real.exp (Gfun u (Sum.inr (Sum.inr (Sum.inr i)))
              (jointFam X Y F G (Sum.inr (Sum.inr (Sum.inr i))) ω)) ∂P)
            = Real.exp ((∑ a, ∑ b, (((delta n m) * (Real.sqrt (m:ℝ))⁻¹) * u a) * covY P muY Y i a b
                * (((delta n m) * (Real.sqrt (m:ℝ))⁻¹) * u b)) / 2) := by
        intro i
        show (∫ ω, Real.exp (∑ j, (((delta n m) * (Real.sqrt (m:ℝ))⁻¹) * u j) * (G i ω j - muY j)) ∂P)
            = Real.exp ((∑ a, ∑ b, (((delta n m) * (Real.sqrt (m:ℝ))⁻¹) * u a) * covY P muY Y i a b
                * (((delta n m) * (Real.sqrt (m:ℝ))⁻¹) * u b)) / 2)
        exact (hGcov i).mgf_eq (fun j => ((delta n m) * (Real.sqrt (m:ℝ))⁻¹) * u j)
      have hprodval : (∏ t : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)),
            (∫ ω, Real.exp (Gfun u t (jointFam X Y F G t ω)) ∂P))
          = (∏ i : Fin n,
              (∫ ω, Real.exp (Gfun u (Sum.inr (Sum.inr (Sum.inl i)))
                (jointFam X Y F G (Sum.inr (Sum.inr (Sum.inl i))) ω)) ∂P))
            * ∏ i : Fin m,
              (∫ ω, Real.exp (Gfun u (Sum.inr (Sum.inr (Sum.inr i)))
                (jointFam X Y F G (Sum.inr (Sum.inr (Sum.inr i))) ω)) ∂P) := by
        rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type]
        simp [hone1, hone2]
      have hquad : (∑ i : Fin n, (∑ a, ∑ b,
              ((Real.sqrt (n:ℝ))⁻¹ * u a) * covX P muX X i a b * ((Real.sqrt (n:ℝ))⁻¹ * u b)) / 2)
          + (∑ i : Fin m, (∑ a, ∑ b, (((delta n m) * (Real.sqrt (m:ℝ))⁻¹) * u a) * covY P muY Y i a b
              * (((delta n m) * (Real.sqrt (m:ℝ))⁻¹) * u b)) / 2)
          = (∑ a, ∑ b, u a * Sigma a b * u b) / 2 := by
        have hpn : (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ = (n:ℝ)⁻¹ := by
          have hsq : Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ) = (n:ℝ) := by
            rw [← pow_two, Real.sq_sqrt (by positivity : (0:ℝ) ≤ (n:ℝ))]
          have h1 : (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹
              = (Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ))⁻¹ := by
            rw [← mul_inv_rev]
          rw [h1, hsq]
        have hpm : (Real.sqrt (m:ℝ))⁻¹ * (Real.sqrt (m:ℝ))⁻¹ = (m:ℝ)⁻¹ := by
          have hsq : Real.sqrt (m:ℝ) * Real.sqrt (m:ℝ) = (m:ℝ) := by
            rw [← pow_two, Real.sq_sqrt (by positivity : (0:ℝ) ≤ (m:ℝ))]
          have h1 : (Real.sqrt (m:ℝ))⁻¹ * (Real.sqrt (m:ℝ))⁻¹
              = (Real.sqrt (m:ℝ) * Real.sqrt (m:ℝ))⁻¹ := by
            rw [← mul_inv_rev]
          rw [h1, hsq]
        have hsig : ∀ (a b : Fin p), Sigma a b
            = (∑ i : Fin n, (n:ℝ)⁻¹ * covX P muX X i a b)
              + ∑ i : Fin m, ((delta n m)^2 * (m:ℝ)⁻¹) * covY P muY Y i a b := by
          intro a b
          simp only [hSigma, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
        have hX : (∑ a, ∑ b, u a * (∑ i : Fin n, (n:ℝ)⁻¹ * covX P muX X i a b) * u b)
            = ∑ i : Fin n, ∑ a, ∑ b,
                ((Real.sqrt (n:ℝ))⁻¹ * u a) * covX P muX X i a b
                  * ((Real.sqrt (n:ℝ))⁻¹ * u b) := by
          rw [show (∑ a, ∑ b, u a * (∑ i : Fin n, (n:ℝ)⁻¹ * covX P muX X i a b) * u b)
              = ∑ a, ∑ b, ∑ i : Fin n,
                  u a * ((n:ℝ)⁻¹ * covX P muX X i a b) * u b from by
            refine Finset.sum_congr rfl ?_
            intro a _
            refine Finset.sum_congr rfl ?_
            intro b _
            rw [Finset.mul_sum, Finset.sum_mul]]
          rw [show (∑ a, ∑ b, ∑ i : Fin n,
                u a * ((n:ℝ)⁻¹ * covX P muX X i a b) * u b)
              = ∑ a, ∑ i : Fin n, ∑ b,
                  u a * ((n:ℝ)⁻¹ * covX P muX X i a b) * u b from by
            refine Finset.sum_congr rfl ?_
            intro a _
            exact Finset.sum_comm]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro i _
          refine Finset.sum_congr rfl ?_
          intro a _
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [← hpn]
          ring
        have hY : (∑ a, ∑ b,
              u a * (∑ i : Fin m, ((delta n m)^2 * (m:ℝ)⁻¹) * covY P muY Y i a b) * u b)
            = ∑ i : Fin m, ∑ a, ∑ b,
                (((delta n m) * (Real.sqrt (m:ℝ))⁻¹) * u a) * covY P muY Y i a b
                  * (((delta n m) * (Real.sqrt (m:ℝ))⁻¹) * u b) := by
          rw [show (∑ a, ∑ b,
                u a * (∑ i : Fin m, ((delta n m)^2 * (m:ℝ)⁻¹) * covY P muY Y i a b) * u b)
              = ∑ a, ∑ b, ∑ i : Fin m,
                  u a * (((delta n m)^2 * (m:ℝ)⁻¹) * covY P muY Y i a b) * u b from by
            refine Finset.sum_congr rfl ?_
            intro a _
            refine Finset.sum_congr rfl ?_
            intro b _
            rw [Finset.mul_sum, Finset.sum_mul]]
          rw [show (∑ a, ∑ b, ∑ i : Fin m,
                u a * (((delta n m)^2 * (m:ℝ)⁻¹) * covY P muY Y i a b) * u b)
              = ∑ a, ∑ i : Fin m, ∑ b,
                  u a * (((delta n m)^2 * (m:ℝ)⁻¹) * covY P muY Y i a b) * u b from by
            refine Finset.sum_congr rfl ?_
            intro a _
            exact Finset.sum_comm]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro i _
          refine Finset.sum_congr rfl ?_
          intro a _
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [show ((delta n m)^2 * (m:ℝ)⁻¹)
              = ((delta n m) * (Real.sqrt (m:ℝ))⁻¹)
                * ((delta n m) * (Real.sqrt (m:ℝ))⁻¹) from by
            rw [sq, ← hpm]
            ring]
          ring
        have hquad0 : (∑ i : Fin n, ∑ a, ∑ b,
              ((Real.sqrt (n:ℝ))⁻¹ * u a) * covX P muX X i a b * ((Real.sqrt (n:ℝ))⁻¹ * u b))
            + (∑ i : Fin m, ∑ a, ∑ b, (((delta n m) * (Real.sqrt (m:ℝ))⁻¹) * u a) * covY P muY Y i a b
                * (((delta n m) * (Real.sqrt (m:ℝ))⁻¹) * u b))
            = ∑ a, ∑ b, u a * Sigma a b * u b := by
          rw [show (∑ a, ∑ b, u a * Sigma a b * u b)
              = ∑ a, ∑ b, u a * ((∑ i : Fin n, (n:ℝ)⁻¹ * covX P muX X i a b)
                  + ∑ i : Fin m, ((delta n m)^2 * (m:ℝ)⁻¹) * covY P muY Y i a b) * u b from by
            refine Finset.sum_congr rfl ?_
            intro a _
            refine Finset.sum_congr rfl ?_
            intro b _
            rw [hsig a b]]
          rw [show (∑ a, ∑ b, u a * ((∑ i : Fin n, (n:ℝ)⁻¹ * covX P muX X i a b)
                + ∑ i : Fin m, ((delta n m)^2 * (m:ℝ)⁻¹) * covY P muY Y i a b) * u b)
              = (∑ a, ∑ b, u a * (∑ i : Fin n, (n:ℝ)⁻¹ * covX P muX X i a b) * u b)
                + ∑ a, ∑ b,
                    u a * (∑ i : Fin m, ((delta n m)^2 * (m:ℝ)⁻¹) * covY P muY Y i a b) * u b from by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro b _
            rw [mul_add, add_mul]]
          rw [hX, hY]
        have hX2 : (∑ i : Fin n, (∑ a, ∑ b,
              ((Real.sqrt (n:ℝ))⁻¹ * u a) * covX P muX X i a b * ((Real.sqrt (n:ℝ))⁻¹ * u b)) / 2)
            = ((∑ i : Fin n, ∑ a, ∑ b,
              ((Real.sqrt (n:ℝ))⁻¹ * u a) * covX P muX X i a b * ((Real.sqrt (n:ℝ))⁻¹ * u b))) / 2 := by
          rw [← Finset.sum_div]
        have hY2 : (∑ i : Fin m, (∑ a, ∑ b,
              (((delta n m) * (Real.sqrt (m:ℝ))⁻¹) * u a) * covY P muY Y i a b
                * (((delta n m) * (Real.sqrt (m:ℝ))⁻¹) * u b)) / 2)
            = ((∑ i : Fin m, ∑ a, ∑ b,
              (((delta n m) * (Real.sqrt (m:ℝ))⁻¹) * u a) * covY P muY Y i a b
                * (((delta n m) * (Real.sqrt (m:ℝ))⁻¹) * u b))) / 2 := by
          rw [← Finset.sum_div]
        rw [hX2, hY2, ← hquad0, ← add_div]
      have hmainval : (∫ ω, Real.exp (∑ j, u j * combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j) ∂P)
          = Real.exp ((∑ a, ∑ b, u a * Sigma a b * u b) / 2) := by
        rw [hfun, hInt, hprodval]
        simp only [hFX, hGY]
        rw [← hexp_sum, ← hexp_sum, ← Real.exp_add]
        exact congrArg Real.exp hquad
      exact hmainval
  · intro j
    have hid := statopia_math_node_227172929_e53d1a52 P delta muX muY X Y F G hindep hXmean
      hYmean hXL2 hYL2 hX hY j
    simpa only [hid] using hbvar j
  /- @proof-region region.target-node.session.b6a6f878120850bf end -/

end

end Statlib.Imported

