import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Statlib.StatFoundation.RandomVariable.Gaussian.Standard
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_b34aa34a4b446c8039a4
import ProverJobs.ResidualE2ESupport20261106.M_7083a1b6a11e6d978b5b
import ProverJobs.ResidualE2ESupport20261106.M_a2ab28a3dd34e00e94b5
import ProverJobs.ResidualE2ESupport20261106.M_13372419cbaa298931d2
import ProverJobs.ResidualE2ESupport20261106.M_f563494b66a5583a8f7d

namespace PaperProofTasks.ResidualE2ESupport20261106
open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported
open scoped Matrix.Norms.L2Operator

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_1512738410_45e8a322 : ∃ C : ℝ, 0 < C ∧ ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
      let Ω := ((Fin m × Fin n) → ℝ)
      let μ : Measure Ω :=
        MeasureTheory.Measure.pi (fun _ : (Fin m × Fin n) => ProbabilityTheory.gaussianReal 0 1)
      let W : Ω → Matrix (Fin m) (Fin n) ℝ := fun ω i j => ω (i, j)
      ∫ ω, ‖W ω‖ ∂μ ≤ Real.sqrt (m : ℝ) + Real.sqrt (n : ℝ) + C := by
  /- @proof-region region.target-node.session.aa85431675a71ae0 begin -/
  refine ⟨2, by norm_num, ?_⟩
  intro m n hm hn
  have hgauss_bridge : ∀ {p : ℕ} (X : ((Fin m × Fin n) → ℝ) → Fin p → ℝ)
      (SigmaX : Matrix (Fin p) (Fin p) ℝ),
      Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector
        (MeasureTheory.Measure.pi (fun _ : (Fin m × Fin n) => ProbabilityTheory.gaussianReal 0 1))
        X SigmaX →
      SigmaX.PosSemidef →
      ∀ a : Fin p → ℝ, ∃ v : NNReal,
        Measure.map (fun ω => ∑ k : Fin p, a k * X ω k)
            (MeasureTheory.Measure.pi (fun _ : (Fin m × Fin n) => ProbabilityTheory.gaussianReal 0 1))
          = ProbabilityTheory.gaussianReal 0 v := by
    intro p X SigmaX hX hSig a
    exact ⟨_, Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.map_linearCombination
      _ X SigmaX hX hSig a⟩

  have hcoord_indep : iIndepFun (fun p : Fin m × Fin n => fun ω : (Fin m × Fin n) → ℝ => ω p)
      (MeasureTheory.Measure.pi (fun _ : (Fin m × Fin n) => ProbabilityTheory.gaussianReal 0 1)) :=
    ProbabilityTheory.iIndepFun_pi (fun _ => measurable_id.aemeasurable)


  have hsqsq : Integrable (fun x : ℝ => x ^ 2) (ProbabilityTheory.gaussianReal 0 1) :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (Statlib.StatFoundation.RandomVariable.Gaussian.memLp_pow_id_gaussianReal 2 1 (by simp))

  have hmemLp : MeasureTheory.MemLp (fun x : ℝ => x) 2 (ProbabilityTheory.gaussianReal 0 1) := by
    simpa using Statlib.StatFoundation.RandomVariable.Gaussian.memLp_pow_id_gaussianReal
      (μ₀ := (0 : ℝ)) (v := (1 : NNReal)) 1 2 (by simp)


  have hlin : (∫⁻ x : ℝ, ENNReal.ofReal (x ^ 2) ∂(ProbabilityTheory.gaussianReal 0 1))
      = ENNReal.ofReal (∫ x : ℝ, x ^ 2 ∂(ProbabilityTheory.gaussianReal 0 1)) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hsqsq
      (Filter.Eventually.of_forall (fun x : ℝ => by positivity))).symm

  have hEx : (∫ x : ℝ, x ∂(ProbabilityTheory.gaussianReal 0 1)) = 0 := by
    simpa using ProbabilityTheory.integral_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal))

  have hmoment : (∫ x : ℝ, x ^ 2 ∂(ProbabilityTheory.gaussianReal 0 1)) = 1 := by
    have hvar : ProbabilityTheory.variance (fun x : ℝ => x) (ProbabilityTheory.gaussianReal 0 1) = 1 := by
      simpa using ProbabilityTheory.variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal))
    have hpt : ((fun x : ℝ => x) ^ 2) = fun x : ℝ => x ^ 2 := rfl
    rw [ProbabilityTheory.variance_eq_sub hmemLp, hpt] at hvar
    simpa [hEx] using hvar

  have hwidth_m : (∫ g : Fin m → ℝ, Real.sqrt (∑ i : Fin m, (g i) ^ 2)
      ∂(MeasureTheory.Measure.pi (fun _ : Fin m => ProbabilityTheory.gaussianReal 0 1)))
      ≤ Real.sqrt (m : ℝ) :=
    statopia_math_node_3511190190_0d8a3dbd m hm

  have hwidth_n : (∫ g : Fin n → ℝ, Real.sqrt (∑ i : Fin n, (g i) ^ 2)
      ∂(MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)))
      ≤ Real.sqrt (n : ℝ) :=
    statopia_math_node_3511190190_0d8a3dbd n hn

  have hcoord_sq : ∀ p : Fin m × Fin n,
      (∫ ω : (Fin m × Fin n) → ℝ, (ω p) ^ 2
        ∂(MeasureTheory.Measure.pi (fun _ : (Fin m × Fin n) => ProbabilityTheory.gaussianReal 0 1)))
      = 1 := by
    intro p
    have hpoint : (fun ω : (Fin m × Fin n) → ℝ => (ω p) ^ 2)
        = fun ω : (Fin m × Fin n) → ℝ =>
            ∏ i : Fin m × Fin n, (if i = p then (ω i) ^ 2 else 1) := by
      funext ω
      simp
    rw [hpoint]
    rw [MeasureTheory.integral_fintype_prod_eq_prod
      (f := fun i (x : ℝ) => if i = p then x ^ 2 else 1)
      (μ := fun _ : Fin m × Fin n => ProbabilityTheory.gaussianReal 0 1)]
    have hfac : ∀ i : Fin m × Fin n,
        (∫ x : ℝ, (if i = p then x ^ 2 else 1)
          ∂(ProbabilityTheory.gaussianReal 0 1)) = 1 := by
      intro i
      by_cases hi : i = p
      · simp [hi, hmoment]
      · simp [hi]
    simp [hfac]

  have hcoord_cross : ∀ p q : Fin m × Fin n, p ≠ q →
      (∫ ω : (Fin m × Fin n) → ℝ, ω p * ω q
        ∂(MeasureTheory.Measure.pi (fun _ : (Fin m × Fin n) => ProbabilityTheory.gaussianReal 0 1)))
      = 0 := by
    intro p q hpq
    have hpoint : (fun ω : (Fin m × Fin n) → ℝ => ω p * ω q)
        = fun ω : (Fin m × Fin n) → ℝ =>
            ∏ i : Fin m × Fin n,
              ((if i = p then ω i else 1) * (if i = q then ω i else 1)) := by
      funext ω
      rw [Finset.prod_mul_distrib]
      simp
    rw [hpoint]
    rw [MeasureTheory.integral_fintype_prod_eq_prod
      (f := fun i (x : ℝ) => (if i = p then x else 1) * (if i = q then x else 1))
      (μ := fun _ : Fin m × Fin n => ProbabilityTheory.gaussianReal 0 1)]
    have hfac : ∀ i : Fin m × Fin n,
        (∫ x : ℝ, ((if i = p then x else 1) * (if i = q then x else 1))
          ∂(ProbabilityTheory.gaussianReal 0 1))
        = (if i = p then (0 : ℝ) else 1) * (if i = q then 0 else 1) := by
      intro i
      by_cases h1 : i = p
      · subst h1
        simp [hpq, hEx]
      · by_cases h2 : i = q
        · subst h2
          simp [h1, hEx]
        · simp [h1, h2]
    simp only [hfac]
    rw [Finset.prod_mul_distrib]
    simp

  have hgauss_coord : ∀ c : (Fin m × Fin n) → ℝ, ∃ v : NNReal,
      Measure.map (fun ω : (Fin m × Fin n) → ℝ => ∑ p : Fin m × Fin n, c p * ω p)
        (MeasureTheory.Measure.pi (fun _ : (Fin m × Fin n) => ProbabilityTheory.gaussianReal 0 1))
      = ProbabilityTheory.gaussianReal 0 v := fun c =>
    ⟨_, statopia_math_node_647033768_7a6b2259 (Fin m × Fin n) c⟩

  have hbilin_eq : ∀ (N : ℕ) (x : Fin N → Fin m → ℝ) (y : Fin N → Fin n → ℝ) (k : Fin N)
      (ω : (Fin m × Fin n) → ℝ),
      (∑ i : Fin m, ∑ j : Fin n, x k i * y k j * ω (i, j))
        = ∑ p : Fin m × Fin n, (x k p.1 * y k p.2) * ω p := by
    intro N x y k ω
    rw [Fintype.sum_prod_type]

  have hmoment_gen : ∀ v : NNReal,
      (∫ x : ℝ, x ^ 2 ∂(ProbabilityTheory.gaussianReal 0 v)) = (v : ℝ) := by
    intro v
    have hmem : MeasureTheory.MemLp (fun x : ℝ => x) 2 (ProbabilityTheory.gaussianReal 0 v) := by
      simpa using Statlib.StatFoundation.RandomVariable.Gaussian.memLp_pow_id_gaussianReal
        (μ₀ := (0 : ℝ)) (v := v) 1 2 (by simp)
    have hvar : ProbabilityTheory.variance (fun x : ℝ => x)
        (ProbabilityTheory.gaussianReal 0 v) = (v : ℝ) := by
      simpa using ProbabilityTheory.variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := v)
    have hExv : (∫ x : ℝ, x ∂(ProbabilityTheory.gaussianReal 0 v)) = 0 := by
      simpa using ProbabilityTheory.integral_id_gaussianReal (μ := (0 : ℝ)) (v := v)
    have hpt : ((fun x : ℝ => x) ^ 2) = fun x : ℝ => x ^ 2 := rfl
    rw [ProbabilityTheory.variance_eq_sub hmem, hpt] at hvar
    simpa [hExv] using hvar

  have hsecond : ∀ {ι : Type} [Fintype ι] (c : ι → ℝ),
      (∫ ω : ι → ℝ, (∑ p : ι, c p * ω p) ^ 2
        ∂(MeasureTheory.Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1)))
      = ∑ p : ι, (c p) ^ 2 := by
    intro ι _ c
    have hmeas : Measurable
        (fun ω : ι → ℝ => ∑ p : ι, c p * ω p) := by
      refine Finset.measurable_sum Finset.univ ?_
      intro p _
      exact measurable_const.mul (measurable_pi_apply p)
    have hfm : AEStronglyMeasurable (fun y : ℝ => y ^ 2)
        (Measure.map (fun ω : ι → ℝ => ∑ p : ι, c p * ω p)
          (MeasureTheory.Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1))) := by
      refine Measurable.aestronglyMeasurable ?_
      simpa [pow_two] using (measurable_id.mul measurable_id : Measurable fun y : ℝ => y * y)
    have hchange : (∫ y : ℝ, y ^ 2
        ∂(Measure.map (fun ω : ι → ℝ => ∑ p : ι, c p * ω p)
          (MeasureTheory.Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1))))
        = ∫ ω : ι → ℝ, (∑ p : ι, c p * ω p) ^ 2
          ∂(MeasureTheory.Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1)) :=
      MeasureTheory.integral_map hmeas.aemeasurable hfm
    rw [← hchange]
    rw [statopia_math_node_647033768_7a6b2259 ι c]
    exact hmoment_gen _

  have hlin_memLp : ∀ {ι : Type} [Fintype ι] (c : ι → ℝ),
      MeasureTheory.MemLp (fun ω : ι → ℝ => ∑ p : ι, c p * ω p) 2
        (MeasureTheory.Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1)) := by
    intro ι _ c
    have hmeas : Measurable
        (fun ω : ι → ℝ => ∑ p : ι, c p * ω p) := by
      refine Finset.measurable_sum Finset.univ ?_
      intro p _
      exact measurable_const.mul (measurable_pi_apply p)
    have hlaw := statopia_math_node_647033768_7a6b2259 ι c
    have hmem : MeasureTheory.MemLp (fun x : ℝ => x) 2
        (ProbabilityTheory.gaussianReal 0 ⟨∑ p : ι, (c p) ^ 2,
          Finset.sum_nonneg fun p _ => sq_nonneg (c p)⟩) := by
      simpa using Statlib.StatFoundation.RandomVariable.Gaussian.memLp_pow_id_gaussianReal
        (μ₀ := (0 : ℝ))
        (v := ⟨∑ p : ι, (c p) ^ 2, Finset.sum_nonneg fun p _ => sq_nonneg (c p)⟩)
        1 2 (by simp)
    rw [← hlaw] at hmem
    simpa using MeasureTheory.MemLp.comp_of_map hmem hmeas.aemeasurable

  have hlin_sq_int : ∀ {ι : Type} [Fintype ι] (c : ι → ℝ),
      MeasureTheory.Integrable (fun ω : ι → ℝ => (∑ p : ι, c p * ω p) ^ 2)
        (MeasureTheory.Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1)) := by
    intro ι _ c
    exact MeasureTheory.MemLp.integrable_sq (hlin_memLp c)

  have hprod_int : ∀ {ι : Type} [Fintype ι] (c d : ι → ℝ),
      MeasureTheory.Integrable (fun ω : ι → ℝ =>
        (∑ p : ι, c p * ω p) * (∑ p : ι, d p * ω p))
        (MeasureTheory.Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1)) := by
    intro ι _ c d
    exact MeasureTheory.MemLp.integrable (q := 1) (by norm_num) ((hlin_memLp d).mul (hlin_memLp c))


  have hsq_add : ∀ {ι : Type} [Fintype ι] (a b : ((ι → ℝ) → ℝ)),
      MeasureTheory.Integrable (fun ω : ι → ℝ => (a ω) ^ 2)
        (MeasureTheory.Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1)) →
      MeasureTheory.Integrable (fun ω : ι → ℝ => (b ω) ^ 2)
        (MeasureTheory.Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1)) →
      MeasureTheory.Integrable (fun ω : ι → ℝ => a ω * b ω)
        (MeasureTheory.Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1)) →
      (∫ ω : ι → ℝ, (a ω + b ω) ^ 2
        ∂(MeasureTheory.Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1)))
      = (∫ ω : ι → ℝ, (a ω) ^ 2
          ∂(MeasureTheory.Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1)))
        + (∫ ω : ι → ℝ, (b ω) ^ 2
          ∂(MeasureTheory.Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1)))
        + 2 * (∫ ω : ι → ℝ, a ω * b ω
          ∂(MeasureTheory.Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1))) := by
    intro ι _ a b ha hb hab
    have hpt : (fun ω : ι → ℝ => (a ω + b ω) ^ 2)
        = fun ω => (a ω) ^ 2 + (b ω) ^ 2 + 2 * (a ω * b ω) := by
      funext ω
      ring
    have hA : MeasureTheory.Integrable (fun ω : ι → ℝ => (a ω) ^ 2 + (b ω) ^ 2)
        (MeasureTheory.Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1)) :=
      ha.add hb
    have hB : MeasureTheory.Integrable (fun ω : ι → ℝ => 2 * (a ω * b ω))
        (MeasureTheory.Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1)) :=
      hab.const_mul 2
    have s1 : (∫ ω : ι → ℝ, ((a ω) ^ 2 + (b ω) ^ 2) + 2 * (a ω * b ω)
          ∂(MeasureTheory.Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1)))
        = (∫ ω : ι → ℝ, (a ω) ^ 2 + (b ω) ^ 2
            ∂(MeasureTheory.Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1)))
          + (∫ ω : ι → ℝ, 2 * (a ω * b ω)
            ∂(MeasureTheory.Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1))) :=
      MeasureTheory.integral_add hA hB
    have s2 : (∫ ω : ι → ℝ, (a ω) ^ 2 + (b ω) ^ 2
          ∂(MeasureTheory.Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1)))
        = (∫ ω : ι → ℝ, (a ω) ^ 2
            ∂(MeasureTheory.Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1)))
          + (∫ ω : ι → ℝ, (b ω) ^ 2
            ∂(MeasureTheory.Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1))) :=
      MeasureTheory.integral_add ha hb
    have s3 : (∫ ω : ι → ℝ, 2 * (a ω * b ω)
          ∂(MeasureTheory.Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1)))
        = 2 * (∫ ω : ι → ℝ, a ω * b ω
            ∂(MeasureTheory.Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1))) :=
      MeasureTheory.integral_const_mul 2 (fun ω : ι → ℝ => a ω * b ω)
    rw [hpt, s1, s2, s3]

  have hcov : ∀ {ι : Type} [Fintype ι] (c d : ι → ℝ),
      (∫ ω : ι → ℝ,
        (∑ p : ι, c p * ω p) * (∑ p : ι, d p * ω p)
        ∂(MeasureTheory.Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1)))
      = ∑ p : ι, c p * d p := by
    intro ι _ c d
    have hcd : (∫ ω : ι → ℝ,
          ((∑ p : ι, c p * ω p) + (∑ p : ι, d p * ω p)) ^ 2
          ∂(MeasureTheory.Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1)))
        = ∑ p : ι, (c p + d p) ^ 2 := by
      have hpt : (fun ω : ι → ℝ =>
            ((∑ p : ι, c p * ω p) + (∑ p : ι, d p * ω p)) ^ 2)
          = fun ω => (∑ p : ι, (c p + d p) * ω p) ^ 2 := by
        funext ω
        have hsum_eq : (∑ p : ι, (c p * ω p + d p * ω p))
            = ∑ p : ι, (c p + d p) * ω p :=
          Finset.sum_congr rfl (fun p _ => by ring)
        rw [← Finset.sum_add_distrib, hsum_eq]
      rw [hpt]
      exact hsecond (c + d)
    have hkey := hsq_add (fun ω : ι → ℝ => ∑ p : ι, c p * ω p)
      (fun ω : ι → ℝ => ∑ p : ι, d p * ω p)
      (hlin_sq_int c) (hlin_sq_int d) (hprod_int c d)
    have halg : (∑ p : ι, (c p + d p) ^ 2)
        = (∑ p : ι, (c p) ^ 2) + (∑ p : ι, (d p) ^ 2)
          + 2 * (∑ p : ι, c p * d p) := by
      have h1 : (∑ p : ι, (c p + d p) ^ 2)
          = ∑ p : ι, ((c p) ^ 2 + (d p) ^ 2 + 2 * (c p * d p)) :=
        Finset.sum_congr rfl (fun p _ => by ring)
      rw [h1, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    linarith [hcd, hkey, hsecond c, hsecond d, halg]

  have hbilin_cov : ∀ (N : ℕ) (x : Fin N → Fin m → ℝ) (y : Fin N → Fin n → ℝ) (k l : Fin N),
      (∫ ω : (Fin m × Fin n) → ℝ,
        (∑ i : Fin m, ∑ j : Fin n, x k i * y k j * ω (i, j))
          * (∑ i : Fin m, ∑ j : Fin n, x l i * y l j * ω (i, j))
        ∂(MeasureTheory.Measure.pi (fun _ : (Fin m × Fin n) => ProbabilityTheory.gaussianReal 0 1)))
      = (∑ i : Fin m, x k i * x l i) * (∑ j : Fin n, y k j * y l j) := by
    intro N x y k l
    have hpt : (fun ω : (Fin m × Fin n) → ℝ =>
        (∑ i : Fin m, ∑ j : Fin n, x k i * y k j * ω (i, j))
          * (∑ i : Fin m, ∑ j : Fin n, x l i * y l j * ω (i, j)))
        = fun ω : (Fin m × Fin n) → ℝ =>
          (∑ p : Fin m × Fin n, (x k p.1 * y k p.2) * ω p)
            * (∑ p : Fin m × Fin n, (x l p.1 * y l p.2) * ω p) := by
      funext ω
      rw [hbilin_eq, hbilin_eq]
    rw [hpt]
    rw [hcov]
    rw [Fintype.sum_prod_type, Fintype.sum_mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    show x k i * y k j * (x l i * y l j) = x k i * x l i * (y k j * y l j)
    ring

  have hX_incr : ∀ (N : ℕ) (x : Fin N → Fin m → ℝ) (y : Fin N → Fin n → ℝ),
      (∀ k : Fin N, (∑ i : Fin m, (x k i) ^ 2) = 1) →
      (∀ k : Fin N, (∑ j : Fin n, (y k j) ^ 2) = 1) →
      ∀ k l : Fin N,
        (∫ ω : (Fin m × Fin n) → ℝ,
          (∑ i : Fin m, ∑ j : Fin n, x k i * y k j * ω (i, j))
            * (∑ i : Fin m, ∑ j : Fin n, x k i * y k j * ω (i, j))
          ∂(MeasureTheory.Measure.pi (fun _ : (Fin m × Fin n) => ProbabilityTheory.gaussianReal 0 1)))
        + (∫ ω : (Fin m × Fin n) → ℝ,
          (∑ i : Fin m, ∑ j : Fin n, x l i * y l j * ω (i, j))
            * (∑ i : Fin m, ∑ j : Fin n, x l i * y l j * ω (i, j))
          ∂(MeasureTheory.Measure.pi (fun _ : (Fin m × Fin n) => ProbabilityTheory.gaussianReal 0 1)))
        - 2 * (∫ ω : (Fin m × Fin n) → ℝ,
          (∑ i : Fin m, ∑ j : Fin n, x k i * y k j * ω (i, j))
            * (∑ i : Fin m, ∑ j : Fin n, x l i * y l j * ω (i, j))
          ∂(MeasureTheory.Measure.pi (fun _ : (Fin m × Fin n) => ProbabilityTheory.gaussianReal 0 1)))
        = 2 - 2 * ((∑ i : Fin m, x k i * x l i) * (∑ j : Fin n, y k j * y l j)) := by
    intro N x y hx hy k l
    have hkk := hbilin_cov N x y k k
    have hll := hbilin_cov N x y l l
    have hkl := hbilin_cov N x y k l
    have hxk : (∑ i : Fin m, x k i * x k i) = 1 := by
      simpa [pow_two] using hx k
    have hxl : (∑ i : Fin m, x l i * x l i) = 1 := by
      simpa [pow_two] using hx l
    have hyk : (∑ j : Fin n, y k j * y k j) = 1 := by
      simpa [pow_two] using hy k
    have hyl : (∑ j : Fin n, y l j * y l j) = 1 := by
      simpa [pow_two] using hy l
    rw [hkk, hll, hkl, hxk, hxl, hyk, hyl]
    ring

  have hdot_bounds : ∀ (N : ℕ) (x y : Fin N → ℝ),
      (∑ i : Fin N, (x i) ^ 2) = 1 → (∑ i : Fin N, (y i) ^ 2) = 1 →
      (∑ i : Fin N, x i * y i) ≤ 1 ∧ -1 ≤ ∑ i : Fin N, x i * y i := by
    intro N x y hx hy
    have h1 : (0 : ℝ) ≤ ∑ i : Fin N, (x i - y i) ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have h2 : (0 : ℝ) ≤ ∑ i : Fin N, (x i + y i) ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have e1 : (∑ i : Fin N, (x i - y i) ^ 2)
        = (∑ i : Fin N, (x i) ^ 2) - 2 * (∑ i : Fin N, x i * y i)
          + (∑ i : Fin N, (y i) ^ 2) := by
      have hh : (∑ i : Fin N, (x i - y i) ^ 2)
          = ∑ i : Fin N, ((x i) ^ 2 - 2 * (x i * y i) + (y i) ^ 2) :=
        Finset.sum_congr rfl (fun i _ => by ring)
      rw [hh, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have e2 : (∑ i : Fin N, (x i + y i) ^ 2)
        = (∑ i : Fin N, (x i) ^ 2) + 2 * (∑ i : Fin N, x i * y i)
          + (∑ i : Fin N, (y i) ^ 2) := by
      have hh : (∑ i : Fin N, (x i + y i) ^ 2)
          = ∑ i : Fin N, ((x i) ^ 2 + 2 * (x i * y i) + (y i) ^ 2) :=
        Finset.sum_congr rfl (fun i _ => by ring)
      rw [hh, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    constructor <;> linarith

  have hbase_indep : ProbabilityTheory.IndepFun
      (Prod.fst : (((Fin m × Fin n) → ℝ) × ((Fin m → ℝ) × (Fin n → ℝ))) → ((Fin m × Fin n) → ℝ))
      (Prod.snd : (((Fin m × Fin n) → ℝ) × ((Fin m → ℝ) × (Fin n → ℝ))) →
        ((Fin m → ℝ) × (Fin n → ℝ)))
      ((MeasureTheory.Measure.pi (fun _ : (Fin m × Fin n) => ProbabilityTheory.gaussianReal 0 1)).prod
        ((MeasureTheory.Measure.pi (fun _ : Fin m => ProbabilityTheory.gaussianReal 0 1)).prod
          (MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)))) := by
    rw [ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      measurable_fst.aemeasurable measurable_snd.aemeasurable]
    have hid : (fun z : ((Fin m × Fin n) → ℝ) × ((Fin m → ℝ) × (Fin n → ℝ)) => (z.1, z.2)) = id := by
      funext z
      rfl
    rw [hid, MeasureTheory.Measure.map_id]
    have h1 : MeasureTheory.Measure.map Prod.fst
        ((MeasureTheory.Measure.pi (fun _ : (Fin m × Fin n) => ProbabilityTheory.gaussianReal 0 1)).prod
          ((MeasureTheory.Measure.pi (fun _ : Fin m => ProbabilityTheory.gaussianReal 0 1)).prod
            (MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1))))
        = MeasureTheory.Measure.pi (fun _ : (Fin m × Fin n) => ProbabilityTheory.gaussianReal 0 1) :=
      MeasureTheory.Measure.fst_prod
    have h2 : MeasureTheory.Measure.map Prod.snd
        ((MeasureTheory.Measure.pi (fun _ : (Fin m × Fin n) => ProbabilityTheory.gaussianReal 0 1)).prod
          ((MeasureTheory.Measure.pi (fun _ : Fin m => ProbabilityTheory.gaussianReal 0 1)).prod
            (MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1))))
        = (MeasureTheory.Measure.pi (fun _ : Fin m => ProbabilityTheory.gaussianReal 0 1)).prod
            (MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)) :=
      MeasureTheory.Measure.snd_prod
    rw [h1, h2]

  have hcauchy : ∀ (s : ℕ) (x g : Fin s → ℝ), (∑ i : Fin s, (x i) ^ 2) = 1 →
      (∑ i : Fin s, x i * g i) ≤ Real.sqrt (∑ i : Fin s, (g i) ^ 2) := by
    intro s x g hx
    set t : ℝ := Real.sqrt (∑ i : Fin s, (g i) ^ 2) with ht
    have htnn : 0 ≤ t := Real.sqrt_nonneg _
    have ht2 : t ^ 2 = ∑ i : Fin s, (g i) ^ 2 := by
      rw [ht]
      exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (g i))
    have hnn : (0 : ℝ) ≤ ∑ i : Fin s, (x i * t - g i) ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hpt : (∑ i : Fin s, (x i * t - g i) ^ 2)
        = (∑ i : Fin s, (x i) ^ 2) * t ^ 2 - 2 * t * (∑ i : Fin s, x i * g i)
          + (∑ i : Fin s, (g i) ^ 2) := by
      have key : (∑ i : Fin s, (x i * t - g i) ^ 2)
          = ∑ i : Fin s, ((x i) ^ 2 * t ^ 2 - 2 * t * (x i * g i) + (g i) ^ 2) :=
        Finset.sum_congr rfl (fun i _ => by ring)
      rw [key, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
    rw [hpt, hx] at hnn
    have hkey2 : 2 * t * (∑ i : Fin s, x i * g i) ≤ 2 * (∑ i : Fin s, (g i) ^ 2) := by
      nlinarith [hnn, ht2]
    by_cases ht0 : t = 0
    · have hzero : (∑ i : Fin s, (g i) ^ 2) = 0 := by
        rw [← ht2, ht0]
        ring
      have hS : (∑ i : Fin s, x i * g i) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        have hle : (g i) ^ 2 ≤ ∑ j : Fin s, (g j) ^ 2 :=
          Finset.single_le_sum (f := fun j : Fin s => (g j) ^ 2)
            (fun j _ => sq_nonneg (g j)) (Finset.mem_univ i)
        have h1 : (g i) ^ 2 = 0 :=
          le_antisymm (by rw [hzero] at hle; exact hle) (sq_nonneg _)
        rw [pow_two] at h1
        have hgi : g i = 0 := mul_self_eq_zero.mp h1
        rw [hgi, mul_zero]
      rw [hS, ht0]
    · have htpos : 0 < t := lt_of_le_of_ne htnn (Ne.symm ht0)
      nlinarith [hkey2, ht2, htpos]

  have harith : ∀ A B : ℝ, 0 ≤ B →
      (∀ δ : ℝ, 0 < δ → δ < 1 / 4 → A ≤ (1 - 2 * δ)⁻¹ * B) → A ≤ B := by
    intro A B hB hkey
    by_contra hcon
    push_neg at hcon
    have hApos : 0 < A := lt_of_le_of_lt hB hcon
    have hdpos : 0 < A - B := by linarith
    set δ : ℝ := min (1 / 8) ((A - B) / (4 * A)) with hδdef
    have hδpos : 0 < δ := by
      rw [hδdef]
      exact lt_min (by norm_num) (div_pos hdpos (by linarith))
    have hδq : δ < 1 / 4 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    have hcpos : (0 : ℝ) < 1 - 2 * δ := by linarith
    have hstep : (1 - 2 * δ) * A ≤ B := by
      have h2 := mul_le_mul_of_nonneg_left (hkey δ hδpos hδq) (le_of_lt hcpos)
      have h3 : (1 - 2 * δ) * ((1 - 2 * δ)⁻¹ * B) = B := by
        field_simp
      linarith [h2, h3]
    have hδle : δ ≤ (A - B) / (4 * A) := min_le_right _ _
    have hbound : 2 * δ * A ≤ (A - B) / 2 := by
      have h3 : δ * A ≤ ((A - B) / (4 * A)) * A :=
        mul_le_mul_of_nonneg_right hδle (le_of_lt hApos)
      have h4 : ((A - B) / (4 * A)) * A = (A - B) / 4 := by
        field_simp
      rw [h4] at h3
      linarith
    nlinarith [hstep, hbound, hdpos]

  have hXmeas : ∀ (N : ℕ) (x : Fin N → Fin m → ℝ) (y : Fin N → Fin n → ℝ),
      Measurable (fun z : ((Fin m × Fin n) → ℝ) × ((Fin m → ℝ) × (Fin n → ℝ)) =>
        fun k : Fin N => ∑ i : Fin m, ∑ j : Fin n, x k i * z.1 (i, j) * y k j) := by
    intro N x y
    rw [measurable_pi_iff]
    intro k
    refine Finset.measurable_sum Finset.univ ?_
    intro i _
    refine Finset.measurable_sum Finset.univ ?_
    intro j _
    have h1 : Measurable fun z : ((Fin m × Fin n) → ℝ) × ((Fin m → ℝ) × (Fin n → ℝ)) =>
        z.1 (i, j) :=
      (measurable_pi_apply (i, j)).comp measurable_fst
    exact (measurable_const.mul h1).mul measurable_const

  have hYmeas : ∀ (N : ℕ) (x : Fin N → Fin m → ℝ) (y : Fin N → Fin n → ℝ),
      Measurable (fun w : (Fin m → ℝ) × (Fin n → ℝ) =>
        fun k : Fin N => (∑ i : Fin m, x k i * w.1 i) + (∑ j : Fin n, y k j * w.2 j)) := by
    intro N x y
    rw [measurable_pi_iff]
    intro k
    refine Measurable.add ?_ ?_
    · refine Finset.measurable_sum Finset.univ ?_
      intro i _
      have h1 : Measurable fun w : (Fin m → ℝ) × (Fin n → ℝ) => w.1 i :=
        (measurable_pi_apply i).comp measurable_fst
      exact measurable_const.mul h1
    · refine Finset.measurable_sum Finset.univ ?_
      intro j _
      have h1 : Measurable fun w : (Fin m → ℝ) × (Fin n → ℝ) => w.2 j :=
        (measurable_pi_apply j).comp measurable_snd
      exact measurable_const.mul h1

  have hIndepXY : ∀ (N : ℕ) (x : Fin N → Fin m → ℝ) (y : Fin N → Fin n → ℝ),
      ProbabilityTheory.IndepFun
        (fun z : ((Fin m × Fin n) → ℝ) × ((Fin m → ℝ) × (Fin n → ℝ)) =>
          fun k : Fin N => ∑ i : Fin m, ∑ j : Fin n, x k i * z.1 (i, j) * y k j)
        (fun z : ((Fin m × Fin n) → ℝ) × ((Fin m → ℝ) × (Fin n → ℝ)) =>
          fun k : Fin N => (∑ i : Fin m, x k i * z.2.1 i) + (∑ j : Fin n, y k j * z.2.2 j))
        ((MeasureTheory.Measure.pi (fun _ : (Fin m × Fin n) => ProbabilityTheory.gaussianReal 0 1)).prod
          ((MeasureTheory.Measure.pi (fun _ : Fin m => ProbabilityTheory.gaussianReal 0 1)).prod
            (MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)))) := by
    intro N x y
    have hXm : Measurable (fun ω : (Fin m × Fin n) → ℝ =>
        fun k : Fin N => ∑ i : Fin m, ∑ j : Fin n, x k i * ω (i, j) * y k j) := by
      rw [measurable_pi_iff]
      intro k
      refine Finset.measurable_sum Finset.univ ?_
      intro i _
      refine Finset.measurable_sum Finset.univ ?_
      intro j _
      exact (measurable_const.mul (measurable_pi_apply (i, j))).mul measurable_const
    exact ProbabilityTheory.indepFun_prod
      (X := fun ω : (Fin m × Fin n) → ℝ =>
        fun k : Fin N => ∑ i : Fin m, ∑ j : Fin n, x k i * ω (i, j) * y k j)
      (Y := fun w : (Fin m → ℝ) × (Fin n → ℝ) =>
        fun k : Fin N => (∑ i : Fin m, x k i * w.1 i) + (∑ j : Fin n, y k j * w.2 j))
      hXm (hYmeas N x y)

  have hfst_map : MeasureTheory.Measure.map
      (Prod.fst : (((Fin m × Fin n) → ℝ) × ((Fin m → ℝ) × (Fin n → ℝ))) → ((Fin m × Fin n) → ℝ))
      ((MeasureTheory.Measure.pi (fun _ : (Fin m × Fin n) => ProbabilityTheory.gaussianReal 0 1)).prod
        ((MeasureTheory.Measure.pi (fun _ : Fin m => ProbabilityTheory.gaussianReal 0 1)).prod
          (MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1))))
      = MeasureTheory.Measure.pi (fun _ : (Fin m × Fin n) => ProbabilityTheory.gaussianReal 0 1) :=
    MeasureTheory.Measure.fst_prod

  have hsnd_map : MeasureTheory.Measure.map
      (Prod.snd : (((Fin m × Fin n) → ℝ) × ((Fin m → ℝ) × (Fin n → ℝ))) →
        ((Fin m → ℝ) × (Fin n → ℝ)))
      ((MeasureTheory.Measure.pi (fun _ : (Fin m × Fin n) => ProbabilityTheory.gaussianReal 0 1)).prod
        ((MeasureTheory.Measure.pi (fun _ : Fin m => ProbabilityTheory.gaussianReal 0 1)).prod
          (MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1))))
      = (MeasureTheory.Measure.pi (fun _ : Fin m => ProbabilityTheory.gaussianReal 0 1)).prod
          (MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)) :=
    MeasureTheory.Measure.snd_prod

  have hXgauss : ∀ (N : ℕ) (x : Fin N → Fin m → ℝ) (y : Fin N → Fin n → ℝ) (a : Fin N → ℝ),
      ∃ v : NNReal,
        Measure.map (fun z : ((Fin m × Fin n) → ℝ) × ((Fin m → ℝ) × (Fin n → ℝ)) =>
          ∑ k : Fin N, a k * (∑ i : Fin m, ∑ j : Fin n, x k i * z.1 (i, j) * y k j))
          ((MeasureTheory.Measure.pi (fun _ : (Fin m × Fin n) => ProbabilityTheory.gaussianReal 0 1)).prod
            ((MeasureTheory.Measure.pi (fun _ : Fin m => ProbabilityTheory.gaussianReal 0 1)).prod
              (MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1))))
        = ProbabilityTheory.gaussianReal 0 v := by
    intro N x y a
    obtain ⟨v, hv⟩ := hgauss_coord
      (fun p : Fin m × Fin n => ∑ k : Fin N, a k * (x k p.1 * y k p.2))
    refine ⟨v, ?_⟩
    have hinner : ∀ k : Fin N, ∀ ω : (Fin m × Fin n) → ℝ,
        (∑ i : Fin m, ∑ j : Fin n, x k i * ω (i, j) * y k j)
          = ∑ p : Fin m × Fin n, (x k p.1 * y k p.2) * ω p := by
      intro k ω
      rw [← hbilin_eq N x y k ω]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
    have hpt : (fun z : ((Fin m × Fin n) → ℝ) × ((Fin m → ℝ) × (Fin n → ℝ)) =>
          ∑ k : Fin N, a k * (∑ i : Fin m, ∑ j : Fin n, x k i * z.1 (i, j) * y k j))
        = fun z => ∑ p : Fin m × Fin n,
            (∑ k : Fin N, a k * (x k p.1 * y k p.2)) * z.1 p := by
      funext z
      calc ∑ k : Fin N, a k * (∑ i : Fin m, ∑ j : Fin n, x k i * z.1 (i, j) * y k j)
          = ∑ k : Fin N, a k * (∑ p : Fin m × Fin n, (x k p.1 * y k p.2) * z.1 p) := by
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [hinner k z.1]
        _ = ∑ k : Fin N, ∑ p : Fin m × Fin n, a k * ((x k p.1 * y k p.2) * z.1 p) := by
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [Finset.mul_sum]
        _ = ∑ p : Fin m × Fin n, ∑ k : Fin N, a k * ((x k p.1 * y k p.2) * z.1 p) :=
            Finset.sum_comm
        _ = ∑ p : Fin m × Fin n,
              (∑ k : Fin N, a k * (x k p.1 * y k p.2)) * z.1 p := by
            refine Finset.sum_congr rfl (fun p _ => ?_)
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [hpt]
    have hgm : Measurable (fun ω : (Fin m × Fin n) → ℝ =>
        ∑ p : Fin m × Fin n, (∑ k : Fin N, a k * (x k p.1 * y k p.2)) * ω p) := by
      refine Finset.measurable_sum Finset.univ ?_
      intro p _
      exact measurable_const.mul (measurable_pi_apply p)
    have hcomp : (fun z : ((Fin m × Fin n) → ℝ) × ((Fin m → ℝ) × (Fin n → ℝ)) =>
          ∑ p : Fin m × Fin n, (∑ k : Fin N, a k * (x k p.1 * y k p.2)) * z.1 p)
        = (fun ω : (Fin m × Fin n) → ℝ =>
            ∑ p : Fin m × Fin n, (∑ k : Fin N, a k * (x k p.1 * y k p.2)) * ω p) ∘ Prod.fst := by
      funext z
      rfl
    rw [hcomp, ← MeasureTheory.Measure.map_map hgm measurable_fst, hfst_map]
    exact hv

  have hgauss_general : ∀ {ι : Type} [Fintype ι] (c : ι → ℝ), ∃ v : NNReal,
      Measure.map (fun ω : ι → ℝ => ∑ p : ι, c p * ω p)
        (MeasureTheory.Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1))
      = ProbabilityTheory.gaussianReal 0 v := by
    intro ι _ c
    exact ⟨_, statopia_math_node_647033768_7a6b2259 ι c⟩

  have hadd_gauss : ∀ (v₁ v₂ : NNReal),
      Measure.map (fun p : ℝ × ℝ => p.1 + p.2)
        ((ProbabilityTheory.gaussianReal 0 v₁).prod (ProbabilityTheory.gaussianReal 0 v₂))
      = ProbabilityTheory.gaussianReal 0 (v₁ + v₂) := by
    intro v₁ v₂
    have hind : ProbabilityTheory.IndepFun (Prod.fst : ℝ × ℝ → ℝ) (Prod.snd : ℝ × ℝ → ℝ)
        ((ProbabilityTheory.gaussianReal 0 v₁).prod (ProbabilityTheory.gaussianReal 0 v₂)) :=
      ProbabilityTheory.indepFun_prod measurable_id measurable_id
    have h1 : Measure.map (Prod.fst : ℝ × ℝ → ℝ)
        ((ProbabilityTheory.gaussianReal 0 v₁).prod (ProbabilityTheory.gaussianReal 0 v₂))
        = ProbabilityTheory.gaussianReal 0 v₁ := MeasureTheory.Measure.fst_prod
    have h2 : Measure.map (Prod.snd : ℝ × ℝ → ℝ)
        ((ProbabilityTheory.gaussianReal 0 v₁).prod (ProbabilityTheory.gaussianReal 0 v₂))
        = ProbabilityTheory.gaussianReal 0 v₂ := MeasureTheory.Measure.snd_prod
    have h := ProbabilityTheory.gaussianReal_add_gaussianReal_of_indepFun hind h1 h2
    simpa using h

  have htransfer_snd : ∀ (g : (Fin m → ℝ) × (Fin n → ℝ) → ℝ), Measurable g →
      Measure.map (fun z : ((Fin m × Fin n) → ℝ) × ((Fin m → ℝ) × (Fin n → ℝ)) => g z.2)
        ((MeasureTheory.Measure.pi (fun _ : (Fin m × Fin n) => ProbabilityTheory.gaussianReal 0 1)).prod
          ((MeasureTheory.Measure.pi (fun _ : Fin m => ProbabilityTheory.gaussianReal 0 1)).prod
            (MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1))))
      = Measure.map g
          ((MeasureTheory.Measure.pi (fun _ : Fin m => ProbabilityTheory.gaussianReal 0 1)).prod
            (MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1))) := by
    intro g hg
    have hcomp : (fun z : ((Fin m × Fin n) → ℝ) × ((Fin m → ℝ) × (Fin n → ℝ)) => g z.2)
        = g ∘ Prod.snd := by
      funext z
      rfl
    rw [hcomp, ← MeasureTheory.Measure.map_map hg measurable_snd, hsnd_map]

  have hYgauss : ∀ (N : ℕ) (x : Fin N → Fin m → ℝ) (y : Fin N → Fin n → ℝ) (a : Fin N → ℝ),
      ∃ v : NNReal,
        Measure.map (fun z : ((Fin m × Fin n) → ℝ) × ((Fin m → ℝ) × (Fin n → ℝ)) =>
          ∑ k : Fin N, a k * ((∑ i : Fin m, x k i * z.2.1 i) + (∑ j : Fin n, y k j * z.2.2 j)))
          ((MeasureTheory.Measure.pi (fun _ : (Fin m × Fin n) => ProbabilityTheory.gaussianReal 0 1)).prod
            ((MeasureTheory.Measure.pi (fun _ : Fin m => ProbabilityTheory.gaussianReal 0 1)).prod
              (MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1))))
        = ProbabilityTheory.gaussianReal 0 v := by
    intro N x y a
    obtain ⟨v₁, hv₁⟩ := hgauss_general (fun i : Fin m => ∑ k : Fin N, a k * x k i)
    obtain ⟨v₂, hv₂⟩ := hgauss_general (fun j : Fin n => ∑ k : Fin N, a k * y k j)
    refine ⟨v₁ + v₂, ?_⟩
    have hpt : (fun z : ((Fin m × Fin n) → ℝ) × ((Fin m → ℝ) × (Fin n → ℝ)) =>
          ∑ k : Fin N, a k * ((∑ i : Fin m, x k i * z.2.1 i) + (∑ j : Fin n, y k j * z.2.2 j)))
        = fun z => (∑ i : Fin m, (∑ k : Fin N, a k * x k i) * z.2.1 i)
            + (∑ j : Fin n, (∑ k : Fin N, a k * y k j) * z.2.2 j) := by
      funext z
      have hstep1 : ∀ k : Fin N, a k * (∑ i : Fin m, x k i * z.2.1 i)
          = ∑ i : Fin m, (a k * x k i) * z.2.1 i := by
        intro k
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      have hstep2 : ∀ k : Fin N, a k * (∑ j : Fin n, y k j * z.2.2 j)
          = ∑ j : Fin n, (a k * y k j) * z.2.2 j := by
        intro k
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      have hmain : ∀ k : Fin N,
          a k * ((∑ i : Fin m, x k i * z.2.1 i) + (∑ j : Fin n, y k j * z.2.2 j))
            = (∑ i : Fin m, (a k * x k i) * z.2.1 i)
              + (∑ j : Fin n, (a k * y k j) * z.2.2 j) := by
        intro k
        rw [mul_add, hstep1 k, hstep2 k]
      have hfirst : (∑ k : Fin N, ∑ i : Fin m, (a k * x k i) * z.2.1 i)
          = ∑ i : Fin m, (∑ k : Fin N, a k * x k i) * z.2.1 i := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_mul]
      have hsec : (∑ k : Fin N, ∑ j : Fin n, (a k * y k j) * z.2.2 j)
          = ∑ j : Fin n, (∑ k : Fin N, a k * y k j) * z.2.2 j := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.sum_mul]
      calc (∑ k : Fin N,
            a k * ((∑ i : Fin m, x k i * z.2.1 i) + (∑ j : Fin n, y k j * z.2.2 j)))
          = ∑ k : Fin N, ((∑ i : Fin m, (a k * x k i) * z.2.1 i)
              + (∑ j : Fin n, (a k * y k j) * z.2.2 j)) :=
            Finset.sum_congr rfl (fun k _ => hmain k)
        _ = (∑ k : Fin N, ∑ i : Fin m, (a k * x k i) * z.2.1 i)
              + (∑ k : Fin N, ∑ j : Fin n, (a k * y k j) * z.2.2 j) :=
            Finset.sum_add_distrib
        _ = (∑ i : Fin m, (∑ k : Fin N, a k * x k i) * z.2.1 i)
              + (∑ j : Fin n, (∑ k : Fin N, a k * y k j) * z.2.2 j) := by
            rw [hfirst, hsec]
    rw [hpt]
    have hf1 : Measurable (fun g : Fin m → ℝ =>
        ∑ i : Fin m, (∑ k : Fin N, a k * x k i) * g i) := by
      refine Finset.measurable_sum Finset.univ ?_
      intro i _
      exact measurable_const.mul (measurable_pi_apply i)
    have hf2 : Measurable (fun h : Fin n → ℝ =>
        ∑ j : Fin n, (∑ k : Fin N, a k * y k j) * h j) := by
      refine Finset.measurable_sum Finset.univ ?_
      intro j _
      exact measurable_const.mul (measurable_pi_apply j)
    have hF : Measurable (fun w : (Fin m → ℝ) × (Fin n → ℝ) =>
        (∑ i : Fin m, (∑ k : Fin N, a k * x k i) * w.1 i)
          + (∑ j : Fin n, (∑ k : Fin N, a k * y k j) * w.2 j)) :=
      (hf1.comp measurable_fst).add (hf2.comp measurable_snd)
    have hinner_law : Measure.map (fun w : (Fin m → ℝ) × (Fin n → ℝ) =>
          (∑ i : Fin m, (∑ k : Fin N, a k * x k i) * w.1 i)
            + (∑ j : Fin n, (∑ k : Fin N, a k * y k j) * w.2 j))
        ((MeasureTheory.Measure.pi (fun _ : Fin m => ProbabilityTheory.gaussianReal 0 1)).prod
          (MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)))
        = ProbabilityTheory.gaussianReal 0 (v₁ + v₂) := by
      have hcomp : (fun w : (Fin m → ℝ) × (Fin n → ℝ) =>
            (∑ i : Fin m, (∑ k : Fin N, a k * x k i) * w.1 i)
              + (∑ j : Fin n, (∑ k : Fin N, a k * y k j) * w.2 j))
          = (fun p : ℝ × ℝ => p.1 + p.2) ∘ Prod.map
              (fun g : Fin m → ℝ => ∑ i : Fin m, (∑ k : Fin N, a k * x k i) * g i)
              (fun h : Fin n → ℝ => ∑ j : Fin n, (∑ k : Fin N, a k * y k j) * h j) := by
        funext w
        rfl
      rw [hcomp]
      rw [← MeasureTheory.Measure.map_map (measurable_fst.add measurable_snd)
        (hf1.prodMap hf2)]
      rw [← MeasureTheory.Measure.map_prod_map
        (MeasureTheory.Measure.pi (fun _ : Fin m => ProbabilityTheory.gaussianReal 0 1))
        (MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1))
        hf1 hf2, hv₁, hv₂]
      exact hadd_gauss v₁ v₂
    rw [htransfer_snd (fun w : (Fin m → ℝ) × (Fin n → ℝ) =>
        (∑ i : Fin m, (∑ k : Fin N, a k * x k i) * w.1 i)
          + (∑ j : Fin n, (∑ k : Fin N, a k * y k j) * w.2 j)) hF]
    exact hinner_law

  let ΩW : Type := (Fin m × Fin n) → ℝ
  let μW : Measure ΩW :=
    MeasureTheory.Measure.pi (fun _ : (Fin m × Fin n) => ProbabilityTheory.gaussianReal 0 1)
  let νm : Measure ((Fin m → ℝ)) :=
    MeasureTheory.Measure.pi (fun _ : Fin m => ProbabilityTheory.gaussianReal 0 1)
  let νn : Measure ((Fin n → ℝ)) :=
    MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)
  let ΩGH : Type := (Fin m → ℝ) × (Fin n → ℝ)
  let νGH : Measure ΩGH := νm.prod νn
  let ΩB : Type := ΩW × ΩGH
  let μB : Measure ΩB := μW.prod νGH

  have hfst_map' : MeasureTheory.Measure.map (Prod.fst : ΩB → ΩW) μB = μW := hfst_map
  have hsnd_map' : MeasureTheory.Measure.map (Prod.snd : ΩB → ΩGH) μB = νGH := hsnd_map
  have hfst_map_inner :
      MeasureTheory.Measure.map (Prod.fst : ΩGH → (Fin m → ℝ)) νGH = νm :=
    MeasureTheory.Measure.fst_prod
  have hsnd_map_inner :
      MeasureTheory.Measure.map (Prod.snd : ΩGH → (Fin n → ℝ)) νGH = νn :=
    MeasureTheory.Measure.snd_prod

  have hInt_fst : ∀ (F : ΩW → ℝ), MeasureTheory.Integrable F μW →
      MeasureTheory.Integrable (fun z : ΩB => F z.1) μB := by
    intro F hF
    have hF' : MeasureTheory.Integrable F (MeasureTheory.Measure.map (Prod.fst : ΩB → ΩW) μB) := by
      rw [hfst_map']
      exact hF
    exact MeasureTheory.Integrable.comp_measurable hF' measurable_fst

  have hInt_snd : ∀ (G : ΩGH → ℝ), MeasureTheory.Integrable G νGH →
      MeasureTheory.Integrable (fun z : ΩB => G z.2) μB := by
    intro G hG
    have hG' : MeasureTheory.Integrable G (MeasureTheory.Measure.map (Prod.snd : ΩB → ΩGH) μB) := by
      rw [hsnd_map']
      exact hG
    exact MeasureTheory.Integrable.comp_measurable hG' measurable_snd

  have hInt_inner_fst : ∀ (A : (Fin m → ℝ) → ℝ), MeasureTheory.Integrable A νm →
      MeasureTheory.Integrable (fun w : ΩGH => A w.1) νGH := by
    intro A hA
    have hA' : MeasureTheory.Integrable A
        (MeasureTheory.Measure.map (Prod.fst : ΩGH → (Fin m → ℝ)) νGH) := by
      rw [hfst_map_inner]
      exact hA
    exact MeasureTheory.Integrable.comp_measurable hA' measurable_fst

  have hInt_inner_snd : ∀ (B : (Fin n → ℝ) → ℝ), MeasureTheory.Integrable B νn →
      MeasureTheory.Integrable (fun w : ΩGH => B w.2) νGH := by
    intro B hB
    have hB' : MeasureTheory.Integrable B
        (MeasureTheory.Measure.map (Prod.snd : ΩGH → (Fin n → ℝ)) νGH) := by
      rw [hsnd_map_inner]
      exact hB
    exact MeasureTheory.Integrable.comp_measurable hB' measurable_snd

  have hint_fst : ∀ (F : ΩW → ℝ), MeasureTheory.Integrable F μW →
      (∫ z : ΩB, F z.1 ∂μB) = ∫ ω : ΩW, F ω ∂μW := by
    intro F hF
    have hF' : MeasureTheory.Integrable F (MeasureTheory.Measure.map (Prod.fst : ΩB → ΩW) μB) := by
      rw [hfst_map']
      exact hF
    rw [← hfst_map']
    exact (MeasureTheory.integral_map measurable_fst.aemeasurable hF'.1).symm

  have hint_snd : ∀ (G : ΩGH → ℝ), MeasureTheory.Integrable G νGH →
      (∫ z : ΩB, G z.2 ∂μB) = ∫ w : ΩGH, G w ∂νGH := by
    intro G hG
    have hG' : MeasureTheory.Integrable G (MeasureTheory.Measure.map (Prod.snd : ΩB → ΩGH) μB) := by
      rw [hsnd_map']
      exact hG
    rw [← hsnd_map']
    exact (MeasureTheory.integral_map measurable_snd.aemeasurable hG'.1).symm

  have hint_inner_fst : ∀ (A : (Fin m → ℝ) → ℝ), MeasureTheory.Integrable A νm →
      (∫ w : ΩGH, A w.1 ∂νGH) = ∫ g : Fin m → ℝ, A g ∂νm := by
    intro A hA
    have hA' : MeasureTheory.Integrable A
        (MeasureTheory.Measure.map (Prod.fst : ΩGH → (Fin m → ℝ)) νGH) := by
      rw [hfst_map_inner]
      exact hA
    rw [← hfst_map_inner]
    exact (MeasureTheory.integral_map measurable_fst.aemeasurable hA'.1).symm

  have hint_inner_snd : ∀ (B : (Fin n → ℝ) → ℝ), MeasureTheory.Integrable B νn →
      (∫ w : ΩGH, B w.2 ∂νGH) = ∫ h : Fin n → ℝ, B h ∂νn := by
    intro B hB
    have hB' : MeasureTheory.Integrable B
        (MeasureTheory.Measure.map (Prod.snd : ΩGH → (Fin n → ℝ)) νGH) := by
      rw [hsnd_map_inner]
      exact hB
    rw [← hsnd_map_inner]
    exact (MeasureTheory.integral_map measurable_snd.aemeasurable hB'.1).symm

  have hX_sq : ∀ (N : ℕ) (x : Fin N → Fin m → ℝ) (y : Fin N → Fin n → ℝ) (k : Fin N),
      MeasureTheory.Integrable (fun z : ΩB =>
        (∑ i : Fin m, ∑ j : Fin n, x k i * z.1 (i, j) * y k j) ^ 2) μB := by
    intro N x y k
    have hF : MeasureTheory.MemLp (fun ω : ΩW =>
        ∑ p : Fin m × Fin n, (x k p.1 * y k p.2) * ω p) 2
        (MeasureTheory.Measure.map (Prod.fst : ΩB → ΩW) μB) := by
      rw [hfst_map']
      exact hlin_memLp (fun p : Fin m × Fin n => x k p.1 * y k p.2)
    have hmem : MeasureTheory.MemLp (fun z : ΩB =>
        ∑ p : Fin m × Fin n, (x k p.1 * y k p.2) * z.1 p) 2 μB := by
      have hcomp : MeasureTheory.MemLp
          ((fun ω : ΩW => ∑ p : Fin m × Fin n, (x k p.1 * y k p.2) * ω p) ∘ Prod.fst) 2 μB :=
        MeasureTheory.MemLp.comp_of_map hF measurable_fst.aemeasurable
      simpa using hcomp
    have hfun : (fun z : ΩB =>
          (∑ i : Fin m, ∑ j : Fin n, x k i * z.1 (i, j) * y k j) ^ 2)
        = fun z : ΩB => (∑ p : Fin m × Fin n, (x k p.1 * y k p.2) * z.1 p) ^ 2 := by
      funext z
      have hstep : (∑ i : Fin m, ∑ j : Fin n, x k i * z.1 (i, j) * y k j)
          = ∑ p : Fin m × Fin n, (x k p.1 * y k p.2) * z.1 p := by
        rw [← hbilin_eq N x y k z.1]
        exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
      rw [hstep]
    rw [hfun]
    exact MeasureTheory.MemLp.integrable_sq hmem

  have hY_sq : ∀ (N : ℕ) (x : Fin N → Fin m → ℝ) (y : Fin N → Fin n → ℝ) (k : Fin N),
      MeasureTheory.Integrable (fun z : ΩB =>
        ((∑ i : Fin m, x k i * z.2.1 i) + (∑ j : Fin n, y k j * z.2.2 j)) ^ 2) μB := by
    intro N x y k
    have hAmem : MeasureTheory.MemLp (fun g : Fin m → ℝ => ∑ i : Fin m, x k i * g i) 2 νm :=
      hlin_memLp (fun i : Fin m => x k i)
    have hBmem : MeasureTheory.MemLp (fun h : Fin n → ℝ => ∑ j : Fin n, y k j * h j) 2 νn :=
      hlin_memLp (fun j : Fin n => y k j)
    have hAmemGH : MeasureTheory.MemLp (fun w : ΩGH => ∑ i : Fin m, x k i * w.1 i) 2 νGH := by
      have h' : MeasureTheory.MemLp (fun g : Fin m → ℝ => ∑ i : Fin m, x k i * g i) 2
          (MeasureTheory.Measure.map (Prod.fst : ΩGH → (Fin m → ℝ)) νGH) := by
        rw [hfst_map_inner]
        exact hAmem
      have hcomp : MeasureTheory.MemLp
          ((fun g : Fin m → ℝ => ∑ i : Fin m, x k i * g i) ∘ Prod.fst) 2 νGH :=
        MeasureTheory.MemLp.comp_of_map h' measurable_fst.aemeasurable
      simpa using hcomp
    have hBmemGH : MeasureTheory.MemLp (fun w : ΩGH => ∑ j : Fin n, y k j * w.2 j) 2 νGH := by
      have h' : MeasureTheory.MemLp (fun h : Fin n → ℝ => ∑ j : Fin n, y k j * h j) 2
          (MeasureTheory.Measure.map (Prod.snd : ΩGH → (Fin n → ℝ)) νGH) := by
        rw [hsnd_map_inner]
        exact hBmem
      have hcomp : MeasureTheory.MemLp
          ((fun h : Fin n → ℝ => ∑ j : Fin n, y k j * h j) ∘ Prod.snd) 2 νGH :=
        MeasureTheory.MemLp.comp_of_map h' measurable_snd.aemeasurable
      simpa using hcomp
    have hWmem : MeasureTheory.MemLp (fun w : ΩGH =>
        (∑ i : Fin m, x k i * w.1 i) + (∑ j : Fin n, y k j * w.2 j)) 2 νGH :=
      hAmemGH.add hBmemGH
    have hmem : MeasureTheory.MemLp (fun z : ΩB =>
        (∑ i : Fin m, x k i * z.2.1 i) + (∑ j : Fin n, y k j * z.2.2 j)) 2 μB := by
      have h' : MeasureTheory.MemLp (fun w : ΩGH =>
          (∑ i : Fin m, x k i * w.1 i) + (∑ j : Fin n, y k j * w.2 j)) 2
          (MeasureTheory.Measure.map (Prod.snd : ΩB → ΩGH) μB) := by
        rw [hsnd_map']
        exact hWmem
      have hcomp : MeasureTheory.MemLp
          ((fun w : ΩGH =>
            (∑ i : Fin m, x k i * w.1 i) + (∑ j : Fin n, y k j * w.2 j)) ∘ Prod.snd) 2 μB :=
        MeasureTheory.MemLp.comp_of_map h' measurable_snd.aemeasurable
      simpa using hcomp
    exact MeasureTheory.MemLp.integrable_sq hmem

  have hid_gauss : ∀ v : NNReal, MeasureTheory.Integrable (fun x : ℝ => x)
      (ProbabilityTheory.gaussianReal 0 v) := by
    intro v
    have hmem1 : MeasureTheory.MemLp (fun x : ℝ => x) 1 (ProbabilityTheory.gaussianReal 0 v) := by
      simpa using Statlib.StatFoundation.RandomVariable.Gaussian.memLp_pow_id_gaussianReal
        (μ₀ := (0 : ℝ)) (v := v) 1 1 (by simp)
    exact MeasureTheory.memLp_one_iff_integrable.mp hmem1

  have hlin_int : ∀ {s : ℕ} (c : Fin s → ℝ),
      MeasureTheory.Integrable (fun g : Fin s → ℝ => ∑ i : Fin s, c i * g i)
        (MeasureTheory.Measure.pi (fun _ : Fin s => ProbabilityTheory.gaussianReal 0 1)) := by
    intro s c
    obtain ⟨v, hv⟩ := hgauss_general c
    have hmeas : Measurable (fun g : Fin s → ℝ => ∑ i : Fin s, c i * g i) := by
      refine Finset.measurable_sum Finset.univ ?_
      intro i _
      exact measurable_const.mul (measurable_pi_apply i)
    have hmapint : MeasureTheory.Integrable (fun x : ℝ => x)
        (MeasureTheory.Measure.map (fun g : Fin s → ℝ => ∑ i : Fin s, c i * g i)
          (MeasureTheory.Measure.pi (fun _ : Fin s => ProbabilityTheory.gaussianReal 0 1))) := by
      rw [hv]
      exact hid_gauss v
    exact (MeasureTheory.integrable_map_measure measurable_id.aestronglyMeasurable
      hmeas.aemeasurable).mp hmapint

  have hmean_lin : ∀ {s : ℕ} (c : Fin s → ℝ),
      (∫ g : Fin s → ℝ, ∑ i : Fin s, c i * g i
        ∂(MeasureTheory.Measure.pi (fun _ : Fin s => ProbabilityTheory.gaussianReal 0 1))) = 0 := by
    intro s c
    obtain ⟨v, hv⟩ := hgauss_general c
    have hmeas : Measurable (fun g : Fin s → ℝ => ∑ i : Fin s, c i * g i) := by
      refine Finset.measurable_sum Finset.univ ?_
      intro i _
      exact measurable_const.mul (measurable_pi_apply i)
    have hzero : (∫ x : ℝ, x ∂(ProbabilityTheory.gaussianReal 0 v)) = 0 := by
      simpa using ProbabilityTheory.integral_id_gaussianReal (μ := (0 : ℝ)) (v := v)
    have hkey : (∫ x : ℝ, x
        ∂(MeasureTheory.Measure.map (fun g : Fin s → ℝ => ∑ i : Fin s, c i * g i)
          (MeasureTheory.Measure.pi (fun _ : Fin s => ProbabilityTheory.gaussianReal 0 1))))
        = ∫ g : Fin s → ℝ, ∑ i : Fin s, c i * g i
          ∂(MeasureTheory.Measure.pi (fun _ : Fin s => ProbabilityTheory.gaussianReal 0 1)) :=
      MeasureTheory.integral_map hmeas.aemeasurable
        (Measurable.aestronglyMeasurable (measurable_id : Measurable fun x : ℝ => x))
    rw [← hkey, hv]
    exact hzero

  have hYmemGH : ∀ (N : ℕ) (x : Fin N → Fin m → ℝ) (y : Fin N → Fin n → ℝ) (k : Fin N),
      MeasureTheory.MemLp (fun w : ΩGH =>
        (∑ i : Fin m, x k i * w.1 i) + (∑ j : Fin n, y k j * w.2 j)) 2 νGH := by
    intro N x y k
    have hA : MeasureTheory.MemLp (fun w : ΩGH => ∑ i : Fin m, x k i * w.1 i) 2 νGH := by
      have h' : MeasureTheory.MemLp (fun g : Fin m → ℝ => ∑ i : Fin m, x k i * g i) 2
          (MeasureTheory.Measure.map (Prod.fst : ΩGH → (Fin m → ℝ)) νGH) := by
        rw [hfst_map_inner]
        exact hlin_memLp (fun i : Fin m => x k i)
      have hc : MeasureTheory.MemLp
          ((fun g : Fin m → ℝ => ∑ i : Fin m, x k i * g i) ∘ Prod.fst) 2 νGH :=
        MeasureTheory.MemLp.comp_of_map h' measurable_fst.aemeasurable
      simpa using hc
    have hB : MeasureTheory.MemLp (fun w : ΩGH => ∑ j : Fin n, y k j * w.2 j) 2 νGH := by
      have h' : MeasureTheory.MemLp (fun h : Fin n → ℝ => ∑ j : Fin n, y k j * h j) 2
          (MeasureTheory.Measure.map (Prod.snd : ΩGH → (Fin n → ℝ)) νGH) := by
        rw [hsnd_map_inner]
        exact hlin_memLp (fun j : Fin n => y k j)
      have hc : MeasureTheory.MemLp
          ((fun h : Fin n → ℝ => ∑ j : Fin n, y k j * h j) ∘ Prod.snd) 2 νGH :=
        MeasureTheory.MemLp.comp_of_map h' measurable_snd.aemeasurable
      simpa using hc
    exact hA.add hB

  have hSum_map : MeasureTheory.Measure.map
      (⇑(MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n => ℝ)))
      (MeasureTheory.Measure.pi (fun _ : Fin m ⊕ Fin n => ProbabilityTheory.gaussianReal 0 1))
      = νGH :=
    (MeasureTheory.measurePreserving_sumPiEquivProdPi
      (fun _ : Fin m ⊕ Fin n => ProbabilityTheory.gaussianReal 0 1)).map_eq

  have hYcov : ∀ (N : ℕ) (x : Fin N → Fin m → ℝ) (y : Fin N → Fin n → ℝ) (k l : Fin N),
      (∫ z : ΩB,
        ((∑ i : Fin m, x k i * z.2.1 i) + (∑ j : Fin n, y k j * z.2.2 j))
          * ((∑ i : Fin m, x l i * z.2.1 i) + (∑ j : Fin n, y l j * z.2.2 j))
        ∂μB)
      = (∑ i : Fin m, x k i * x l i) + (∑ j : Fin n, y k j * y l j) := by
    intro N x y k l
    have hmemGH : MeasureTheory.Integrable (fun w : ΩGH =>
        ((∑ i : Fin m, x k i * w.1 i) + (∑ j : Fin n, y k j * w.2 j))
          * ((∑ i : Fin m, x l i * w.1 i) + (∑ j : Fin n, y l j * w.2 j))) νGH :=
      MeasureTheory.MemLp.integrable (q := 1) (by norm_num)
        ((hYmemGH N x y l).mul (hYmemGH N x y k))
    have hcomp : (∫ u : Fin m ⊕ Fin n → ℝ,
        (fun w : ΩGH =>
          ((∑ i : Fin m, x k i * w.1 i) + (∑ j : Fin n, y k j * w.2 j))
            * ((∑ i : Fin m, x l i * w.1 i) + (∑ j : Fin n, y l j * w.2 j)))
          (⇑(MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n => ℝ)) u)
        ∂(MeasureTheory.Measure.pi (fun _ : Fin m ⊕ Fin n => ProbabilityTheory.gaussianReal 0 1)))
        = ∫ w : ΩGH,
          ((∑ i : Fin m, x k i * w.1 i) + (∑ j : Fin n, y k j * w.2 j))
            * ((∑ i : Fin m, x l i * w.1 i) + (∑ j : Fin n, y l j * w.2 j)) ∂νGH := by
      rw [← hSum_map]
      exact (MeasureTheory.integral_map_equiv
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n => ℝ))
        (fun w : ΩGH =>
          ((∑ i : Fin m, x k i * w.1 i) + (∑ j : Fin n, y k j * w.2 j))
            * ((∑ i : Fin m, x l i * w.1 i) + (∑ j : Fin n, y l j * w.2 j)))).symm
    have hlaw : (∫ u : Fin m ⊕ Fin n → ℝ,
        (fun w : ΩGH =>
          ((∑ i : Fin m, x k i * w.1 i) + (∑ j : Fin n, y k j * w.2 j))
            * ((∑ i : Fin m, x l i * w.1 i) + (∑ j : Fin n, y l j * w.2 j)))
          (⇑(MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n => ℝ)) u)
        ∂(MeasureTheory.Measure.pi (fun _ : Fin m ⊕ Fin n => ProbabilityTheory.gaussianReal 0 1)))
        = (∑ i : Fin m, x k i * x l i) + (∑ j : Fin n, y k j * y l j) := by
      have hpt : (fun u : Fin m ⊕ Fin n → ℝ =>
          (fun w : ΩGH =>
            ((∑ i : Fin m, x k i * w.1 i) + (∑ j : Fin n, y k j * w.2 j))
              * ((∑ i : Fin m, x l i * w.1 i) + (∑ j : Fin n, y l j * w.2 j)))
            (⇑(MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n => ℝ)) u))
          = fun u : Fin m ⊕ Fin n → ℝ =>
            (∑ p : Fin m ⊕ Fin n, Sum.elim (x k) (y k) p * u p)
              * (∑ p : Fin m ⊕ Fin n, Sum.elim (x l) (y l) p * u p) := by
        funext u
        have h1 : ∀ i : Fin m,
            ((⇑(MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n => ℝ))) u).1 i
              = u (Sum.inl i) := fun i => rfl
        have h2 : ∀ j : Fin n,
            ((⇑(MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n => ℝ))) u).2 j
              = u (Sum.inr j) := fun j => rfl
        simp [h1, h2, Fintype.sum_sum_type]
      rw [hpt, hcov (Sum.elim (x k) (y k)) (Sum.elim (x l) (y l))]
      rw [Fintype.sum_sum_type]
      simp
    exact (hint_snd (fun w : ΩGH =>
        ((∑ i : Fin m, x k i * w.1 i) + (∑ j : Fin n, y k j * w.2 j))
          * ((∑ i : Fin m, x l i * w.1 i) + (∑ j : Fin n, y l j * w.2 j))) hmemGH).trans
      (hcomp.symm.trans hlaw)

  have hbilin_eq2 : ∀ (N : ℕ) (x : Fin N → Fin m → ℝ) (y : Fin N → Fin n → ℝ) (k : Fin N)
      (ω : (Fin m × Fin n) → ℝ),
      (∑ i : Fin m, ∑ j : Fin n, x k i * ω (i, j) * y k j)
        = ∑ p : Fin m × Fin n, (x k p.1 * y k p.2) * ω p := by
    intro N x y k ω
    rw [← hbilin_eq N x y k ω]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

  have hXint : ∀ (N : ℕ) (x : Fin N → Fin m → ℝ) (y : Fin N → Fin n → ℝ) (k l : Fin N),
      (∫ z : ΩB,
        (∑ i : Fin m, ∑ j : Fin n, x k i * z.1 (i, j) * y k j)
          * (∑ i : Fin m, ∑ j : Fin n, x l i * z.1 (i, j) * y l j) ∂μB)
      = (∑ i : Fin m, x k i * x l i) * (∑ j : Fin n, y k j * y l j) := by
    intro N x y k l
    have hF : MeasureTheory.Integrable (fun ω : ΩW =>
        (∑ i : Fin m, ∑ j : Fin n, x k i * ω (i, j) * y k j)
          * (∑ i : Fin m, ∑ j : Fin n, x l i * ω (i, j) * y l j)) μW := by
      have h1 : (fun ω : ΩW =>
          (∑ i : Fin m, ∑ j : Fin n, x k i * ω (i, j) * y k j)
            * (∑ i : Fin m, ∑ j : Fin n, x l i * ω (i, j) * y l j))
          = fun ω : ΩW => (∑ p : Fin m × Fin n, (x k p.1 * y k p.2) * ω p)
            * (∑ p : Fin m × Fin n, (x l p.1 * y l p.2) * ω p) := by
        funext ω
        rw [hbilin_eq2 N x y k ω, hbilin_eq2 N x y l ω]
      rw [h1]
      exact hprod_int (fun p : Fin m × Fin n => x k p.1 * y k p.2)
        (fun p : Fin m × Fin n => x l p.1 * y l p.2)
    have hFT : (∫ ω : ΩW,
        (∑ i : Fin m, ∑ j : Fin n, x k i * ω (i, j) * y k j)
          * (∑ i : Fin m, ∑ j : Fin n, x l i * ω (i, j) * y l j) ∂μW)
        = (∑ i : Fin m, x k i * x l i) * (∑ j : Fin n, y k j * y l j) := by
      have h1 : (fun ω : ΩW =>
          (∑ i : Fin m, ∑ j : Fin n, x k i * ω (i, j) * y k j)
            * (∑ i : Fin m, ∑ j : Fin n, x l i * ω (i, j) * y l j))
          = fun ω : ΩW =>
            (∑ i : Fin m, ∑ j : Fin n, x k i * y k j * ω (i, j))
              * (∑ i : Fin m, ∑ j : Fin n, x l i * y l j * ω (i, j)) := by
        funext ω
        rw [hbilin_eq2 N x y k ω, hbilin_eq2 N x y l ω, ← hbilin_eq N x y k ω,
          ← hbilin_eq N x y l ω]
      rw [h1]
      exact hbilin_cov N x y k l
    exact (hint_fst (fun ω : ΩW =>
        (∑ i : Fin m, ∑ j : Fin n, x k i * ω (i, j) * y k j)
          * (∑ i : Fin m, ∑ j : Fin n, x l i * ω (i, j) * y l j)) hF).trans hFT

  have hincr : ∀ (N : ℕ) (x : Fin N → Fin m → ℝ) (y : Fin N → Fin n → ℝ),
      (∀ k : Fin N, (∑ i : Fin m, (x k i) ^ 2) = 1) →
      (∀ k : Fin N, (∑ j : Fin n, (y k j) ^ 2) = 1) →
      ∀ k l : Fin N,
        (∫ z : ΩB,
          (∑ i : Fin m, ∑ j : Fin n, x k i * z.1 (i, j) * y k j)
            * (∑ i : Fin m, ∑ j : Fin n, x k i * z.1 (i, j) * y k j) ∂μB)
          + (∫ z : ΩB,
            (∑ i : Fin m, ∑ j : Fin n, x l i * z.1 (i, j) * y l j)
              * (∑ i : Fin m, ∑ j : Fin n, x l i * z.1 (i, j) * y l j) ∂μB)
          - 2 * (∫ z : ΩB,
            (∑ i : Fin m, ∑ j : Fin n, x k i * z.1 (i, j) * y k j)
              * (∑ i : Fin m, ∑ j : Fin n, x l i * z.1 (i, j) * y l j) ∂μB)
        ≤ (∫ z : ΩB,
            ((∑ i : Fin m, x k i * z.2.1 i) + (∑ j : Fin n, y k j * z.2.2 j))
              * ((∑ i : Fin m, x k i * z.2.1 i) + (∑ j : Fin n, y k j * z.2.2 j)) ∂μB)
          + (∫ z : ΩB,
            ((∑ i : Fin m, x l i * z.2.1 i) + (∑ j : Fin n, y l j * z.2.2 j))
              * ((∑ i : Fin m, x l i * z.2.1 i) + (∑ j : Fin n, y l j * z.2.2 j)) ∂μB)
          - 2 * (∫ z : ΩB,
            ((∑ i : Fin m, x k i * z.2.1 i) + (∑ j : Fin n, y k j * z.2.2 j))
              * ((∑ i : Fin m, x l i * z.2.1 i) + (∑ j : Fin n, y l j * z.2.2 j)) ∂μB) := by
    intro N x y hx hy k l
    have e1 : (∑ i : Fin m, x k i * x k i) = 1 := by
      rw [← hx k]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have e2 : (∑ i : Fin m, x l i * x l i) = 1 := by
      rw [← hx l]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have e3 : (∑ j : Fin n, y k j * y k j) = 1 := by
      rw [← hy k]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have e4 : (∑ j : Fin n, y l j * y l j) = 1 := by
      rw [← hy l]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have hLHS : (∫ z : ΩB,
          (∑ i : Fin m, ∑ j : Fin n, x k i * z.1 (i, j) * y k j)
            * (∑ i : Fin m, ∑ j : Fin n, x k i * z.1 (i, j) * y k j) ∂μB)
          + (∫ z : ΩB,
            (∑ i : Fin m, ∑ j : Fin n, x l i * z.1 (i, j) * y l j)
              * (∑ i : Fin m, ∑ j : Fin n, x l i * z.1 (i, j) * y l j) ∂μB)
          - 2 * (∫ z : ΩB,
            (∑ i : Fin m, ∑ j : Fin n, x k i * z.1 (i, j) * y k j)
              * (∑ i : Fin m, ∑ j : Fin n, x l i * z.1 (i, j) * y l j) ∂μB)
        = 2 - 2 * ((∑ i : Fin m, x k i * x l i) * (∑ j : Fin n, y k j * y l j)) := by
      rw [hXint N x y k k, hXint N x y l l, hXint N x y k l, e1, e2, e3, e4]
      ring
    have hRHS : (∫ z : ΩB,
            ((∑ i : Fin m, x k i * z.2.1 i) + (∑ j : Fin n, y k j * z.2.2 j))
              * ((∑ i : Fin m, x k i * z.2.1 i) + (∑ j : Fin n, y k j * z.2.2 j)) ∂μB)
          + (∫ z : ΩB,
            ((∑ i : Fin m, x l i * z.2.1 i) + (∑ j : Fin n, y l j * z.2.2 j))
              * ((∑ i : Fin m, x l i * z.2.1 i) + (∑ j : Fin n, y l j * z.2.2 j)) ∂μB)
          - 2 * (∫ z : ΩB,
            ((∑ i : Fin m, x k i * z.2.1 i) + (∑ j : Fin n, y k j * z.2.2 j))
              * ((∑ i : Fin m, x l i * z.2.1 i) + (∑ j : Fin n, y l j * z.2.2 j)) ∂μB)
        = 4 - 2 * (∑ i : Fin m, x k i * x l i) - 2 * (∑ j : Fin n, y k j * y l j) := by
      rw [hYcov N x y k k, hYcov N x y l l, hYcov N x y k l, e1, e2, e3, e4]
      ring
    rw [hLHS, hRHS]
    have hdx := (hdot_bounds m (x k) (x l) (hx k) (hx l)).1
    have hdy := (hdot_bounds n (y k) (y l) (hy k) (hy l)).1
    nlinarith [hdx, hdy,
      mul_nonneg (by linarith : (0:ℝ) ≤ 1 - ∑ i : Fin m, x k i * x l i)
        (by linarith : (0:ℝ) ≤ 1 - ∑ j : Fin n, y k j * y l j)]

  have hnet : ∀ (δ : ℝ), 0 < δ → δ < 1 / 4 →
      ∃ (N : ℕ) (hN : 1 ≤ N) (x : Fin N → Fin m → ℝ) (y : Fin N → Fin n → ℝ),
        (∀ k : Fin N, (∑ i : Fin m, (x k i) ^ 2) = 1) ∧
        (∀ k : Fin N, (∑ j : Fin n, (y k j) ^ 2) = 1) ∧
        (∀ (u : Fin m → ℝ) (v : Fin n → ℝ),
          (∑ i : Fin m, (u i) ^ 2) = 1 → (∑ j : Fin n, (v j) ^ 2) = 1 →
          ∃ k : Fin N,
            (∑ i : Fin m, (x k i - u i) ^ 2) ≤ δ ^ 2 ∧
            (∑ j : Fin n, (y k j - v j) ^ 2) ≤ δ ^ 2) ∧
        (∀ z : ΩB, ‖Matrix.of (fun i j => z.1 (i, j))‖ ≤ (1 - 2 * δ)⁻¹ *
          (⨆ k : Fin N, ∑ i : Fin m, ∑ j : Fin n, x k i * z.1 (i, j) * y k j)) := by
    intro δ hδ hδ4
    obtain ⟨N, hN, x, y, hx, hy, hcov', hM⟩ :=
      statopia_math_node_2221798330_49ffe8bf m n hm hn δ hδ hδ4
    exact ⟨N, hN, x, y, hx, hy, hcov', fun z => hM (Matrix.of (fun i j => z.1 (i, j)))⟩

  have hYpt : ∀ (N : ℕ) (hN : 1 ≤ N) (x : Fin N → Fin m → ℝ) (y : Fin N → Fin n → ℝ),
      (∀ k : Fin N, (∑ i : Fin m, (x k i) ^ 2) = 1) →
      (∀ k : Fin N, (∑ j : Fin n, (y k j) ^ 2) = 1) →
      ∀ z : ΩB,
        (⨆ k : Fin N, ((∑ i : Fin m, x k i * z.2.1 i) + (∑ j : Fin n, y k j * z.2.2 j)))
          ≤ Real.sqrt (∑ i : Fin m, (z.2.1 i) ^ 2) + Real.sqrt (∑ j : Fin n, (z.2.2 j) ^ 2) := by
    intro N hN x y hx hy z
    haveI hne : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
    refine ciSup_le (fun k => ?_)
    have h1 := hcauchy m (x k) (fun i : Fin m => z.2.1 i) (hx k)
    have h2 := hcauchy n (y k) (fun j : Fin n => z.2.2 j) (hy k)
    linarith

  have hSFstep : ∀ (N : ℕ) (hN : 1 ≤ N) (x : Fin N → Fin m → ℝ) (y : Fin N → Fin n → ℝ),
      (∀ k : Fin N, (∑ i : Fin m, (x k i) ^ 2) = 1) →
      (∀ k : Fin N, (∑ j : Fin n, (y k j) ^ 2) = 1) →
      (∫ z : ΩB, (⨆ k : Fin N, ∑ i : Fin m, ∑ j : Fin n, x k i * z.1 (i, j) * y k j) ∂μB)
        ≤ (∫ z : ΩB,
            (⨆ k : Fin N,
              ((∑ i : Fin m, x k i * z.2.1 i) + (∑ j : Fin n, y k j * z.2.2 j))) ∂μB) := by
    intro N hN x y hx hy
    exact statopia_math_node_3027071526_9b78d881 μB N hN
      (fun z k => ∑ i : Fin m, ∑ j : Fin n, x k i * z.1 (i, j) * y k j)
      (fun z k => (∑ i : Fin m, x k i * z.2.1 i) + (∑ j : Fin n, y k j * z.2.2 j))
      (fun k => measurable_pi_iff.mp (hXmeas N x y) k)
      (fun k => measurable_pi_iff.mp ((hYmeas N x y).comp measurable_snd) k)
      (fun k => hX_sq N x y k)
      (fun k => hY_sq N x y k)
      (fun a => hXgauss N x y a)
      (fun a => hYgauss N x y a)
      (hIndepXY N x y)
      (hincr N x y hx hy)

  have hprobe_mono : MeasureTheory.Integrable (fun _ : ΩB => (0 : ℝ)) μB := by
    have h1 : MeasureTheory.Integrable (fun _ : ΩB => (1 : ℝ)) μB := integrable_const 1
    refine h1.mono ?_ ?_
    · exact Measurable.aestronglyMeasurable measurable_const
    · exact Filter.Eventually.of_forall (fun z => by simp)

  have hptW : ∀ (δ : ℝ) (hδ : 0 < δ) (hδ4 : δ < 1 / 4),
      ∃ (N : ℕ) (hN : 1 ≤ N) (x : Fin N → Fin m → ℝ) (y : Fin N → Fin n → ℝ),
        (∀ k : Fin N, (∑ i : Fin m, (x k i) ^ 2) = 1) ∧
        (∀ k : Fin N, (∑ j : Fin n, (y k j) ^ 2) = 1) ∧
        (∀ ω : (Fin m × Fin n) → ℝ,
          ‖Matrix.of (fun i j => ω (i, j))‖ ≤ (1 - 2 * δ)⁻¹ *
            (⨆ k : Fin N, ∑ i : Fin m, ∑ j : Fin n, x k i * ω (i, j) * y k j)) := by
    intro δ hδ hδ4
    obtain ⟨N, hN, x, y, hx, hy, hcov', hM⟩ := hnet δ hδ hδ4
    exact ⟨N, hN, x, y, hx, hy,
      fun ω => hM (ω, ((fun _ => (0 : ℝ)), (fun _ => (0 : ℝ))))⟩

  have supInt_general : ∀ (N : ℕ) (hN : 1 ≤ N) (F : ΩB → Fin N → ℝ),
      (∀ k : Fin N, Measurable fun z => F z k) →
      (∀ k : Fin N, MeasureTheory.Integrable (fun z => (F z k) ^ 2) μB) →
      MeasureTheory.Integrable (fun z => ⨆ k : Fin N, F z k) μB := by
    intro N hN F hFmeas hFsq
    haveI hne : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    have hD : MeasureTheory.Integrable (fun z : ΩB => ∑ k : Fin N, (1 + (F z k) ^ 2)) μB :=
      MeasureTheory.integrable_finset_sum Finset.univ
        (fun k _ => (integrable_const (1 : ℝ)).add (hFsq k))
    refine hD.mono ?_ ?_
    · exact Measurable.aestronglyMeasurable (Measurable.iSup (fun k => hFmeas k))
    · refine Filter.Eventually.of_forall (fun z => ?_)
      have hupper : (⨆ k : Fin N, F z k) ≤ ∑ k : Fin N, (1 + (F z k) ^ 2) := by
        refine ciSup_le (fun k => ?_)
        have h1 : F z k ≤ 1 + (F z k) ^ 2 := by
          nlinarith [sq_nonneg (F z k - 1 / 2)]
        exact h1.trans (Finset.single_le_sum (f := fun k : Fin N => 1 + (F z k) ^ 2)
          (fun k _ => by positivity) (Finset.mem_univ k))
      have hle_sup : F z ⟨0, hN⟩ ≤ ⨆ k : Fin N, F z k :=
        le_ciSup (f := fun k : Fin N => F z k) (Set.finite_range _).bddAbove ⟨0, hN⟩
      have hlow : -(∑ k : Fin N, (1 + (F z k) ^ 2)) ≤ F z ⟨0, hN⟩ := by
        have hsingle : (1 + (F z ⟨0, hN⟩) ^ 2) ≤ ∑ k : Fin N, (1 + (F z k) ^ 2) :=
          Finset.single_le_sum (f := fun k : Fin N => 1 + (F z k) ^ 2)
            (fun k _ => by positivity) (Finset.mem_univ (⟨0, hN⟩ : Fin N))
        nlinarith [sq_nonneg (F z ⟨0, hN⟩ + 1 / 2)]
      have hDnn : (0 : ℝ) ≤ ∑ k : Fin N, (1 + (F z k) ^ 2) :=
        Finset.sum_nonneg (fun k _ => by positivity)
      have habs : |(⨆ k : Fin N, F z k)| ≤ |(∑ k : Fin N, (1 + (F z k) ^ 2))| := by
        rw [abs_of_nonneg hDnn]
        rcases le_total 0 (⨆ k : Fin N, F z k) with hs | hs
        · rwa [abs_of_nonneg hs]
        · rw [abs_of_nonpos hs]
          linarith
      calc ‖(⨆ k : Fin N, F z k)‖ = |(⨆ k : Fin N, F z k)| := Real.norm_eq_abs _
        _ ≤ |(∑ k : Fin N, (1 + (F z k) ^ 2))| := habs
        _ = ‖(∑ k : Fin N, (1 + (F z k) ^ 2))‖ := (Real.norm_eq_abs _).symm

  have hsupX_int : ∀ (N : ℕ) (hN : 1 ≤ N) (x : Fin N → Fin m → ℝ) (y : Fin N → Fin n → ℝ),
      MeasureTheory.Integrable (fun z : ΩB =>
        ⨆ k : Fin N, ∑ i : Fin m, ∑ j : Fin n, x k i * z.1 (i, j) * y k j) μB := by
    intro N hN x y
    exact supInt_general N hN
      (fun z k => ∑ i : Fin m, ∑ j : Fin n, x k i * z.1 (i, j) * y k j)
      (fun k => measurable_pi_iff.mp (hXmeas N x y) k)
      (fun k => hX_sq N x y k)

  have hcoordsq_m : ∀ i : Fin m, MeasureTheory.Integrable (fun g : Fin m → ℝ => (g i) ^ 2) νm := by
    intro i
    have h := hlin_sq_int (fun j : Fin m => if j = i then (1 : ℝ) else 0)
    have h' : (fun g : Fin m → ℝ => (∑ j : Fin m, (if j = i then (1 : ℝ) else 0) * g j) ^ 2)
        = fun g : Fin m → ℝ => (g i) ^ 2 := by
      funext g
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [hj]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    rwa [h'] at h

  have hcoordsq_n : ∀ j : Fin n, MeasureTheory.Integrable (fun h : Fin n → ℝ => (h j) ^ 2) νn := by
    intro j
    have h := hlin_sq_int (fun k : Fin n => if k = j then (1 : ℝ) else 0)
    have h' : (fun h : Fin n → ℝ => (∑ k : Fin n, (if k = j then (1 : ℝ) else 0) * h k) ^ 2)
        = fun h : Fin n → ℝ => (h j) ^ 2 := by
      funext h
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hk
        simp [hk]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    rwa [h'] at h

  have hsqrtm_int : MeasureTheory.Integrable
      (fun g : Fin m → ℝ => Real.sqrt (∑ i : Fin m, (g i) ^ 2)) νm := by
    have hdom : MeasureTheory.Integrable (fun g : Fin m → ℝ => 1 + ∑ i : Fin m, (g i) ^ 2) νm :=
      (integrable_const (1 : ℝ)).add
        (MeasureTheory.integrable_finset_sum Finset.univ (fun i _ => hcoordsq_m i))
    refine hdom.mono ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      exact Real.continuous_sqrt.measurable.comp
        (Finset.measurable_sum Finset.univ (fun i _ => by
          simpa [pow_two] using (measurable_pi_apply i).mul (measurable_pi_apply i)))
    · refine Filter.Eventually.of_forall (fun g => ?_)
      have hx0 : (0 : ℝ) ≤ ∑ i : Fin m, (g i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
      have hsq : (∑ i : Fin m, (g i) ^ 2) ≤ (1 + ∑ i : Fin m, (g i) ^ 2) ^ 2 := by
        nlinarith [hx0, sq_nonneg (∑ i : Fin m, (g i) ^ 2)]
      have hnn : (0 : ℝ) ≤ 1 + ∑ i : Fin m, (g i) ^ 2 := by linarith
      have hl : Real.sqrt (∑ i : Fin m, (g i) ^ 2) ≤ 1 + ∑ i : Fin m, (g i) ^ 2 :=
        (Real.sqrt_le_sqrt hsq).trans_eq (Real.sqrt_sq hnn)
      have e1 : ‖Real.sqrt (∑ i : Fin m, (g i) ^ 2)‖ = Real.sqrt (∑ i : Fin m, (g i) ^ 2) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      have e2 : ‖(1 : ℝ) + ∑ i : Fin m, (g i) ^ 2‖ = 1 + ∑ i : Fin m, (g i) ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      rw [e1, e2]
      exact hl

  have hsqrtn_int : MeasureTheory.Integrable
      (fun h : Fin n → ℝ => Real.sqrt (∑ j : Fin n, (h j) ^ 2)) νn := by
    have hdom : MeasureTheory.Integrable (fun h : Fin n → ℝ => 1 + ∑ j : Fin n, (h j) ^ 2) νn :=
      (integrable_const (1 : ℝ)).add
        (MeasureTheory.integrable_finset_sum Finset.univ (fun j _ => hcoordsq_n j))
    refine hdom.mono ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      exact Real.continuous_sqrt.measurable.comp
        (Finset.measurable_sum Finset.univ (fun j _ => by
          simpa [pow_two] using (measurable_pi_apply j).mul (measurable_pi_apply j)))
    · refine Filter.Eventually.of_forall (fun h => ?_)
      have hx0 : (0 : ℝ) ≤ ∑ j : Fin n, (h j) ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
      have hsq : (∑ j : Fin n, (h j) ^ 2) ≤ (1 + ∑ j : Fin n, (h j) ^ 2) ^ 2 := by
        nlinarith [hx0, sq_nonneg (∑ j : Fin n, (h j) ^ 2)]
      have hnn : (0 : ℝ) ≤ 1 + ∑ j : Fin n, (h j) ^ 2 := by linarith
      have hl : Real.sqrt (∑ j : Fin n, (h j) ^ 2) ≤ 1 + ∑ j : Fin n, (h j) ^ 2 :=
        (Real.sqrt_le_sqrt hsq).trans_eq (Real.sqrt_sq hnn)
      have e1 : ‖Real.sqrt (∑ j : Fin n, (h j) ^ 2)‖ = Real.sqrt (∑ j : Fin n, (h j) ^ 2) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      have e2 : ‖(1 : ℝ) + ∑ j : Fin n, (h j) ^ 2‖ = 1 + ∑ j : Fin n, (h j) ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      rw [e1, e2]
      exact hl

  have hAsqrtGH : MeasureTheory.Integrable
      (fun w : ΩGH => Real.sqrt (∑ i : Fin m, (w.1 i) ^ 2)) νGH :=
    hInt_inner_fst _ hsqrtm_int

  have hBsqrtGH : MeasureTheory.Integrable
      (fun w : ΩGH => Real.sqrt (∑ j : Fin n, (w.2 j) ^ 2)) νGH :=
    hInt_inner_snd _ hsqrtn_int

  have hAint : MeasureTheory.Integrable
      (fun z : ΩB => Real.sqrt (∑ i : Fin m, (z.2.1 i) ^ 2)) μB :=
    hInt_snd _ hAsqrtGH

  have hBint : MeasureTheory.Integrable
      (fun z : ΩB => Real.sqrt (∑ j : Fin n, (z.2.2 j) ^ 2)) μB :=
    hInt_snd _ hBsqrtGH

  have hLintB : MeasureTheory.Integrable (fun z : ΩB =>
      Real.sqrt (∑ i : Fin m, (z.2.1 i) ^ 2) + Real.sqrt (∑ j : Fin n, (z.2.2 j) ^ 2)) μB :=
    hAint.add hBint

  have hAval : (∫ z : ΩB, Real.sqrt (∑ i : Fin m, (z.2.1 i) ^ 2) ∂μB)
      ≤ Real.sqrt (m : ℝ) := by
    have h1 : (∫ z : ΩB, Real.sqrt (∑ i : Fin m, (z.2.1 i) ^ 2) ∂μB)
        = ∫ w : ΩGH, Real.sqrt (∑ i : Fin m, (w.1 i) ^ 2) ∂νGH :=
      hint_snd _ hAsqrtGH
    have h2 : (∫ w : ΩGH, Real.sqrt (∑ i : Fin m, (w.1 i) ^ 2) ∂νGH)
        = ∫ g : Fin m → ℝ, Real.sqrt (∑ i : Fin m, (g i) ^ 2) ∂νm :=
      hint_inner_fst _ hsqrtm_int
    rw [h1, h2]
    exact hwidth_m

  have hBval : (∫ z : ΩB, Real.sqrt (∑ j : Fin n, (z.2.2 j) ^ 2) ∂μB)
      ≤ Real.sqrt (n : ℝ) := by
    have h1 : (∫ z : ΩB, Real.sqrt (∑ j : Fin n, (z.2.2 j) ^ 2) ∂μB)
        = ∫ w : ΩGH, Real.sqrt (∑ j : Fin n, (w.2 j) ^ 2) ∂νGH :=
      hint_snd _ hBsqrtGH
    have h2 : (∫ w : ΩGH, Real.sqrt (∑ j : Fin n, (w.2 j) ^ 2) ∂νGH)
        = ∫ h : Fin n → ℝ, Real.sqrt (∑ j : Fin n, (h j) ^ 2) ∂νn :=
      hint_inner_snd _ hsqrtn_int
    rw [h1, h2]
    exact hwidth_n

  have hLval : (∫ z : ΩB,
      (Real.sqrt (∑ i : Fin m, (z.2.1 i) ^ 2) + Real.sqrt (∑ j : Fin n, (z.2.2 j) ^ 2)) ∂μB)
      ≤ Real.sqrt (m : ℝ) + Real.sqrt (n : ℝ) := by
    rw [MeasureTheory.integral_add hAint hBint]
    linarith [hAval, hBval]

  have hWmeas : Measurable (fun ω : ΩW => ‖Matrix.of (fun i j => ω (i, j))‖) := by
    have hm : Measurable (fun ω : ΩW => Matrix.of (fun i j => ω (i, j))) := by
      refine measurable_pi_iff.mpr (fun i => ?_)
      refine measurable_pi_iff.mpr (fun j => ?_)
      exact measurable_pi_apply (i, j)
    exact continuous_norm.measurable.comp hm
  have hsupY_int : ∀ (N : ℕ) (hN : 1 ≤ N) (x : Fin N → Fin m → ℝ) (y : Fin N → Fin n → ℝ),
      MeasureTheory.Integrable (fun z : ΩB =>
        ⨆ k : Fin N, ((∑ i : Fin m, x k i * z.2.1 i) + (∑ j : Fin n, y k j * z.2.2 j))) μB := by
    intro N hN x y
    exact supInt_general N hN
      (fun z k => (∑ i : Fin m, x k i * z.2.1 i) + (∑ j : Fin n, y k j * z.2.2 j))
      (fun k => measurable_pi_iff.mp ((hYmeas N x y).comp measurable_snd) k)
      (fun k => hY_sq N x y k)
  have hsharp : (∫ ω : (Fin m × Fin n) → ℝ,
      ‖Matrix.of (fun i j => ω (i, j))‖
        ∂(MeasureTheory.Measure.pi (fun _ : (Fin m × Fin n) => ProbabilityTheory.gaussianReal 0 1)))
      ≤ Real.sqrt (m : ℝ) + Real.sqrt (n : ℝ) := by
    have key : ∀ δ : ℝ, 0 < δ → δ < 1 / 4 →
        (∫ ω : ΩW, ‖Matrix.of (fun i j => ω (i, j))‖ ∂μW)
          ≤ (1 - 2 * δ)⁻¹ * (Real.sqrt (m : ℝ) + Real.sqrt (n : ℝ)) := by
      intro δ hδ hδ4
      obtain ⟨N, hN, x, y, hx, hy, hbound⟩ := hptW δ hδ hδ4
      have hXint := hsupX_int N hN x y
      have hscaled : MeasureTheory.Integrable (fun z : ΩB =>
          (1 - 2 * δ)⁻¹ * ⨆ k : Fin N,
            ∑ i : Fin m, ∑ j : Fin n, x k i * z.1 (i, j) * y k j) μB :=
        hXint.const_mul ((1 - 2 * δ)⁻¹)
      have hcpos : (0 : ℝ) < 1 - 2 * δ := by linarith
      have hWintB : MeasureTheory.Integrable
          (fun z : ΩB => ‖Matrix.of (fun i j => z.1 (i, j))‖) μB := by
        refine hscaled.mono ?_ ?_
        · exact Measurable.aestronglyMeasurable (hWmeas.comp measurable_fst)
        · refine Filter.Eventually.of_forall (fun z => ?_)
          have hb := hbound z.1
          have hnn : (0 : ℝ) ≤ (1 - 2 * δ)⁻¹ * ⨆ k : Fin N,
              ∑ i : Fin m, ∑ j : Fin n, x k i * z.1 (i, j) * y k j :=
            le_trans (norm_nonneg _) hb
          have e1 : ‖‖Matrix.of (fun i j => z.1 (i, j))‖‖
              = ‖Matrix.of (fun i j => z.1 (i, j))‖ := by
            rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
          have e2 : ‖(1 - 2 * δ)⁻¹ * ⨆ k : Fin N,
                ∑ i : Fin m, ∑ j : Fin n, x k i * z.1 (i, j) * y k j‖
              = (1 - 2 * δ)⁻¹ * ⨆ k : Fin N,
                ∑ i : Fin m, ∑ j : Fin n, x k i * z.1 (i, j) * y k j := by
            rw [Real.norm_eq_abs, abs_of_nonneg hnn]
          rw [e1, e2]
          exact hb
      have hstep1 : (∫ z : ΩB, ‖Matrix.of (fun i j => z.1 (i, j))‖ ∂μB)
          ≤ (1 - 2 * δ)⁻¹ * ∫ z : ΩB,
              ⨆ k : Fin N, ∑ i : Fin m, ∑ j : Fin n, x k i * z.1 (i, j) * y k j ∂μB :=
        (MeasureTheory.integral_mono hWintB hscaled (fun z => hbound z.1)).trans_eq
          (MeasureTheory.integral_const_mul ((1 - 2 * δ)⁻¹)
            (fun z : ΩB => ⨆ k : Fin N,
              ∑ i : Fin m, ∑ j : Fin n, x k i * z.1 (i, j) * y k j))
      have hstep2 : (∫ z : ΩB,
            ⨆ k : Fin N, ∑ i : Fin m, ∑ j : Fin n, x k i * z.1 (i, j) * y k j ∂μB)
          ≤ ∫ z : ΩB, ⨆ k : Fin N,
              ((∑ i : Fin m, x k i * z.2.1 i) + (∑ j : Fin n, y k j * z.2.2 j)) ∂μB :=
        hSFstep N hN x y hx hy
      have hstep3 : (∫ z : ΩB, ⨆ k : Fin N,
            ((∑ i : Fin m, x k i * z.2.1 i) + (∑ j : Fin n, y k j * z.2.2 j)) ∂μB)
          ≤ ∫ z : ΩB,
              (Real.sqrt (∑ i : Fin m, (z.2.1 i) ^ 2)
                + Real.sqrt (∑ j : Fin n, (z.2.2 j) ^ 2)) ∂μB :=
        MeasureTheory.integral_mono (hsupY_int N hN x y) hLintB
          (fun z => hYpt N hN x y hx hy z)
      have hchain : (∫ z : ΩB,
            ⨆ k : Fin N, ∑ i : Fin m, ∑ j : Fin n, x k i * z.1 (i, j) * y k j ∂μB)
          ≤ Real.sqrt (m : ℝ) + Real.sqrt (n : ℝ) := hstep2.trans (hstep3.trans hLval)
      have hEq : (∫ ω : ΩW, ‖Matrix.of (fun i j => ω (i, j))‖ ∂μW)
          = ∫ z : ΩB, ‖Matrix.of (fun i j => z.1 (i, j))‖ ∂μB := by
        have hAE : AEStronglyMeasurable (fun ω : ΩW => ‖Matrix.of (fun i j => ω (i, j))‖)
            (MeasureTheory.Measure.map (Prod.fst : ΩB → ΩW) μB) := by
          rw [hfst_map']
          exact Measurable.aestronglyMeasurable hWmeas
        rw [← hfst_map']
        exact MeasureTheory.integral_map measurable_fst.aemeasurable hAE
      rw [hEq]
      calc ∫ z : ΩB, ‖Matrix.of (fun i j => z.1 (i, j))‖ ∂μB
          ≤ (1 - 2 * δ)⁻¹ * ∫ z : ΩB,
              ⨆ k : Fin N, ∑ i : Fin m, ∑ j : Fin n, x k i * z.1 (i, j) * y k j ∂μB := hstep1
        _ ≤ (1 - 2 * δ)⁻¹ * (Real.sqrt (m : ℝ) + Real.sqrt (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hchain (le_of_lt (inv_pos.mpr hcpos))
    have hmain : (∫ ω : ΩW, ‖Matrix.of (fun i j => ω (i, j))‖ ∂μW)
        ≤ Real.sqrt (m : ℝ) + Real.sqrt (n : ℝ) :=
      harith (∫ ω : ΩW, ‖Matrix.of (fun i j => ω (i, j))‖ ∂μW)
        (Real.sqrt (m : ℝ) + Real.sqrt (n : ℝ)) (by positivity) key
    exact hmain
  dsimp only
  calc (∫ ω : (Fin m × Fin n) → ℝ,
      ‖Matrix.of (fun i j => ω (i, j))‖
        ∂(MeasureTheory.Measure.pi (fun _ : (Fin m × Fin n) => ProbabilityTheory.gaussianReal 0 1)))
      ≤ Real.sqrt (m : ℝ) + Real.sqrt (n : ℝ) := hsharp
    _ ≤ Real.sqrt (m : ℝ) + Real.sqrt (n : ℝ) + 2 := by linarith
  /- @proof-region region.target-node.session.aa85431675a71ae0 end -/

end Statlib.Imported

