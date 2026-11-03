import Lean
import ProverJobs.job_paper_110bb96e917848c19df0625891303d5c.Vocabulary
import ProverJobs.job_paper_110bb96e917848c19df0625891303d5c.Base
import ProverJobs.job_paper_110bb96e917848c19df0625891303d5c.ExternalNodes.Node_e9c35d4af3284e03b008

namespace PaperProofTasks.job_paper_110bb96e917848c19df0625891303d5c

open _root_.PaperProofTasks.job_paper_110bb96e917848c19df0625891303d5c.Statlib.Imported
open MeasureTheory ProbabilityTheory

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_3438139564_b75b36c2 : ∀ (L : NNReal) (hL : 0 < L),
    ∃ V : ℝ, 0 < V ∧
      ∀ (p q : ℕ), 2 ≤ p → 1 ≤ q →
        ∀ (B_phi : ℝ) (d : EuclideanSpace ℝ (Fin q)),
          0 ≤ B_phi → ‖d‖ ≤ B_phi →
          ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
            (f : (Fin q → ℝ) → (Fin p → ℝ)), Measurable f →
            ∀ (E : Ω → Fin p → ℝ) (H : Ω → Fin q → ℝ) (M : Matrix (Fin p) (Fin q) ℝ),
              (∀ i : Fin p, Measurable fun ω => E ω i) →
              (∀ l : Fin q, Measurable fun ω => H ω l) →
              (∀ i : Fin p, HasSubgaussianMGF (fun ω => E ω i) L μ) →
              (∀ l : Fin q, HasSubgaussianMGF (fun ω => H ω l) L μ) →
              (∀ k : Fin p, HasSubgaussianMGF (fun ω => f (H ω) k) L μ) →
              (∀ i : Fin p, Integrable (fun ω => E ω i) μ) →
              (∀ l : Fin q, Integrable (fun ω => H ω l) μ) →
              (∀ k : Fin p, Integrable (fun ω => f (H ω) k) μ) →
              (∀ i : Fin p, ∫ ω, E ω i ∂μ = 0) →
              (∀ l : Fin q, ∫ ω, H ω l ∂μ = 0) →
              (∀ k : Fin p, ∫ ω, f (H ω) k ∂μ = 0) →
              (∀ (i : Fin p) (l : Fin q), ∫ ω, E ω i * H ω l ∂μ = 0) →
              (∀ (j : Fin p) (l : Fin q),
                M j l = ∫ ω, (f (H ω) j + E ω j) * H ω l ∂μ) →
              ∀ (j : Fin p) (r : ℕ), 2 ≤ r →
                ∫⁻ (ω : Ω), ENNReal.ofReal
                  (|∑ l : Fin q, (d l) * ((f (H ω) j + E ω j) * H ω l - M j l)| ^ r) ∂μ
                ≤ ENNReal.ofReal ((r.factorial : ℝ) * (V * B_phi * Real.sqrt (q : ℝ)) ^ r) := by
  /- @proof-region region.target-node.session.28e2d82d81882796 begin -/
  intro L hL
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hLspos : 0 < Real.sqrt (L : ℝ) := Real.sqrt_pos.mpr hLpos
  have hLssq : Real.sqrt (L : ℝ) ^ 2 = (L : ℝ) := Real.sq_sqrt (le_of_lt hLpos)
  obtain ⟨Vd, hVdpos, hVd⟩ :=
    PaperProofTasks.job_paper_6881610d85e44b6089ed4cd810570574.Statlib.Imported.paper_6881610d85e44b6089ed4cd810570574
      (Real.sqrt (L : ℝ)) (Real.sqrt (L : ℝ)) hLspos hLspos
  refine ⟨Vd, hVdpos, ?_⟩
  intro p q hp hq B_phi d hB hdB Ω instΩ μ instμ f hf E H M hE_meas hH_meas hE_sg hH_sg hfH_sg
    hE_int hH_int hfH_int hE_cent hH_cent hfH_cent hEH_orth hM j r hr
  let cc : NNReal := ⟨Real.sqrt (L : ℝ) ^ 2, sq_nonneg (Real.sqrt (L : ℝ))⟩
  have hc : cc = L := Subtype.ext hLssq
  let fH' : Ω → Fin p → ℝ := fun ω => f (H ω)
  let E' : Ω → Fin p → ℝ := fun ω _ => E ω j
  let X' : Ω → Fin p → ℝ := fun ω i => f (H ω) i + E ω j
  let eps' : Ω → ℝ := fun ω => E ω j
  let mc := PaperProofTasks.job_paper_6881610d85e44b6089ed4cd810570574.Statlib.Imported.momentCoord E' fH' X' H eps'
  let aI : Fin q → PaperProofTasks.job_paper_6881610d85e44b6089ed4cd810570574.Statlib.Imported.MomentCoordIdx p q :=
    fun _ => ULift.up (Sum.inr (Sum.inr (Sum.inr (Sum.inl j))) : PaperProofTasks.job_paper_6881610d85e44b6089ed4cd810570574.Statlib.Imported.MomentCoordPoolIdx p q)
  let bI : Fin q → PaperProofTasks.job_paper_6881610d85e44b6089ed4cd810570574.Statlib.Imported.MomentCoordIdx p q :=
    fun l => ULift.up (Sum.inr (Sum.inl l) : PaperProofTasks.job_paper_6881610d85e44b6089ed4cd810570574.Statlib.Imported.MomentCoordPoolIdx p q)
  set D : ℝ := B_phi * Real.sqrt (q : ℝ) with hDdef
  have keymgf : ∀ (X : Ω → ℝ), HasSubgaussianMGF X L μ → HasSubgaussianMGF X cc μ := by
    intro X hX
    rw [hc]
    exact hX
  have hE'_meas : ∀ i : Fin p, Measurable fun ω => E' ω i := fun i => hE_meas j
  have hE'_int : ∀ i : Fin p, Integrable (fun ω => E' ω i) μ := fun i => hE_int j
  have hE'_cent : ∀ i : Fin p, ∫ ω, E' ω i ∂μ = 0 := fun i => hE_cent j
  have hE'_sg : ∀ i : Fin p, HasSubgaussianMGF (fun ω => E' ω i) cc μ := fun i => keymgf _ (hE_sg j)
  have hHmeas : Measurable H := measurable_pi_iff.mpr hH_meas
  have hfHmeas : Measurable fH' := hf.comp hHmeas
  have hfH_meas2 : ∀ k : Fin p, Measurable fun ω => fH' ω k :=
    fun k => (measurable_pi_apply k).comp hfHmeas
  have hX'_meas : ∀ i : Fin p, Measurable fun ω => X' ω i :=
    fun i => (hfH_meas2 i).add (hE_meas j)
  have heps_meas : Measurable eps' := hE_meas j
  have hX'_int : ∀ i : Fin p, Integrable (fun ω => X' ω i) μ :=
    fun i => (hfH_int i).add (hE_int j)
  have heps_int : Integrable eps' μ := hE_int j
  have hH_sg' : ∀ l : Fin q, HasSubgaussianMGF (fun ω => H ω l) cc μ := fun l => keymgf _ (hH_sg l)
  have hfH_sg' : ∀ k : Fin p, HasSubgaussianMGF (fun ω => fH' ω k) cc μ := fun k => keymgf _ (hfH_sg k)
  have heps_sg : HasSubgaussianMGF eps' cc μ := keymgf _ (hE_sg j)
  have hHL2 : ∀ l : Fin q, MemLp (fun ω => H ω l) 2 μ := fun l => by simpa using (hH_sg l).memLp 2
  have hfHL2 : ∀ k : Fin p, MemLp (fun ω => fH' ω k) 2 μ := fun k => by simpa using (hfH_sg k).memLp 2
  have hEL2 : MemLp eps' 2 μ := by simpa using (hE_sg j).memLp 2
  have hXL2 : ∀ i : Fin p, MemLp (fun ω => X' ω i) 2 μ := fun i => (hfHL2 i).add hEL2
  have mul_memLp : ∀ {u v : Ω → ℝ}, MemLp u 2 μ → MemLp v 2 μ → Integrable (fun ω => u ω * v ω) μ :=
    fun hu hv => hu.integrable_mul hv
  have memL2 : ∀ a, MemLp (mc a) 2 μ := by
    intro a
    cases a with
    | up x =>
      cases x with
      | inl i => exact hEL2
      | inr r1 =>
        cases r1 with
        | inl l => exact hHL2 l
        | inr r2 =>
          cases r2 with
          | inl k => exact hfHL2 k
          | inr r3 =>
            cases r3 with
            | inl l => exact hXL2 l
            | inr u => exact hEL2
  have hpair : ∀ a b, Integrable (fun ω => mc a ω * mc b ω) μ :=
    fun a b => mul_memLp (memL2 a) (memL2 b)
  have hdep := hVd (Ω := Ω) μ p q hp hq E' fH' X' H eps'
    hE'_meas hH_meas hfH_meas2 hX'_meas heps_meas
    hE'_int hH_int hfH_int hX'_int heps_int
    hpair hE'_cent hH_cent hfH_cent (hE_cent j)
    hE'_sg hH_sg' hfH_sg' heps_sg
    (fun ω i => rfl)
  have hDnn : 0 ≤ D := by
    rw [hDdef]
    exact mul_nonneg hB (Real.sqrt_nonneg _)
  have hDsum : (∑ l : Fin q, |d l|) ≤ D := by
    rw [hDdef]
    have hcs' : (∑ l : Fin q, |d l|) ^ 2 ≤ (q : ℝ) * ∑ l : Fin q, (d l) ^ 2 := by
      have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin q))
        (fun _ : Fin q => (1 : ℝ)) (fun l => |d l|)
      simpa [sq_abs] using hh
    have hnorm : (∑ l : Fin q, (d l) ^ 2) = ‖d‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq d]
      simp [Real.norm_eq_abs, sq_abs]
    rw [hnorm] at hcs'
    have h2 : (q : ℝ) * ‖d‖ ^ 2 ≤ (q : ℝ) * B_phi ^ 2 := by
      have h0 : ‖d‖ ^ 2 ≤ B_phi ^ 2 := by nlinarith [norm_nonneg d, hB, hdB]
      nlinarith
    have h3 : (B_phi * Real.sqrt (q : ℝ)) ^ 2 = B_phi ^ 2 * (q : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg q)]
    have hsq_le : (∑ l : Fin q, |d l|) ^ 2 ≤ (B_phi * Real.sqrt (q : ℝ)) ^ 2 := by
      rw [h3]
      nlinarith [hcs', h2]
    have h1 : 0 ≤ ∑ l : Fin q, |d l| := Finset.sum_nonneg (fun l _ => abs_nonneg (d l))
    have h2' : 0 ≤ B_phi * Real.sqrt (q : ℝ) := mul_nonneg hB (Real.sqrt_nonneg _)
    have h3' := Real.sqrt_le_sqrt hsq_le
    rw [Real.sqrt_sq h1, Real.sqrt_sq h2'] at h3'
    linarith
  have key : ∀ ω : Ω,
      (∑ l : Fin q, (d l) * ((f (H ω) j + E ω j) * H ω l - M j l))
        = ∑ k : Fin q, (d k) * (mc (aI k) ω * mc (bI k) ω
            - ∫ ω', mc (aI k) ω' * mc (bI k) ω' ∂μ) := by
    intro ω
    refine Finset.sum_congr rfl ?_
    intro l _
    have hC : (∫ ω', mc (aI l) ω' * mc (bI l) ω' ∂μ) = M j l := by
      show (∫ ω', (f (H ω') j + E ω' j) * H ω' l ∂μ) = M j l
      exact (hM j l).symm
    rw [hC]
    rfl
  have hDval : Vd * D = Vd * B_phi * Real.sqrt (q : ℝ) := by
    rw [hDdef]
    ring
  have hlin := hdep.2 (Fin q) aI bI (fun l => d l) D hDnn hDsum r hr
  rw [hDval] at hlin
  refine le_trans (le_of_eq ?_) hlin
  simp only [key]
  rfl
  /- @proof-region region.target-node.session.28e2d82d81882796 end -/

end Statlib.Imported

