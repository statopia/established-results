import Lean
import ProverJobs.job_paper_4a6904a098fa4fcebf3058bbb4e15c0e.Vocabulary
import ProverJobs.job_paper_4a6904a098fa4fcebf3058bbb4e15c0e.Base
import ProverJobs.job_paper_4a6904a098fa4fcebf3058bbb4e15c0e.ExternalNodes.Node_823fbb6926464c629003

namespace PaperProofTasks.job_paper_4a6904a098fa4fcebf3058bbb4e15c0e

open _root_.PaperProofTasks.job_paper_4a6904a098fa4fcebf3058bbb4e15c0e.Statlib.Imported
open MeasureTheory ProbabilityTheory

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_3331897167_3f7edc77 : ∀ (L : ℝ) (hL : 0 < L),
    ∃ V : ℝ, 0 < V ∧
      ∀ (q : ℕ) (hq : 1 ≤ q) (p : ℕ) (hp : 1 ≤ p)
        (f : (Fin q → ℝ) → (Fin p → ℝ)) (hf : Measurable f)
        (P : Measure ((Fin q → ℝ) × (Fin p → ℝ))) (hP : IsProbabilityMeasure P),
        (∀ i : Fin p, Integrable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => z.2 i) P) →
        (∀ j : Fin q, Integrable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => z.1 j) P) →
        (∀ k : Fin p, Integrable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => f z.1 k) P) →
        (∀ i : Fin p, ∫ z, z.2 i ∂P = 0) →
        (∀ j : Fin q, ∫ z, z.1 j ∂P = 0) →
        (∀ k : Fin p, ∫ z, f z.1 k ∂P = 0) →
        (∀ i : Fin p,
          HasSubgaussianMGF (fun z : (Fin q → ℝ) × (Fin p → ℝ) => z.2 i)
            (Real.toNNReal (L ^ 2)) P) →
        (∀ j : Fin q,
          HasSubgaussianMGF (fun z : (Fin q → ℝ) × (Fin p → ℝ) => z.1 j)
            (Real.toNNReal (L ^ 2)) P) →
        (∀ k : Fin p,
          HasSubgaussianMGF (fun z : (Fin q → ℝ) × (Fin p → ℝ) => f z.1 k)
            (Real.toNNReal (L ^ 2)) P) →
        (∀ (i j : Fin p),
          Integrable (fun z : (Fin q → ℝ) × (Fin p → ℝ) =>
            (f z.1 i + z.2 i) * (f z.1 j + z.2 j)) P) →
        ∀ (i j : Fin p) (r : ℕ), 2 ≤ r →
          (∫ z : (Fin q → ℝ) × (Fin p → ℝ),
              |(f z.1 i + z.2 i) * (f z.1 j + z.2 j)
                 - (∫ z' : (Fin q → ℝ) × (Fin p → ℝ),
                      (f z'.1 i + z'.2 i) * (f z'.1 j + z'.2 j) ∂P)| ^ r ∂P)
            ≤ (r.factorial : ℝ) * V ^ r := by
  /- @proof-region region.target-node.session.30cf0672c7f1fd98 begin -/
  intro L hL
  obtain ⟨V, hV, hb⟩ :=
    PaperProofTasks.job_paper_6881610d85e44b6089ed4cd810570574.Statlib.Imported.paper_6881610d85e44b6089ed4cd810570574
      L L hL hL
  refine ⟨V, hV, ?_⟩
  intro q hq p hp f hf P hP hEint hHint hfint hE0 hH0 hf0 hEsub hHsub hfsub hprod i j r hr
  have hNN : Real.toNNReal (L ^ 2) = ⟨L ^ 2, sq_nonneg L⟩ := by
    rw [Real.toNNReal_of_nonneg (sq_nonneg L)]
  set g : Fin 2 → Fin p := fun l => if l = 0 then i else j with hg
  set j0 : Fin q := ⟨0, by omega⟩ with hj0
  set Hq : (Fin q → ℝ) × (Fin p → ℝ) → Fin q → ℝ := fun z => z.1 with hHq
  set eps : (Fin q → ℝ) × (Fin p → ℝ) → ℝ := fun z => z.1 j0 with heps
  set E2 : (Fin q → ℝ) × (Fin p → ℝ) → Fin 2 → ℝ := fun z l => z.2 (g l) with hE2
  set F2 : (Fin q → ℝ) × (Fin p → ℝ) → Fin 2 → ℝ := fun z l => f z.1 (g l) with hF2
  set X2 : (Fin q → ℝ) × (Fin p → ℝ) → Fin 2 → ℝ := fun z l => f z.1 (g l) + z.2 (g l) with hX2
  have hmE : ∀ k : Fin p, Measurable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => z.2 k) :=
    fun k => (measurable_pi_apply k).comp measurable_snd
  have hmH : ∀ k : Fin q, Measurable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => z.1 k) :=
    fun k => (measurable_pi_apply k).comp measurable_fst
  have hmF : ∀ k : Fin p, Measurable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => f z.1 k) :=
    fun k => (measurable_pi_apply k).comp (hf.comp measurable_fst)
  have hmeasE : ∀ l : Fin 2, Measurable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => E2 z l) :=
    fun l => by simpa [hE2] using hmE (g l)
  have hmeasH : ∀ l : Fin q, Measurable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => Hq z l) :=
    fun l => by simpa [hHq] using hmH l
  have hmeasF : ∀ l : Fin 2, Measurable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => F2 z l) :=
    fun l => by simpa [hF2] using hmF (g l)
  have hmeasX : ∀ l : Fin 2, Measurable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => X2 z l) :=
    fun l => by simpa [hX2] using (hmF (g l)).add (hmE (g l))
  have hmeasEps : Measurable eps := by simpa [heps] using hmH j0
  have hintE : ∀ l : Fin 2, Integrable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => E2 z l) P :=
    fun l => by simpa [hE2] using hEint (g l)
  have hintH : ∀ l : Fin q, Integrable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => Hq z l) P :=
    fun l => by simpa [hHq] using hHint l
  have hintF : ∀ l : Fin 2, Integrable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => F2 z l) P :=
    fun l => by simpa [hF2] using hfint (g l)
  have hintX : ∀ l : Fin 2, Integrable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => X2 z l) P :=
    fun l => by simpa [hX2] using (hfint (g l)).add (hEint (g l))
  have hintEps : Integrable eps P := by simpa [heps] using hHint j0
  have hzE : ∀ l : Fin 2, ∫ z : (Fin q → ℝ) × (Fin p → ℝ), E2 z l ∂P = 0 :=
    fun l => by simpa [hE2] using hE0 (g l)
  have hzH : ∀ l : Fin q, ∫ z : (Fin q → ℝ) × (Fin p → ℝ), Hq z l ∂P = 0 :=
    fun l => by simpa [hHq] using hH0 l
  have hzF : ∀ l : Fin 2, ∫ z : (Fin q → ℝ) × (Fin p → ℝ), F2 z l ∂P = 0 :=
    fun l => by simpa [hF2] using hf0 (g l)
  have hzEps : ∫ z : (Fin q → ℝ) × (Fin p → ℝ), eps z ∂P = 0 := by simpa [heps] using hH0 j0
  have hsE : ∀ l : Fin 2, HasSubgaussianMGF (fun z : (Fin q → ℝ) × (Fin p → ℝ) => E2 z l) ⟨L ^ 2, sq_nonneg L⟩ P :=
    fun l => by simpa [hE2, hNN] using hEsub (g l)
  have hsH : ∀ l : Fin q, HasSubgaussianMGF (fun z : (Fin q → ℝ) × (Fin p → ℝ) => Hq z l) ⟨L ^ 2, sq_nonneg L⟩ P :=
    fun l => by simpa [hHq, hNN] using hHsub l
  have hsF : ∀ l : Fin 2, HasSubgaussianMGF (fun z : (Fin q → ℝ) × (Fin p → ℝ) => F2 z l) ⟨L ^ 2, sq_nonneg L⟩ P :=
    fun l => by simpa [hF2, hNN] using hfsub (g l)
  have hsEps : HasSubgaussianMGF eps ⟨L ^ 2, sq_nonneg L⟩ P := by
    simpa [heps, hNN] using hHsub j0
  have hmc : ∀ a : PaperProofTasks.job_paper_6881610d85e44b6089ed4cd810570574.Statlib.Imported.MomentCoordIdx 2 q,
      MemLp (fun z : (Fin q → ℝ) × (Fin p → ℝ) =>
        PaperProofTasks.job_paper_6881610d85e44b6089ed4cd810570574.Statlib.Imported.momentCoord
          E2 F2 X2 Hq eps a z) (2 : ENNReal) P := by
    intro a
    obtain ⟨x⟩ := a
    cases x with
    | inl l =>
      change MemLp (fun z : (Fin q → ℝ) × (Fin p → ℝ) => E2 z l) (2 : ENNReal) P
      simpa [hE2] using (hEsub (g l)).memLp (2 : NNReal)
    | inr b =>
      cases b with
      | inl l =>
        change MemLp (fun z : (Fin q → ℝ) × (Fin p → ℝ) => Hq z l) (2 : ENNReal) P
        simpa [hHq] using (hHsub l).memLp (2 : NNReal)
      | inr c =>
        cases c with
        | inl l =>
          change MemLp (fun z : (Fin q → ℝ) × (Fin p → ℝ) => F2 z l) (2 : ENNReal) P
          simpa [hF2] using (hfsub (g l)).memLp (2 : NNReal)
        | inr d =>
          cases d with
          | inl l =>
            change MemLp (fun z : (Fin q → ℝ) × (Fin p → ℝ) => X2 z l) (2 : ENNReal) P
            simpa [hX2] using
              (MeasureTheory.MemLp.add ((hfsub (g l)).memLp (2 : NNReal))
                ((hEsub (g l)).memLp (2 : NNReal)))
          | inr e =>
            change MemLp (fun z : (Fin q → ℝ) × (Fin p → ℝ) => eps z) (2 : ENNReal) P
            simpa [heps] using (hHsub j0).memLp (2 : NNReal)
  have hpair : ∀ a b : PaperProofTasks.job_paper_6881610d85e44b6089ed4cd810570574.Statlib.Imported.MomentCoordIdx 2 q,
      Integrable (fun z : (Fin q → ℝ) × (Fin p → ℝ) =>
        PaperProofTasks.job_paper_6881610d85e44b6089ed4cd810570574.Statlib.Imported.momentCoord E2 F2 X2 Hq eps a z *
        PaperProofTasks.job_paper_6881610d85e44b6089ed4cd810570574.Statlib.Imported.momentCoord E2 F2 X2 Hq eps b z) P :=
    fun a b => MeasureTheory.MemLp.integrable_mul (hmc a) (hmc b)
  have hXeq : ∀ (z : (Fin q → ℝ) × (Fin p → ℝ)) (l : Fin 2), X2 z l = F2 z l + E2 z l :=
    fun z l => rfl
  obtain ⟨hmain, hlin⟩ := hb (Ω := (Fin q → ℝ) × (Fin p → ℝ)) (μ := P)
    2 q (by norm_num) hq
    E2 F2 X2 Hq eps
    hmeasE hmeasH hmeasF hmeasX hmeasEps
    hintE hintH hintF hintX hintEps
    hpair
    hzE hzH hzF hzEps
    hsE hsH hsF hsEps
    hXeq
  have hkey := hmain r hr
    (ULift.up (Sum.inr (Sum.inr (Sum.inr (Sum.inl (0 : Fin 2))))) :
      PaperProofTasks.job_paper_6881610d85e44b6089ed4cd810570574.Statlib.Imported.MomentCoordIdx 2 q)
    (ULift.up (Sum.inr (Sum.inr (Sum.inr (Sum.inl (1 : Fin 2))))) :
      PaperProofTasks.job_paper_6881610d85e44b6089ed4cd810570574.Statlib.Imported.MomentCoordIdx 2 q)
  have hA : ∀ z : (Fin q → ℝ) × (Fin p → ℝ),
      PaperProofTasks.job_paper_6881610d85e44b6089ed4cd810570574.Statlib.Imported.momentCoord E2 F2 X2 Hq eps
        (ULift.up (Sum.inr (Sum.inr (Sum.inr (Sum.inl (0 : Fin 2))))) :
          PaperProofTasks.job_paper_6881610d85e44b6089ed4cd810570574.Statlib.Imported.MomentCoordIdx 2 q) z
        = f z.1 i + z.2 i := by
    intro z
    simp [PaperProofTasks.job_paper_6881610d85e44b6089ed4cd810570574.Statlib.Imported.momentCoord, hX2, hg]
  have hB : ∀ z : (Fin q → ℝ) × (Fin p → ℝ),
      PaperProofTasks.job_paper_6881610d85e44b6089ed4cd810570574.Statlib.Imported.momentCoord E2 F2 X2 Hq eps
        (ULift.up (Sum.inr (Sum.inr (Sum.inr (Sum.inl (1 : Fin 2))))) :
          PaperProofTasks.job_paper_6881610d85e44b6089ed4cd810570574.Statlib.Imported.MomentCoordIdx 2 q) z
        = f z.1 j + z.2 j := by
    intro z
    simp [PaperProofTasks.job_paper_6881610d85e44b6089ed4cd810570574.Statlib.Imported.momentCoord, hX2, hg]
  have hkey2 :
      ∫⁻ z : (Fin q → ℝ) × (Fin p → ℝ),
          ENNReal.ofReal (|(f z.1 i + z.2 i) * (f z.1 j + z.2 j)
            - (∫ z' : (Fin q → ℝ) × (Fin p → ℝ),
                (f z'.1 i + z'.2 i) * (f z'.1 j + z'.2 j) ∂P)| ^ r) ∂P
        ≤ ENNReal.ofReal ((r.factorial : ℝ) * V ^ r) := by
    simpa only [hA, hB] using hkey
  have hnn : 0 ≤ᵐ[P] (fun z : (Fin q → ℝ) × (Fin p → ℝ) =>
      |(f z.1 i + z.2 i) * (f z.1 j + z.2 j)
        - (∫ z' : (Fin q → ℝ) × (Fin p → ℝ),
            (f z'.1 i + z'.2 i) * (f z'.1 j + z'.2 j) ∂P)| ^ r) :=
    Filter.Eventually.of_forall (fun z => by positivity)
  have hm1 : Measurable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => f z.1 i + z.2 i) :=
    ((measurable_pi_apply i).comp (hf.comp measurable_fst)).add
      ((measurable_pi_apply i).comp measurable_snd)
  have hm2 : Measurable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => f z.1 j + z.2 j) :=
    ((measurable_pi_apply j).comp (hf.comp measurable_fst)).add
      ((measurable_pi_apply j).comp measurable_snd)
  have haesm : AEStronglyMeasurable (fun z : (Fin q → ℝ) × (Fin p → ℝ) =>
      |(f z.1 i + z.2 i) * (f z.1 j + z.2 j)
        - (∫ z' : (Fin q → ℝ) × (Fin p → ℝ),
            (f z'.1 i + z'.2 i) * (f z'.1 j + z'.2 j) ∂P)| ^ r) P :=
    (((hm1.mul hm2).sub measurable_const).abs.pow_const r).aemeasurable.aestronglyMeasurable
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnn haesm]
  have hbfin : ENNReal.ofReal ((r.factorial : ℝ) * V ^ r) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hle := ENNReal.toReal_mono hbfin hkey2
  rwa [ENNReal.toReal_ofReal (by positivity)] at hle
  /- @proof-region region.target-node.session.30cf0672c7f1fd98 end -/

end Statlib.Imported

