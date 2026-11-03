import Statlib.HighDim.CovarianceMatrix.SampleCovariance
import Lean
import ProverJobs.job_paper_110bb96e917848c19df0625891303d5c.ExternalNodes.Node_db00c2de82804572b050
import ProverJobs.job_paper_110bb96e917848c19df0625891303d5c.ExternalNodes.Node_e9c35d4af3284e03b008
import ProverJobs.job_paper_110bb96e917848c19df0625891303d5c.Vocabulary
import ProverJobs.job_paper_110bb96e917848c19df0625891303d5c.ProvedNodes
import ProverJobs.job_paper_110bb96e917848c19df0625891303d5c.Base

namespace PaperProofTasks.job_paper_110bb96e917848c19df0625891303d5c

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
open MeasureTheory ProbabilityTheory

theorem paper_110bb96e917848c19df0625891303d5c
    (L : NNReal) (hL : 0 < L) :
    ∀ c : ℝ, 0 < c →
      ∃ Cd Nd : ℝ, 0 < Cd ∧ 0 < Nd ∧
        ∀ (p q K : ℕ) (hp : 2 ≤ p) (hq : 1 ≤ q) (hK : 1 ≤ K)
          (n_t : ℕ) (ns : Fin K → ℕ) (hnt : 0 < n_t)
          (hns : ∀ k, 0 < ns k) (hsum : n_t ≤ pooledSourceSize ns)
          (B_phi : ℝ) (hB : 0 < B_phi)
          {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (f : (Fin q → ℝ) → (Fin p → ℝ))
          (E : (k : Fin K) → Fin (ns k) → Ω → (Fin p → ℝ))
          (H : (k : Fin K) → Fin (ns k) → Ω → (Fin q → ℝ))
          (M : Matrix (Fin p) (Fin q) ℝ)
          (d : Fin K → EuclideanSpace ℝ (Fin q))
          (hf : Measurable f)
          (hE_meas : ∀ k i, Measurable (E k i))
          (hH_meas : ∀ k i, Measurable (H k i))
          (hE_sg : ∀ k i j, HasSubgaussianMGF (fun ω => E k i ω j) L μ)
          (hH_sg : ∀ k i l, HasSubgaussianMGF (fun ω => H k i ω l) L μ)
          (hfH_sg : ∀ k i j, HasSubgaussianMGF (fun ω => f (H k i ω) j) L μ)
          (hE_int : ∀ k i j, Integrable (fun ω => E k i ω j) μ)
          (hH_int : ∀ k i l, Integrable (fun ω => H k i ω l) μ)
          (hfH_int : ∀ k i j, Integrable (fun ω => f (H k i ω) j) μ)
          (hEH_int : ∀ k i j l, Integrable (fun ω => E k i ω j * H k i ω l) μ)
          (hXH_int : ∀ k i j l,
            Integrable (fun ω => (f (H k i ω) j + E k i ω j) * H k i ω l) μ)
          (hE_cent : ∀ k i j, ∫ ω, E k i ω j ∂μ = 0)
          (hH_cent : ∀ k i l, ∫ ω, H k i ω l ∂μ = 0)
          (hfH_cent : ∀ k i j, ∫ ω, f (H k i ω) j ∂μ = 0)
          (hEH_orth : ∀ k i j l, ∫ ω, E k i ω j * H k i ω l ∂μ = 0)
          (hM : ∀ k i j l,
            M j l = ∫ ω, (f (H k i ω) j + E k i ω j) * H k i ω l ∂μ)
          (h_indep : iIndepFun
            (fun x : (k : Fin K) × Fin (ns k) =>
              fun ω => (E x.1 x.2 ω, H x.1 x.2 ω)) μ)
          (h_ident : ∀ x y : (k : Fin K) × Fin (ns k),
            IdentDistrib (fun ω => (E x.1 x.2 ω, H x.1 x.2 ω))
              (fun ω => (E y.1 y.2 ω, H y.1 y.2 ω)) μ μ)
          (hd : ∀ k, ‖d k‖ ≤ B_phi)
          (hN : Nd * Real.log (p : ℝ) ≤ (pooledSourceSize ns : ℝ)),
          1 - (p : ℝ) ^ (-c) / 20 ≤
            μ.real {ω : Ω |
              ‖weightedTransferVec ns f E H M d ω‖ ≤
                Cd * B_phi * Real.sqrt (q : ℝ) *
                  Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))}
:= by
  /- @proof-region region.root.56f4601e0a10 begin -/
  classical
  intro c hc
  obtain ⟨V, hVpos, hVall⟩ := statopia_math_node_3438139564_b75b36c2 L hL
  obtain ⟨b, hbpos, hb⟩ :=
    PaperProofTasks.job_paper_ebad183ded244602a77f3710a9957efa.Statlib.Imported.paper_ebad183ded244602a77f3710a9957efa.{u_1}
  refine ⟨max 1 ((c + 10) / b) * V, 1, ?_, ?_, ?_⟩
  · exact mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hVpos
  · exact one_pos
  · intro p q K hp hq hK n_t ns hnt hns hsum B_phi hB Ω instΩ μ instμ f E H M d hf
      hE_meas hH_meas hE_sg hH_sg hfH_sg hE_int hH_int hfH_int hEH_int hXH_int
      hE_cent hH_cent hfH_cent hEH_orth hM h_indep h_ident hd hN
    classical
    let U : ((k : Fin K) × Fin (ns k)) → Fin p → Ω → ℝ :=
      fun x j ω => ∑ l : Fin q,
        (d x.1) l * ((f (H x.1 x.2 ω) j + E x.1 x.2 ω j) * H x.1 x.2 ω l - M j l)
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by linarith)
    have hlogp_le : Real.log (p : ℝ) ≤ (pooledSourceSize ns : ℝ) := by
      simpa using hN
    have hNpos_real : 0 < (pooledSourceSize ns : ℝ) := lt_of_lt_of_le hlogp hlogp_le
    have hNpos : 0 < pooledSourceSize ns := by
      have hne : (pooledSourceSize ns : ℝ) ≠ 0 := ne_of_gt hNpos_real
      exact Nat.pos_of_ne_zero (Nat.cast_ne_zero.mp hne)
    have hstep1 : ∀ (j : Fin p) (ω : Ω),
        weightedTransferVec ns f E H M d ω j
          = (1 / (pooledSourceSize ns : ℝ)) * ∑ x, U x j ω := by
      intro j ω
      have hconst : ∀ (k : Fin K) (l : Fin q),
          (∑ i : Fin (ns k), M j l) = (ns k : ℝ) * M j l := by
        intro k l
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hinner : ∀ k : Fin K,
          (∑ l : Fin q,
            ((∑ i : Fin (ns k), (f (H k i ω) j + E k i ω j) * H k i ω l)
              - (ns k : ℝ) * M j l) * (d k) l)
          = ∑ i : Fin (ns k), ∑ l : Fin q,
              (d k) l * ((f (H k i ω) j + E k i ω j) * H k i ω l - M j l) := by
        intro k
        calc
          (∑ l : Fin q,
            ((∑ i : Fin (ns k), (f (H k i ω) j + E k i ω j) * H k i ω l)
              - (ns k : ℝ) * M j l) * (d k) l)
              = ∑ l : Fin q,
                  (∑ i : Fin (ns k),
                    ((f (H k i ω) j + E k i ω j) * H k i ω l - M j l)) *
                    (d k) l := by
                refine Finset.sum_congr rfl (fun l _ => ?_)
                rw [← hconst k l, ← Finset.sum_sub_distrib]
          _ = ∑ l : Fin q, ∑ i : Fin (ns k),
                ((f (H k i ω) j + E k i ω j) * H k i ω l - M j l) * (d k) l := by
                simp_rw [Finset.sum_mul]
          _ = ∑ i : Fin (ns k), ∑ l : Fin q,
                ((f (H k i ω) j + E k i ω j) * H k i ω l - M j l) * (d k) l := by
                rw [Finset.sum_comm]
          _ = ∑ i : Fin (ns k), ∑ l : Fin q,
                (d k) l * ((f (H k i ω) j + E k i ω j) * H k i ω l - M j l) := by
                refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun l _ => ?_))
                exact mul_comm _ _
      have hmain :
          (∑ k : Fin K, ∑ l : Fin q,
            ((∑ i : Fin (ns k), (f (H k i ω) j + E k i ω j) * H k i ω l)
              - (ns k : ℝ) * M j l) * (d k) l)
          = ∑ x : (k : Fin K) × Fin (ns k), ∑ l : Fin q,
              (d x.1) l * ((f (H x.1 x.2 ω) j + E x.1 x.2 ω j) * H x.1 x.2 ω l - M j l) := by
        calc
          (∑ k : Fin K, ∑ l : Fin q,
            ((∑ i : Fin (ns k), (f (H k i ω) j + E k i ω j) * H k i ω l)
              - (ns k : ℝ) * M j l) * (d k) l)
              = ∑ k : Fin K, ∑ i : Fin (ns k), ∑ l : Fin q,
                  (d k) l * ((f (H k i ω) j + E k i ω j) * H k i ω l - M j l) := by
                refine Finset.sum_congr rfl (fun k _ => ?_)
                exact hinner k
          _ = ∑ x : (k : Fin K) × Fin (ns k), ∑ l : Fin q,
                (d x.1) l * ((f (H x.1 x.2 ω) j + E x.1 x.2 ω j) * H x.1 x.2 ω l - M j l) := by
                rw [Finset.sum_sigma' (Finset.univ : Finset (Fin K))
                  (fun k => (Finset.univ : Finset (Fin (ns k))))]
                simp [Finset.univ_sigma_univ]
      show (1 / (pooledSourceSize ns : ℝ)) *
          (∑ k : Fin K, ∑ l : Fin q,
            ((∑ i : Fin (ns k), (f (H k i ω) j + E k i ω j) * H k i ω l)
              - (ns k : ℝ) * M j l) * (d k) l)
        = (1 / (pooledSourceSize ns : ℝ)) *
          (∑ x : (k : Fin K) × Fin (ns k), ∑ l : Fin q,
            (d x.1) l * ((f (H x.1 x.2 ω) j + E x.1 x.2 ω j) * H x.1 x.2 ω l - M j l))
      rw [hmain]
    set Vstar : ℝ := V * B_phi * Real.sqrt (q : ℝ) with hVstar
    have hqpos : (0 : ℝ) < (q : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
    have hVstar_pos : 0 < Vstar := by
      rw [hVstar]
      exact mul_pos (mul_pos hVpos hB) (Real.sqrt_pos.mpr hqpos)
    have hmom : ∀ (x : (k : Fin K) × Fin (ns k)) (j : Fin p) (r : ℕ), 2 ≤ r →
        ∫⁻ (ω : Ω), ENNReal.ofReal (|U x j ω| ^ r) ∂μ
          ≤ ENNReal.ofReal ((r.factorial : ℝ) * Vstar ^ r) := by
      intro x j r hr
      have hmain := hVall p q hp hq B_phi (d x.1) (le_of_lt hB) (hd x.1)
        μ f hf (E x.1 x.2) (H x.1 x.2) M
        (fun i => (measurable_pi_apply i).comp (hE_meas x.1 x.2))
        (fun l => (measurable_pi_apply l).comp (hH_meas x.1 x.2))
        (fun i => hE_sg x.1 x.2 i) (fun l => hH_sg x.1 x.2 l)
        (fun k => hfH_sg x.1 x.2 k)
        (fun i => hE_int x.1 x.2 i) (fun l => hH_int x.1 x.2 l)
        (fun k => hfH_int x.1 x.2 k)
        (fun i => hE_cent x.1 x.2 i) (fun l => hH_cent x.1 x.2 l)
        (fun k => hfH_cent x.1 x.2 k)
        (fun i l => hEH_orth x.1 x.2 i l)
        (fun j' l => hM x.1 x.2 j' l)
        j r hr
      rw [hVstar]
      exact hmain
    have hcent : ∀ (x : (k : Fin K) × Fin (ns k)) (j : Fin p),
        ∫ (ω : Ω), U x j ω ∂μ = 0 := by
      intro x j
      change ∫ (ω : Ω), (∑ l : Fin q,
        (d x.1) l * ((f (H x.1 x.2 ω) j + E x.1 x.2 ω j) * H x.1 x.2 ω l - M j l)) ∂μ = 0
      have hInt : ∀ l : Fin q,
          Integrable (fun ω => (d x.1).ofLp l *
            ((f (H x.1 x.2 ω) j + E x.1 x.2 ω j) * H x.1 x.2 ω l - M j l)) μ := by
        intro l
        exact ((hXH_int x.1 x.2 j l).sub (integrable_const (M j l))).const_mul ((d x.1).ofLp l)
      rw [integral_finset_sum (Finset.univ : Finset (Fin q)) (fun l _ => hInt l)]
      refine Finset.sum_eq_zero (fun l _ => ?_)
      rw [integral_const_mul,
        integral_sub (hXH_int x.1 x.2 j l) (integrable_const (M j l))]
      have hc : ∫ (ω : Ω), M j l ∂μ = M j l := by simp
      rw [← hM x.1 x.2 j l, hc, sub_self, mul_zero]
    have hindep : ∀ j : Fin p, iIndepFun (fun x => U x j) μ := by
      intro j
      let P : ((k : Fin K) × Fin (ns k)) → Ω → (Fin p → ℝ) × (Fin q → ℝ) :=
        fun x ω => (E x.1 x.2 ω, H x.1 x.2 ω)
      let Ψ : ((k : Fin K) × Fin (ns k)) → (Fin p → ℝ) × (Fin q → ℝ) → ℝ :=
        fun x e => ∑ l : Fin q, (d x.1).ofLp l * ((f e.2 j + e.1 j) * e.2 l - M j l)
      have hP_meas : ∀ x, Measurable (P x) := fun x =>
        Measurable.prod (hE_meas x.1 x.2) (hH_meas x.1 x.2)
      have hP_indep : iIndepFun P μ := h_indep
      have hΨ_ae : ∀ x, AEMeasurable (Ψ x) (Measure.map (P x) μ) := by
        intro x
        have hFj : Measurable fun e : (Fin p → ℝ) × (Fin q → ℝ) => f e.2 j :=
          (measurable_pi_apply j).comp (hf.comp measurable_snd)
        have hEj : Measurable fun e : (Fin p → ℝ) × (Fin q → ℝ) => e.1 j :=
          (measurable_pi_apply j).comp measurable_fst
        have hHl : ∀ l : Fin q, Measurable fun e : (Fin p → ℝ) × (Fin q → ℝ) => e.2 l :=
          fun l => (measurable_pi_apply l).comp measurable_snd
        have hterm : ∀ l : Fin q,
            Measurable fun e : (Fin p → ℝ) × (Fin q → ℝ) =>
              (d x.1).ofLp l * ((f e.2 j + e.1 j) * e.2 l - M j l) := by
          intro l
          have hc : Measurable fun _ : (Fin p → ℝ) × (Fin q → ℝ) => M j l := measurable_const
          exact (((hFj.add hEj).mul (hHl l)).sub hc).const_mul ((d x.1).ofLp l)
        have hsum : ∀ s : Finset (Fin q),
            Measurable fun e : (Fin p → ℝ) × (Fin q → ℝ) =>
              ∑ l ∈ s, (d x.1).ofLp l * ((f e.2 j + e.1 j) * e.2 l - M j l) := by
          intro s
          induction s using Finset.induction_on with
          | empty =>
              simpa using
                (measurable_const : Measurable fun _ : (Fin p → ℝ) × (Fin q → ℝ) => (0 : ℝ))
          | insert a s ha ih =>
              have hfun : (fun e : (Fin p → ℝ) × (Fin q → ℝ) =>
                  ∑ l ∈ insert a s, (d x.1).ofLp l * ((f e.2 j + e.1 j) * e.2 l - M j l))
                  = fun e => (d x.1).ofLp a * ((f e.2 j + e.1 j) * e.2 a - M j a)
                    + ∑ l ∈ s, (d x.1).ofLp l * ((f e.2 j + e.1 j) * e.2 l - M j l) := by
                funext e
                rw [Finset.sum_insert ha]
              rw [hfun]
              exact (hterm a).add ih
        show AEMeasurable (fun e : (Fin p → ℝ) × (Fin q → ℝ) =>
          ∑ l : Fin q, (d x.1).ofLp l * ((f e.2 j + e.1 j) * e.2 l - M j l))
          (Measure.map (P x) μ)
        exact (hsum Finset.univ).aemeasurable
      have hres :=
        statopia_math_node_2085562850_a652be1c μ P hP_meas hP_indep Ψ hΨ_ae hΨ_ae
      simpa only [Ψ, P] using hres
    have hAEm : ∀ (x : (k : Fin K) × Fin (ns k)) (j : Fin p), AEMeasurable (U x j) μ := by
      intro x j
      have hF : AEMeasurable (fun ω => f (H x.1 x.2 ω) j) μ :=
        ((hfH_sg x.1 x.2 j).memLp (1 : NNReal)).aestronglyMeasurable.aemeasurable
      have hE : AEMeasurable (fun ω => E x.1 x.2 ω j) μ :=
        ((hE_sg x.1 x.2 j).memLp (1 : NNReal)).aestronglyMeasurable.aemeasurable
      have hHm : ∀ l : Fin q, AEMeasurable (fun ω => H x.1 x.2 ω l) μ := fun l =>
        ((hH_sg x.1 x.2 l).memLp (1 : NNReal)).aestronglyMeasurable.aemeasurable
      have hterm : ∀ l : Fin q,
          AEMeasurable (fun ω => (d x.1).ofLp l *
            ((f (H x.1 x.2 ω) j + E x.1 x.2 ω j) * H x.1 x.2 ω l - M j l)) μ := by
        intro l
        have hc' : AEMeasurable (fun _ : Ω => M j l) μ := aemeasurable_const
        exact ((((hF.add hE).mul (hHm l)).sub hc').const_mul ((d x.1).ofLp l))
      have hmain : ∀ s : Finset (Fin q),
          AEMeasurable (fun ω => ∑ l ∈ s, (d x.1).ofLp l *
            ((f (H x.1 x.2 ω) j + E x.1 x.2 ω j) * H x.1 x.2 ω l - M j l)) μ := by
        intro s
        induction s using Finset.induction_on with
        | empty =>
            simpa using (aemeasurable_const : AEMeasurable (fun _ : Ω => (0 : ℝ)) μ)
        | insert a s ha ih =>
            have hfun : (fun ω => ∑ l ∈ insert a s, (d x.1).ofLp l *
                ((f (H x.1 x.2 ω) j + E x.1 x.2 ω j) * H x.1 x.2 ω l - M j l))
                = fun ω => (d x.1).ofLp a *
                    ((f (H x.1 x.2 ω) j + E x.1 x.2 ω j) * H x.1 x.2 ω a - M j a)
                  + ∑ l ∈ s, (d x.1).ofLp l *
                    ((f (H x.1 x.2 ω) j + E x.1 x.2 ω j) * H x.1 x.2 ω l - M j l) := by
              funext ω
              rw [Finset.sum_insert ha]
            rw [hfun]
            exact (hterm a).add ih
      exact hmain Finset.univ
    have hU_meas : ∀ (x : (k : Fin K) × Fin (ns k)) (j : Fin p), Measurable (U x j) := by
      intro x j
      have hF : Measurable (fun ω => f (H x.1 x.2 ω) j) :=
        (measurable_pi_apply j).comp (hf.comp (hH_meas x.1 x.2))
      have hE : Measurable (fun ω => E x.1 x.2 ω j) :=
        (measurable_pi_apply j).comp (hE_meas x.1 x.2)
      have hHm : ∀ l : Fin q, Measurable (fun ω => H x.1 x.2 ω l) := fun l =>
        (measurable_pi_apply l).comp (hH_meas x.1 x.2)
      have hterm : ∀ l : Fin q,
          Measurable (fun ω => (d x.1).ofLp l *
            ((f (H x.1 x.2 ω) j + E x.1 x.2 ω j) * H x.1 x.2 ω l - M j l)) := by
        intro l
        have hc' : Measurable (fun _ : Ω => M j l) := measurable_const
        exact (((hF.add hE).mul (hHm l)).sub hc').const_mul ((d x.1).ofLp l)
      have hmain : ∀ s : Finset (Fin q),
          Measurable (fun ω => ∑ l ∈ s, (d x.1).ofLp l *
            ((f (H x.1 x.2 ω) j + E x.1 x.2 ω j) * H x.1 x.2 ω l - M j l)) := by
        intro s
        induction s using Finset.induction_on with
        | empty =>
            simpa using (measurable_const : Measurable fun _ : Ω => (0 : ℝ))
        | insert a s ha ih =>
            have hfun : (fun ω => ∑ l ∈ insert a s, (d x.1).ofLp l *
                ((f (H x.1 x.2 ω) j + E x.1 x.2 ω j) * H x.1 x.2 ω l - M j l))
                = fun ω => (d x.1).ofLp a *
                    ((f (H x.1 x.2 ω) j + E x.1 x.2 ω j) * H x.1 x.2 ω a - M j a)
                  + ∑ l ∈ s, (d x.1).ofLp l *
                    ((f (H x.1 x.2 ω) j + E x.1 x.2 ω j) * H x.1 x.2 ω l - M j l) := by
              funext ω
              rw [Finset.sum_insert ha]
            rw [hfun]
            exact (hterm a).add ih
      exact hmain Finset.univ
    have hU_int : ∀ (x : (k : Fin K) × Fin (ns k)) (j : Fin p), Integrable (U x j) μ := by
      intro x j
      have hterm : ∀ l : Fin q,
          Integrable (fun ω => (d x.1).ofLp l *
            ((f (H x.1 x.2 ω) j + E x.1 x.2 ω j) * H x.1 x.2 ω l - M j l)) μ := by
        intro l
        exact ((hXH_int x.1 x.2 j l).sub (integrable_const (M j l))).const_mul ((d x.1).ofLp l)
      have hmain : ∀ s : Finset (Fin q),
          Integrable (fun ω => ∑ l ∈ s, (d x.1).ofLp l *
            ((f (H x.1 x.2 ω) j + E x.1 x.2 ω j) * H x.1 x.2 ω l - M j l)) μ := by
        intro s
        induction s using Finset.induction_on with
        | empty =>
            simpa using (integrable_const (0 : ℝ) : Integrable (fun _ : Ω => (0 : ℝ)) μ)
        | insert a s ha ih =>
            have hfun : (fun ω => ∑ l ∈ insert a s, (d x.1).ofLp l *
                ((f (H x.1 x.2 ω) j + E x.1 x.2 ω j) * H x.1 x.2 ω l - M j l))
                = fun ω => (d x.1).ofLp a *
                    ((f (H x.1 x.2 ω) j + E x.1 x.2 ω j) * H x.1 x.2 ω a - M j a)
                  + ∑ l ∈ s, (d x.1).ofLp l *
                    ((f (H x.1 x.2 ω) j + E x.1 x.2 ω j) * H x.1 x.2 ω l - M j l) := by
              funext ω
              rw [Finset.sum_insert ha]
            rw [hfun]
            exact (hterm a).add ih
      exact hmain Finset.univ
    have hcard : Fintype.card ((k : Fin K) × Fin (ns k)) = pooledSourceSize ns := by
      rw [Fintype.card_sigma]
      simp [pooledSourceSize]
    let e : ((k : Fin K) × Fin (ns k)) ≃ Fin (pooledSourceSize ns) :=
      (Fintype.equivFin _).trans (finCongr hcard)
    set C : ℝ := max 1 ((c + 10) / b) with hCdef
    have hCpos : 0 < C := by
      rw [hCdef]
      exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hbern : ∀ j : Fin p,
        μ.real {ω | C * Vstar *
            Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))
          < |(1 / (pooledSourceSize ns : ℝ)) * ∑ x, U x j ω|}
          ≤ 2 * (p : ℝ) ^ (-(c + 10)) := by
      intro j
      let Uj : Fin (pooledSourceSize ns) → Ω → ℝ := fun l => U (e.symm l) j
      have hUj_meas : ∀ l, Measurable (Uj l) := fun l => hU_meas (e.symm l) j
      have hUj_indep : iIndepFun Uj μ :=
        iIndepFun.precomp (f := fun x => U x j) (g := fun l => e.symm l)
          e.symm.injective (hindep j)
      have hUj_int : ∀ l, Integrable (Uj l) μ := fun l => hU_int (e.symm l) j
      have hUj_cent : ∀ l, ∫ ω, Uj l ω ∂μ = 0 := fun l => hcent (e.symm l) j
      have hUj_mom : ∀ (l : Fin (pooledSourceSize ns)) (r : ℕ), 2 ≤ r →
          ∫⁻ (ω : Ω), ENNReal.ofReal (|Uj l ω| ^ r) ∂μ
            ≤ ENNReal.ofReal ((r.factorial : ℝ) * Vstar ^ r) :=
        fun l r hr => hmom (e.symm l) j r hr
      have htpos : 0 < C * Vstar *
          Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ)) := by
        refine mul_pos (mul_pos hCpos hVstar_pos) ?_
        exact Real.sqrt_pos.mpr (div_pos hlogp hNpos_real)
      have hmain := hb (pooledSourceSize ns) hNpos Vstar hVstar_pos Ω μ Uj
        hUj_meas hUj_indep hUj_int hUj_cent hUj_mom
        (C * Vstar * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))) htpos
      have hsum_l : ∀ ω : Ω, (∑ l : Fin (pooledSourceSize ns), Uj l ω) = ∑ x, U x j ω :=
        fun ω => Equiv.sum_comp e.symm (fun x => U x j ω)
      have hset : {ω : Ω | C * Vstar * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))
            < |(1 / (pooledSourceSize ns : ℝ)) * ∑ x, U x j ω|}
          = {ω : Ω | C * Vstar * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))
            < |((pooledSourceSize ns : ℝ))⁻¹ * ∑ l : Fin (pooledSourceSize ns), Uj l ω|} := by
        ext ω
        simp only [Set.mem_setOf_eq, one_div, hsum_l ω]
      rw [hset]
      refine le_trans hmain ?_
      have hppos : (0 : ℝ) < (p : ℝ) := by
        exact_mod_cast (by omega : 0 < p)
      have hCge1 : 1 ≤ C := by
        rw [hCdef]; exact le_max_left _ _
      have hCge : (c + 10) / b ≤ C := by
        rw [hCdef]; exact le_max_right _ _
      have hxpos : 0 < Real.log (p : ℝ) / (pooledSourceSize ns : ℝ) :=
        div_pos hlogp hNpos_real
      have hxle1 : Real.log (p : ℝ) / (pooledSourceSize ns : ℝ) ≤ 1 :=
        (div_le_one hNpos_real).mpr hlogp_le
      have hxnn : 0 ≤ Real.log (p : ℝ) / (pooledSourceSize ns : ℝ) := le_of_lt hxpos
      have hs1 : Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ)) ≤ 1 := by
        have h := Real.sqrt_le_sqrt hxle1
        simpa using h
      have hnn : 0 ≤ Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ)) :=
        Real.sqrt_nonneg _
      have hsqrt_ge :
          Real.log (p : ℝ) / (pooledSourceSize ns : ℝ)
            ≤ Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ)) := by
        have hsq := Real.sq_sqrt hxnn
        nlinarith [hsq, hs1, hnn]
      have hsqval : (Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))) ^ 2
          = Real.log (p : ℝ) / (pooledSourceSize ns : ℝ) := Real.sq_sqrt hxnn
      have ht_sq :
          (C * Vstar * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))) ^ 2 / Vstar ^ 2
            = C ^ 2 * (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ)) := by
        rw [show (C * Vstar * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))) ^ 2 /
            Vstar ^ 2
            = C ^ 2 * (Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))) ^ 2 by
          field_simp]
        rw [hsqval]
      have ht_lin :
          (C * Vstar * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))) / Vstar
            = C * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ)) := by
        field_simp
      have harg1 : C * (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))
          ≤ C ^ 2 * (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ)) := by
        have hCC : C ≤ C ^ 2 := by nlinarith [hCge1]
        exact mul_le_mul_of_nonneg_right hCC hxnn
      have harg2 : C * (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))
          ≤ C * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ)) :=
        mul_le_mul_of_nonneg_left hsqrt_ge (le_of_lt hCpos)
      have hmin : C * (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))
          ≤ min ((C * Vstar * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))) ^ 2 / Vstar ^ 2)
              ((C * Vstar * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))) / Vstar) := by
        rw [ht_sq, ht_lin]
        exact le_min harg1 harg2
      have hNm : C * Real.log (p : ℝ) ≤ (pooledSourceSize ns : ℝ) *
          min ((C * Vstar * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))) ^ 2 / Vstar ^ 2)
              ((C * Vstar * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))) / Vstar) := by
        have h := mul_le_mul_of_nonneg_left hmin (le_of_lt hNpos_real)
        have heq : (pooledSourceSize ns : ℝ) *
            (C * (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))) = C * Real.log (p : ℝ) := by
          field_simp
        rwa [heq] at h
      have hbC : (c + 10) ≤ b * C := by
        have h := mul_le_mul_of_nonneg_left hCge (le_of_lt hbpos)
        have heq : b * ((c + 10) / b) = c + 10 := by field_simp
        rwa [heq] at h
      have hbN : (c + 10) * Real.log (p : ℝ) ≤ b * ((pooledSourceSize ns : ℝ) *
          min ((C * Vstar * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))) ^ 2 / Vstar ^ 2)
              ((C * Vstar * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))) / Vstar)) := by
        have h1 : (c + 10) * Real.log (p : ℝ) ≤ (b * C) * Real.log (p : ℝ) :=
          mul_le_mul_of_nonneg_right hbC (le_of_lt hlogp)
        have h2 : b * C * Real.log (p : ℝ) ≤ b * ((pooledSourceSize ns : ℝ) *
            min ((C * Vstar * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))) ^ 2 / Vstar ^ 2)
                ((C * Vstar * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))) / Vstar)) := by
          have h := mul_le_mul_of_nonneg_left hNm (le_of_lt hbpos)
          calc b * C * Real.log (p : ℝ) = b * (C * Real.log (p : ℝ)) := by ring
            _ ≤ b * ((pooledSourceSize ns : ℝ) *
                min ((C * Vstar * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))) ^ 2 /
                    Vstar ^ 2)
                  ((C * Vstar * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))) / Vstar)) := h
        linarith
      have hexp : Real.exp (-((c + 10) * Real.log (p : ℝ))) = (p : ℝ) ^ (-(c + 10)) := by
        rw [Real.rpow_def_of_pos hppos]
        congr 1
        ring
      have hexp_le : Real.exp (-(b * (pooledSourceSize ns : ℝ) *
          min ((C * Vstar * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))) ^ 2 / Vstar ^ 2)
              ((C * Vstar * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))) / Vstar)))
          ≤ (p : ℝ) ^ (-(c + 10)) := by
        have hmono : -(b * (pooledSourceSize ns : ℝ) *
            min ((C * Vstar * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))) ^ 2 /
                Vstar ^ 2)
              ((C * Vstar * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))) / Vstar))
            ≤ -((c + 10) * Real.log (p : ℝ)) := by linarith [hbN]
        calc Real.exp (-(b * (pooledSourceSize ns : ℝ) *
              min ((C * Vstar * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))) ^ 2 /
                  Vstar ^ 2)
                ((C * Vstar * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))) / Vstar)))
            ≤ Real.exp (-((c + 10) * Real.log (p : ℝ))) := Real.exp_le_exp.mpr hmono
          _ = (p : ℝ) ^ (-(c + 10)) := hexp
      exact mul_le_mul_of_nonneg_left hexp_le (by norm_num : (0 : ℝ) ≤ 2)
    have huniv_real : μ.real (Set.univ : Set Ω) = 1 := by simp
    have hthr : C * V * B_phi * Real.sqrt (q : ℝ) *
        Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))
        = C * Vstar * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ)) := by
      rw [hVstar]
      ring
    rw [hthr]
    haveI : Nonempty (Fin p) := ⟨⟨0, by omega⟩⟩
    have hset_eq : {ω : Ω | ¬ (‖weightedTransferVec ns f E H M d ω‖ ≤
          C * Vstar * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ)))}
        = ⋃ j : Fin p, {ω : Ω | C * Vstar *
              Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))
            < |weightedTransferVec ns f E H M d ω j|} := by
      ext ω
      have h1 : ¬ (‖weightedTransferVec ns f E H M d ω‖ ≤
            C * Vstar * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ)))
          ↔ ∃ j : Fin p, C * Vstar *
              Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))
            < |weightedTransferVec ns f E H M d ω j| := by
        rw [Statlib.HighDim.CovarianceMatrix.pi_real_norm_eq_sup_abs
          (weightedTransferVec ns f E H M d ω)]
        rw [Finset.sup'_le_iff]
        simp
      simpa only [Set.mem_setOf_eq, Set.mem_iUnion] using h1
    have hbound : μ.real {ω : Ω | ¬ (‖weightedTransferVec ns f E H M d ω‖ ≤
          C * Vstar * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ)))}
        ≤ (p : ℝ) * (2 * (p : ℝ) ^ (-(c + 10))) := by
      rw [hset_eq]
      refine le_trans (measureReal_iUnion_fintype_le
        (fun j : Fin p => {ω : Ω | C * Vstar *
              Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))
            < |weightedTransferVec ns f E H M d ω j|})) ?_
      have h2 : ∀ j : Fin p, μ.real {ω : Ω | C * Vstar *
            Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))
          < |weightedTransferVec ns f E H M d ω j|} ≤ 2 * (p : ℝ) ^ (-(c + 10)) := by
        intro j
        have hsetj : {ω : Ω | C * Vstar *
              Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))
            < |weightedTransferVec ns f E H M d ω j|}
            = {ω : Ω | C * Vstar * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))
              < |(1 / (pooledSourceSize ns : ℝ)) * ∑ x, U x j ω|} := by
          ext ω
          simp only [Set.mem_setOf_eq, hstep1 j ω]
        rw [hsetj]
        exact hbern j
      calc ∑ j : Fin p, μ.real {ω : Ω | C * Vstar *
              Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))
            < |weightedTransferVec ns f E H M d ω j|}
          ≤ ∑ _j : Fin p, (2 * (p : ℝ) ^ (-(c + 10))) :=
            Finset.sum_le_sum (fun j _ => h2 j)
        _ = (p : ℝ) * (2 * (p : ℝ) ^ (-(c + 10))) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hcompl : μ.real {ω : Ω | ¬ (‖weightedTransferVec ns f E H M d ω‖ ≤
          C * Vstar * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ)))} ≤
        (p : ℝ) ^ (-c) / 20 := by
      refine le_trans hbound ?_
      have hppos : (0 : ℝ) < (p : ℝ) := by linarith
      have hE1 : (p : ℝ) ^ (-c) = Real.exp (Real.log (p : ℝ) * (-c)) := by
        rw [Real.rpow_def_of_pos hppos]
      have hE2 : (p : ℝ) ^ (-(c + 10)) = Real.exp (Real.log (p : ℝ) * (-(c + 10))) := by
        rw [Real.rpow_def_of_pos hppos]
      have hKpos : 0 < Real.exp (Real.log (p : ℝ) * (-(c + 10))) := Real.exp_pos _
      have hkey : Real.exp (Real.log (p : ℝ) * (-c))
          = Real.exp (Real.log (p : ℝ) * (-(c + 10))) * (p : ℝ) ^ 10 := by
        have h10 : (p : ℝ) ^ 10 = Real.exp ((10 : ℕ) * Real.log (p : ℝ)) := by
          rw [show (p : ℝ) ^ 10 = (Real.exp (Real.log (p : ℝ))) ^ 10 by
            rw [Real.exp_log hppos]]
          exact (Real.exp_nat_mul (Real.log (p : ℝ)) 10).symm
        rw [h10, ← Real.exp_add]
        congr 1
        push_cast
        ring
      rw [hE1, hE2, hkey]
      have hp9 : (40 : ℝ) ≤ (p : ℝ) ^ 9 := by
        have h : (2 : ℝ) ^ 9 ≤ (p : ℝ) ^ 9 := by
          gcongr <;> linarith [hp2]
        norm_num at h
        linarith
      have hp0 : (0 : ℝ) ≤ (p : ℝ) := by linarith
      have hp10 : (40 : ℝ) * (p : ℝ) ≤ (p : ℝ) ^ 10 := by
        calc (40 : ℝ) * (p : ℝ) ≤ (p : ℝ) ^ 9 * p := mul_le_mul_of_nonneg_right hp9 hp0
          _ = (p : ℝ) ^ 10 := by ring
      have h2p : 2 * (p : ℝ) ≤ (p : ℝ) ^ 10 / 20 := by nlinarith [hp10]
      have hmul := mul_le_mul_of_nonneg_left h2p (le_of_lt hKpos)
      nlinarith [hmul]
    have hpartition : (1 : ℝ) ≤
        μ.real {ω : Ω | ‖weightedTransferVec ns f E H M d ω‖ ≤
          C * Vstar * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))} +
        μ.real {ω : Ω | ¬ (‖weightedTransferVec ns f E H M d ω‖ ≤
          C * Vstar * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ)))} := by
      have h := measureReal_union_le (μ := μ)
        {ω : Ω | ‖weightedTransferVec ns f E H M d ω‖ ≤
          C * Vstar * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))}
        {ω : Ω | ¬ (‖weightedTransferVec ns f E H M d ω‖ ≤
          C * Vstar * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ)))}
      have hunion : {ω : Ω | ‖weightedTransferVec ns f E H M d ω‖ ≤
            C * Vstar * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))} ∪
          {ω : Ω | ¬ (‖weightedTransferVec ns f E H M d ω‖ ≤
            C * Vstar * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ)))} = Set.univ := by
        ext ω
        by_cases h : ‖weightedTransferVec ns f E H M d ω‖ ≤
            C * Vstar * Real.sqrt (Real.log (p : ℝ) / (pooledSourceSize ns : ℝ))
        · exact ⟨fun _ => trivial, fun _ => Or.inl h⟩
        · exact ⟨fun _ => trivial, fun _ => Or.inr h⟩
      rw [hunion, huniv_real] at h
      exact h
    linarith
  /- @proof-region region.root.56f4601e0a10 end -/

end Statlib.Imported

-- Paper root revision 12662f51-8cf3-456d-a31c-a0603d2387ca

