import Lean
import ProverJobs.ResidualE2ESupport20261106.M_07619582e197b023f046
import ProverJobs.ResidualE2ESupport20261106.M_c6e6716ab874a75a3ac2
import ProverJobs.ResidualE2ESupport20261106.M_00c436c24a07e32d2a50
import ProverJobs.ResidualE2ESupport20261106.M_768d89edee376a3171f4

namespace PaperProofTasks.ResidualE2ESupport20261106
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace ResidualLoss20261106.Statlib.Imported
universe u

set_option maxHeartbeats 4000000 in
theorem sparse_rigidity_loss_vocabulary (K rhoMin : ℝ) (hK : 0 < K) (hrhoMin : 0 < rhoMin)
    (alpha0 : ℝ) (halpha0 : 15 < alpha0) :
    ∃ CR cR : ℝ, 0 < CR ∧ 0 < cR ∧ ∃ m0att : ℕ, ∀ (m n : ℕ) (hnm : n ≤ m) (hn : 0 < n) (p : ℝ) (γ : Fin n → ℝ)
        (hp0 : 0 < p) (hp1 : p ≤ 1) (hrho_lo : rhoMin ≤ (rho m n)) (hrho_hi : (rho m n) ≤ 1)
        (hm : m0att ≤ m)
        (hmp : Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p)
        (hgamma : ∀ i : Fin n,
          (∫ x, nuRho (rho m n) x ∂(volume.restrict (Set.Icc (γ i) (lambdaPlus (rho m n)))))
            = (((i : ℕ) : ℝ) + 1 - 1 / 2) / (n : ℝ))
        {Ωs : Type u} [MeasurableSpace Ωs] (μ : Measure Ωs) [IsProbabilityMeasure μ]
        (Om : Ωs → Matrix (Fin m) (Fin n) ℝ) (Xi : Ωs → Matrix (Fin m) (Fin n) ℝ)
        (hOm_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun s : Ωs => Om s i j)
        (hOm_bin : ∀ (s : Ωs) (i : Fin m) (j : Fin n), Om s i j = 0 ∨ Om s i j = 1)
        (hOm_prob : ∀ (i : Fin m) (j : Fin n), μ {s : Ωs | Om s i j = 1} = ENNReal.ofReal p)
        (hXi_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun s : Ωs => Xi s i j)
        (hXi_int : ∀ (i : Fin m) (j : Fin n), Integrable (fun s : Ωs => Xi s i j) μ)
        (hXi_mean : ∀ (i : Fin m) (j : Fin n), (∫ s, Xi s i j ∂μ) = 0)
        (hXi_int2 : ∀ (i : Fin m) (j : Fin n), Integrable (fun s : Ωs => (Xi s i j) ^ 2) μ)
        (hXi_var : ∀ (i : Fin m) (j : Fin n), (∫ s, (Xi s i j) ^ 2 ∂μ) = 1)
        (hXi_tail : ∀ (i : Fin m) (j : Fin n) (t : ℝ), 0 < t →
          μ {s : Ωs | t < |Xi s i j|} ≤ ENNReal.ofReal (2 * Real.exp (-(t / K))))
        (hindep : iIndepFun (fun (x : (Fin m × Fin n) ⊕ (Fin m × Fin n)) => fun s : Ωs =>
          match x with
          | Sum.inl q => Om s q.1 q.2
          | Sum.inr q => Xi s q.1 q.2) μ),
        μ {s : Ωs | ∃ i : Fin n,
              CR * deltaM m
                < |sv hnm (maskOp (Om s) (Xi s)) i / Real.sqrt ((m : ℝ) * p) - γ i|}
            ≤ ENNReal.ofReal (cR * Real.rpow (n : ℝ) (-4 : ℝ)) ∧
        (∀ s : Ωs, ¬ (∃ i : Fin n,
              CR * deltaM m
                < |sv hnm (maskOp (Om s) (Xi s)) i / Real.sqrt ((m : ℝ) * p) - γ i|) →
          sv hnm (maskOp (Om s) (Xi s)) ⟨0, hn⟩
              / Real.sqrt ((m : ℝ) * p)
            ≤ 1 + Real.sqrt (rho m n) + CR * deltaM m) := by
  classical
  obtain ⟨M0, hM0, CR, cR, hCR, hcR, hRig⟩ :=
    _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.sparse_coarse_rigidity_all_alpha.{u}
      4 (by norm_num) rhoMin hrhoMin K hK alpha0 halpha0
  refine ⟨CR, cR, hCR, hcR, M0, ?_⟩
  intro m n hnm hn p gamma hp0 hp1 hrholo hrhohi hm hmp hgamma Ωs _ μ _ Om Xi
    hOmmeas hOmbin hOmprob hXimeas hXiint hXimean hXiint2 hXivar hXitail hindep
  have hm1 : 1 ≤ m := by omega
  have hn1 : 1 ≤ n := hn
  have hind := ResidualLoss20261106.sum_independence μ
    (fun ω (ij : Fin m × Fin n) => Xi ω ij.1 ij.2) (fun ω (ij : Fin m × Fin n) => Om ω ij.1 ij.2)
    (fun ij => hXimeas ij.1 ij.2) (fun ij => hOmmeas ij.1 ij.2) (by
      convert hindep using 1
      funext k ω
      cases k <;> rfl)
  have hq : _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.mpQuantile ((n : ℝ) / (m : ℝ)) n = gamma := by
    funext i
    exact statopia_math_node_2169097838_d24405fa (rho m n)
      (lt_of_lt_of_le hrhoMin hrholo) hrhohi n gamma hgamma i
  have hv : ∀ ω i, _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.svals
        (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.maskedScaled p (Xi ω) (Om ω)) i
      = sv hnm (maskOp (Om ω) (Xi ω)) i / Real.sqrt ((m : ℝ) * p) := by
    intro ω i
    rw [← sv_eq_sparse_svals hnm]
    have heq : _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.maskedScaled p (Xi ω) (Om ω) =
        fun a b => (Real.sqrt ((m : ℝ) * p))⁻¹ * maskOp (Om ω) (Xi ω) a b := by
      ext a b
      simp only [_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.maskedScaled, maskOp, div_eq_mul_inv]
      ring
    rw [heq, statopia_math_node_3402644224_aa9fa448 m n hnm _ (by positivity)]
    ring
  have happ := hRig m n hm1 hn1 hm hrholo hrhohi p hp0.le hp1 hmp μ Xi Om
    hXimeas hXiint hXiint2 hind.1 hXimean hXivar (by simpa only [neg_div] using hXitail) hOmmeas
    (fun i j ω => hOmbin ω i j) hOmprob hind.2.1 hind.2.2
  rw [hq] at happ
  have hset : {ω | CR * _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.deltaM m <
      _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.maxDeviation
        (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.svals (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.maskedScaled p (Xi ω) (Om ω))) gamma}
      = {ω | ∃ i : Fin n, CR * deltaM m <
          |sv hnm (maskOp (Om ω) (Xi ω)) i / Real.sqrt ((m : ℝ) * p) - gamma i|} := by
    ext ω
    let f : Fin n → ℝ := fun i =>
      |sv hnm (maskOp (Om ω) (Xi ω)) i / Real.sqrt ((m : ℝ) * p) - gamma i|
    have hb : BddAbove (Set.range f) := (Set.finite_range f).bddAbove
    have hnE : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    letI := hnE
    simp only [Set.mem_setOf_eq, _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.maxDeviation]
    simp_rw [hv]
    change CR * deltaM m < sSup (Set.range f) ↔ ∃ i, CR * deltaM m < f i
    rw [lt_csSup_iff hb (Set.range_nonempty f)]
    simp
  constructor
  · simpa only [hset] using happ.1
  · intro ω hnot
    have hle : _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.maxDeviation
        (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.svals (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.maskedScaled p (Xi ω) (Om ω))) gamma
        ≤ CR * _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.deltaM m := by
      by_contra hh
      have hmemb : ω ∈ {ω | CR * _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.deltaM m <
        _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.maxDeviation
          (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.svals (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.maskedScaled p (Xi ω) (Om ω))) gamma} :=
        lt_of_not_ge hh
      rw [hset] at hmemb
      exact hnot hmemb
    simpa only [hv] using happ.2 ω hle

end ResidualLoss20261106.Statlib.Imported
#print axioms ResidualLoss20261106.Statlib.Imported.sparse_rigidity_loss_vocabulary

