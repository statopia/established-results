import Lean
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.Vocabulary
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.Base
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.ExternalNodes.Node_6515c10a3b2a6920f75d

namespace PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
open _root_.PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
noncomputable section
set_option maxHeartbeats 1000000

set_option autoImplicit false in
theorem statopia_math_node_1156518618_e13ca37b : ∀ (S : Type*) [MeasurableSpace S]
    (Rand : Type*) [MeasurableSpace Rand]
    (P : Measure Rand) [IsProbabilityMeasure P]
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (B1 : ℝ) (hB1 : 0 < B1)
    (f0 : S → ℝ) (X : Fin n → Fin m → Rand → S)
    (sigma : Fin n → Fin m → Rand → ℝ)
    (Fs : Finset (S → ℝ)) (Psi : ℝ → ℝ)
    (hf0_meas : Measurable f0)
    (hFs_meas : ∀ f ∈ (Fs : Set (S → ℝ)), Measurable f)
    (hf0_bound : ∀ x : S, |f0 x| ≤ B1)
    (hFs_bound : ∀ f ∈ (Fs : Set (S → ℝ)), ∀ x : S, |f x| ≤ B1)
    (hX_meas : ∀ p : Fin n × Fin m, Measurable (X p.1 p.2))
    (hsigma_meas : ∀ p : Fin n × Fin m, Measurable (sigma p.1 p.2))
    (hsigma_law : ∀ p : Fin n × Fin m,
      Measure.map (sigma p.1 p.2) P = Statlib.Imported.rademacherLaw)
    (hsigma_indep : iIndepFun (fun p : Fin n × Fin m => sigma p.1 p.2) P)
    (hsigma_indep_X :
      IndepFun (fun ω => fun p : Fin n × Fin m => sigma p.1 p.2 ω)
        (fun ω => fun p : Fin n × Fin m => X p.1 p.2 ω) P)
    (hPsi_lip : LipschitzWith (⟨4 * B1, by positivity⟩ : NNReal) Psi)
    (hPsi_zero : Psi 0 = 0),
    ∫ ω, sSup ((fun f : S → ℝ =>
        |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          sigma i j ω * Psi (f (X i j ω) - f0 (X i j ω))|) '' (Fs : Set (S → ℝ))) ∂P
      ≤ 8 * B1 * ∫ ω, sSup ((fun f : S → ℝ =>
        |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          sigma i j ω * (f (X i j ω) - f0 (X i j ω))|) '' (Fs : Set (S → ℝ))) ∂P := by
  /- @proof-region region.target-node.session.a5aa5a2303894279 begin -/
  intro S instS Rand instRand P instP n m hn hm B1 hB1 f0 X sigma Fs Psi
    hf0_meas hFs_meas hf0_bound hFs_bound hX_meas hsigma_meas hsigma_law hsigma_indep
    hsigma_indep_X hPsi_lip hPsi_zero
  classical
  haveI hRadem_prob : IsProbabilityMeasure rademacherLaw := by
    have hp : Fin n × Fin m := (⟨0, hn⟩, ⟨0, hm⟩)
    have hinst := Measure.isProbabilityMeasure_map (μ := P) (f := sigma hp.1 hp.2)
      (hsigma_meas hp).aemeasurable
    rwa [hsigma_law hp] at hinst
  haveI hRadem_sf : SigmaFinite rademacherLaw := inferInstance
  have hPsi_bound : ∀ t : ℝ, |Psi t| ≤ 4 * B1 * |t| := by
    intro t
    have h := (lipschitzWith_iff_dist_le_mul.mp hPsi_lip) t 0
    rw [Real.dist_eq, Real.dist_eq, hPsi_zero, sub_zero, sub_zero] at h
    simpa using h
  let sv : Rand → (Fin n × Fin m → ℝ) := fun ω p => sigma p.1 p.2 ω
  let xv : Rand → (Fin n × Fin m → S) := fun ω p => X p.1 p.2 ω
  have hsv_meas : Measurable sv := by
    refine measurable_pi_iff.mpr ?_
    intro p
    exact hsigma_meas p
  have hxv_meas : Measurable xv := by
    refine measurable_pi_iff.mpr ?_
    intro p
    exact hX_meas p
  have hsv_law : Measure.map sv P = Measure.pi (fun _ : Fin n × Fin m => rademacherLaw) := by
    have h' : Measure.map sv P
        = Measure.pi (fun i : Fin n × Fin m => Measure.map (sigma i.1 i.2) P) :=
      (iIndepFun_iff_map_fun_eq_pi_map (f := fun p : Fin n × Fin m => sigma p.1 p.2)
        (fun p => (hsigma_meas p).aemeasurable)).mp hsigma_indep
    rw [h']
    congr 1
    funext p
    exact hsigma_law p
  have hjoint :
      Measure.map (fun ω : Rand => (xv ω, sv ω)) P
        = (Measure.map xv P).prod (Measure.pi (fun _ : Fin n × Fin m => rademacherLaw)) := by
    rw [← hsv_law]
    exact (indepFun_iff_map_prod_eq_prod_map_map hxv_meas.aemeasurable
      hsv_meas.aemeasurable).mp hsigma_indep_X.symm
  haveI : IsProbabilityMeasure (Measure.map xv P) :=
    Measure.isProbabilityMeasure_map hxv_meas.aemeasurable
  have hcard : Fintype.card (Fin n × Fin m) = n * m := by
    simp [Fintype.card_prod]
  let e : (Fin n × Fin m) ≃ Fin (n * m) := Fintype.equivFinOfCardEq hcard
  have heN : ((n * m : ℕ) : ℝ) = (n : ℝ) * (m : ℝ) := by push_cast; ring
  have hmapR : Measure.map (fun τ : Fin (n * m) → ℝ => fun p : Fin n × Fin m => τ (e p))
      (Measure.pi (fun _ : Fin (n * m) => rademacherLaw))
      = Measure.pi (fun _ : Fin n × Fin m => rademacherLaw) := by
    have hR_meas : Measurable (fun τ : Fin (n * m) → ℝ => fun p : Fin n × Fin m => τ (e p)) := by
      refine measurable_pi_iff.mpr ?_
      intro p
      exact measurable_pi_apply (e p)
    refine (Measure.pi_eq ?_).symm
    intro s hs
    rw [Measure.map_apply hR_meas (MeasurableSet.univ_pi hs)]
    have hpre : (fun τ : Fin (n * m) → ℝ => fun p : Fin n × Fin m => τ (e p)) ⁻¹' Set.univ.pi s
        = Set.univ.pi (fun k : Fin (n * m) => s (e.symm k)) := by
      ext τ
      rw [Set.mem_preimage, Set.mem_univ_pi, Set.mem_univ_pi]
      constructor
      · intro h i
        have := h (e.symm i)
        simpa using this
      · intro h p
        have h1 := h (e p)
        rw [Equiv.symm_apply_apply] at h1
        exact h1
    rw [hpre, Measure.pi_pi]
    refine (Equiv.prod_comp e
      (fun k : Fin (n * m) => rademacherLaw (s (e.symm k)))).symm.trans ?_
    exact Finset.prod_congr rfl (fun p _ => by simp)
  have hsum_reindex : ∀ (τ : Fin (n * m) → ℝ) (a : Fin n × Fin m → ℝ),
      (∑ i : Fin n, ∑ j : Fin m, τ (e (i, j)) * a (i, j))
        = ∑ k : Fin (n * m), τ k * a (e.symm k) := by
    intro τ a
    rw [← Fintype.sum_prod_type (f := fun p : Fin n × Fin m => τ (e p) * a p)]
    rw [← Equiv.sum_comp e (fun k : Fin (n * m) => τ k * a (e.symm k))]
    exact Finset.sum_congr rfl (fun p _ => by simp)
  have t1 : ∀ (s : Set ℝ), BddAbove s → ∀ x ∈ s, x ≤ sSup s :=
    fun s hB x hx => le_csSup hB hx
  have t2 : ∀ (s : Set ℝ) (a : ℝ), s.Nonempty → (∀ x ∈ s, x ≤ a) → sSup s ≤ a :=
    fun s a hne h => csSup_le hne h
  have t3 : ∀ (s : Set ℝ), (∀ x ∈ s, 0 ≤ x) → 0 ≤ sSup s :=
    fun s h => Real.sSup_nonneg h
  have t4 : sSup (∅ : Set ℝ) = 0 := Real.sSup_empty
  have t5 : ∀ (s : Set ℝ), s.Finite → Bornology.IsBounded s :=
    fun s hs => hs.isBounded
  have hsup_insert : ∀ (a : ℝ) (T : Set ℝ), T.Finite → 0 ≤ a →
      sSup (insert a T) = max a (sSup T) := by
    intro a T hT ha
    have hbdd : BddAbove T := hT.bddAbove
    refine le_antisymm ?_ ?_
    · refine Real.sSup_le ?_ ?_
      · intro x hx
        rw [Set.mem_insert_iff] at hx
        rcases hx with rfl | hx
        · exact le_max_left _ _
        · exact le_trans (le_csSup hbdd hx) (le_max_right _ _)
      · exact le_trans ha (le_max_left _ _)
    · refine max_le ?_ ?_
      · exact le_csSup (hT.insert a).bddAbove (Set.mem_insert a T)
      · rcases T.eq_empty_or_nonempty with hT0 | hTne
        · subst hT0
          rw [Real.sSup_empty]
          exact le_trans ha (le_csSup (hT.insert a).bddAbove (Set.mem_insert a ∅))
        · refine csSup_le hTne ?_
          intro x hx
          exact le_csSup (hT.insert a).bddAbove (Set.mem_insert_of_mem a hx)
  have hsup_meas : ∀ (T : Finset (S → ℝ))
      (G : (S → ℝ) → ((Fin n × Fin m → S) × (Fin n × Fin m → ℝ)) → ℝ),
      (∀ f ∈ (T : Set (S → ℝ)), Measurable (G f)) →
      (∀ (f : S → ℝ) (z : (Fin n × Fin m → S) × (Fin n × Fin m → ℝ)), 0 ≤ G f z) →
      Measurable (fun z : (Fin n × Fin m → S) × (Fin n × Fin m → ℝ) =>
        sSup ((fun f => G f z) '' (T : Set (S → ℝ)))) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
        intro G _ _
        have h0 : (fun z : (Fin n × Fin m → S) × (Fin n × Fin m → ℝ) =>
            sSup ((fun f => G f z) '' ((∅ : Finset (S → ℝ)) : Set (S → ℝ))))
            = fun _ => (0 : ℝ) := by
          funext z
          rw [Finset.coe_empty, Set.image_empty, Real.sSup_empty]
        rw [h0]
        exact measurable_const
    | insert a s ha ih =>
        intro G hGmeas hGnn
        have hfun : (fun z : (Fin n × Fin m → S) × (Fin n × Fin m → ℝ) =>
            sSup ((fun f => G f z) '' ((insert a s : Finset (S → ℝ)) : Set (S → ℝ))))
            = fun z => max (G a z) (sSup ((fun f => G f z) '' (s : Set (S → ℝ)))) := by
          funext z
          rw [Finset.coe_insert, Set.image_insert_eq]
          exact hsup_insert (G a z) ((fun f => G f z) '' (s : Set (S → ℝ)))
            (s.finite_toSet.image _) (hGnn a z)
        rw [hfun]
        exact (hGmeas a (Finset.mem_insert_self a s)).max
          (ih G (fun f hf => hGmeas f (Finset.mem_insert_of_mem hf)) hGnn)
  have htransport :
      ∀ (G : (Fin n × Fin m → S) → (Fin n × Fin m → ℝ) → ℝ),
        Measurable (fun z : (Fin n × Fin m → S) × (Fin n × Fin m → ℝ) => G z.1 z.2) →
        Integrable (fun z : (Fin n × Fin m → S) × (Fin n × Fin m → ℝ) => G z.1 z.2)
          ((Measure.map xv P).prod (Measure.pi (fun _ : Fin n × Fin m => rademacherLaw))) →
        ∫ ω, G (xv ω) (sv ω) ∂P
          = ∫ x, ∫ σ, G x σ ∂(Measure.pi (fun _ : Fin n × Fin m => rademacherLaw))
              ∂(Measure.map xv P) := by
    intro G hGmeas hint
    have hstep1 : ∫ ω, G (xv ω) (sv ω) ∂P
        = ∫ z : (Fin n × Fin m → S) × (Fin n × Fin m → ℝ), G z.1 z.2
            ∂(Measure.map (fun ω => (xv ω, sv ω)) P) := by
      refine (integral_map (μ := P) (φ := fun ω : Rand => (xv ω, sv ω))
        (f := fun z : (Fin n × Fin m → S) × (Fin n × Fin m → ℝ) => G z.1 z.2)
        ?_ ?_).symm
      · exact AEMeasurable.prodMk hxv_meas.aemeasurable hsv_meas.aemeasurable
      · rw [hjoint]
        exact hGmeas.aestronglyMeasurable
    have hstep2 : ∫ z : (Fin n × Fin m → S) × (Fin n × Fin m → ℝ), G z.1 z.2
          ∂(Measure.map (fun ω => (xv ω, sv ω)) P)
        = ∫ x, ∫ σ, G x σ ∂(Measure.pi (fun _ : Fin n × Fin m => rademacherLaw))
            ∂(Measure.map xv P) := by
      rw [hjoint]
      exact MeasureTheory.integral_prod
        (fun z : (Fin n × Fin m → S) × (Fin n × Fin m → ℝ) => G z.1 z.2) hint
    rw [hstep1, hstep2]
  have hradem_ae : ∀ᵐ x ∂rademacherLaw, |x| = 1 := by
    rw [MeasureTheory.ae_iff]
    simp only [rademacherLaw, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply]
    simp
  have hsignp : ∀ p : Fin n × Fin m, ∀ᵐ ω ∂P, |sigma p.1 p.2 ω| = 1 := by
    intro p
    have hset : MeasurableSet {x : ℝ | |x| = 1} :=
      (measurableSet_singleton (1 : ℝ)).preimage continuous_abs.measurable
    have hradem' : ∀ᵐ y ∂(Measure.map (sigma p.1 p.2) P), |y| = 1 := by
      rw [hsigma_law p]
      exact hradem_ae
    exact (MeasureTheory.ae_map_iff (hsigma_meas p).aemeasurable
      (p := fun x : ℝ => |x| = 1) hset).mp hradem'
  have hsign : ∀ᵐ ω ∂P, ∀ p : Fin n × Fin m, |sigma p.1 p.2 ω| = 1 := by
    have key : ∀ (s : Finset (Fin n × Fin m)), ∀ᵐ ω ∂P, ∀ p ∈ s, |sigma p.1 p.2 ω| = 1 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert a t ha ih =>
          filter_upwards [hsignp a, ih] with ω h1 h2
          intro p hp
          rcases Finset.mem_insert.mp hp with rfl | hp
          · exact h1
          · exact h2 p hp
    simpa using key Finset.univ
  have hPsi_meas : Measurable Psi := hPsi_lip.continuous.measurable
  have hGPsi_meas : Measurable (fun z : (Fin n × Fin m → S) × (Fin n × Fin m → ℝ) =>
      sSup ((fun f : S → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
        z.2 (i, j) * Psi (f (z.1 (i, j)) - f0 (z.1 (i, j)))|) '' (Fs : Set (S → ℝ)))) := by
    refine hsup_meas Fs
      (fun f z => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
        z.2 (i, j) * Psi (f (z.1 (i, j)) - f0 (z.1 (i, j)))|) ?_ (fun f z => abs_nonneg _)
    intro f hf
    have hf_meas : Measurable f := hFs_meas f hf
    fun_prop
  have hGid_meas : Measurable (fun z : (Fin n × Fin m → S) × (Fin n × Fin m → ℝ) =>
      sSup ((fun f : S → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
        z.2 (i, j) * (f (z.1 (i, j)) - f0 (z.1 (i, j)))|) '' (Fs : Set (S → ℝ)))) := by
    refine hsup_meas Fs
      (fun f z => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
        z.2 (i, j) * (f (z.1 (i, j)) - f0 (z.1 (i, j)))|) ?_ (fun f z => abs_nonneg _)
    intro f hf
    have hf_meas : Measurable f := hFs_meas f hf
    fun_prop
  have hsup_meas2 : ∀ (T : Finset (S → ℝ))
      (G : (S → ℝ) → (Fin n × Fin m → ℝ) → ℝ),
      (∀ f ∈ (T : Set (S → ℝ)), Measurable (G f)) →
      (∀ (f : S → ℝ) (z : Fin n × Fin m → ℝ), 0 ≤ G f z) →
      Measurable (fun z : Fin n × Fin m → ℝ =>
        sSup ((fun f => G f z) '' (T : Set (S → ℝ)))) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
        intro G _ _
        have h0 : (fun z : Fin n × Fin m → ℝ =>
            sSup ((fun f => G f z) '' ((∅ : Finset (S → ℝ)) : Set (S → ℝ))))
            = fun _ => (0 : ℝ) := by
          funext z
          rw [Finset.coe_empty, Set.image_empty, Real.sSup_empty]
        rw [h0]
        exact measurable_const
    | insert a s ha ih =>
        intro G hGmeas hGnn
        have hfun : (fun z : Fin n × Fin m → ℝ =>
            sSup ((fun f => G f z) '' ((insert a s : Finset (S → ℝ)) : Set (S → ℝ))))
            = fun z => max (G a z) (sSup ((fun f => G f z) '' (s : Set (S → ℝ)))) := by
          funext z
          rw [Finset.coe_insert, Set.image_insert_eq]
          exact hsup_insert (G a z) ((fun f => G f z) '' (s : Set (S → ℝ)))
            (s.finite_toSet.image _) (hGnn a z)
        rw [hfun]
        exact (hGmeas a (Finset.mem_insert_self a s)).max
          (ih G (fun f hf => hGmeas f (Finset.mem_insert_of_mem hf)) hGnn)
  have hcond : ∀ (x : Fin n × Fin m → S),
      ∫ σ : Fin n × Fin m → ℝ, sSup ((fun f : S → ℝ =>
          |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
            σ (i, j) * Psi (f (x (i, j)) - f0 (x (i, j)))|) '' (Fs : Set (S → ℝ)))
          ∂(Measure.pi (fun _ : Fin n × Fin m => rademacherLaw))
        ≤ 8 * B1 * ∫ σ : Fin n × Fin m → ℝ, sSup ((fun f : S → ℝ =>
          |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
            σ (i, j) * (f (x (i, j)) - f0 (x (i, j)))|) '' (Fs : Set (S → ℝ)))
          ∂(Measure.pi (fun _ : Fin n × Fin m => rademacherLaw)) := by
    intro x
    have hR_meas : Measurable (fun τ : Fin (n * m) → ℝ => fun p : Fin n × Fin m => τ (e p)) := by
      refine measurable_pi_iff.mpr ?_
      intro p
      exact measurable_pi_apply (e p)
    set phi : (S → ℝ) → (Fin (n * m) → ℝ) :=
      fun f k => f (x (e.symm k)) - f0 (x (e.symm k)) with hphi
    set Om : Set (Fin (n * m) → ℝ) := phi '' (Fs : Set (S → ℝ)) with hOm
    have hbdd : Bornology.IsBounded Om := by
      rw [hOm]
      exact Set.Finite.isBounded (Fs.finite_toSet.image phi)
    have hkey := ext_model_1 (n := n * m) (Nat.mul_pos hn hm) (4 * B1) (by positivity)
      (fun _ : Fin (n * m) => Psi) Om (fun _ => hPsi_lip) (fun _ => hPsi_zero) hbdd
      (Measure.pi (fun _ : Fin (n * m) => rademacherLaw)) rfl
    have htr : ∀ (F : (Fin n × Fin m → ℝ) → ℝ), Measurable F →
        ∫ σ : Fin n × Fin m → ℝ, F σ ∂(Measure.pi (fun _ : Fin n × Fin m => rademacherLaw))
          = ∫ τ : Fin (n * m) → ℝ, F (fun p => τ (e p))
              ∂(Measure.pi (fun _ : Fin (n * m) => rademacherLaw)) := by
      intro F hF
      have h' : AEStronglyMeasurable F
          (Measure.map (fun τ : Fin (n * m) → ℝ => fun p : Fin n × Fin m => τ (e p))
            (Measure.pi (fun _ : Fin (n * m) => rademacherLaw))) := hF.aestronglyMeasurable
      have h2 := integral_map (μ := Measure.pi (fun _ : Fin (n * m) => rademacherLaw))
        (φ := fun τ : Fin (n * m) → ℝ => fun p : Fin n × Fin m => τ (e p)) (f := F)
        hR_meas.aemeasurable h'
      rwa [hmapR] at h2
    have hF1 : Measurable (fun σ : Fin n × Fin m → ℝ => sSup ((fun f : S → ℝ =>
        |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          σ (i, j) * Psi (f (x (i, j)) - f0 (x (i, j)))|) '' (Fs : Set (S → ℝ)))) := by
      refine hsup_meas2 Fs
        (fun f σ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          σ (i, j) * Psi (f (x (i, j)) - f0 (x (i, j)))|) ?_ (fun f σ => abs_nonneg _)
      intro f hf
      have hf_meas : Measurable f := hFs_meas f hf
      fun_prop
    have hF2 : Measurable (fun σ : Fin n × Fin m → ℝ => sSup ((fun f : S → ℝ =>
        |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          σ (i, j) * (f (x (i, j)) - f0 (x (i, j)))|) '' (Fs : Set (S → ℝ)))) := by
      refine hsup_meas2 Fs
        (fun f σ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          σ (i, j) * (f (x (i, j)) - f0 (x (i, j)))|) ?_ (fun f σ => abs_nonneg _)
      intro f hf
      have hf_meas : Measurable f := hFs_meas f hf
      fun_prop
    have htrL : ∫ σ : Fin n × Fin m → ℝ, sSup ((fun f : S → ℝ =>
        |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          σ (i, j) * Psi (f (x (i, j)) - f0 (x (i, j)))|) '' (Fs : Set (S → ℝ)))
        ∂(Measure.pi (fun _ : Fin n × Fin m => rademacherLaw))
        = ∫ τ : Fin (n * m) → ℝ, sSup ((fun f : S → ℝ =>
        |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          τ (e (i, j)) * Psi (f (x (i, j)) - f0 (x (i, j)))|) '' (Fs : Set (S → ℝ)))
        ∂(Measure.pi (fun _ : Fin (n * m) => rademacherLaw)) := htr _ hF1
    have htrR : ∫ σ : Fin n × Fin m → ℝ, sSup ((fun f : S → ℝ =>
        |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          σ (i, j) * (f (x (i, j)) - f0 (x (i, j)))|) '' (Fs : Set (S → ℝ)))
        ∂(Measure.pi (fun _ : Fin n × Fin m => rademacherLaw))
        = ∫ τ : Fin (n * m) → ℝ, sSup ((fun f : S → ℝ =>
        |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          τ (e (i, j)) * (f (x (i, j)) - f0 (x (i, j)))|) '' (Fs : Set (S → ℝ)))
        ∂(Measure.pi (fun _ : Fin (n * m) => rademacherLaw)) := htr _ hF2
    have hpt1 : ∀ (τ : Fin (n * m) → ℝ), ∀ f ∈ (Fs : Set (S → ℝ)),
        |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
            τ (e (i, j)) * Psi (f (x (i, j)) - f0 (x (i, j)))|
          = |((n * m : ℕ) : ℝ)⁻¹ * ∑ k : Fin (n * m),
              τ k * Psi (f (x (e.symm k)) - f0 (x (e.symm k)))| := by
      intro τ f hf
      rw [hsum_reindex τ (fun p : Fin n × Fin m => Psi (f (x p) - f0 (x p))), ← heN]
    have hpt2 : ∀ (τ : Fin (n * m) → ℝ), ∀ f ∈ (Fs : Set (S → ℝ)),
        |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
            τ (e (i, j)) * (f (x (i, j)) - f0 (x (i, j)))|
          = |((n * m : ℕ) : ℝ)⁻¹ * ∑ k : Fin (n * m),
              τ k * (f (x (e.symm k)) - f0 (x (e.symm k)))| := by
      intro τ f hf
      rw [hsum_reindex τ (fun p : Fin n × Fin m => f (x p) - f0 (x p)), ← heN]
    have hIF1 : ∫ τ : Fin (n * m) → ℝ, sSup ((fun f : S → ℝ =>
        |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          τ (e (i, j)) * Psi (f (x (i, j)) - f0 (x (i, j)))|) '' (Fs : Set (S → ℝ)))
        ∂(Measure.pi (fun _ : Fin (n * m) => rademacherLaw))
        = ∫ τ : Fin (n * m) → ℝ, sSup ((fun t : Fin (n * m) → ℝ =>
            |((n * m : ℕ) : ℝ)⁻¹ * ∑ k : Fin (n * m), τ k * Psi (t k)|) '' Om)
        ∂(Measure.pi (fun _ : Fin (n * m) => rademacherLaw)) := by
      refine integral_congr_ae ?_
      filter_upwards with τ
      have hset : ((fun f : S → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
            τ (e (i, j)) * Psi (f (x (i, j)) - f0 (x (i, j)))|) '' (Fs : Set (S → ℝ)))
          = ((fun t : Fin (n * m) → ℝ =>
              |((n * m : ℕ) : ℝ)⁻¹ * ∑ k : Fin (n * m), τ k * Psi (t k)|) ''
              (phi '' (Fs : Set (S → ℝ)))) := by
        ext y
        constructor
        · rintro ⟨f, hf, rfl⟩
          exact ⟨phi f, ⟨f, hf, rfl⟩, (hpt1 τ f hf).symm⟩
        · rintro ⟨t, ⟨f, hf, rfl⟩, hyt⟩
          exact ⟨f, hf, (hpt1 τ f hf).trans hyt⟩
      show sSup ((fun f : S → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          τ (e (i, j)) * Psi (f (x (i, j)) - f0 (x (i, j)))|) '' (Fs : Set (S → ℝ)))
        = sSup ((fun t : Fin (n * m) → ℝ =>
            |((n * m : ℕ) : ℝ)⁻¹ * ∑ k : Fin (n * m), τ k * Psi (t k)|) '' Om)
      rw [hset, hOm]
    have hIF2 : ∫ τ : Fin (n * m) → ℝ, sSup ((fun f : S → ℝ =>
        |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          τ (e (i, j)) * (f (x (i, j)) - f0 (x (i, j)))|) '' (Fs : Set (S → ℝ)))
        ∂(Measure.pi (fun _ : Fin (n * m) => rademacherLaw))
        = ∫ τ : Fin (n * m) → ℝ, sSup ((fun t : Fin (n * m) → ℝ =>
            |((n * m : ℕ) : ℝ)⁻¹ * ∑ k : Fin (n * m), τ k * t k|) '' Om)
        ∂(Measure.pi (fun _ : Fin (n * m) => rademacherLaw)) := by
      refine integral_congr_ae ?_
      filter_upwards with τ
      have hset : ((fun f : S → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
            τ (e (i, j)) * (f (x (i, j)) - f0 (x (i, j)))|) '' (Fs : Set (S → ℝ)))
          = ((fun t : Fin (n * m) → ℝ =>
              |((n * m : ℕ) : ℝ)⁻¹ * ∑ k : Fin (n * m), τ k * t k|) ''
              (phi '' (Fs : Set (S → ℝ)))) := by
        ext y
        constructor
        · rintro ⟨f, hf, rfl⟩
          exact ⟨phi f, ⟨f, hf, rfl⟩, (hpt2 τ f hf).symm⟩
        · rintro ⟨t, ⟨f, hf, rfl⟩, hyt⟩
          exact ⟨f, hf, (hpt2 τ f hf).trans hyt⟩
      show sSup ((fun f : S → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          τ (e (i, j)) * (f (x (i, j)) - f0 (x (i, j)))|) '' (Fs : Set (S → ℝ)))
        = sSup ((fun t : Fin (n * m) → ℝ =>
            |((n * m : ℕ) : ℝ)⁻¹ * ∑ k : Fin (n * m), τ k * t k|) '' Om)
      rw [hset, hOm]
    rw [htrL, htrR, hIF1, hIF2]
    refine le_trans hkey (le_of_eq ?_)
    rw [show (2 : ℝ) * (4 * B1) = 8 * B1 from by ring]
  have hbPsi : ∀ (x : Fin n × Fin m → S) (σ : Fin n × Fin m → ℝ),
      (∀ p : Fin n × Fin m, |σ p| = 1) →
      ‖sSup ((fun f : S → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
        σ (i, j) * Psi (f (x (i, j)) - f0 (x (i, j)))|) '' (Fs : Set (S → ℝ)))‖
        ≤ 8 * B1 ^ 2 := by
    intro x σ hσ
    have hpos : (0 : ℝ) < (n : ℝ) * (m : ℝ) := by
      have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      exact mul_pos hn' hm'
    have hterm : ∀ (f : S → ℝ), f ∈ (Fs : Set (S → ℝ)) → ∀ (i : Fin n) (j : Fin m),
        |σ (i, j) * Psi (f (x (i, j)) - f0 (x (i, j)))| ≤ (4 * B1) * (2 * B1) := by
      intro f hf i j
      rw [abs_mul, hσ (i, j), one_mul]
      have hb : |f (x (i, j)) - f0 (x (i, j))| ≤ 2 * B1 := by
        have h2 := hFs_bound f hf (x (i, j))
        have h3 := hf0_bound (x (i, j))
        rw [abs_le] at h2 h3 ⊢
        exact ⟨by linarith [h2.1, h3.1], by linarith [h2.2, h3.2]⟩
      calc |Psi (f (x (i, j)) - f0 (x (i, j)))|
          ≤ 4 * B1 * |f (x (i, j)) - f0 (x (i, j))| := hPsi_bound _
        _ ≤ 4 * B1 * (2 * B1) := by nlinarith [hB1, hb]
    have hsum : (∑ i : Fin n, ∑ j : Fin m, (4 * B1) * (2 * B1))
        = ((n : ℝ) * (m : ℝ)) * (8 * B1 ^ 2) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hcount : ∀ f ∈ (Fs : Set (S → ℝ)),
        |∑ i : Fin n, ∑ j : Fin m, σ (i, j) * Psi (f (x (i, j)) - f0 (x (i, j)))|
          ≤ ((n : ℝ) * (m : ℝ)) * (8 * B1 ^ 2) := by
      intro f hf
      calc |∑ i : Fin n, ∑ j : Fin m, σ (i, j) * Psi (f (x (i, j)) - f0 (x (i, j)))|
          ≤ ∑ i : Fin n, |∑ j : Fin m, σ (i, j) * Psi (f (x (i, j)) - f0 (x (i, j)))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : Fin n, ∑ j : Fin m,
              |σ (i, j) * Psi (f (x (i, j)) - f0 (x (i, j)))| :=
            Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
        _ ≤ ∑ i : Fin n, ∑ j : Fin m, (4 * B1) * (2 * B1) :=
            Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm f hf i j))
        _ = ((n : ℝ) * (m : ℝ)) * (8 * B1 ^ 2) := hsum
    have hle : ∀ y ∈ ((fun f : S → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
        σ (i, j) * Psi (f (x (i, j)) - f0 (x (i, j)))|) '' (Fs : Set (S → ℝ))),
        y ≤ 8 * B1 ^ 2 := by
      intro y hy
      obtain ⟨f, hf, rfl⟩ := hy
      simp only [abs_mul, abs_of_pos (inv_pos.mpr hpos)]
      calc ((n : ℝ) * (m : ℝ))⁻¹ * |∑ i : Fin n, ∑ j : Fin m,
            σ (i, j) * Psi (f (x (i, j)) - f0 (x (i, j)))|
          ≤ ((n : ℝ) * (m : ℝ))⁻¹ * (((n : ℝ) * (m : ℝ)) * (8 * B1 ^ 2)) :=
            mul_le_mul_of_nonneg_left (hcount f hf) (le_of_lt (inv_pos.mpr hpos))
        _ = 8 * B1 ^ 2 := by
            rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]
    have hnn : ∀ y ∈ ((fun f : S → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
        σ (i, j) * Psi (f (x (i, j)) - f0 (x (i, j)))|) '' (Fs : Set (S → ℝ))), 0 ≤ y := by
      intro y hy
      obtain ⟨f, hf, rfl⟩ := hy
      exact abs_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sSup_nonneg hnn)]
    exact Real.sSup_le hle (by positivity)
  have hbId : ∀ (x : Fin n × Fin m → S) (σ : Fin n × Fin m → ℝ),
      (∀ p : Fin n × Fin m, |σ p| = 1) →
      ‖sSup ((fun f : S → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
        σ (i, j) * (f (x (i, j)) - f0 (x (i, j)))|) '' (Fs : Set (S → ℝ)))‖ ≤ 2 * B1 := by
    intro x σ hσ
    have hpos : (0 : ℝ) < (n : ℝ) * (m : ℝ) := by
      have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      exact mul_pos hn' hm'
    have hterm : ∀ (f : S → ℝ), f ∈ (Fs : Set (S → ℝ)) → ∀ (i : Fin n) (j : Fin m),
        |σ (i, j) * (f (x (i, j)) - f0 (x (i, j)))| ≤ 2 * B1 := by
      intro f hf i j
      rw [abs_mul, hσ (i, j), one_mul]
      have h2 := hFs_bound f hf (x (i, j))
      have h3 := hf0_bound (x (i, j))
      rw [abs_le] at h2 h3 ⊢
      exact ⟨by linarith [h2.1, h3.1], by linarith [h2.2, h3.2]⟩
    have hsum : (∑ i : Fin n, ∑ j : Fin m, 2 * B1)
        = ((n : ℝ) * (m : ℝ)) * (2 * B1) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hcount : ∀ f ∈ (Fs : Set (S → ℝ)),
        |∑ i : Fin n, ∑ j : Fin m, σ (i, j) * (f (x (i, j)) - f0 (x (i, j)))|
          ≤ ((n : ℝ) * (m : ℝ)) * (2 * B1) := by
      intro f hf
      calc |∑ i : Fin n, ∑ j : Fin m, σ (i, j) * (f (x (i, j)) - f0 (x (i, j)))|
          ≤ ∑ i : Fin n, |∑ j : Fin m, σ (i, j) * (f (x (i, j)) - f0 (x (i, j)))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : Fin n, ∑ j : Fin m, |σ (i, j) * (f (x (i, j)) - f0 (x (i, j)))| :=
            Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
        _ ≤ ∑ i : Fin n, ∑ j : Fin m, 2 * B1 :=
            Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm f hf i j))
        _ = ((n : ℝ) * (m : ℝ)) * (2 * B1) := hsum
    have hle : ∀ y ∈ ((fun f : S → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
        σ (i, j) * (f (x (i, j)) - f0 (x (i, j)))|) '' (Fs : Set (S → ℝ))),
        y ≤ 2 * B1 := by
      intro y hy
      obtain ⟨f, hf, rfl⟩ := hy
      simp only [abs_mul, abs_of_pos (inv_pos.mpr hpos)]
      calc ((n : ℝ) * (m : ℝ))⁻¹ * |∑ i : Fin n, ∑ j : Fin m,
            σ (i, j) * (f (x (i, j)) - f0 (x (i, j)))|
          ≤ ((n : ℝ) * (m : ℝ))⁻¹ * (((n : ℝ) * (m : ℝ)) * (2 * B1)) :=
            mul_le_mul_of_nonneg_left (hcount f hf) (le_of_lt (inv_pos.mpr hpos))
        _ = 2 * B1 := by
            rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]
    have hnn : ∀ y ∈ ((fun f : S → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
        σ (i, j) * (f (x (i, j)) - f0 (x (i, j)))|) '' (Fs : Set (S → ℝ))), 0 ≤ y := by
      intro y hy
      obtain ⟨f, hf, rfl⟩ := hy
      exact abs_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sSup_nonneg hnn)]
    exact Real.sSup_le hle (by linarith [hB1])
  have hpair_meas : Measurable (fun ω : Rand => (xv ω, sv ω)) := Measurable.prodMk hxv_meas hsv_meas
  have hcompPsi : Measurable (fun ω : Rand =>
      (fun z : (Fin n × Fin m → S) × (Fin n × Fin m → ℝ) =>
        sSup ((fun f : S → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          z.2 (i, j) * Psi (f (z.1 (i, j)) - f0 (z.1 (i, j)))|) '' (Fs : Set (S → ℝ))))
        (xv ω, sv ω)) :=
    hGPsi_meas.comp hpair_meas
  have hcompId : Measurable (fun ω : Rand =>
      (fun z : (Fin n × Fin m → S) × (Fin n × Fin m → ℝ) =>
        sSup ((fun f : S → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          z.2 (i, j) * (f (z.1 (i, j)) - f0 (z.1 (i, j)))|) '' (Fs : Set (S → ℝ))))
        (xv ω, sv ω)) :=
    hGid_meas.comp hpair_meas
  have hIntPsiω : Integrable (fun ω : Rand =>
      (fun z : (Fin n × Fin m → S) × (Fin n × Fin m → ℝ) =>
        sSup ((fun f : S → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          z.2 (i, j) * Psi (f (z.1 (i, j)) - f0 (z.1 (i, j)))|) '' (Fs : Set (S → ℝ))))
        (xv ω, sv ω)) P := by
    refine Integrable.of_bound hcompPsi.aestronglyMeasurable (8 * B1 ^ 2) ?_
    filter_upwards [hsign] with ω hω
    exact hbPsi (xv ω) (sv ω) hω
  have hIntIdω : Integrable (fun ω : Rand =>
      (fun z : (Fin n × Fin m → S) × (Fin n × Fin m → ℝ) =>
        sSup ((fun f : S → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          z.2 (i, j) * (f (z.1 (i, j)) - f0 (z.1 (i, j)))|) '' (Fs : Set (S → ℝ))))
        (xv ω, sv ω)) P := by
    refine Integrable.of_bound hcompId.aestronglyMeasurable (2 * B1) ?_
    filter_upwards [hsign] with ω hω
    exact hbId (xv ω) (sv ω) hω
  have hIntPsi : Integrable (fun z : (Fin n × Fin m → S) × (Fin n × Fin m → ℝ) =>
      sSup ((fun f : S → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
        z.2 (i, j) * Psi (f (z.1 (i, j)) - f0 (z.1 (i, j)))|) '' (Fs : Set (S → ℝ))))
      ((Measure.map xv P).prod (Measure.pi (fun _ : Fin n × Fin m => rademacherLaw))) := by
    rw [← hjoint]
    exact (integrable_map_measure hGPsi_meas.aestronglyMeasurable hpair_meas.aemeasurable).mpr
      hIntPsiω
  have hIntId : Integrable (fun z : (Fin n × Fin m → S) × (Fin n × Fin m → ℝ) =>
      sSup ((fun f : S → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
        z.2 (i, j) * (f (z.1 (i, j)) - f0 (z.1 (i, j)))|) '' (Fs : Set (S → ℝ))))
      ((Measure.map xv P).prod (Measure.pi (fun _ : Fin n × Fin m => rademacherLaw))) := by
    rw [← hjoint]
    exact (integrable_map_measure hGid_meas.aestronglyMeasurable hpair_meas.aemeasurable).mpr
      hIntIdω
  have hTPsi : ∫ ω, sSup ((fun f : S → ℝ =>
      |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
        sigma i j ω * Psi (f (X i j ω) - f0 (X i j ω))|) '' (Fs : Set (S → ℝ))) ∂P
      = ∫ x : Fin n × Fin m → S, ∫ σ : Fin n × Fin m → ℝ,
        sSup ((fun f : S → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          σ (i, j) * Psi (f (x (i, j)) - f0 (x (i, j)))|) '' (Fs : Set (S → ℝ)))
        ∂(Measure.pi (fun _ : Fin n × Fin m => rademacherLaw)) ∂(Measure.map xv P) :=
    htransport (fun x σ => sSup ((fun f : S → ℝ =>
        |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          σ (i, j) * Psi (f (x (i, j)) - f0 (x (i, j)))|) '' (Fs : Set (S → ℝ))))
      hGPsi_meas hIntPsi
  have hTId : ∫ ω, sSup ((fun f : S → ℝ =>
      |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
        sigma i j ω * (f (X i j ω) - f0 (X i j ω))|) '' (Fs : Set (S → ℝ))) ∂P
      = ∫ x : Fin n × Fin m → S, ∫ σ : Fin n × Fin m → ℝ,
        sSup ((fun f : S → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          σ (i, j) * (f (x (i, j)) - f0 (x (i, j)))|) '' (Fs : Set (S → ℝ)))
        ∂(Measure.pi (fun _ : Fin n × Fin m => rademacherLaw)) ∂(Measure.map xv P) :=
    htransport (fun x σ => sSup ((fun f : S → ℝ =>
        |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          σ (i, j) * (f (x (i, j)) - f0 (x (i, j)))|) '' (Fs : Set (S → ℝ))))
      hGid_meas hIntId
  have hmain : ∫ x : Fin n × Fin m → S, ∫ σ : Fin n × Fin m → ℝ,
      sSup ((fun f : S → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
        σ (i, j) * Psi (f (x (i, j)) - f0 (x (i, j)))|) '' (Fs : Set (S → ℝ)))
      ∂(Measure.pi (fun _ : Fin n × Fin m => rademacherLaw)) ∂(Measure.map xv P)
      ≤ ∫ x : Fin n × Fin m → S, 8 * B1 * ∫ σ : Fin n × Fin m → ℝ,
        sSup ((fun f : S → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          σ (i, j) * (f (x (i, j)) - f0 (x (i, j)))|) '' (Fs : Set (S → ℝ)))
        ∂(Measure.pi (fun _ : Fin n × Fin m => rademacherLaw)) ∂(Measure.map xv P) := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
    · filter_upwards with x
      refine MeasureTheory.integral_nonneg ?_
      intro σ
      exact Real.sSup_nonneg (fun y hy => by
        obtain ⟨f, hf, rfl⟩ := hy
        exact abs_nonneg _)
    · exact (MeasureTheory.Integrable.integral_prod_left hIntId).const_mul (8 * B1)
    · filter_upwards with x
      exact hcond x
  rw [hTPsi]
  rw [hTId]
  rw [MeasureTheory.integral_const_mul] at hmain
  exact hmain
  /- @proof-region region.target-node.session.a5aa5a2303894279 end -/

end

end Statlib.Imported

