import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053

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
theorem statopia_math_node_527567249_0af0d987 : ∀ (m n : ℕ) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xi Mask : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hXi_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun ω => Xi ω i j)
    (hMask_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun ω => Mask ω i j)
    (hXi_indep : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Xi ω ij.1 ij.2) μ)
    (hMask_indep : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Mask ω ij.1 ij.2) μ)
    (hIndep : IndepFun (fun ω (ij : Fin m × Fin n) => Xi ω ij.1 ij.2)
      (fun ω (ij : Fin m × Fin n) => Mask ω ij.1 ij.2) μ),
    iIndepFun (fun (j : Fin n) (ω : Ω) =>
      ((fun i : Fin m => Xi ω i j), (fun i : Fin m => Mask ω i j))) μ := by
  /- @proof-region region.target-node.session.3b76def4d3b357d3 begin -/
  intro m n Ω _inst μ Xi Mask hXi_meas hMask_meas hXi_indep hMask_indep hIndep
  have hxi : ∀ (S : Finset (Fin m × Fin n)) (t : (Fin m × Fin n) → Set Ω),
      (∀ p ∈ S, MeasurableSet[MeasurableSpace.comap (fun ω : Ω => Xi ω p.1 p.2)
        (inferInstance : MeasurableSpace ℝ)] (t p)) →
      μ (⋂ p ∈ S, t p) = ∏ p ∈ S, μ (t p) :=
    fun S t ht => iIndepFun.meas_biInter hXi_indep ht
  have hmask : ∀ (S : Finset (Fin m × Fin n)) (t : (Fin m × Fin n) → Set Ω),
      (∀ p ∈ S, MeasurableSet[MeasurableSpace.comap (fun ω : Ω => Mask ω p.1 p.2)
        (inferInstance : MeasurableSpace ℝ)] (t p)) →
      μ (⋂ p ∈ S, t p) = ∏ p ∈ S, μ (t p) :=
    fun S t ht => iIndepFun.meas_biInter hMask_indep ht
  have hC : ∀ (A B : Set Ω),
      MeasurableSet[MeasurableSpace.comap (fun ω : Ω => fun ij : Fin m × Fin n => Xi ω ij.1 ij.2)
        (inferInstance : MeasurableSpace (Fin m × Fin n → ℝ))] A →
      MeasurableSet[MeasurableSpace.comap (fun ω : Ω => fun ij : Fin m × Fin n => Mask ω ij.1 ij.2)
        (inferInstance : MeasurableSpace (Fin m × Fin n → ℝ))] B →
      μ (A ∩ B) = μ A * μ B := by
    intro A B h1 h2
    simpa using hIndep A B h1 h2
  have hpi : (inferInstance : MeasurableSpace ((ij : Fin m × Fin n) → ℝ)) =
      ⨆ ij, MeasurableSpace.comap (fun f : (ij : Fin m × Fin n) → ℝ => f ij)
        (inferInstance : MeasurableSpace ℝ) := rfl
  have hXiArr : MeasurableSpace.comap (fun ω : Ω => fun ij : Fin m × Fin n => Xi ω ij.1 ij.2)
      (inferInstance : MeasurableSpace (Fin m × Fin n → ℝ))
      = ⨆ (ij : Fin m × Fin n), MeasurableSpace.comap (fun ω : Ω => Xi ω ij.1 ij.2)
        (inferInstance : MeasurableSpace ℝ) := by
    rw [hpi, MeasurableSpace.comap_iSup]
    simp only [MeasurableSpace.comap_comp, Function.comp_def]
  have hMaskArr : MeasurableSpace.comap (fun ω : Ω => fun ij : Fin m × Fin n => Mask ω ij.1 ij.2)
      (inferInstance : MeasurableSpace (Fin m × Fin n → ℝ))
      = ⨆ (ij : Fin m × Fin n), MeasurableSpace.comap (fun ω : Ω => Mask ω ij.1 ij.2)
        (inferInstance : MeasurableSpace ℝ) := by
    rw [hpi, MeasurableSpace.comap_iSup]
    simp only [MeasurableSpace.comap_comp, Function.comp_def]
  have hliftX : ∀ (p : Fin m × Fin n) (A : Set Ω),
      MeasurableSet[MeasurableSpace.comap (fun ω : Ω => Xi ω p.1 p.2)
        (inferInstance : MeasurableSpace ℝ)] A →
      MeasurableSet[MeasurableSpace.comap (fun ω : Ω => fun ij : Fin m × Fin n => Xi ω ij.1 ij.2)
        (inferInstance : MeasurableSpace (Fin m × Fin n → ℝ))] A := by
    intro p A hA
    rw [hXiArr]
    exact (le_iSup (fun ij : Fin m × Fin n => MeasurableSpace.comap (fun ω : Ω => Xi ω ij.1 ij.2)
      (inferInstance : MeasurableSpace ℝ)) p) A hA
  have hliftM : ∀ (p : Fin m × Fin n) (A : Set Ω),
      MeasurableSet[MeasurableSpace.comap (fun ω : Ω => Mask ω p.1 p.2)
        (inferInstance : MeasurableSpace ℝ)] A →
      MeasurableSet[MeasurableSpace.comap (fun ω : Ω => fun ij : Fin m × Fin n => Mask ω ij.1 ij.2)
        (inferInstance : MeasurableSpace (Fin m × Fin n → ℝ))] A := by
    intro p A hA
    rw [hMaskArr]
    exact (le_iSup (fun ij : Fin m × Fin n => MeasurableSpace.comap (fun ω : Ω => Mask ω ij.1 ij.2)
      (inferInstance : MeasurableSpace ℝ)) p) A hA
  have hpiFin : (inferInstance : MeasurableSpace (Fin m → ℝ)) =
      ⨆ i : Fin m, MeasurableSpace.comap (fun f : Fin m → ℝ => f i)
        (inferInstance : MeasurableSpace ℝ) := rfl
  have hProdR : (inferInstance : MeasurableSpace (ℝ × ℝ)) =
      MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace ℝ)
        ⊔ MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace ℝ) := rfl
  have hWsplit : ∀ p : Fin m × Fin n,
      MeasurableSpace.comap (fun ω : Ω => (Xi ω p.1 p.2, Mask ω p.1 p.2))
        (inferInstance : MeasurableSpace (ℝ × ℝ))
      = MeasurableSpace.comap (fun ω : Ω => Xi ω p.1 p.2) (inferInstance : MeasurableSpace ℝ)
        ⊔ MeasurableSpace.comap (fun ω : Ω => Mask ω p.1 p.2) (inferInstance : MeasurableSpace ℝ) := by
    intro p
    rw [hProdR]
    simp only [MeasurableSpace.comap_sup, MeasurableSpace.comap_comp, Function.comp_def]
  have hIndepForm : ∀ {M1 M2 : MeasurableSpace Ω}, Indep M1 M2 μ → ∀ (A B : Set Ω),
      MeasurableSet[M1] A → MeasurableSet[M2] B → μ (A ∩ B) = μ A * μ B := by
    intro M1 M2 h A B h1 h2
    simpa using h A B h1 h2
  have hcanon : ∀ (S : Finset (Fin m × Fin n)) (A B : (Fin m × Fin n) → Set Ω),
      (∀ p ∈ S, MeasurableSet[MeasurableSpace.comap (fun ω : Ω => Xi ω p.1 p.2)
        (inferInstance : MeasurableSpace ℝ)] (A p)) →
      (∀ p ∈ S, MeasurableSet[MeasurableSpace.comap (fun ω : Ω => Mask ω p.1 p.2)
        (inferInstance : MeasurableSpace ℝ)] (B p)) →
      μ (⋂ p ∈ S, (A p ∩ B p)) = ∏ p ∈ S, μ (A p ∩ B p) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        intro A B hA hB
        exact hxi (∅ : Finset (Fin m × Fin n)) (fun p => A p ∩ B p) (by simp)
    | insert a S ha ih =>
        intro A B hA hB
        have hsplitA : (⋂ p ∈ insert a S, A p) = A a ∩ ⋂ p ∈ S, A p := by
          ext ω
          simp only [Set.mem_iInter, Set.mem_inter_iff, Finset.mem_insert]
          exact ⟨fun h => ⟨h a (Or.inl rfl), fun p hp => h p (Or.inr hp)⟩,
            fun h p hp => hp.elim (fun h1 => h1 ▸ h.1) (fun h2 => h.2 p h2)⟩
        have hsplitB : (⋂ p ∈ insert a S, B p) = B a ∩ ⋂ p ∈ S, B p := by
          ext ω
          simp only [Set.mem_iInter, Set.mem_inter_iff, Finset.mem_insert]
          exact ⟨fun h => ⟨h a (Or.inl rfl), fun p hp => h p (Or.inr hp)⟩,
            fun h p hp => hp.elim (fun h1 => h1 ▸ h.1) (fun h2 => h.2 p h2)⟩
        have hxiA : μ (A a ∩ ⋂ p ∈ S, A p) = μ (A a) * μ (⋂ p ∈ S, A p) := by
          have hx1 : μ (⋂ p ∈ insert a S, A p) = ∏ p ∈ insert a S, μ (A p) :=
            hxi _ _ (fun p hp => hA p hp)
          have hx2 : μ (⋂ p ∈ S, A p) = ∏ p ∈ S, μ (A p) :=
            hxi _ _ (fun p hp => hA p (Finset.mem_insert_of_mem hp))
          rw [← hsplitA, hx1, Finset.prod_insert ha, hx2]
        have hxiB : μ (B a ∩ ⋂ p ∈ S, B p) = μ (B a) * μ (⋂ p ∈ S, B p) := by
          have hx1 : μ (⋂ p ∈ insert a S, B p) = ∏ p ∈ insert a S, μ (B p) :=
            hmask _ _ (fun p hp => hB p hp)
          have hx2 : μ (⋂ p ∈ S, B p) = ∏ p ∈ S, μ (B p) :=
            hmask _ _ (fun p hp => hB p (Finset.mem_insert_of_mem hp))
          rw [← hsplitB, hx1, Finset.prod_insert ha, hx2]
        have hIH : μ (⋂ p ∈ S, (A p ∩ B p)) = ∏ p ∈ S, μ (A p ∩ B p) :=
          ih A B (fun p hp => hA p (Finset.mem_insert_of_mem hp))
            (fun p hp => hB p (Finset.mem_insert_of_mem hp))
        have hAa : MeasurableSet[MeasurableSpace.comap (fun ω : Ω => fun ij : Fin m × Fin n => Xi ω ij.1 ij.2)
            (inferInstance : MeasurableSpace (Fin m × Fin n → ℝ))] (A a) :=
          hliftX a (A a) (hA a (Finset.mem_insert_self a S))
        have hBa : MeasurableSet[MeasurableSpace.comap (fun ω : Ω => fun ij : Fin m × Fin n => Mask ω ij.1 ij.2)
            (inferInstance : MeasurableSpace (Fin m × Fin n → ℝ))] (B a) :=
          hliftM a (B a) (hB a (Finset.mem_insert_self a S))
        have hAS : MeasurableSet[MeasurableSpace.comap (fun ω : Ω => fun ij : Fin m × Fin n => Xi ω ij.1 ij.2)
            (inferInstance : MeasurableSpace (Fin m × Fin n → ℝ))] (⋂ p ∈ S, A p) :=
          MeasurableSet.iInter (fun p => MeasurableSet.iInter (fun hp =>
            hliftX p (A p) (hA p (Finset.mem_insert_of_mem hp))))
        have hBS : MeasurableSet[MeasurableSpace.comap (fun ω : Ω => fun ij : Fin m × Fin n => Mask ω ij.1 ij.2)
            (inferInstance : MeasurableSpace (Fin m × Fin n → ℝ))] (⋂ p ∈ S, B p) :=
          MeasurableSet.iInter (fun p => MeasurableSet.iInter (fun hp =>
            hliftM p (B p) (hB p (Finset.mem_insert_of_mem hp))))
        have hC1 := hC (A a ∩ ⋂ p ∈ S, A p) (B a ∩ ⋂ p ∈ S, B p) (hAa.inter hAS) (hBa.inter hBS)
        have hC2 := hC (A a) (B a) hAa hBa
        have hC3 := hC (⋂ p ∈ S, A p) (⋂ p ∈ S, B p) hAS hBS
        have hsplitF : (⋂ p ∈ insert a S, (A p ∩ B p)) = (A a ∩ B a) ∩ ⋂ p ∈ S, (A p ∩ B p) := by
          ext ω
          simp only [Set.mem_iInter, Set.mem_inter_iff, Finset.mem_insert]
          exact ⟨fun h => ⟨h a (Or.inl rfl), fun p hp => h p (Or.inr hp)⟩,
            fun h p hp => hp.elim (fun h1 => h1 ▸ h.1) (fun h2 => h.2 p h2)⟩
        have hsplit2 : (⋂ p ∈ S, (A p ∩ B p)) = (⋂ p ∈ S, A p) ∩ (⋂ p ∈ S, B p) := by
          ext ω
          simp only [Set.mem_iInter, Set.mem_inter_iff]
          exact ⟨fun h => ⟨fun p hp => (h p hp).1, fun p hp => (h p hp).2⟩,
            fun h p hp => ⟨h.1 p hp, h.2 p hp⟩⟩
        have hrear : (A a ∩ B a) ∩ ((⋂ p ∈ S, A p) ∩ (⋂ p ∈ S, B p)) =
            (A a ∩ ⋂ p ∈ S, A p) ∩ (B a ∩ ⋂ p ∈ S, B p) := by
          ext ω
          simp only [Set.mem_inter_iff]
          tauto
        rw [hsplitF, hsplit2, hrear, hC1, hxiA, hxiB, mul_mul_mul_comm, ← hC2, ← hC3, ← hsplit2, hIH,
          Finset.prod_insert ha]
  set πW : (Fin m × Fin n) → Set (Set Ω) := fun p => {s : Set Ω | ∃ A B : Set Ω,
      MeasurableSet[MeasurableSpace.comap (fun ω : Ω => Xi ω p.1 p.2)
        (inferInstance : MeasurableSpace ℝ)] A ∧
      MeasurableSet[MeasurableSpace.comap (fun ω : Ω => Mask ω p.1 p.2)
        (inferInstance : MeasurableSpace ℝ)] B ∧
      s = A ∩ B} with hπW
  have hmonoMS : ∀ {M1 M2 : MeasurableSpace Ω}, M1 ≤ M2 → ∀ {s : Set Ω},
      MeasurableSet[M1] s → MeasurableSet[M2] s := fun hM s hs => hM s hs
  have hπWsys : ∀ p : Fin m × Fin n, IsPiSystem (πW p) := by
    intro p s1 h1 s2 h2
    obtain ⟨A1, B1, hA1, hB1, rfl⟩ := h1
    obtain ⟨A2, B2, hA2, hB2, rfl⟩ := h2
    intro _
    refine ⟨A1 ∩ A2, B1 ∩ B2, hA1.inter hA2, hB1.inter hB2, ?_⟩
    ext ω
    simp only [Set.mem_inter_iff]
    tauto
  have hgenW : ∀ p : Fin m × Fin n,
      MeasurableSpace.comap (fun ω : Ω => (Xi ω p.1 p.2, Mask ω p.1 p.2))
        (inferInstance : MeasurableSpace (ℝ × ℝ)) = MeasurableSpace.generateFrom (πW p) := by
    intro p
    have hpre : ∀ u : Set ℝ, MeasurableSet u →
        MeasurableSet[MeasurableSpace.generateFrom (πW p)]
          ((fun ω : Ω => Xi ω p.1 p.2) ⁻¹' u) := by
      intro u hu
      have hmem : ((fun ω : Ω => Xi ω p.1 p.2) ⁻¹' u) ∈ πW p :=
        ⟨(fun ω : Ω => Xi ω p.1 p.2) ⁻¹' u, Set.univ,
          (MeasurableSpace.measurableSet_comap (f := fun ω : Ω => Xi ω p.1 p.2)
            (m := (inferInstance : MeasurableSpace ℝ))).mpr ⟨u, hu, rfl⟩,
          MeasurableSet.univ, (Set.inter_univ _).symm⟩
      exact (MeasurableSpace.generateFrom_le_iff _).mp le_rfl hmem
    have hpre2 : ∀ u : Set ℝ, MeasurableSet u →
        MeasurableSet[MeasurableSpace.generateFrom (πW p)]
          ((fun ω : Ω => Mask ω p.1 p.2) ⁻¹' u) := by
      intro u hu
      have hmem : ((fun ω : Ω => Mask ω p.1 p.2) ⁻¹' u) ∈ πW p :=
        ⟨Set.univ, (fun ω : Ω => Mask ω p.1 p.2) ⁻¹' u, MeasurableSet.univ,
          (MeasurableSpace.measurableSet_comap (f := fun ω : Ω => Mask ω p.1 p.2)
            (m := (inferInstance : MeasurableSpace ℝ))).mpr ⟨u, hu, rfl⟩,
          (Set.univ_inter _).symm⟩
      exact (MeasurableSpace.generateFrom_le_iff _).mp le_rfl hmem
    have hge : MeasurableSpace.generateFrom (πW p) ≤
        MeasurableSpace.comap (fun ω : Ω => Xi ω p.1 p.2) (inferInstance : MeasurableSpace ℝ)
          ⊔ MeasurableSpace.comap (fun ω : Ω => Mask ω p.1 p.2)
            (inferInstance : MeasurableSpace ℝ) := by
      refine (MeasurableSpace.generateFrom_le_iff _).mpr ?_
      rintro t ⟨A, B, hA, hB, rfl⟩
      have hA' : MeasurableSet[MeasurableSpace.comap (fun ω : Ω => Xi ω p.1 p.2)
          (inferInstance : MeasurableSpace ℝ)
          ⊔ MeasurableSpace.comap (fun ω : Ω => Mask ω p.1 p.2)
            (inferInstance : MeasurableSpace ℝ)] A :=
        hmonoMS le_sup_left hA
      have hB' : MeasurableSet[MeasurableSpace.comap (fun ω : Ω => Xi ω p.1 p.2)
          (inferInstance : MeasurableSpace ℝ)
          ⊔ MeasurableSpace.comap (fun ω : Ω => Mask ω p.1 p.2)
            (inferInstance : MeasurableSpace ℝ)] B :=
        hmonoMS le_sup_right hB
      exact hA'.inter hB'
    rw [hWsplit p]
    refine le_antisymm ?_ hge
    refine sup_le ?_ ?_
    · rw [MeasurableSpace.comap_eq_generateFrom (inferInstance : MeasurableSpace ℝ)
        (fun ω : Ω => Xi ω p.1 p.2)]
      exact (MeasurableSpace.generateFrom_le_iff _).mpr (fun t ht => by
        obtain ⟨u, hu, rfl⟩ := ht
        exact hpre u hu)
    · rw [MeasurableSpace.comap_eq_generateFrom (inferInstance : MeasurableSpace ℝ)
        (fun ω : Ω => Mask ω p.1 p.2)]
      exact (MeasurableSpace.generateFrom_le_iff _).mpr (fun t ht => by
        obtain ⟨u, hu, rfl⟩ := ht
        exact hpre2 u hu)
  have hDataW : iIndepSets πW μ := by
    refine (ProbabilityTheory.iIndepSets_iff πW μ).mpr ?_
    intro S f hf
    classical
    have hex : ∀ p : Fin m × Fin n, ∃ A B : Set Ω,
        MeasurableSet[MeasurableSpace.comap (fun ω : Ω => Xi ω p.1 p.2)
          (inferInstance : MeasurableSpace ℝ)] A ∧
        MeasurableSet[MeasurableSpace.comap (fun ω : Ω => Mask ω p.1 p.2)
          (inferInstance : MeasurableSpace ℝ)] B ∧
        (p ∈ S → f p = A ∩ B) := by
      intro p
      by_cases hp : p ∈ S
      · obtain ⟨A, B, hA, hB, hAB⟩ := hf p hp
        exact ⟨A, B, hA, hB, fun _ => hAB⟩
      · exact ⟨Set.univ, Set.univ, MeasurableSet.univ, MeasurableSet.univ,
          fun hh => absurd hh hp⟩
    choose A B hA hB hAB using hex
    have hkey := hcanon S A B (fun p _ => hA p) (fun p _ => hB p)
    have h1 : (⋂ p ∈ S, (A p ∩ B p)) = ⋂ p ∈ S, f p := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_inter_iff]
      exact ⟨fun h p hp => by rw [hAB p hp]; exact h p hp,
        fun h p hp => by
          have hh := h p hp
          rw [hAB p hp] at hh
          exact hh⟩
    have h2 : (∏ p ∈ S, μ (A p ∩ B p)) = ∏ p ∈ S, μ (f p) := by
      refine Finset.prod_congr rfl (fun p hp => ?_)
      rw [hAB p hp]
    rw [← h1, ← h2]
    exact hkey
  have hProdPi : (inferInstance : MeasurableSpace ((Fin m → ℝ) × (Fin m → ℝ))) =
      MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace (Fin m → ℝ))
        ⊔ MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace (Fin m → ℝ)) := rfl
  have hCXsplit : ∀ j : Fin n,
      MeasurableSpace.comap (fun ω : Ω => ((fun i => Xi ω i j), (fun i => Mask ω i j)))
        (inferInstance : MeasurableSpace ((Fin m → ℝ) × (Fin m → ℝ)))
      = (⨆ i : Fin m, MeasurableSpace.comap (fun ω : Ω => Xi ω i j)
          (inferInstance : MeasurableSpace ℝ))
        ⊔ (⨆ i : Fin m, MeasurableSpace.comap (fun ω : Ω => Mask ω i j)
          (inferInstance : MeasurableSpace ℝ)) := by
    intro j
    rw [hProdPi, MeasurableSpace.comap_sup]
    simp only [MeasurableSpace.comap_comp, Function.comp_def]
    congr 1
    · rw [hpiFin, MeasurableSpace.comap_iSup]
      simp only [MeasurableSpace.comap_comp, Function.comp_def]
    · rw [hpiFin, MeasurableSpace.comap_iSup]
      simp only [MeasurableSpace.comap_comp, Function.comp_def]
  have hleX : ∀ p : Fin m × Fin n,
      MeasurableSpace.comap (fun ω : Ω => Xi ω p.1 p.2) (inferInstance : MeasurableSpace ℝ)
        ≤ (inferInstance : MeasurableSpace Ω) := by
    intro p s hs
    obtain ⟨u, hu, rfl⟩ := (MeasurableSpace.measurableSet_comap (f := fun ω : Ω => Xi ω p.1 p.2)
      (m := (inferInstance : MeasurableSpace ℝ))).mp hs
    exact hXi_meas p.1 p.2 hu
  have hleM : ∀ p : Fin m × Fin n,
      MeasurableSpace.comap (fun ω : Ω => Mask ω p.1 p.2) (inferInstance : MeasurableSpace ℝ)
        ≤ (inferInstance : MeasurableSpace Ω) := by
    intro p s hs
    obtain ⟨u, hu, rfl⟩ := (MeasurableSpace.measurableSet_comap (f := fun ω : Ω => Mask ω p.1 p.2)
      (m := (inferInstance : MeasurableSpace ℝ))).mp hs
    exact hMask_meas p.1 p.2 hu
  have hleW : ∀ p : Fin m × Fin n,
      MeasurableSpace.generateFrom (πW p) ≤ (inferInstance : MeasurableSpace Ω) := by
    intro p
    rw [← hgenW p, hWsplit p]
    exact sup_le (hleX p) (hleM p)
  have hI : iIndep (fun p : Fin m × Fin n => MeasurableSpace.generateFrom (πW p)) μ :=
    ProbabilityTheory.iIndepSets.iIndep (fun p => hleW p) πW hπWsys (fun p => rfl) hDataW
  have hsupdist : ∀ (A B : Fin m → MeasurableSpace Ω),
      (⨆ i : Fin m, A i) ⊔ (⨆ i : Fin m, B i) = ⨆ i : Fin m, (A i ⊔ B i) := by
    intro A B
    refine le_antisymm ?_ ?_
    · refine sup_le (iSup_le fun i => ?_) (iSup_le fun i => ?_)
      · exact le_trans le_sup_left (le_iSup (fun i => A i ⊔ B i) i)
      · exact le_trans le_sup_right (le_iSup (fun i => A i ⊔ B i) i)
    · exact iSup_le fun i => sup_le (le_trans (le_iSup A i) le_sup_left)
        (le_trans (le_iSup B i) le_sup_right)
  have hMcol : ∀ j : Fin n,
      MeasurableSpace.comap (fun ω : Ω => ((fun i => Xi ω i j), (fun i => Mask ω i j)))
        (inferInstance : MeasurableSpace ((Fin m → ℝ) × (Fin m → ℝ)))
      = ⨆ i : Fin m, MeasurableSpace.generateFrom (πW (i, j)) := by
    intro j
    rw [hCXsplit j, hsupdist]
    refine le_antisymm ?_ ?_
    · refine iSup_le fun i => ?_
      have h : MeasurableSpace.comap (fun ω : Ω => Xi ω i j) (inferInstance : MeasurableSpace ℝ)
          ⊔ MeasurableSpace.comap (fun ω : Ω => Mask ω i j) (inferInstance : MeasurableSpace ℝ)
          = MeasurableSpace.generateFrom (πW (i, j)) :=
        (hWsplit (i, j)).symm.trans (hgenW (i, j))
      rw [h]
      exact le_iSup (fun k : Fin m => MeasurableSpace.generateFrom (πW (k, j))) i
    · refine iSup_le fun i => ?_
      have h : MeasurableSpace.comap (fun ω : Ω => Xi ω i j) (inferInstance : MeasurableSpace ℝ)
          ⊔ MeasurableSpace.comap (fun ω : Ω => Mask ω i j) (inferInstance : MeasurableSpace ℝ)
          = MeasurableSpace.generateFrom (πW (i, j)) :=
        (hWsplit (i, j)).symm.trans (hgenW (i, j))
      rw [← h]
      exact le_iSup (fun k : Fin m => MeasurableSpace.comap (fun ω : Ω => Xi ω k j)
        (inferInstance : MeasurableSpace ℝ) ⊔ MeasurableSpace.comap (fun ω : Ω => Mask ω k j)
          (inferInstance : MeasurableSpace ℝ)) i
  have hπWint : ∀ p : Fin m × Fin n, ∀ s1 ∈ πW p, ∀ s2 ∈ πW p, s1 ∩ s2 ∈ πW p := by
    intro p s1 h1 s2 h2
    obtain ⟨A1, B1, hA1, hB1, rfl⟩ := h1
    obtain ⟨A2, B2, hA2, hB2, rfl⟩ := h2
    refine ⟨A1 ∩ A2, B1 ∩ B2, hA1.inter hA2, hB1.inter hB2, ?_⟩
    ext ω
    simp only [Set.mem_inter_iff]
    tauto
  have hπWuniv : ∀ p : Fin m × Fin n, (Set.univ : Set Ω) ∈ πW p := by
    intro p
    exact ⟨Set.univ, Set.univ, MeasurableSet.univ, MeasurableSet.univ,
      (Set.univ_inter Set.univ).symm⟩
  set πc : Fin n → Set (Set Ω) := fun j => {t : Set Ω |
      ∃ (T : Finset (Fin m × Fin n)) (f : (Fin m × Fin n) → Set Ω),
        (∀ p ∈ T, p.2 = j) ∧ (∀ p ∈ T, f p ∈ πW p) ∧ t = ⋂ p ∈ T, f p} with hπc
  have hπcsys : ∀ j : Fin n, IsPiSystem (πc j) := by
    intro j t1 h1 t2 h2
    obtain ⟨T1, f1, hT1, hf1, rfl⟩ := h1
    obtain ⟨T2, f2, hT2, hf2, rfl⟩ := h2
    intro _
    refine ⟨T1 ∪ T2, fun p => (if p ∈ T1 then f1 p else Set.univ)
        ∩ (if p ∈ T2 then f2 p else Set.univ), ?_, ?_, ?_⟩
    · intro p hp
      rcases Finset.mem_union.mp hp with hp | hp
      · exact hT1 p hp
      · exact hT2 p hp
    · intro p hp
      refine hπWint p _ ?_ _ ?_
      · by_cases h : p ∈ T1
        · rw [if_pos h]; exact hf1 p h
        · rw [if_neg h]; exact hπWuniv p
      · by_cases h : p ∈ T2
        · rw [if_pos h]; exact hf2 p h
        · rw [if_neg h]; exact hπWuniv p
    · ext ω
      simp only [Set.mem_inter_iff, Set.mem_iInter, Finset.mem_union]
      constructor
      · rintro ⟨h1', h2'⟩ p (hp | hp)
        · by_cases h : p ∈ T2
          · exact ⟨by rw [if_pos hp]; exact h1' p hp, by rw [if_pos h]; exact h2' p h⟩
          · exact ⟨by rw [if_pos hp]; exact h1' p hp, by rw [if_neg h]; exact trivial⟩
        · by_cases h : p ∈ T1
          · exact ⟨by rw [if_pos h]; exact h1' p h, by rw [if_pos hp]; exact h2' p hp⟩
          · exact ⟨by rw [if_neg h]; exact trivial, by rw [if_pos hp]; exact h2' p hp⟩
      · intro h
        refine ⟨fun p hp => ?_, fun p hp => ?_⟩
        · have hh := h p (Or.inl hp)
          rw [if_pos hp] at hh
          exact hh.1
        · by_cases hT : p ∈ T1
          · have hh := h p (Or.inl hT)
            rw [if_pos hT, if_pos hp] at hh
            exact hh.2
          · have hh := h p (Or.inr hp)
            rw [if_neg hT, if_pos hp] at hh
            exact hh.2
  have hgenC : ∀ j : Fin n, MeasurableSpace.generateFrom (πc j)
      = ⨆ i : Fin m, MeasurableSpace.generateFrom (πW (i, j)) := by
    intro j
    refine le_antisymm ?_ ?_
    · refine (MeasurableSpace.generateFrom_le_iff
        (⨆ i : Fin m, MeasurableSpace.generateFrom (πW (i, j)))).mpr ?_
      rintro t ht
      obtain ⟨T, f, hT, hf, rfl⟩ := ht
      have hstep : ∀ p : Fin m × Fin n, p ∈ T →
          MeasurableSet[⨆ i : Fin m, MeasurableSpace.generateFrom (πW (i, j))] (f p) := by
        intro p hp
        obtain ⟨a, b⟩ := p
        have hbj : b = j := hT (a, b) hp
        rw [hbj] at hp ⊢
        exact (le_iSup (fun i : Fin m => MeasurableSpace.generateFrom (πW (i, j))) a) (f (a, j))
          ((MeasurableSpace.generateFrom_le_iff _).mp le_rfl (hf (a, j) hp))
      have hmeas : MeasurableSet[⨆ i : Fin m, MeasurableSpace.generateFrom (πW (i, j))]
          (⋂ p ∈ T, f p) :=
        MeasurableSet.iInter (fun p : Fin m × Fin n =>
          MeasurableSet.iInter (fun hp : p ∈ T => hstep p hp))
      exact hmeas
    · refine iSup_le fun i => ?_
      refine (MeasurableSpace.generateFrom_le_iff
        (MeasurableSpace.generateFrom (πc j))).mpr ?_
      rintro t ht
      have hsingle : t = ⋂ p ∈ ({(i, j)} : Finset (Fin m × Fin n)), (fun _ => t) p := by
        ext ω
        simp
      have hmem : t ∈ πc j :=
        ⟨{(i, j)}, fun _ => t, (by intro p hp; rw [Finset.mem_singleton.mp hp]),
          (by intro p hp; rw [Finset.mem_singleton.mp hp]; exact ht), hsingle⟩
      exact (MeasurableSpace.generateFrom_le_iff _).mp le_rfl hmem
  have hDataC : iIndepSets πc μ := by
    refine (ProbabilityTheory.iIndepSets_iff πc μ).mpr ?_
    intro S f hf
    classical
    have hW : ∀ (S : Finset (Fin m × Fin n)) (t : (Fin m × Fin n) → Set Ω),
        (∀ p ∈ S, t p ∈ πW p) → μ (⋂ p ∈ S, t p) = ∏ p ∈ S, μ (t p) :=
      (ProbabilityTheory.iIndepSets_iff πW μ).mp hDataW
    have hex : ∀ j : Fin n, ∃ (T : Finset (Fin m × Fin n)) (g : (Fin m × Fin n) → Set Ω),
        (∀ p ∈ T, p.2 = j) ∧ (∀ p ∈ T, g p ∈ πW p) ∧ (j ∈ S → f j = ⋂ p ∈ T, g p) := by
      intro j
      by_cases hj : j ∈ S
      · obtain ⟨T, g, hT, hg, hfg⟩ := hf j hj
        exact ⟨T, g, hT, hg, fun _ => hfg⟩
      · exact ⟨∅, fun _ => Set.univ, by simp, by simp, fun h => absurd h hj⟩
    choose T g hT hg hfg using hex
    set G : (Fin m × Fin n) → Set Ω := fun q => g q.2 q with hG
    have hGp : ∀ q : Fin m × Fin n, G q = g q.2 q := fun q => rfl
    have hset : (⋂ j ∈ S, f j) = ⋂ p ∈ S.biUnion T, G p := by
      ext ω
      simp only [Set.mem_iInter]
      constructor
      · intro h q hq
        obtain ⟨j, hj, hqj⟩ := Finset.mem_biUnion.mp hq
        have h1 : ω ∈ f j := h j hj
        rw [hfg j hj] at h1
        simp only [Set.mem_iInter] at h1
        have h2 : ω ∈ g j q := h1 q hqj
        rw [hGp q, show q.2 = j from hT j q hqj]
        exact h2
      · intro h j hj
        rw [hfg j hj]
        simp only [Set.mem_iInter]
        intro q hq
        have hh := h q (Finset.mem_biUnion.mpr ⟨j, hj, hq⟩)
        rw [hGp q] at hh
        rw [show q.2 = j from hT j q hq] at hh
        exact hh
    have hprod : (∏ j ∈ S, μ (f j)) = ∏ p ∈ S.biUnion T, μ (G p) := by
      have hstep : ∀ j ∈ S, μ (f j) = ∏ p ∈ T j, μ (g j p) := by
        intro j hj
        rw [hfg j hj]
        exact hW (T j) (g j) (hg j)
      have key : ∀ U : Finset (Fin n),
          (∏ j ∈ U, ∏ p ∈ T j, μ (g j p)) = ∏ p ∈ U.biUnion T, μ (G p) := by
        intro U
        induction U using Finset.induction_on with
        | empty =>
            have hb : (∅ : Finset (Fin n)).biUnion T = ∅ := by
              ext p
              simp
            rw [hb]
            simp
        | insert a U ha ih =>
            have hb : (insert a U).biUnion T = T a ∪ U.biUnion T := by
              ext p
              simp only [Finset.mem_biUnion, Finset.mem_union, Finset.mem_insert]
              constructor
              · rintro ⟨j, rfl | hj, hp⟩
                · exact Or.inl hp
                · exact Or.inr ⟨j, hj, hp⟩
              · rintro (hp | ⟨j, hj, hp⟩)
                · exact ⟨a, Or.inl rfl, hp⟩
                · exact ⟨j, Or.inr hj, hp⟩
            have hdisj : Disjoint (T a) (U.biUnion T) := by
              rw [Finset.disjoint_left]
              intro p hp hq
              obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hq
              have h1 : a = j := (hT a p hp).symm.trans (hT j p hpj)
              exact ha (h1 ▸ hj)
            have hcol : (∏ p ∈ T a, μ (G p)) = ∏ p ∈ T a, μ (g a p) := by
              refine Finset.prod_congr rfl (fun p hp => ?_)
              rw [hGp p, show p.2 = a from hT a p hp]
            rw [Finset.prod_insert ha, hb, Finset.prod_union hdisj, hcol, ← ih]
      have hleft : (∏ j ∈ S, μ (f j)) = ∏ j ∈ S, ∏ p ∈ T j, μ (g j p) :=
        Finset.prod_congr rfl (fun j hj => hstep j hj)
      rw [hleft]
      exact key S
    rw [hset, hprod]
    refine hW (S.biUnion T) G ?_
    intro p hp
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
    rw [hGp p, show p.2 = j from hT j p hpj]
    exact hg j p hpj
  have hleC : ∀ j : Fin n,
      MeasurableSpace.generateFrom (πc j) ≤ (inferInstance : MeasurableSpace Ω) := by
    intro j
    rw [hgenC j]
    exact iSup_le fun i => hleW (i, j)
  have hcolI : iIndep (fun j : Fin n => MeasurableSpace.generateFrom (πc j)) μ :=
    ProbabilityTheory.iIndepSets.iIndep (fun j => hleC j) πc hπcsys (fun j => rfl) hDataC
  have hcolC : iIndep (fun j : Fin n => MeasurableSpace.comap
      (fun ω : Ω => ((fun i => Xi ω i j), (fun i => Mask ω i j)))
      (inferInstance : MeasurableSpace ((Fin m → ℝ) × (Fin m → ℝ)))) μ := by
    have heq : (fun j : Fin n => MeasurableSpace.generateFrom (πc j)) =
        (fun j : Fin n => MeasurableSpace.comap
          (fun ω : Ω => ((fun i => Xi ω i j), (fun i => Mask ω i j)))
          (inferInstance : MeasurableSpace ((Fin m → ℝ) × (Fin m → ℝ)))) := by
      funext j
      rw [hgenC j, ← hMcol j]
    rw [heq] at hcolI
    exact hcolI
  exact (ProbabilityTheory.iIndepFun_iff_iIndep
    (fun _ : Fin n => (inferInstance : MeasurableSpace ((Fin m → ℝ) × (Fin m → ℝ))))
    (fun (j : Fin n) (ω : Ω) => ((fun i : Fin m => Xi ω i j), (fun i : Fin m => Mask ω i j)))
    μ).mpr hcolC
  /- @proof-region region.target-node.session.3b76def4d3b357d3 end -/

end Statlib.Imported

