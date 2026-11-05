import ProverJobs.jobea4701a9720de21f681f2da3.Vocabulary
import ProverJobs.jobea4701a9720de21f681f2da3.Base
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_1496902400_516b8071_161399db
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_4210197691_a11d29d9_0dda85dc
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_79440718_8647c8d9_38e2d9f6
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
open Statlib.Imported
open Statlib.Imported.T24
open T24

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
namespace Statlib.Imported
noncomputable section
open T24

set_option autoImplicit false in
theorem statopia_math_node_4242285578_94052d98 : ∀ {X Y U Θ V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [TopologicalSpace.SeparableSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [MeasurableSpace U] [BorelSpace U]
    [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
    [TopologicalSpace.SeparableSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [TopologicalSpace.SeparableSpace V] [MeasurableSpace V] [BorelSpace V]
    (M : Model X Y U Θ V)
    (hℓ : Measurable (Function.uncurry M.ℓ))
    (𝒬 : ProbabilityMeasure Θ)
    (n : ℕ) (hn : 0 < n)
    (ω : Fin n → Block (X × Y))
    (hLgibbs_int : ∀ (k : ℕ) (S : Fin k → X × Y) (θ : Θ) (D : ProbabilityMeasure (X × Y)),
      Integrable (fun u : U => Lmean M.ℓ u (D : Measure (X × Y)))
        (basePost M k S θ : Measure U))
    (hLgibbsEmp_int : ∀ (k : ℕ) (S : Fin k → X × Y) (θ : Θ),
      Integrable (fun u : U => Lemp M.ℓ u S) (basePost M k S θ : Measure U))
    (hPost_meas : ∀ i : Fin n,
      Measurable fun θ : Θ => (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)),
    (let v : Θ → Measure (Fin n → U) := fun θ =>
        Measure.pi fun i : Fin n => (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)
     let phi : Θ × (Fin n → U) → ℝ := fun x =>
        (1 / (n : ℝ)) * ∑ i : Fin n,
          (Lmean M.ℓ (x.2 i) (DOf ω i : Measure (X × Y)) - Lemp M.ℓ (x.2 i) (SOF ω i))
     let nu : Measure (Θ × (Fin n → U)) :=
        (𝒬 : Measure Θ).bind fun θ => (v θ).map (fun u : Fin n → U => (θ, u))
     let G : Θ → ℝ := fun θ =>
        (1 / (n : ℝ)) * ∑ i : Fin n,
          Lgibbs M.ℓ (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)
            (DOf ω i : Measure (X × Y))
     let GE : Θ → ℝ := fun θ =>
        (1 / (n : ℝ)) * ∑ i : Fin n,
          LgibbsEmp M.ℓ (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U) (SOF ω i)
     ((∀ θ : Θ, Integrable (fun u : Fin n → U => phi (θ, u)) (v θ) ∧
        (∫ u, phi (θ, u) ∂(v θ) = G θ - GE θ)) ∧
      ((∫⁻ x, ENNReal.ofReal (phi x) ∂nu) =
        ∫⁻ θ, (∫⁻ u, ENNReal.ofReal (phi (θ, u)) ∂(v θ)) ∂(𝒬 : Measure Θ)) ∧
      ((∫⁻ x, ENNReal.ofReal (-(phi x)) ∂nu) =
        ∫⁻ θ, (∫⁻ u, ENNReal.ofReal (-(phi (θ, u))) ∂(v θ)) ∂(𝒬 : Measure Θ)) ∧
      ((∫⁻ θ, ENNReal.ofReal (G θ - GE θ) ∂(𝒬 : Measure Θ)) ≤
        ∫⁻ x, ENNReal.ofReal (phi x) ∂nu) ∧
      ((∫⁻ θ, ENNReal.ofReal (-(G θ - GE θ)) ∂(𝒬 : Measure Θ)) ≤
        ∫⁻ x, ENNReal.ofReal (-(phi x)) ∂nu) ∧
      (Integrable (fun x : Θ × (Fin n → U) => phi x) nu →
        Integrable (fun θ : Θ => G θ - GE θ) (𝒬 : Measure Θ) ∧
        (∫ x, phi x ∂nu = ∫ θ, (G θ - GE θ) ∂(𝒬 : Measure Θ))))) := by
  /- @proof-region region.target-node.session.2c25dc412a78e260 begin -/
  classical
  intro X Y U Θ V hX1 hX2 hX3 hX4 hX5 hX6
    hY1 hY2 hY3 hY4 hY5 hY6 hU1 hU2 hU3 hU4 hU5 hU6
    hΘ1 hΘ2 hΘ3 hΘ4 hΘ5 hΘ6 hV1 hV2 hV3 hV4 hV5 hV6
    M hℓ 𝒬 n hn ω hLgibbs_int hLgibbsEmp_int hPost_meas
  dsimp only
  have hℓswap : Measurable (Function.uncurry fun (z : X × Y) (u : U) => M.ℓ u z) := by
    have hswap : Measurable fun p : (X × Y) × U => (p.2, p.1) :=
      Measurable.prod measurable_snd measurable_fst
    exact hℓ.comp hswap
  have hLm : ∀ (D : ProbabilityMeasure (X × Y)), Measurable fun u : U => ∫ z, M.ℓ u z ∂(D : Measure (X × Y)) := by
    intro D
    haveI : IsFiniteKernel (⟨fun _ : U => (D : Measure (X × Y)), measurable_const⟩ : Kernel U (X × Y)) :=
      ⟨1, by simp, fun _ => by simp⟩
    have h := MeasureTheory.StronglyMeasurable.integral_kernel_prod_left
      (κ := (⟨fun _ : U => (D : Measure (X × Y)), measurable_const⟩ : Kernel U (X × Y)))
      (f := fun (z : X × Y) (u : U) => M.ℓ u z) hℓswap.stronglyMeasurable
    exact h.measurable
  have hEm : ∀ (m : ℕ) (S : Fin m → X × Y), Measurable fun u : U => Lemp M.ℓ u S := by
    intro m S
    simp only [Lemp]
    refine (measurable_const : Measurable fun _ : U => (1 / (m : ℝ))).mul
      (Finset.measurable_sum _ (fun j _ => ?_))
    exact hℓ.comp ((measurable_id.prod (measurable_const : Measurable fun _ : U => S j) :
      Measurable fun u : U => (u, S j)))
  have hphi : Measurable fun x : Θ × (Fin n → U) =>
      (1 / (n : ℝ)) * ∑ i : Fin n,
        (Lmean M.ℓ (x.2 i) (↑(DOf ω i) : Measure (X × Y)) - Lemp M.ℓ (x.2 i) (SOF ω i)) := by
    have hproj : ∀ i : Fin n, Measurable fun x : Θ × (Fin n → U) => x.2 i :=
      fun i => (measurable_pi_apply i).comp measurable_snd
    have hterm : ∀ i : Fin n, Measurable fun x : Θ × (Fin n → U) =>
        (Lmean M.ℓ (x.2 i) (↑(DOf ω i) : Measure (X × Y)) - Lemp M.ℓ (x.2 i) (SOF ω i)) := by
      intro i
      exact ((hLm (DOf ω i)).comp (hproj i)).sub ((hEm (↑(mOf ω i)) (SOF ω i)).comp (hproj i))
    exact (measurable_const : Measurable fun _ : Θ × (Fin n → U) => (1 / (n : ℝ))).mul
      (Finset.measurable_sum _ (fun i _ => hterm i))
  have hK_meas : Measurable fun θ : Θ =>
      Measure.pi fun i : Fin n => (↑(basePost M (↑(mOf ω i)) (SOF ω i) θ) : Measure U) :=
    statopia_math_node_79440718_8647c8d9 n
      (fun i θ => (↑(basePost M (↑(mOf ω i)) (SOF ω i) θ) : Measure U))
      (fun i θ => inferInstance) hPost_meas
  have hker : AEMeasurable (fun θ : Θ => Measure.map (fun u : Fin n → U => (θ, u))
      (Measure.pi fun i : Fin n => (↑(basePost M (↑(mOf ω i)) (SOF ω i) θ) : Measure U)))
      (↑𝒬) :=
    (statopia_math_node_4210197691_a11d29d9 n
      (fun i θ => (↑(basePost M (↑(mOf ω i)) (SOF ω i) θ) : Measure U))
      (fun i θ => inferInstance) hPost_meas).aemeasurable
  have hbind : ∀ (g : Θ × (Fin n → U) → ENNReal), Measurable g →
      ∫⁻ x, g x ∂((fun θ => Measure.map (fun u : Fin n → U => (θ, u))
          (Measure.pi fun i : Fin n => (↑(basePost M (↑(mOf ω i)) (SOF ω i) θ) : Measure U)))
        ∘ₘ (↑𝒬 : Measure Θ)) =
        ∫⁻ θ, (∫⁻ u, g (θ, u) ∂(Measure.pi fun i : Fin n =>
          (↑(basePost M (↑(mOf ω i)) (SOF ω i) θ) : Measure U))) ∂(↑𝒬 : Measure Θ) := by
    intro g hg
    rw [MeasureTheory.Measure.lintegral_bind hker hg.aemeasurable]
    apply lintegral_congr
    intro θ
    exact MeasureTheory.lintegral_map hg
      ((measurable_const : Measurable fun _ : Fin n → U => θ).prod measurable_id)
  have hB1 := hbind (fun x : Θ × (Fin n → U) => ENNReal.ofReal ((1 / (n : ℝ)) * ∑ i : Fin n,
      (Lmean M.ℓ (x.2 i) (↑(DOf ω i) : Measure (X × Y)) - Lemp M.ℓ (x.2 i) (SOF ω i))))
    hphi.ennreal_ofReal
  have hB2 := hbind (fun x : Θ × (Fin n → U) => ENNReal.ofReal (-((1 / (n : ℝ)) * ∑ i : Fin n,
      (Lmean M.ℓ (x.2 i) (↑(DOf ω i) : Measure (X × Y)) - Lemp M.ℓ (x.2 i) (SOF ω i)))))
    hphi.neg.ennreal_ofReal
  have hA : ∀ θ : Θ,
      Integrable (fun u : Fin n → U =>
          (1 / (n : ℝ)) * ∑ i : Fin n,
            (Lmean M.ℓ (u i) (↑(DOf ω i) : Measure (X × Y)) - Lemp M.ℓ (u i) (SOF ω i)))
        (Measure.pi fun j : Fin n => (↑(basePost M (↑(mOf ω j)) (SOF ω j) θ) : Measure U)) ∧
      (∫ u : Fin n → U,
          (1 / (n : ℝ)) * ∑ i : Fin n,
            (Lmean M.ℓ (u i) (↑(DOf ω i) : Measure (X × Y)) - Lemp M.ℓ (u i) (SOF ω i))
        ∂(Measure.pi fun j : Fin n => (↑(basePost M (↑(mOf ω j)) (SOF ω j) θ) : Measure U)) =
        (1 / (n : ℝ)) * ∑ i : Fin n,
          Lgibbs M.ℓ (↑(basePost M (↑(mOf ω i)) (SOF ω i) θ)) (↑(DOf ω i) : Measure (X × Y)) -
        (1 / (n : ℝ)) * ∑ i : Fin n,
          LgibbsEmp M.ℓ (↑(basePost M (↑(mOf ω i)) (SOF ω i) θ)) (SOF ω i)) := by
    intro θ
    have hmarg : ∀ i : Fin n,
        Measure.map (fun u : Fin n → U => u i)
            (Measure.pi fun j : Fin n => (↑(basePost M (↑(mOf ω j)) (SOF ω j) θ) : Measure U)) =
          (↑(basePost M (↑(mOf ω i)) (SOF ω i) θ) : Measure U) := by
      intro i
      haveI huniq : Unique ↥({i} : Finset (Fin n)) :=
        ⟨⟨i, Finset.mem_singleton_self i⟩, fun x => Subtype.ext (Finset.mem_singleton.mp x.2)⟩
      refine Measure.ext (fun s hs => ?_)
      rw [Measure.map_apply (measurable_pi_apply i) hs]
      set T : Set ((j : ↥({i} : Finset (Fin n))) → U) :=
        {f | f ⟨i, Finset.mem_singleton_self i⟩ ∈ s} with hT
      have hcyl : (fun u : Fin n → U => u i) ⁻¹' s
          = cylinder ({i} : Finset (Fin n)) T := by
        ext u
        simp [T, cylinder]
      rw [hcyl]
      have hTmeas : MeasurableSet T :=
        measurable_pi_apply (⟨i, Finset.mem_singleton_self i⟩ : ↥({i} : Finset (Fin n))) hs
      have hmeas : MeasurableSet (cylinder ({i} : Finset (Fin n)) T : Set (Fin n → U)) :=
        MeasurableSet.cylinder ({i} : Finset (Fin n)) hTmeas
      rw [← MeasureTheory.piContent_eq_measure_pi (X := fun _ : Fin n => U)
            (fun j : Fin n => (↑(basePost M (↑(mOf ω j)) (SOF ω j) θ) : Measure U)) hmeas,
        MeasureTheory.piContent_cylinder (X := fun _ : Fin n => U)
            (fun j : Fin n => (↑(basePost M (↑(mOf ω j)) (SOF ω j) θ) : Measure U))
            (I := ({i} : Finset (Fin n))) (S := T) hTmeas]
      have hS : T = ⇑(MeasurableEquiv.piUnique (fun _ : ↥({i} : Finset (Fin n)) => U)) ⁻¹' s := by
        rw [hT]
        ext f
        have hd : (default : ↥({i} : Finset (Fin n))) = ⟨i, Finset.mem_singleton_self i⟩ :=
          Subtype.ext (Finset.mem_singleton.mp (default : ↥({i} : Finset (Fin n))).2)
        simp [MeasurableEquiv.piUnique, hd]
      rw [hS, ← Measure.map_apply (MeasurableEquiv.measurable _) hs]
      have hpe := (measurePreserving_piUnique (fun j : ↥({i} : Finset (Fin n)) =>
          (↑(basePost M (↑(mOf ω ↑j)) (SOF ω ↑j) θ) : Measure U))).map_eq
      have hdef : ((default : ↥({i} : Finset (Fin n))) : Fin n) = i :=
        Finset.mem_singleton.mp (default : ↥({i} : Finset (Fin n))).2
      rw [hdef] at hpe
      exact congrArg (fun m : Measure U => m s) hpe
    have hmp : ∀ i : Fin n, MeasurePreserving (fun u : Fin n → U => u i)
        (Measure.pi fun j : Fin n => (↑(basePost M (↑(mOf ω j)) (SOF ω j) θ) : Measure U))
        (↑(basePost M (↑(mOf ω i)) (SOF ω i) θ) : Measure U) :=
      fun i => ⟨measurable_pi_apply i, hmarg i⟩
    have hint : ∀ i : Fin n,
        Integrable (fun u : Fin n → U => Lmean M.ℓ (u i) (↑(DOf ω i) : Measure (X × Y)))
          (Measure.pi fun j : Fin n => (↑(basePost M (↑(mOf ω j)) (SOF ω j) θ) : Measure U)) := by
      intro i
      have hbase := hLgibbs_int (↑(mOf ω i)) (SOF ω i) θ (DOf ω i)
      exact ((hmp i).integrable_comp hbase.aestronglyMeasurable).2 hbase
    have hintEmp : ∀ i : Fin n,
        Integrable (fun u : Fin n → U => Lemp M.ℓ (u i) (SOF ω i))
          (Measure.pi fun j : Fin n => (↑(basePost M (↑(mOf ω j)) (SOF ω j) θ) : Measure U)) := by
      intro i
      have hbase := hLgibbsEmp_int (↑(mOf ω i)) (SOF ω i) θ
      exact ((hmp i).integrable_comp hbase.aestronglyMeasurable).2 hbase
    have hmean : ∀ i : Fin n,
        (∫ u : Fin n → U, Lmean M.ℓ (u i) (↑(DOf ω i) : Measure (X × Y))
            ∂(Measure.pi fun j : Fin n => (↑(basePost M (↑(mOf ω j)) (SOF ω j) θ) : Measure U))) =
          Lgibbs M.ℓ (↑(basePost M (↑(mOf ω i)) (SOF ω i) θ)) (↑(DOf ω i) : Measure (X × Y)) := by
      intro i
      have hbase := hLgibbs_int (↑(mOf ω i)) (SOF ω i) θ (DOf ω i)
      have h := MeasureTheory.integral_map
        (μ := Measure.pi fun j : Fin n => (↑(basePost M (↑(mOf ω j)) (SOF ω j) θ) : Measure U))
        (φ := fun u : Fin n → U => u i)
        (f := fun u' : U => Lmean M.ℓ u' (↑(DOf ω i) : Measure (X × Y)))
        (measurable_pi_apply i).aemeasurable
        (by rw [hmarg i]; exact hbase.aestronglyMeasurable)
      simp only [Lgibbs]
      rw [← hmarg i]
      exact h.symm
    have hemp : ∀ i : Fin n,
        (∫ u : Fin n → U, Lemp M.ℓ (u i) (SOF ω i)
            ∂(Measure.pi fun j : Fin n => (↑(basePost M (↑(mOf ω j)) (SOF ω j) θ) : Measure U))) =
          LgibbsEmp M.ℓ (↑(basePost M (↑(mOf ω i)) (SOF ω i) θ)) (SOF ω i) := by
      intro i
      have hbase := hLgibbsEmp_int (↑(mOf ω i)) (SOF ω i) θ
      have h := MeasureTheory.integral_map
        (μ := Measure.pi fun j : Fin n => (↑(basePost M (↑(mOf ω j)) (SOF ω j) θ) : Measure U))
        (φ := fun u : Fin n → U => u i)
        (f := fun u' : U => Lemp M.ℓ u' (SOF ω i))
        (measurable_pi_apply i).aemeasurable
        (by rw [hmarg i]; exact hbase.aestronglyMeasurable)
      simp only [LgibbsEmp]
      rw [← hmarg i]
      exact h.symm
    have hInner_int : Integrable (fun u : Fin n → U => ∑ i : Fin n,
        (Lmean M.ℓ (u i) (↑(DOf ω i) : Measure (X × Y)) - Lemp M.ℓ (u i) (SOF ω i)))
        (Measure.pi fun j : Fin n => (↑(basePost M (↑(mOf ω j)) (SOF ω j) θ) : Measure U)) := by
      apply integrable_finset_sum
      intro i _
      exact (hint i).sub (hintEmp i)
    have hsum_int_eq : (∫ u : Fin n → U, ∑ i : Fin n,
        (Lmean M.ℓ (u i) (↑(DOf ω i) : Measure (X × Y)) - Lemp M.ℓ (u i) (SOF ω i))
        ∂(Measure.pi fun j : Fin n => (↑(basePost M (↑(mOf ω j)) (SOF ω j) θ) : Measure U))) =
      ∑ i : Fin n, (∫ u : Fin n → U,
        (Lmean M.ℓ (u i) (↑(DOf ω i) : Measure (X × Y)) - Lemp M.ℓ (u i) (SOF ω i))
        ∂(Measure.pi fun j : Fin n => (↑(basePost M (↑(mOf ω j)) (SOF ω j) θ) : Measure U))) :=
      integral_finset_sum (Finset.univ) (fun i _ => (hint i).sub (hintEmp i))
    refine ⟨?_, ?_⟩
    · simpa only [smul_eq_mul] using hInner_int.const_mul (1 / (n : ℝ))
    · rw [integral_const_mul, hsum_int_eq]
      have hstep : ∀ i : Fin n,
          (∫ u : Fin n → U,
              (Lmean M.ℓ (u i) (↑(DOf ω i) : Measure (X × Y)) - Lemp M.ℓ (u i) (SOF ω i))
              ∂(Measure.pi fun j : Fin n => (↑(basePost M (↑(mOf ω j)) (SOF ω j) θ) : Measure U))) =
            (Lgibbs M.ℓ (↑(basePost M (↑(mOf ω i)) (SOF ω i) θ)) (↑(DOf ω i) : Measure (X × Y)) -
              LgibbsEmp M.ℓ (↑(basePost M (↑(mOf ω i)) (SOF ω i) θ)) (SOF ω i)) := by
        intro i
        rw [integral_sub (hint i) (hintEmp i), hmean i, hemp i]
      rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hstep i), Finset.sum_sub_distrib,
        mul_sub]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hA
  · exact hB1
  · exact hB2
  · refine le_trans ?_ (le_of_eq hB1.symm)
    apply lintegral_mono
    intro θ
    dsimp only
    rw [← (hA θ).2]
    have hsub := MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hA θ).1
    rw [hsub]
    exact le_trans (ENNReal.ofReal_le_ofReal (sub_le_self _ ENNReal.toReal_nonneg))
      ENNReal.ofReal_toReal_le
  · refine le_trans ?_ (le_of_eq hB2.symm)
    apply lintegral_mono
    intro θ
    dsimp only
    rw [← (hA θ).2]
    have hsub := MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hA θ).1
    rw [hsub, neg_sub]
    exact le_trans (ENNReal.ofReal_le_ofReal (sub_le_self _ ENNReal.toReal_nonneg))
      ENNReal.ofReal_toReal_le
  · intro hInt
    obtain ⟨hint2, heq2⟩ := statopia_math_node_1496902400_516b8071 (↑𝒬 : Measure Θ)
      (fun θ : Θ => Measure.pi fun i : Fin n =>
        (↑(basePost M (↑(mOf ω i)) (SOF ω i) θ) : Measure U))
      (statopia_math_node_4210197691_a11d29d9 n
        (fun i θ => (↑(basePost M (↑(mOf ω i)) (SOF ω i) θ) : Measure U))
        (fun i θ => inferInstance) hPost_meas)
      (fun θ u => (1 / (n : ℝ)) * ∑ i : Fin n,
        (Lmean M.ℓ (u i) (↑(DOf ω i) : Measure (X × Y)) - Lemp M.ℓ (u i) (SOF ω i)))
      hphi (fun θ => (hA θ).1) hInt
    refine ⟨hint2.congr (Filter.Eventually.of_forall fun θ => (hA θ).2), ?_⟩
    exact heq2.trans (integral_congr_ae (Filter.Eventually.of_forall fun θ => (hA θ).2))
  /- @proof-region region.target-node.session.2c25dc412a78e260 end -/

end
end Statlib.Imported
