import Lean
import ProverJobs.job_paper_2d165b9668ee43088292ee6f2129e2cd.ExternalNodes.Node_8fc053db3f364ab0a6f3
import ProverJobs.job_paper_2d165b9668ee43088292ee6f2129e2cd.Vocabulary
import ProverJobs.job_paper_2d165b9668ee43088292ee6f2129e2cd.ProvedNodes
import ProverJobs.job_paper_2d165b9668ee43088292ee6f2129e2cd.Base

namespace PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported.XuYaoL4 then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported.XuYaoL4))
open _root_.PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4

theorem paper_2d165b9668ee43088292ee6f2129e2cd :
    ∀ b : ℝ, 0 < b →
      ∃ Kstar : ℝ, 0 < Kstar ∧
        ∃ K1 : ℝ, 0 < K1 ∧ K1 ≤ (max Kstar 2)⁻¹ ∧
          ∃ K2 : ℝ, 0 < K2 ∧
            ∀ (n m p : ℕ) (hn : 0 < n) (hm : 0 < m) (hp : 2 ≤ p)
              (δ : ℕ → ℕ → ℝ) (hδ : δ n m ≠ 0),
              ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
                (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
                (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
                (μX μY : Fin p → ℝ) (LbarX LbarY : ℝ),
              
              (∀ i j, Measurable fun ω => X i ω j) →
              (∀ i j, Measurable fun ω => Y i ω j) →
              (∀ i j, Measurable fun ω => F i ω j) →
              (∀ i j, Measurable fun ω => G i ω j) →
              
              iIndepFun X P →
              iIndepFun Y P →
              iIndepFun F P →
              iIndepFun G P →
              
              iIndepFun (allVars X Y F G) P →
              
              (∀ i j, Integrable (fun ω => X i ω j) P) →
              (∀ i j, ∫ ω, X i ω j ∂P = μX j) →
              (∀ i j, Integrable (fun ω => Y i ω j) P) →
              (∀ i j, ∫ ω, Y i ω j ∂P = μY j) →
              
              (∀ i j, Integrable (fun ω => (X i ω j - μX j) ^ 2) P) →
              (∀ i j, Integrable (fun ω => |X i ω j - μX j| ^ 3) P) →
              (∀ i j k, Integrable (fun ω => (X i ω j - μX j) * (X i ω k - μX k)) P) →
              (∀ i j, Integrable (fun ω => (Y i ω j - μY j) ^ 2) P) →
              (∀ i j, Integrable (fun ω => |Y i ω j - μY j| ^ 3) P) →
              (∀ i j k, Integrable (fun ω => (Y i ω j - μY j) * (Y i ω k - μY k)) P) →
              
              (∀ i j, Integrable (fun ω => F i ω j) P) →
              (∀ i j, ∫ ω, F i ω j ∂P = μX j) →
              (∀ i j, Integrable (fun ω => (F i ω j - μX j) ^ 2) P) →
              (∀ i j, Integrable (fun ω => |F i ω j - μX j| ^ 3) P) →
              (∀ i j k, Integrable (fun ω => (F i ω j - μX j) * (F i ω k - μX k)) P) →
              (∀ i j k, ∫ ω, (F i ω j - μX j) * (F i ω k - μX k) ∂P
                  = ∫ ω, (X i ω j - μX j) * (X i ω k - μX k) ∂P) →
              (∀ i j, Integrable (fun ω => G i ω j) P) →
              (∀ i j, ∫ ω, G i ω j ∂P = μY j) →
              (∀ i j, Integrable (fun ω => (G i ω j - μY j) ^ 2) P) →
              (∀ i j, Integrable (fun ω => |G i ω j - μY j| ^ 3) P) →
              (∀ i j k, Integrable (fun ω => (G i ω j - μY j) * (G i ω k - μY k)) P) →
              (∀ i j k, ∫ ω, (G i ω j - μY j) * (G i ω k - μY k) ∂P
                  = ∫ ω, (Y i ω j - μY j) * (Y i ω k - μY k) ∂P) →
              (∀ i, IsGaussian (P.map (F i))) →
              (∀ i, IsGaussian (P.map (G i))) →
              
              (∀ j, Integrable (fun ω => (combVec X Y μX μY (δ n m) ω j) ^ 2) P) →
              (∀ j, b ≤ ∫ ω, (combVec X Y μX μY (δ n m) ω j) ^ 2 ∂P) →
              
              Lmom P X μX ≤ LbarX →
              Lmom P Y μY ≤ LbarY →
              LbarX ≠ 0 →
              LbarY ≠ 0 →
              2 ≤ phiN K1 LbarX p n →
              2 ≤ phiM K1 LbarY (δ n m) p m →
              
              rho P (combVec X Y μX μY (δ n m))
                  (combVec F G μX μY (δ n m)) ≤
                K2 * (((LbarX ^ 2 * (Real.log (p : ℝ)) ^ 7 / (n : ℝ)) ^ (1 / 6 : ℝ))
                  + Mn P X F μX (phiN K1 LbarX p n) / LbarX
                  + ((LbarY ^ 2 * (Real.log (p : ℝ)) ^ 7 * |δ n m| ^ 6 / (m : ℝ)) ^
                      (1 / 6 : ℝ))
                                  + MmStar P Y G μY (δ n m) (phiM K1 LbarY (δ n m) p m) / LbarY)
:= by
  /- @proof-region region.root.d984c0b77a90 begin -/
  intro b hb
  obtain ⟨Kstar, hKstar_pos, hKstar_bound⟩ :=
    PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported.paper_c88218b13cf249bdb98064482dead315 b hb
  let K1 : ℝ := (max Kstar 2)⁻¹
  let K2 : ℝ := max (2 * Kstar * (K1 ^ 2 + K1⁻¹)) (2⁻¹)
  have hK1_pos : (0 : ℝ) < K1 :=
    inv_pos.mpr (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_right Kstar 2))
  have hK2_pos : (0 : ℝ) < K2 := by
    show (0 : ℝ) < max (2 * Kstar * (K1 ^ 2 + K1⁻¹)) (2⁻¹)
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2⁻¹) (le_max_right _ _)
  refine ⟨Kstar, hKstar_pos, K1, hK1_pos, le_rfl, K2, hK2_pos, ?_⟩
  intro n m p hn hm hp δ hδ Ω _ P _ X Y F G μX μY LbarX LbarY
  intro hXm hYm hFm hGm
  intro hiX hiY hiF hiG hiAll
  intro hXint hXmean hYint hYmean
  intro hX2 hX3 hXcov hY2 hY3 hYcov
  intro hFint hFmean hF2 hF3 hFcov hFcov_eq
  intro hGint hGmean hG2 hG3 hGcov hGcov_eq
  intro hFgauss hGgauss
  intro hvarint hvar
  intro hLX hLY hLX0 hLY0 hphi1 hphi2
  let A1 : ℝ := (LbarX ^ 2 * (Real.log (p : ℝ)) ^ 7 / (n : ℝ)) ^ (1 / 6 : ℝ)
  let B1 : ℝ := (LbarY ^ 2 * (Real.log (p : ℝ)) ^ 7 * |δ n m| ^ 6 / (m : ℝ)) ^ (1 / 6 : ℝ)
  let C1 : ℝ := Mn P X F μX (phiN K1 LbarX p n) / LbarX
  let D1 : ℝ := MmStar P Y G μY (δ n m) (phiM K1 LbarY (δ n m) p m) / LbarY
  have key : rho P (combVec X Y μX μY (δ n m)) (combVec F G μX μY (δ n m))
      ≤ K2 * (A1 + C1 + B1 + D1) := by
    have hnormX : ∀ j : Fin p, Measurable fun ω => normSum X ω j := by
      intro j
      have hsum : Measurable fun ω => ∑ i : Fin n, X i ω j :=
        Finset.measurable_sum Finset.univ (fun i _ => hXm i j)
      show Measurable fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i : Fin n, X i ω j
      exact measurable_const.mul hsum
    have hnormY : ∀ j : Fin p, Measurable fun ω => normSum Y ω j := by
      intro j
      have hsum : Measurable fun ω => ∑ i : Fin m, Y i ω j :=
        Finset.measurable_sum Finset.univ (fun i _ => hYm i j)
      show Measurable fun ω => (Real.sqrt (m : ℝ))⁻¹ * ∑ i : Fin m, Y i ω j
      exact measurable_const.mul hsum
    have hnormF : ∀ j : Fin p, Measurable fun ω => normSum F ω j := by
      intro j
      have hsum : Measurable fun ω => ∑ i : Fin n, F i ω j :=
        Finset.measurable_sum Finset.univ (fun i _ => hFm i j)
      show Measurable fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i : Fin n, F i ω j
      exact measurable_const.mul hsum
    have hnormG : ∀ j : Fin p, Measurable fun ω => normSum G ω j := by
      intro j
      have hsum : Measurable fun ω => ∑ i : Fin m, G i ω j :=
        Finset.measurable_sum Finset.univ (fun i _ => hGm i j)
      show Measurable fun ω => (Real.sqrt (m : ℝ))⁻¹ * ∑ i : Fin m, G i ω j
      exact measurable_const.mul hsum
    have hA : Measurable (fun ω => combVec X Y μX μY (δ n m) ω) := by
      rw [measurable_pi_iff]
      intro j
      show Measurable fun ω =>
        normSum X ω j - Real.sqrt (n : ℝ) * μX j + (δ n m) * normSum Y ω j -
          (δ n m) * Real.sqrt (m : ℝ) * μY j
      exact (((hnormX j).sub measurable_const).add
        (measurable_const.mul (hnormY j))).sub measurable_const
    have hB : Measurable (fun ω => combVec F G μX μY (δ n m) ω) := by
      rw [measurable_pi_iff]
      intro j
      show Measurable fun ω =>
        normSum F ω j - Real.sqrt (n : ℝ) * μX j + (δ n m) * normSum G ω j -
          (δ n m) * Real.sqrt (m : ℝ) * μY j
      exact (((hnormF j).sub measurable_const).add
        (measurable_const.mul (hnormG j))).sub measurable_const
    have hstep1 :
        rho P (combVec X Y μX μY (δ n m)) (combVec F G μX μY (δ n m))
          ≤ PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported.rhoStar
              P X Y F G μX μY (δ n m) := by
      have hSmeas : ∀ S : Set (Fin p → ℝ), IsHyperrect S → MeasurableSet S := by
        rintro S ⟨a, b, hab, rfl⟩
        have hEq : {w : Fin p → ℝ | ∀ j, a j ≤ (w j : EReal) ∧ (w j : EReal) ≤ b j}
            = Set.univ.pi (fun j => {x : ℝ | a j ≤ (x : EReal) ∧ (x : EReal) ≤ b j}) := by
          ext w
          simp only [Set.mem_setOf_eq, Set.mem_univ_pi]
        rw [hEq]
        refine MeasurableSet.univ_pi (fun j => ?_)
        have hpre : {x : ℝ | a j ≤ (x : EReal) ∧ (x : EReal) ≤ b j}
            = Real.toEReal ⁻¹' Set.Icc (a j) (b j) := by
          ext x
          simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Icc]
        rw [hpre]
        exact isClosed_Icc.measurableSet.preimage measurable_coe_real_ereal
      have hinterp1 : ∀ ω : Ω, (fun j : Fin p =>
            Real.sqrt 1 * PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported.partXY X Y μX μY (δ n m) ω j
              + Real.sqrt (1 - 1) * PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported.partFG F G μX μY (δ n m) ω j)
            = combVec X Y μX μY (δ n m) ω := by
        intro ω
        funext j
        simp only [sub_self, Real.sqrt_one, Real.sqrt_zero, one_mul, zero_mul, add_zero]
        rfl
      have hARe_ne :
          (PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported.ARe p).Nonempty := by
        refine ⟨Set.univ, fun _ => ⊥, fun _ => ⊤, fun j => le_top, ?_⟩
        ext w
        simp [PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported.hyperRect]
      have habs_le : ∀ a b : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → |a - b| ≤ 1 := by
        intro a b ha0 ha1 hb0 hb1
        have h1 : a - b ≤ 1 := by linarith
        have h2 : -(1 : ℝ) ≤ a - b := by linarith
        exact abs_le.mpr ⟨h2, h1⟩
      let ga : ℝ → Set (Fin p → ℝ) → ℝ := fun v A' =>
        |(P {ω : Ω | (fun j : Fin p =>
              Real.sqrt v * PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported.partXY X Y μX μY (δ n m) ω j
                + Real.sqrt (1 - v) * PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported.partFG F G μX μY (δ n m) ω j) ∈ A'}).toReal
          - (P {ω : Ω | PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported.partFG F G μX μY (δ n m) ω ∈ A'}).toReal|
      let U : Set ℝ :=
        (fun v : ℝ => sSup (ga v '' PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported.ARe p)) ''
          Set.Icc (0 : ℝ) 1
      have hrhoStar :
          PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported.rhoStar
            P X Y F G μX μY (δ n m) = sSup U := rfl
      have hUnivHyp : IsHyperrect (Set.univ : Set (Fin p → ℝ)) := by
        refine ⟨fun _ => ⊥, fun _ => ⊤, fun j => le_top, ?_⟩
        ext w
        simp
      rw [hrhoStar]
      change sSup {t : ℝ | ∃ S : Set (Fin p → ℝ), IsHyperrect S ∧
          t = |Measure.real (P.map (combVec X Y μX μY (δ n m))) S
              - Measure.real (P.map (combVec F G μX μY (δ n m))) S|} ≤ sSup U
      have hU_bdd : BddAbove U := by
        refine ⟨1, ?_⟩
        rintro _ ⟨v, hv, rfl⟩
        refine csSup_le (hARe_ne.image (ga v)) ?_
        rintro _ ⟨A', hA', rfl⟩
        exact habs_le _ _ measureReal_nonneg measureReal_le_one measureReal_nonneg measureReal_le_one
      refine csSup_le ⟨_, ⟨Set.univ, hUnivHyp, rfl⟩⟩ ?_
      rintro t ⟨S, hS, rfl⟩
      have hSm : MeasurableSet S := hSmeas S hS
      have hbdd1 : BddAbove (ga 1 '' PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported.ARe p) := by
        refine ⟨1, ?_⟩
        rintro _ ⟨A', hA', rfl⟩
        exact habs_le _ _ measureReal_nonneg measureReal_le_one measureReal_nonneg measureReal_le_one
      have hmem : |Measure.real (P.map (combVec X Y μX μY (δ n m))) S
            - Measure.real (P.map (combVec F G μX μY (δ n m))) S|
          ∈ ga 1 '' PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported.ARe p := by
        refine ⟨S, hS, ?_⟩
        have hreal : ∀ s : Set Ω, Measure.real P s = (P s).toReal := fun s => rfl
        have hga1 : ga 1 S = |(P {ω : Ω | (fun j : Fin p =>
              Real.sqrt 1 * PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported.partXY X Y μX μY (δ n m) ω j
                + Real.sqrt (1 - 1) * PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported.partFG F G μX μY (δ n m) ω j) ∈ S}).toReal
            - (P {ω : Ω | PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported.partFG F G μX μY (δ n m) ω ∈ S}).toReal| := rfl
        rw [hga1, MeasureTheory.map_measureReal_apply hA hSm,
          MeasureTheory.map_measureReal_apply hB hSm]
        simp only [hreal]
        have h1 : {ω : Ω | (fun j : Fin p =>
              Real.sqrt 1 * PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported.partXY X Y μX μY (δ n m) ω j
                + Real.sqrt (1 - 1) * PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported.partFG F G μX μY (δ n m) ω j) ∈ S}
            = (combVec X Y μX μY (δ n m)) ⁻¹' S := by
          ext ω
          simp only [Set.mem_setOf_eq, Set.mem_preimage, hinterp1 ω]
        have h2 : {ω : Ω | PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported.partFG F G μX μY (δ n m) ω ∈ S}
            = (combVec F G μX μY (δ n m)) ⁻¹' S := by
          ext ω
          simp only [Set.mem_setOf_eq, Set.mem_preimage]
          rfl
        rw [h1, h2]
      have hle1 : |Measure.real (P.map (combVec X Y μX μY (δ n m))) S
            - Measure.real (P.map (combVec F G μX μY (δ n m))) S|
          ≤ sSup (ga 1 '' PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported.ARe p) :=
        le_csSup hbdd1 hmem
      have hle2 : sSup (ga 1 '' PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported.ARe p)
          ≤ sSup U := le_csSup hU_bdd ⟨1, by norm_num, rfl⟩
      exact le_trans hle1 hle2
    have hallVec :
        (PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported.allVec X Y F G
            : (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) → Ω → (Fin p → ℝ))
          = allVars X Y F G := by
      funext s ω
      cases s with
      | inl i => rfl
      | inr s1 =>
        cases s1 with
        | inl j => rfl
        | inr s2 =>
          cases s2 with
          | inl i' => rfl
          | inr j' => rfl
    have hlogp : (0 : ℝ) < Real.log (p : ℝ) := by
      refine Real.log_pos ?_
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      linarith
    have hnc : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hmc : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hdabs : (0 : ℝ) < |δ n m| := abs_pos.mpr hδ
    have hvar' : b ≤ ⨅ j : Fin p, ∫ ω, (combVec X Y μX μY (δ n m) ω j) ^ 2 ∂P := by
      show b ≤ sInf (Set.range fun j : Fin p => ∫ ω, (combVec X Y μX μY (δ n m) ω j) ^ 2 ∂P)
      refine le_csInf ⟨_, Set.mem_range_self (⟨0, by omega⟩ : Fin p)⟩ ?_
      rintro _ ⟨j, rfl⟩
      exact hvar j
    have hstep2 :=
      @hKstar_bound n m p hn hm hp δ (phiN K1 LbarX p n) (phiM K1 LbarY (δ n m) p m)
        (by linarith) (by linarith) Ω inferInstance P inferInstance μX μY X Y F G
        (fun i => measurable_pi_iff.mpr (fun j => hXm i j))
        (fun i => measurable_pi_iff.mpr (fun j => hYm i j))
        (fun i => measurable_pi_iff.mpr (fun j => hFm i j))
        (fun i => measurable_pi_iff.mpr (fun j => hGm i j))
        (hallVec.symm ▸ hiAll) hXmean hYmean hXint hYint hFint hGint
        hX3 hY3 hF3 hG3 hXcov hYcov hFcov hGcov
        hFgauss hFmean hFcov_eq hGgauss hGmean hGcov_eq
        hvarint hvar'
    have hLA :
        PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported.Lstat P X μX
          = Lmom P X μX := rfl
    have hLB :
        PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported.Lstat P Y μY
          = Lmom P Y μY := rfl
    have hMA :
        PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported.MstatN P X F μX
            (phiN K1 LbarX p n)
          = Mn P X F μX (phiN K1 LbarX p n) := rfl
    have hMB :
        PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported.MstatM P Y G μY
            (phiM K1 LbarY (δ n m) p m) (δ n m)
          = MmStar P Y G μY (δ n m) (phiM K1 LbarY (δ n m) p m) := by
      unfold PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported.MstatM
      rw [if_neg hδ]
      rfl
    rw [hLA, hLB, hMA, hMB] at hstep2
    refine le_trans hstep1 ?_
    set ρs : ℝ := PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported.rhoStar P X Y F G μX μY (δ n m) with hρs
    have hA1 : (0 : ℝ) ≤ A1 := by
      show (0 : ℝ) ≤ (LbarX ^ 2 * (Real.log (p : ℝ)) ^ 7 / (n : ℝ)) ^ (1 / 6 : ℝ)
      exact Real.rpow_nonneg
        (div_nonneg (mul_nonneg (sq_nonneg LbarX) (pow_pos hlogp 7).le) hnc.le) _
    have hB1 : (0 : ℝ) ≤ B1 := by
      show (0 : ℝ) ≤ (LbarY ^ 2 * (Real.log (p : ℝ)) ^ 7 * |δ n m| ^ 6 / (m : ℝ)) ^ (1 / 6 : ℝ)
      exact Real.rpow_nonneg
        (div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg LbarY) (pow_pos hlogp 7).le)
          (pow_nonneg (abs_nonneg _) 6)) hmc.le) _
    have hmaxpos : (0 : ℝ) < max Kstar 2 :=
      lt_of_lt_of_le (by norm_num) (le_max_right Kstar 2)
    have hKstarK1 : Kstar * K1 ≤ 1 := by
      have h : Kstar * (max Kstar 2)⁻¹ ≤ (max Kstar 2) * (max Kstar 2)⁻¹ :=
        mul_le_mul_of_nonneg_right (le_max_left Kstar 2) (le_of_lt (inv_pos.mpr hmaxpos))
      rw [mul_inv_cancel₀ (ne_of_gt hmaxpos)] at h
      exact h
    have hK1_2 : 2 * K1 ≤ 1 := by
      have h : (max Kstar 2)⁻¹ * 2 ≤ (max Kstar 2)⁻¹ * (max Kstar 2) :=
        mul_le_mul_of_nonneg_left (le_max_right Kstar 2) (le_of_lt (inv_pos.mpr hmaxpos))
      rw [inv_mul_cancel₀ (ne_of_gt hmaxpos)] at h
      linarith [h]
    have hK1half : K1 ≤ 1 / 2 := by linarith
    have hK1sq : K1 ^ 2 ≤ 1 / 4 := by nlinarith [hK1half, hK1_pos]
    have hKstarK1cube : Kstar * K1 ^ 3 ≤ 1 / 4 := by
      have h1 : Kstar * K1 ^ 3 = (Kstar * K1) * K1 ^ 2 := by ring
      rw [h1]
      calc (Kstar * K1) * K1 ^ 2 ≤ 1 * (1 / 4) :=
            mul_le_mul hKstarK1 hK1sq (sq_nonneg K1) (by norm_num)
        _ = 1 / 4 := by norm_num
    have h2KstarK1cube : 2 * Kstar * K1 ^ 3 ≤ 1 / 2 := by linarith
    have hcoordMax_nonneg : ∀ f : Fin p → ℝ, (∀ j, 0 ≤ f j) → (0 : ℝ) ≤ coordMax f := by
      intro f hf
      have hbdd : BddAbove (Set.range f) := (Set.finite_range f).bddAbove
      have hmem : f ⟨0, by omega⟩ ∈ Set.range f := Set.mem_range_self _
      have hle : f ⟨0, by omega⟩ ≤ coordMax f := le_csSup hbdd hmem
      linarith [hf ⟨0, by omega⟩]
    have hLmomX_nonneg : (0 : ℝ) ≤ Lmom P X μX := by
      refine hcoordMax_nonneg _ (fun j => ?_)
      refine mul_nonneg (le_of_lt (inv_pos.mpr hnc)) ?_
      exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun ω => pow_nonneg (abs_nonneg _) 3))
    have hLmomY_nonneg : (0 : ℝ) ≤ Lmom P Y μY := by
      refine hcoordMax_nonneg _ (fun j => ?_)
      refine mul_nonneg (le_of_lt (inv_pos.mpr hmc)) ?_
      exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun ω => pow_nonneg (abs_nonneg _) 3))
    have hLXpos : (0 : ℝ) < LbarX :=
      lt_of_le_of_ne (le_trans hLmomX_nonneg hLX) (Ne.symm hLX0)
    have hLYpos : (0 : ℝ) < LbarY :=
      lt_of_le_of_ne (le_trans hLmomY_nonneg hLY) (Ne.symm hLY0)
    have hMtruncN_nonneg : ∀ (Z : Fin n → Ω → Fin p → ℝ) (mz : Fin p → ℝ) (thr : ℝ),
        (0 : ℝ) ≤ Mtrunc P Z mz thr := by
      intro Z mz thr
      have h2 : (0 : ℝ) ≤ ∑ i : Fin n,
          ∫ ω, Set.indicator {ω : Ω | coordMax (fun j => |Z i ω j - mz j|) > thr}
            (fun ω => coordMax (fun j => |Z i ω j - mz j|) ^ 3) ω ∂P := by
        refine Finset.sum_nonneg (fun i _ => ?_)
        refine integral_nonneg (fun ω => ?_)
        by_cases hx : (ω ∈ {ω : Ω | coordMax (fun j => |Z i ω j - mz j|) > thr})
        · rw [Set.indicator_of_mem hx]
          exact pow_nonneg (hcoordMax_nonneg _ (fun j => abs_nonneg _)) 3
        · simp [Set.indicator, hx]
      show (0 : ℝ) ≤ Mtrunc P Z mz thr
      exact mul_nonneg (le_of_lt (inv_pos.mpr hnc)) h2
    have hMtruncM_nonneg : ∀ (Z : Fin m → Ω → Fin p → ℝ) (mz : Fin p → ℝ) (thr : ℝ),
        (0 : ℝ) ≤ Mtrunc P Z mz thr := by
      intro Z mz thr
      have h2 : (0 : ℝ) ≤ ∑ i : Fin m,
          ∫ ω, Set.indicator {ω : Ω | coordMax (fun j => |Z i ω j - mz j|) > thr}
            (fun ω => coordMax (fun j => |Z i ω j - mz j|) ^ 3) ω ∂P := by
        refine Finset.sum_nonneg (fun i _ => ?_)
        refine integral_nonneg (fun ω => ?_)
        by_cases hx : (ω ∈ {ω : Ω | coordMax (fun j => |Z i ω j - mz j|) > thr})
        · rw [Set.indicator_of_mem hx]
          exact pow_nonneg (hcoordMax_nonneg _ (fun j => abs_nonneg _)) 3
        · simp [Set.indicator, hx]
      show (0 : ℝ) ≤ Mtrunc P Z mz thr
      exact mul_nonneg (le_of_lt (inv_pos.mpr hmc)) h2
    have hC1 : (0 : ℝ) ≤ C1 := by
      show (0 : ℝ) ≤ (Mtrunc P X μX (Real.sqrt (n : ℝ) / (4 * phiN K1 LbarX p n * Real.log (p : ℝ)))
          + Mtrunc P F μX (Real.sqrt (n : ℝ) / (4 * phiN K1 LbarX p n * Real.log (p : ℝ)))) / LbarX
      exact div_nonneg
        (add_nonneg (hMtruncN_nonneg X μX _) (hMtruncN_nonneg F μX _)) hLXpos.le
    have hD1 : (0 : ℝ) ≤ D1 := by
      show (0 : ℝ) ≤ (Mtrunc P Y μY
            (Real.sqrt (m : ℝ) / (4 * |δ n m| * phiM K1 LbarY (δ n m) p m * Real.log (p : ℝ)))
          + Mtrunc P G μY
            (Real.sqrt (m : ℝ) / (4 * |δ n m| * phiM K1 LbarY (δ n m) p m * Real.log (p : ℝ)))) / LbarY
      exact div_nonneg
        (add_nonneg (hMtruncM_nonneg Y μY _) (hMtruncM_nonneg G μY _)) hLYpos.le
    have hsn : (Real.sqrt (n : ℝ))⁻¹ = (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow]
      exact (Real.rpow_neg (le_of_lt hnc) (1 / 2 : ℝ)).symm
    have hsm : (Real.sqrt (m : ℝ))⁻¹ = (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow]
      exact (Real.rpow_neg (le_of_lt hmc) (1 / 2 : ℝ)).symm
    have hsqlog : Real.sqrt (Real.log (p : ℝ)) = (Real.log (p : ℝ)) ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
    have hpow227 : (Real.log (p : ℝ)) ^ 2 * (Real.log (p : ℝ)) ^ (1 / 2 : ℝ)
        = (Real.log (p : ℝ)) ^ (5 / 2 : ℝ) := by
      rw [← Real.rpow_natCast (Real.log (p : ℝ)) 2, ← Real.rpow_add hlogp]
      norm_num
    have hradX : LbarX ^ 2 * (Real.log (p : ℝ)) ^ 4 * (1 : ℝ) ^ 2 / (n : ℝ)
        = LbarX ^ 2 * (Real.log (p : ℝ)) ^ 4 / (n : ℝ) := by ring
    have hradX7 : LbarX ^ 2 * (Real.log (p : ℝ)) ^ 7 * (1 : ℝ) ^ 2 / (n : ℝ)
        = LbarX ^ 2 * (Real.log (p : ℝ)) ^ 7 / (n : ℝ) := by ring
    have hradM : LbarY ^ 2 * (Real.log (p : ℝ)) ^ 4 * (|δ n m| ^ 3) ^ 2 / (m : ℝ)
        = LbarY ^ 2 * (Real.log (p : ℝ)) ^ 4 * |δ n m| ^ 6 / (m : ℝ) := by ring
    have hradM7 : LbarY ^ 2 * (Real.log (p : ℝ)) ^ 7 * (|δ n m| ^ 3) ^ 2 / (m : ℝ)
        = LbarY ^ 2 * (Real.log (p : ℝ)) ^ 7 * |δ n m| ^ 6 / (m : ℝ) := by ring
    have hphiX : phiN K1 LbarX p n
        = K1 * ((LbarX ^ 2 * (Real.log (p : ℝ)) ^ 4 * (1 : ℝ) ^ 2 / (n : ℝ)) ^
            (-(1 / 6 : ℝ))) := by
      rw [phiN, hradX]
    have hphiMc : phiM K1 LbarY (δ n m) p m
        = K1 * ((LbarY ^ 2 * (Real.log (p : ℝ)) ^ 4 * (|δ n m| ^ 3) ^ 2 / (m : ℝ)) ^
            (-(1 / 6 : ℝ))) := by
      rw [phiM, hradM]
    have hnodeX := statopia_math_node_1192201732_5ae35332 K1 LbarX (Real.log (p : ℝ)) 1 (n : ℝ)
      hK1_pos hLXpos hlogp one_pos hnc
    have hnodeM :=
      statopia_math_node_1192201732_5ae35332 K1 LbarY (Real.log (p : ℝ)) (|δ n m| ^ 3) (m : ℝ)
        hK1_pos hLYpos hlogp (pow_pos hdabs 3) hmc
    have hX1 : (n : ℝ) ^ (-(1 / 2 : ℝ)) * (phiN K1 LbarX p n) ^ 3 * (Real.log (p : ℝ)) ^ 2
        * LbarX = K1 ^ 3 := by
      have h := hnodeX.1
      rw [← hphiX] at h
      simpa using h
    have hX2 : (n : ℝ) ^ (-(1 / 2 : ℝ)) * (phiN K1 LbarX p n) ^ 2
        * (Real.log (p : ℝ)) ^ (5 / 2 : ℝ) * LbarX = K1 ^ 2 * A1 := by
      have h := hnodeX.2.1
      rw [← hphiX, hradX7] at h
      simpa only [mul_one] using h
    have hX3 : (n : ℝ) ^ (-(1 / 2 : ℝ)) * (phiN K1 LbarX p n) ^ 3 * (Real.log (p : ℝ)) ^ 2
        = K1 ^ 3 / LbarX := by
      have h := hnodeX.2.2.1
      rw [← hphiX] at h
      simpa using h
    have hX4 : (phiN K1 LbarX p n)⁻¹ * (Real.log (p : ℝ)) ^ (1 / 2 : ℝ) = K1⁻¹ * A1 := by
      have h := hnodeX.2.2.2
      rw [← hphiX, hradX7] at h
      exact h
    have hM1 : (m : ℝ) ^ (-(1 / 2 : ℝ)) * (phiM K1 LbarY (δ n m) p m) ^ 3
        * (Real.log (p : ℝ)) ^ 2 * LbarY * |δ n m| ^ 3 = K1 ^ 3 := by
      have h := hnodeM.1
      rw [← hphiMc] at h
      exact h
    have hM2 : (m : ℝ) ^ (-(1 / 2 : ℝ)) * (phiM K1 LbarY (δ n m) p m) ^ 2
        * (Real.log (p : ℝ)) ^ (5 / 2 : ℝ) * LbarY * |δ n m| ^ 3 = K1 ^ 2 * B1 := by
      have h := hnodeM.2.1
      rw [← hphiMc, hradM7] at h
      exact h
    have hM3 : (m : ℝ) ^ (-(1 / 2 : ℝ)) * (phiM K1 LbarY (δ n m) p m) ^ 3
        * (Real.log (p : ℝ)) ^ 2 * |δ n m| ^ 3 = K1 ^ 3 / LbarY := by
      have h := hnodeM.2.2.1
      rw [← hphiMc] at h
      exact h
    have hM4 : (phiM K1 LbarY (δ n m) p m)⁻¹ * (Real.log (p : ℝ)) ^ (1 / 2 : ℝ)
        = K1⁻¹ * B1 := by
      have h := hnodeM.2.2.2
      rw [← hphiMc, hradM7] at h
      exact h
    by_cases hρ : (0 : ℝ) ≤ ρs
    · show ρs ≤ K2 * (A1 + Mn P X F μX (phiN K1 LbarX p n) / LbarX + B1
        + MmStar P Y G μY (δ n m) (phiM K1 LbarY (δ n m) p m) / LbarY)
      rw [hsn, hsm, hsqlog] at hstep2
      have htp : (0 : ℝ) < (Real.log (p : ℝ)) ^ (1 / 2 : ℝ) := by positivity
      have hφ1ge : (0 : ℝ) < phiN K1 LbarX p n := by linarith
      have hφ2ge : (0 : ℝ) < phiM K1 LbarY (δ n m) p m := by linarith
      have hint1 : (0 : ℝ) ≤ (phiN K1 LbarX p n)⁻¹ := (inv_pos.mpr hφ1ge).le
      have hint2 : (0 : ℝ) ≤ (phiM K1 LbarY (δ n m) p m)⁻¹ := (inv_pos.mpr hφ2ge).le
      have hmin : (min (phiN K1 LbarX p n) (phiM K1 LbarY (δ n m) p m))⁻¹
          ≤ (phiN K1 LbarX p n)⁻¹ + (phiM K1 LbarY (δ n m) p m)⁻¹ := by
        rcases le_total (phiN K1 LbarX p n) (phiM K1 LbarY (δ n m) p m) with h | h
        · rw [min_eq_left h]
          linarith [hint2]
        · rw [min_eq_right h]
          linarith [hint1]
      have hBx : phiN K1 LbarX p n * Lmom P X μX * ρs
            + Lmom P X μX * (Real.log (p : ℝ)) ^ (1 / 2 : ℝ)
            + phiN K1 LbarX p n * Mn P X F μX (phiN K1 LbarX p n)
          ≤ phiN K1 LbarX p n * LbarX * ρs + LbarX * (Real.log (p : ℝ)) ^ (1 / 2 : ℝ)
            + phiN K1 LbarX p n * Mn P X F μX (phiN K1 LbarX p n) := by
        refine add_le_add (add_le_add ?_ ?_) (le_refl _)
        · calc phiN K1 LbarX p n * Lmom P X μX * ρs
              = phiN K1 LbarX p n * (Lmom P X μX * ρs) := by ring
            _ ≤ phiN K1 LbarX p n * (LbarX * ρs) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hLX hρ) hφ1ge.le
            _ = phiN K1 LbarX p n * LbarX * ρs := by ring
        · exact mul_le_mul_of_nonneg_right hLX htp.le
      have hBy : phiM K1 LbarY (δ n m) p m * Lmom P Y μY * ρs
            + Lmom P Y μY * (Real.log (p : ℝ)) ^ (1 / 2 : ℝ)
            + phiM K1 LbarY (δ n m) p m * MmStar P Y G μY (δ n m) (phiM K1 LbarY (δ n m) p m)
          ≤ phiM K1 LbarY (δ n m) p m * LbarY * ρs + LbarY * (Real.log (p : ℝ)) ^ (1 / 2 : ℝ)
            + phiM K1 LbarY (δ n m) p m * MmStar P Y G μY (δ n m) (phiM K1 LbarY (δ n m) p m) := by
        refine add_le_add (add_le_add ?_ ?_) (le_refl _)
        · calc phiM K1 LbarY (δ n m) p m * Lmom P Y μY * ρs
              = phiM K1 LbarY (δ n m) p m * (Lmom P Y μY * ρs) := by ring
            _ ≤ phiM K1 LbarY (δ n m) p m * (LbarY * ρs) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hLY hρ) hφ2ge.le
            _ = phiM K1 LbarY (δ n m) p m * LbarY * ρs := by ring
        · exact mul_le_mul_of_nonneg_right hLY htp.le
      have hs1 : (n : ℝ) ^ (-(1 / 2 : ℝ)) * (phiN K1 LbarX p n) ^ 2 * (Real.log (p : ℝ)) ^ 2
            * (phiN K1 LbarX p n * Lmom P X μX * ρs
              + Lmom P X μX * (Real.log (p : ℝ)) ^ (1 / 2 : ℝ)
              + phiN K1 LbarX p n * Mn P X F μX (phiN K1 LbarX p n))
          ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) * (phiN K1 LbarX p n) ^ 2 * (Real.log (p : ℝ)) ^ 2
            * (phiN K1 LbarX p n * LbarX * ρs + LbarX * (Real.log (p : ℝ)) ^ (1 / 2 : ℝ)
              + phiN K1 LbarX p n * Mn P X F μX (phiN K1 LbarX p n)) :=
        mul_le_mul_of_nonneg_left hBx (by positivity)
      have hs2 : (m : ℝ) ^ (-(1 / 2 : ℝ)) * (phiM K1 LbarY (δ n m) p m) ^ 2
            * (Real.log (p : ℝ)) ^ 2 * |δ n m| ^ 3
            * (phiM K1 LbarY (δ n m) p m * Lmom P Y μY * ρs
              + Lmom P Y μY * (Real.log (p : ℝ)) ^ (1 / 2 : ℝ)
              + phiM K1 LbarY (δ n m) p m * MmStar P Y G μY (δ n m) (phiM K1 LbarY (δ n m) p m))
          ≤ (m : ℝ) ^ (-(1 / 2 : ℝ)) * (phiM K1 LbarY (δ n m) p m) ^ 2
            * (Real.log (p : ℝ)) ^ 2 * |δ n m| ^ 3
            * (phiM K1 LbarY (δ n m) p m * LbarY * ρs + LbarY * (Real.log (p : ℝ)) ^ (1 / 2 : ℝ)
              + phiM K1 LbarY (δ n m) p m * MmStar P Y G μY (δ n m) (phiM K1 LbarY (δ n m) p m)) :=
        mul_le_mul_of_nonneg_left hBy (by positivity)
      have hs3 : (min (phiN K1 LbarX p n) (phiM K1 LbarY (δ n m) p m))⁻¹
            * (Real.log (p : ℝ)) ^ (1 / 2 : ℝ)
          ≤ (phiN K1 LbarX p n)⁻¹ * (Real.log (p : ℝ)) ^ (1 / 2 : ℝ)
            + (phiM K1 LbarY (δ n m) p m)⁻¹ * (Real.log (p : ℝ)) ^ (1 / 2 : ℝ) := by
        simpa [add_mul] using mul_le_mul_of_nonneg_right hmin htp.le
      have e1 : (n : ℝ) ^ (-(1 / 2 : ℝ)) * (phiN K1 LbarX p n) ^ 2 * (Real.log (p : ℝ)) ^ 2
            * (phiN K1 LbarX p n * LbarX * ρs) = K1 ^ 3 * ρs := by
        rw [show (n : ℝ) ^ (-(1 / 2 : ℝ)) * (phiN K1 LbarX p n) ^ 2
              * (Real.log (p : ℝ)) ^ 2 * (phiN K1 LbarX p n * LbarX * ρs)
            = ((n : ℝ) ^ (-(1 / 2 : ℝ)) * (phiN K1 LbarX p n) ^ 3
                * (Real.log (p : ℝ)) ^ 2 * LbarX) * ρs by ring, hX1]
      have e2 : (n : ℝ) ^ (-(1 / 2 : ℝ)) * (phiN K1 LbarX p n) ^ 2 * (Real.log (p : ℝ)) ^ 2
            * (LbarX * (Real.log (p : ℝ)) ^ (1 / 2 : ℝ)) = K1 ^ 2 * A1 := by
        rw [show (n : ℝ) ^ (-(1 / 2 : ℝ)) * (phiN K1 LbarX p n) ^ 2
              * (Real.log (p : ℝ)) ^ 2 * (LbarX * (Real.log (p : ℝ)) ^ (1 / 2 : ℝ))
            = (n : ℝ) ^ (-(1 / 2 : ℝ)) * (phiN K1 LbarX p n) ^ 2
                * ((Real.log (p : ℝ)) ^ 2 * (Real.log (p : ℝ)) ^ (1 / 2 : ℝ)) * LbarX by ring,
          hpow227, hX2]
      have e3 : (n : ℝ) ^ (-(1 / 2 : ℝ)) * (phiN K1 LbarX p n) ^ 2 * (Real.log (p : ℝ)) ^ 2
            * (phiN K1 LbarX p n * Mn P X F μX (phiN K1 LbarX p n))
          = K1 ^ 3 * (Mn P X F μX (phiN K1 LbarX p n) / LbarX) := by
        rw [show (n : ℝ) ^ (-(1 / 2 : ℝ)) * (phiN K1 LbarX p n) ^ 2
              * (Real.log (p : ℝ)) ^ 2 * (phiN K1 LbarX p n * Mn P X F μX (phiN K1 LbarX p n))
            = ((n : ℝ) ^ (-(1 / 2 : ℝ)) * (phiN K1 LbarX p n) ^ 3
                * (Real.log (p : ℝ)) ^ 2) * Mn P X F μX (phiN K1 LbarX p n) by ring, hX3]
        ring
      have e4 : (m : ℝ) ^ (-(1 / 2 : ℝ)) * (phiM K1 LbarY (δ n m) p m) ^ 2
            * (Real.log (p : ℝ)) ^ 2 * |δ n m| ^ 3
            * (phiM K1 LbarY (δ n m) p m * LbarY * ρs) = K1 ^ 3 * ρs := by
        rw [show (m : ℝ) ^ (-(1 / 2 : ℝ)) * (phiM K1 LbarY (δ n m) p m) ^ 2
              * (Real.log (p : ℝ)) ^ 2 * |δ n m| ^ 3
              * (phiM K1 LbarY (δ n m) p m * LbarY * ρs)
            = ((m : ℝ) ^ (-(1 / 2 : ℝ)) * (phiM K1 LbarY (δ n m) p m) ^ 3
                * (Real.log (p : ℝ)) ^ 2 * LbarY * |δ n m| ^ 3) * ρs by ring, hM1]
      have e5 : (m : ℝ) ^ (-(1 / 2 : ℝ)) * (phiM K1 LbarY (δ n m) p m) ^ 2
            * (Real.log (p : ℝ)) ^ 2 * |δ n m| ^ 3
            * (LbarY * (Real.log (p : ℝ)) ^ (1 / 2 : ℝ)) = K1 ^ 2 * B1 := by
        rw [show (m : ℝ) ^ (-(1 / 2 : ℝ)) * (phiM K1 LbarY (δ n m) p m) ^ 2
              * (Real.log (p : ℝ)) ^ 2 * |δ n m| ^ 3 * (LbarY * (Real.log (p : ℝ)) ^ (1 / 2 : ℝ))
            = (m : ℝ) ^ (-(1 / 2 : ℝ)) * (phiM K1 LbarY (δ n m) p m) ^ 2
                * ((Real.log (p : ℝ)) ^ 2 * (Real.log (p : ℝ)) ^ (1 / 2 : ℝ))
                * LbarY * |δ n m| ^ 3 by ring,
          hpow227, hM2]
      have e6 : (m : ℝ) ^ (-(1 / 2 : ℝ)) * (phiM K1 LbarY (δ n m) p m) ^ 2
            * (Real.log (p : ℝ)) ^ 2 * |δ n m| ^ 3
            * (phiM K1 LbarY (δ n m) p m
              * MmStar P Y G μY (δ n m) (phiM K1 LbarY (δ n m) p m))
          = K1 ^ 3 * (MmStar P Y G μY (δ n m) (phiM K1 LbarY (δ n m) p m) / LbarY) := by
        rw [show (m : ℝ) ^ (-(1 / 2 : ℝ)) * (phiM K1 LbarY (δ n m) p m) ^ 2
              * (Real.log (p : ℝ)) ^ 2 * |δ n m| ^ 3
              * (phiM K1 LbarY (δ n m) p m
                * MmStar P Y G μY (δ n m) (phiM K1 LbarY (δ n m) p m))
            = ((m : ℝ) ^ (-(1 / 2 : ℝ)) * (phiM K1 LbarY (δ n m) p m) ^ 3
                * (Real.log (p : ℝ)) ^ 2 * |δ n m| ^ 3)
                * MmStar P Y G μY (δ n m) (phiM K1 LbarY (δ n m) p m) by ring, hM3]
        ring
      have hxeq : (n : ℝ) ^ (-(1 / 2 : ℝ)) * (phiN K1 LbarX p n) ^ 2 * (Real.log (p : ℝ)) ^ 2
            * (phiN K1 LbarX p n * LbarX * ρs + LbarX * (Real.log (p : ℝ)) ^ (1 / 2 : ℝ)
              + phiN K1 LbarX p n * Mn P X F μX (phiN K1 LbarX p n))
          = K1 ^ 3 * ρs + K1 ^ 2 * A1
            + K1 ^ 3 * (Mn P X F μX (phiN K1 LbarX p n) / LbarX) := by
        rw [mul_add, mul_add, e1, e2, e3]
      have hyeq : (m : ℝ) ^ (-(1 / 2 : ℝ)) * (phiM K1 LbarY (δ n m) p m) ^ 2
            * (Real.log (p : ℝ)) ^ 2 * |δ n m| ^ 3
            * (phiM K1 LbarY (δ n m) p m * LbarY * ρs + LbarY * (Real.log (p : ℝ)) ^ (1 / 2 : ℝ)
              + phiM K1 LbarY (δ n m) p m * MmStar P Y G μY (δ n m) (phiM K1 LbarY (δ n m) p m))
          = K1 ^ 3 * ρs + K1 ^ 2 * B1
            + K1 ^ 3 * (MmStar P Y G μY (δ n m) (phiM K1 LbarY (δ n m) p m) / LbarY) := by
        rw [mul_add, mul_add, e4, e5, e6]
      have hred : ρs ≤
          Kstar * (2 * K1 ^ 3 * ρs + K1 ^ 2 * A1 + K1⁻¹ * A1 + K1 ^ 2 * B1 + K1⁻¹ * B1
            + K1 ^ 3 * (Mn P X F μX (phiN K1 LbarX p n) / LbarX)
            + K1 ^ 3 * (MmStar P Y G μY (δ n m) (phiM K1 LbarY (δ n m) p m) / LbarY)) := by
        refine le_trans hstep2 ?_
        refine mul_le_mul_of_nonneg_left ?_ hKstar_pos.le
        refine le_trans (add_le_add (add_le_add hs1 hs2) hs3) ?_
        rw [hxeq, hyeq, hX4, hM4]
        linarith only [hX4]
      have habs1 : 2 * Kstar * (K1 ^ 2 + K1⁻¹) ≤ K2 :=
        le_max_left (2 * Kstar * (K1 ^ 2 + K1⁻¹)) (2⁻¹ : ℝ)
      have habs2 : (1 / 2 : ℝ) ≤ K2 :=
        le_trans (by norm_num : (1 / 2 : ℝ) ≤ 2⁻¹)
          (le_max_right (2 * Kstar * (K1 ^ 2 + K1⁻¹)) (2⁻¹ : ℝ))
      have e1 : 2 * Kstar * (K1 ^ 2 + K1⁻¹) * (A1 + B1) ≤ K2 * (A1 + B1) :=
        mul_le_mul_of_nonneg_right habs1 (add_nonneg hA1 hB1)
      have e2 : 2 * Kstar * K1 ^ 3
            * (Mn P X F μX (phiN K1 LbarX p n) / LbarX
              + MmStar P Y G μY (δ n m) (phiM K1 LbarY (δ n m) p m) / LbarY)
          ≤ K2 * (Mn P X F μX (phiN K1 LbarX p n) / LbarX
              + MmStar P Y G μY (δ n m) (phiM K1 LbarY (δ n m) p m) / LbarY) :=
        mul_le_mul_of_nonneg_right (le_trans h2KstarK1cube habs2) (add_nonneg hC1 hD1)
      have e3 : 2 * Kstar * K1 ^ 3 * ρs ≤ (1 / 2) * ρs :=
        mul_le_mul_of_nonneg_right h2KstarK1cube hρ
      have hfin : ρs ≤ K2 * (A1 + Mn P X F μX (phiN K1 LbarX p n) / LbarX + B1
          + MmStar P Y G μY (δ n m) (phiM K1 LbarY (δ n m) p m) / LbarY) := by
        linarith only [hred, e1, e2, e3]
      exact hfin
    · push_neg at hρ
      have hsum : (0 : ℝ) ≤ A1 + C1 + B1 + D1 := by linarith only [hA1, hB1, hC1, hD1]
      have h0 : (0 : ℝ) ≤ K2 * (A1 + C1 + B1 + D1) := mul_nonneg hK2_pos.le hsum
      linarith only [hρ, h0]
  exact key
  /- @proof-region region.root.d984c0b77a90 end -/

end Statlib.Imported

-- Paper root revision 94bd7884-810d-4c6e-8233-9877a6141afe

