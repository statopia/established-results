import Lean
import ProverJobs.ResidualE2ESupport20261106.M_2899ebcb4b6cf51030cf
import ProverJobs.ResidualE2ESupport20261106.M_30e3ebd8c0ecef26f046
import ProverJobs.ResidualE2ESupport20261106.M_53d3ee54de21d6381358
import ProverJobs.ResidualE2ESupport20261106.M_063131cff1ca3159222f
import ProverJobs.ResidualE2ESupport20261106.M_43de51f17c9c68343029
import ProverJobs.ResidualE2ESupport20261106.M_1449e14e4276b073c7b2

namespace PaperProofTasks.ResidualE2ESupport20261106




run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_2830626271_c12488ac : ∀ (rho Cth : ℝ) (hrho : 0 < rho) (hCth : 12 ≤ Cth),
    ∃ N2 : ℕ, 3 ≤ N2 ∧
      ∀ (m n r : ℕ) (p mu0 : ℝ),
        0 < m → 1 ≤ n → n ≤ m → 12 * r ≤ n →
        rho ≤ (n : ℝ) / (m : ℝ) → (n : ℝ) / (m : ℝ) ≤ 1 →
        0 < p → p ≤ 1 → 0 ≤ mu0 * (r : ℝ) →
        N2 ≤ m →
        (n : ℝ) * p ≥ Cth ^ 2 * mu0 * (r : ℝ) * Real.log (m : ℝ) →
        ∀ (U0 : Matrix (Fin m) (Fin r) ℝ) (V0 : Matrix (Fin n) (Fin r) ℝ),
          U0.transpose * U0 = 1 → V0.transpose * V0 = 1 →
          rowNorm U0 ≤ Real.sqrt (mu0 * (r : ℝ) / (m : ℝ)) →
          rowNorm V0 ≤ Real.sqrt (mu0 * (r : ℝ) / (n : ℝ)) →
          ∀ {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
            [IsProbabilityMeasure P] (Om : Fin m → Fin n → Omega → ℝ),
            (∀ (i : Fin m) (j : Fin n), Measurable (Om i j)) →
            iIndepFun (fun (ij : Fin m × Fin n) => Om ij.1 ij.2) P →
            (∀ (i : Fin m) (j : Fin n), ∀ᵐ ω ∂P, Om i j ω = 0 ∨ Om i j ω = 1) →
            (∀ (i : Fin m) (j : Fin n), P {ω | Om i j ω = 1} = ENNReal.ofReal p) →
            (∀ (i : Fin m) (j : Fin n), Integrable (Om i j) P) →
            (∀ (i : Fin m) (j : Fin n), ∫ ω, Om i j ω ∂P = p) →
            1 - ENNReal.ofReal ((1 / 2 : ℝ) / (n : ℝ) ^ 4) ≤
              P {ω | ∀ A B : Matrix (Fin m) (Fin n) ℝ,
                    MemTangentRect U0 V0 A → MemTangentRect U0 V0 B →
                    |frobInner (Tmask p (fun i j => Om i j ω) A) B| ≤
                      Cth * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p)) *
                        frobNorm A * frobNorm B} := by
  /- @proof-region region.target-node.session.6da46e13a5ca1247 begin -/
  intro rhomin Cth hrhomin hCth
  refine ⟨3, le_refl 3, ?_⟩
  intro m n r p mu0 hmpos hn hnm hr hrho1 hrho2 hppos hp1 hmu h3m hnp

  intro U0 V0 hU hV hrowU hrowV
  intro Omega _ P _ Om hmeas hindep h01 hprob hint hmean
  by_cases hr0 : r = 0
  · subst hr0
    have hzero : ∀ X : Matrix (Fin m) (Fin n) ℝ, MemTangentRect U0 V0 X → X = 0 := by
      intro X hX
      obtain ⟨Aa, Ba, rfl⟩ := hX
      have h1 : U0 * Aa.transpose = 0 := by
        ext i j
        simp [Matrix.mul_apply]
      have h2 : Ba * V0.transpose = 0 := by
        ext i j
        simp [Matrix.mul_apply]
      rw [h1, h2, add_zero]
    have hmem : ∀ omega : Omega, ∀ A B : Matrix (Fin m) (Fin n) ℝ,
        MemTangentRect U0 V0 A → MemTangentRect U0 V0 B →
        |frobInner (Tmask p (fun i j => Om i j omega) A) B| ≤
          Cth * Real.sqrt (mu0 * ((0 : ℕ) : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p)) *
            frobNorm A * frobNorm B := by
      intro omega A B hA hB
      rw [hzero A hA, hzero B hB]
      simp [Tmask, Wmask, frobInner, frobNorm]
    have huniv : {omega : Omega | ∀ A B : Matrix (Fin m) (Fin n) ℝ,
        MemTangentRect U0 V0 A → MemTangentRect U0 V0 B →
        |frobInner (Tmask p (fun i j => Om i j omega) A) B| ≤
          Cth * Real.sqrt (mu0 * ((0 : ℕ) : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p)) *
            frobNorm A * frobNorm B} = Set.univ :=
      Set.eq_univ_of_forall hmem
    rw [huniv, measure_univ]
    simp
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
    by_cases hmuz : mu0 * (r : ℝ) = 0
    · have hmu0 : mu0 = 0 := by
        rcases mul_eq_zero.mp hmuz with h | h
        · exact h
        · exact absurd h (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hrpos))
      have hrow0 : rowNorm U0 ≤ 0 := by
        have hz : mu0 * (r : ℝ) / (m : ℝ) = 0 := by rw [hmu0]; simp
        simpa [hz] using hrowU
      have hU0 : U0 = 0 := by
        ext i j
        have hbdd : BddAbove (Set.range fun i : Fin m => Real.sqrt (∑ k : Fin r, (U0 i k) ^ 2)) :=
          (Set.finite_range _).bddAbove
        have hle : Real.sqrt (∑ k : Fin r, (U0 i k) ^ 2) ≤ 0 := by
          have h1 : Real.sqrt (∑ k : Fin r, (U0 i k) ^ 2) ≤ rowNorm U0 := le_ciSup hbdd i
          linarith
        have hsum : ∑ k : Fin r, (U0 i k) ^ 2 = 0 := by
          have h2 : Real.sqrt (∑ k : Fin r, (U0 i k) ^ 2) = 0 :=
            le_antisymm hle (Real.sqrt_nonneg _)
          have h3 : (Real.sqrt (∑ k : Fin r, (U0 i k) ^ 2)) ^ 2 = ∑ k : Fin r, (U0 i k) ^ 2 :=
            Real.sq_sqrt (by positivity)
          rw [h2] at h3
          linarith
        have hnn : ∀ k ∈ (Finset.univ : Finset (Fin r)), (0 : ℝ) ≤ (U0 i k) ^ 2 :=
          fun k _ => sq_nonneg _
        have h4 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum
        have hen : (U0 i j) ^ 2 = 0 := h4 j (Finset.mem_univ j)
        have hen' : U0 i j = 0 := mul_self_eq_zero.mp (by simpa [pow_two] using hen)
        simpa using hen'

      have h01 : (0 : Matrix (Fin r) (Fin r) ℝ) = 1 := by
        rw [← hU, hU0]
        simp
      have hcontra := congrFun (congrFun h01 ⟨0, hrpos⟩) ⟨0, hrpos⟩
      have h01' : (0 : ℝ) = 1 := by simpa using hcontra
      exact absurd h01' (by norm_num)

    · have hmu0pos : 0 < mu0 * (r : ℝ) := lt_of_le_of_ne hmu (Ne.symm hmuz)
      have hm : 1 ≤ m := le_trans hn hnm
      obtain ⟨D, b, z, hb_mem, hb_orth, hb_span, hz_mem, hz_orth, hz_norm⟩ :=
        statopia_math_node_3968230781_9dc3fc25 m n r hrpos hn hnm U0 V0 hU hV
      obtain ⟨hzn_le, hzn_sq2, hzn_sq4, hzeq, hsumsq, hsup, hframe, hD1, hD2⟩ :=
        statopia_math_node_2390824386_f5f4c323 m n r hm hn hnm mu0 U0 V0 hU hV hmu hrowU hrowV
          D b hb_orth hb_mem hb_span z hz_mem hz_orth
      have hident' : ∀ (i : Fin m) (j : Fin n),
          Real.sqrt (∑ q : Fin D, (tangentCoords b i j q) ^ 2) ^ 2
            ≤ 4 * (mu0 * (r : ℝ)) / (n : ℝ) := by
        intro i j
        rw [Real.sq_sqrt (Finset.sum_nonneg (fun q _ => sq_nonneg (tangentCoords b i j q)))]
        exact le_trans (hsumsq i j) (le_of_eq (by ring))
      have hU0ne : U0 ≠ 0 := by
        intro h
        have h10 : (1 : Matrix (Fin r) (Fin r) ℝ) = 0 := by
          rw [← hU, h]; simp
        have hk := congrFun (congrFun h10 ⟨0, hrpos⟩) ⟨0, hrpos⟩
        have hk' : (1 : ℝ) = 0 := by simpa using hk
        exact absurd hk' (by norm_num)
      have hXne : U0 * V0.transpose ≠ 0 := by
        intro hX0
        apply hU0ne
        have h1 : U0 * V0.transpose * V0 = 0 := by rw [hX0]; simp
        rw [Matrix.mul_assoc, hV, Matrix.mul_one] at h1
        exact h1
      have hDpos : 0 < D := by
        rcases Nat.eq_zero_or_pos D with hD0 | hD
        · have hmem : MemTangentRect U0 V0 (U0 * V0.transpose) := ⟨0, U0, by simp⟩
          obtain ⟨c, hc⟩ := hb_span _ hmem
          have hempty : (Finset.univ : Finset (Fin D)) = ∅ := by
            rw [← Finset.card_eq_zero]
            simp [hD0]
          rw [hempty] at hc
          simp at hc
          exact absurd hc hXne
        · exact hD
      have hP := statopia_math_node_1315657654_81913db9 m n r D p mu0 Cth b hDpos h3m hn hnm hr
        hD1 hppos hp1 hmu0pos hCth hnp hident' hframe P Om hmeas hindep h01 hprob hint hmean

      have hsub : {omega : Omega | specNorm (∑ i : Fin m, ∑ j : Fin n,
            (p⁻¹ * Om i j omega - 1) •
              Matrix.vecMulVec (tangentCoords b i j) (tangentCoords b i j)) ≤
            Cth * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))} ⊆
          {omega : Omega | ∀ A B : Matrix (Fin m) (Fin n) ℝ,
            MemTangentRect U0 V0 A → MemTangentRect U0 V0 B →
            |frobInner (Tmask p (fun i j => Om i j omega) A) B| ≤
              Cth * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p)) *
                frobNorm A * frobNorm B} := by
        intro omega hω A B hA hB
        exact statopia_math_node_625384939_fdaf230d m n r D p
          (Cth * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p)))
          U0 V0 b (fun i j => Om i j omega) hb_orth hb_span hω A B hA hB
      exact le_trans hP (measure_mono hsub)






  /- @proof-region region.target-node.session.6da46e13a5ca1247 end -/

end

end Statlib.Imported

