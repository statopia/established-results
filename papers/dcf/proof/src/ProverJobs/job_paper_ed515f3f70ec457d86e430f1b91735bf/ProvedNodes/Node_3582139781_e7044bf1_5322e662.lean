import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base

namespace PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Statlib.StatFoundation.RandomVariable.Gaussian
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Statlib.StatFoundation.RandomVariable.Gaussian
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_3582139781_e7044bf1 : ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m p : ℕ) (hm : 0 < m) (hp : 0 < p)
    (muY : Fin p → ℝ) (Y G : Fin m → Ω → Fin p → ℝ) (theta : ℝ) (htheta : 0 < theta)
    (hYm : ∀ i : Fin m, Measurable (Y i))
    (hGm : ∀ i : Fin m, Measurable (G i))
    (hY3 : ∀ (i : Fin m) (r : Fin p), Integrable (fun ω => |Y i ω r - muY r| ^ 3) P)
    (hG3 : ∀ (i : Fin m) (r : Fin p), Integrable (fun ω => |G i ω r - muY r| ^ 3) P)
    (i : Fin m),
    (let A : Ω × Ω → Fin p → ℝ := fun x r => |Y i x.1 r - muY r|
     let Ab : Ω × Ω → Fin p → ℝ := fun x r => |G i x.1 r - muY r|
     let Bb : Ω × Ω → Fin p → ℝ := fun x r => |G i x.2 r - muY r|
     let Pb : Ω × Ω → Fin p → ℝ := fun x r => A x r + Ab x r + Bb x r
     let maxPb : Ω × Ω → ℝ := fun x => ⨆ r : Fin p, Pb x r
     let Lam : Ω × Ω → Prop := fun x => ∀ r : Fin p, Pb x r ≤ theta
     (∀ x : Ω × Ω, Lam x →
        (maxPb x) ^ 3 ≤ 27 * ∑ r : Fin p, ((A x r) ^ 3 + (Ab x r) ^ 3 + (Bb x r) ^ 3)) ∧
     (∀ x : Ω × Ω, ¬ Lam x →
        (maxPb x) ^ 3 ≤ 81 * ∑ r : Fin p,
          ((A x r) ^ 3 * (if theta < 3 * A x r then (1 : ℝ) else 0)
            + (Ab x r) ^ 3 * (if theta < 3 * Ab x r then (1 : ℝ) else 0)
            + (Bb x r) ^ 3 * (if theta < 3 * Bb x r then (1 : ℝ) else 0))) ∧
     (∫ x, (if Lam x then (maxPb x) ^ 3 else 0) ∂(P.prod P) ≤
        27 * ∑ r : Fin p,
          (∫ ω, |Y i ω r - muY r| ^ 3 ∂P + 2 * ∫ ω, |G i ω r - muY r| ^ 3 ∂P)) ∧
     (∫ x, (if Lam x then 0 else (maxPb x) ^ 3) ∂(P.prod P) ≤
        81 * ∑ r : Fin p,
          (∫ ω, |Y i ω r - muY r| ^ 3 * (if theta < 3 * |Y i ω r - muY r| then (1 : ℝ) else 0) ∂P
            + 2 * ∫ ω, |G i ω r - muY r| ^ 3 * (if theta < 3 * |G i ω r - muY r| then (1 : ℝ) else 0) ∂P))) := by
  /- @proof-region region.target-node.session.e3409c75933e4897 begin -/
  intro Ω _ P _ m p hm hp muY Y G theta htheta hYm hGm hY3 hG3 i
  classical
  let A : Ω × Ω → Fin p → ℝ := fun x r => |Y i x.1 r - muY r|
  let Ab : Ω × Ω → Fin p → ℝ := fun x r => |G i x.1 r - muY r|
  let Bb : Ω × Ω → Fin p → ℝ := fun x r => |G i x.2 r - muY r|
  let Pb : Ω × Ω → Fin p → ℝ := fun x r => A x r + Ab x r + Bb x r
  let maxPb : Ω × Ω → ℝ := fun x => ⨆ r : Fin p, Pb x r
  let Lam : Ω × Ω → Prop := fun x => ∀ r : Fin p, Pb x r ≤ theta
  have cube_mono : ∀ x y : ℝ, 0 ≤ x → x ≤ y → x ^ 3 ≤ y ^ 3 := by
    intro x y hx hxy
    have hfac : (0 : ℝ) ≤ y ^ 2 + x * y + x ^ 2 := by
      nlinarith [sq_nonneg y, sq_nonneg x, mul_nonneg hx (le_trans hx hxy)]
    have hprod : (0 : ℝ) ≤ (y - x) * (y ^ 2 + x * y + x ^ 2) :=
      mul_nonneg (by linarith) hfac
    nlinarith [hprod]
  have pow2v : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → (x + y) ^ 3 ≤ 4 * (x ^ 3 + y ^ 3) := by
    intro x y hx hy
    nlinarith [mul_nonneg (sq_nonneg (x - y)) (show (0 : ℝ) ≤ x + y by linarith)]
  have key3 : ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c →
      (a + b + c) ^ 3 ≤ 27 * (a ^ 3 + b ^ 3 + c ^ 3) := by
    intro a b c ha hb hc
    have e1 : ((a + b) + c) ^ 3 ≤ 4 * ((a + b) ^ 3 + c ^ 3) := pow2v (a + b) c (by linarith) hc
    have e2 : (a + b) ^ 3 ≤ 4 * (a ^ 3 + b ^ 3) := pow2v a b ha hb
    have e3 : (a + b + c) ^ 3 ≤ 16 * (a ^ 3 + b ^ 3) + 4 * c ^ 3 := by nlinarith [e1, e2]
    have e4 : 16 * (a ^ 3 + b ^ 3) + 4 * c ^ 3 ≤ 27 * (a ^ 3 + b ^ 3 + c ^ 3) := by
      nlinarith [pow_nonneg ha 3, pow_nonneg hb 3, pow_nonneg hc 3]
    linarith [e3, e4]
  have key2 : ∀ a b c t : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → t < a + b + c →
      (a + b + c) ^ 3 ≤ 81 * (a ^ 3 * (if t < 3 * a then (1 : ℝ) else 0)
        + b ^ 3 * (if t < 3 * b then (1 : ℝ) else 0)
        + c ^ 3 * (if t < 3 * c then (1 : ℝ) else 0)) := by
    intro a b c t ha hb hc ht
    have ha3 : (0 : ℝ) ≤ a ^ 3 := pow_nonneg ha 3
    have hb3 : (0 : ℝ) ≤ b ^ 3 := pow_nonneg hb 3
    have hc3 : (0 : ℝ) ≤ c ^ 3 := pow_nonneg hc 3
    by_cases hA : t < 3 * a
    · by_cases hB : t < 3 * b
      · by_cases hC : t < 3 * c
        · rw [if_pos hA, if_pos hB, if_pos hC]
          nlinarith [key3 a b c ha hb hc, ha3, hb3, hc3]
        · have hC' : 3 * c ≤ t := not_lt.mp hC
          rw [if_pos hA, if_pos hB, if_neg hC]
          have hc2 : c ^ 3 ≤ 2 * (a ^ 3 + b ^ 3) := by
            have h1 : c ≤ (a + b) / 2 := by linarith
            have h2 : c ^ 3 ≤ ((a + b) / 2) ^ 3 := cube_mono c ((a + b) / 2) hc h1
            have h3 : ((a + b) / 2) ^ 3 ≤ 2 * (a ^ 3 + b ^ 3) := by
              have hp := pow2v a b ha hb
              nlinarith [hp]
            linarith [h2, h3]
          nlinarith [key3 a b c ha hb hc, hc2]
      · have hB' : 3 * b ≤ t := not_lt.mp hB
        by_cases hC : t < 3 * c
        · rw [if_pos hA, if_neg hB, if_pos hC]
          have hb2 : b ^ 3 ≤ 2 * (a ^ 3 + c ^ 3) := by
            have h1 : b ≤ (a + c) / 2 := by linarith
            have h2 : b ^ 3 ≤ ((a + c) / 2) ^ 3 := cube_mono b ((a + c) / 2) hb h1
            have h3 : ((a + c) / 2) ^ 3 ≤ 2 * (a ^ 3 + c ^ 3) := by
              have hp := pow2v a c ha hc
              nlinarith [hp]
            linarith [h2, h3]
          nlinarith [key3 a b c ha hb hc, hb2]
        · have hC' : 3 * c ≤ t := not_lt.mp hC
          rw [if_pos hA, if_neg hB, if_neg hC]
          have hs : a + b + c ≤ 3 * a := by linarith
          have h1 : (a + b + c) ^ 3 ≤ (3 * a) ^ 3 :=
            cube_mono (a + b + c) (3 * a) (by linarith) hs
          have h2 : (3 * a) ^ 3 = 27 * a ^ 3 := by ring
          nlinarith [h1, h2, ha3]
    · have hA' : 3 * a ≤ t := not_lt.mp hA
      by_cases hB : t < 3 * b
      · by_cases hC : t < 3 * c
        · rw [if_neg hA, if_pos hB, if_pos hC]
          have ha2 : a ^ 3 ≤ 2 * (b ^ 3 + c ^ 3) := by
            have h1 : a ≤ (b + c) / 2 := by linarith
            have h2 : a ^ 3 ≤ ((b + c) / 2) ^ 3 := cube_mono a ((b + c) / 2) ha h1
            have h3 : ((b + c) / 2) ^ 3 ≤ 2 * (b ^ 3 + c ^ 3) := by
              have hp := pow2v b c hb hc
              nlinarith [hp]
            linarith [h2, h3]
          nlinarith [key3 a b c ha hb hc, ha2]
        · have hC' : 3 * c ≤ t := not_lt.mp hC
          rw [if_neg hA, if_pos hB, if_neg hC]
          have hs : a + b + c ≤ 3 * b := by linarith
          have h1 : (a + b + c) ^ 3 ≤ (3 * b) ^ 3 :=
            cube_mono (a + b + c) (3 * b) (by linarith) hs
          have h2 : (3 * b) ^ 3 = 27 * b ^ 3 := by ring
          nlinarith [h1, h2, hb3]
      · have hB' : 3 * b ≤ t := not_lt.mp hB
        by_cases hC : t < 3 * c
        · rw [if_neg hA, if_neg hB, if_pos hC]
          have hs : a + b + c ≤ 3 * c := by linarith
          have h1 : (a + b + c) ^ 3 ≤ (3 * c) ^ 3 :=
            cube_mono (a + b + c) (3 * c) (by linarith) hs
          have h2 : (3 * c) ^ 3 = 27 * c ^ 3 := by ring
          nlinarith [h1, h2, hc3]
        · exfalso
          have hC' : 3 * c ≤ t := not_lt.mp hC
          linarith
  have h1 : ∀ x : Ω × Ω, Lam x →
      (maxPb x) ^ 3 ≤ 27 * ∑ r : Fin p, ((A x r) ^ 3 + (Ab x r) ^ 3 + (Bb x r) ^ 3) := by
    intro x _
    haveI : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
    obtain ⟨r0, hr0⟩ := exists_eq_ciSup_of_finite (f := fun r : Fin p => Pb x r)
    have hmax : maxPb x = Pb x r0 := by
      simp only [maxPb]
      exact hr0.symm
    rw [hmax]
    have hA : 0 ≤ A x r0 := abs_nonneg (Y i x.1 r0 - muY r0)
    have hAb : 0 ≤ Ab x r0 := abs_nonneg (G i x.1 r0 - muY r0)
    have hBb : 0 ≤ Bb x r0 := abs_nonneg (G i x.2 r0 - muY r0)
    have hcube : (Pb x r0) ^ 3 ≤ 27 * ((A x r0) ^ 3 + (Ab x r0) ^ 3 + (Bb x r0) ^ 3) := by
      simp only [Pb]
      exact key3 (A x r0) (Ab x r0) (Bb x r0) hA hAb hBb
    have hle : (A x r0) ^ 3 + (Ab x r0) ^ 3 + (Bb x r0) ^ 3
        ≤ ∑ r : Fin p, ((A x r) ^ 3 + (Ab x r) ^ 3 + (Bb x r) ^ 3) := by
      apply Finset.single_le_sum
        (f := fun r : Fin p => (A x r) ^ 3 + (Ab x r) ^ 3 + (Bb x r) ^ 3)
      · intro r _
        have h1a : 0 ≤ A x r := abs_nonneg (Y i x.1 r - muY r)
        have h1b : 0 ≤ Ab x r := abs_nonneg (G i x.1 r - muY r)
        have h1c : 0 ≤ Bb x r := abs_nonneg (G i x.2 r - muY r)
        have p1 := pow_nonneg h1a 3
        have p2 := pow_nonneg h1b 3
        have p3 := pow_nonneg h1c 3
        linarith
      · exact Finset.mem_univ r0
    calc (Pb x r0) ^ 3
        ≤ 27 * ((A x r0) ^ 3 + (Ab x r0) ^ 3 + (Bb x r0) ^ 3) := hcube
      _ ≤ 27 * ∑ r : Fin p, ((A x r) ^ 3 + (Ab x r) ^ 3 + (Bb x r) ^ 3) := by
          apply mul_le_mul_of_nonneg_left hle
          norm_num
  have h2 : ∀ x : Ω × Ω, ¬ Lam x →
      (maxPb x) ^ 3 ≤ 81 * ∑ r : Fin p,
        ((A x r) ^ 3 * (if theta < 3 * A x r then (1 : ℝ) else 0)
          + (Ab x r) ^ 3 * (if theta < 3 * Ab x r then (1 : ℝ) else 0)
          + (Bb x r) ^ 3 * (if theta < 3 * Bb x r then (1 : ℝ) else 0)) := by
    intro x hx
    haveI : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
    obtain ⟨r0, -, hrsup⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun r : Fin p => Pb x r)
    have hmax : maxPb x = Pb x r0 := by
      show (⨆ r : Fin p, Pb x r) = Pb x r0
      rw [← Finset.sup'_univ_eq_ciSup (fun r : Fin p => Pb x r)]
      exact hrsup
    have hx' : ∃ r : Fin p, theta < Pb x r := by
      obtain ⟨r1, hr1⟩ := (Classical.not_forall (p := fun r : Fin p => Pb x r ≤ theta)).mp hx
      exact ⟨r1, not_le.mp hr1⟩
    obtain ⟨r1, hr1⟩ := hx'
    have hle1 : Pb x r1 ≤ Pb x r0 := by
      have h : Pb x r1 ≤ Finset.univ.sup' Finset.univ_nonempty (fun r : Fin p => Pb x r) :=
        (Finset.le_sup'_iff Finset.univ_nonempty).mpr ⟨r1, Finset.mem_univ r1, le_refl _⟩
      rw [hrsup] at h
      exact h
    have hPbt : theta < Pb x r0 := lt_of_lt_of_le hr1 hle1
    have hA : 0 ≤ A x r0 := abs_nonneg (Y i x.1 r0 - muY r0)
    have hAb : 0 ≤ Ab x r0 := abs_nonneg (G i x.1 r0 - muY r0)
    have hBb : 0 ≤ Bb x r0 := abs_nonneg (G i x.2 r0 - muY r0)
    have hpbt : theta < A x r0 + Ab x r0 + Bb x r0 := by
      have e := hPbt
      simp only [Pb] at e
      exact e
    have hkey := key2 (A x r0) (Ab x r0) (Bb x r0) theta hA hAb hBb hpbt
    have hsingle :
        (A x r0) ^ 3 * (if theta < 3 * A x r0 then (1 : ℝ) else 0)
          + (Ab x r0) ^ 3 * (if theta < 3 * Ab x r0 then (1 : ℝ) else 0)
          + (Bb x r0) ^ 3 * (if theta < 3 * Bb x r0 then (1 : ℝ) else 0)
        ≤ ∑ r : Fin p,
          ((A x r) ^ 3 * (if theta < 3 * A x r then (1 : ℝ) else 0)
            + (Ab x r) ^ 3 * (if theta < 3 * Ab x r then (1 : ℝ) else 0)
            + (Bb x r) ^ 3 * (if theta < 3 * Bb x r then (1 : ℝ) else 0)) := by
      apply Finset.single_le_sum (f := fun r : Fin p =>
        (A x r) ^ 3 * (if theta < 3 * A x r then (1 : ℝ) else 0)
          + (Ab x r) ^ 3 * (if theta < 3 * Ab x r then (1 : ℝ) else 0)
          + (Bb x r) ^ 3 * (if theta < 3 * Bb x r then (1 : ℝ) else 0))
      · intro r _
        show (0 : ℝ) ≤ (A x r) ^ 3 * (if theta < 3 * A x r then (1 : ℝ) else 0)
          + (Ab x r) ^ 3 * (if theta < 3 * Ab x r then (1 : ℝ) else 0)
          + (Bb x r) ^ 3 * (if theta < 3 * Bb x r then (1 : ℝ) else 0)
        have i1 : (0 : ℝ) ≤ (if theta < 3 * A x r then (1 : ℝ) else 0) := by split_ifs <;> norm_num
        have i2 : (0 : ℝ) ≤ (if theta < 3 * Ab x r then (1 : ℝ) else 0) := by split_ifs <;> norm_num
        have i3 : (0 : ℝ) ≤ (if theta < 3 * Bb x r then (1 : ℝ) else 0) := by split_ifs <;> norm_num
        have e1 : (0 : ℝ) ≤ (A x r) ^ 3 := pow_nonneg (abs_nonneg (Y i x.1 r - muY r)) 3
        have e2 : (0 : ℝ) ≤ (Ab x r) ^ 3 := pow_nonneg (abs_nonneg (G i x.1 r - muY r)) 3
        have e3 : (0 : ℝ) ≤ (Bb x r) ^ 3 := pow_nonneg (abs_nonneg (G i x.2 r - muY r)) 3
        have m1 := mul_nonneg e1 i1
        have m2 := mul_nonneg e2 i2
        have m3 := mul_nonneg e3 i3
        linarith
      · exact Finset.mem_univ r0
    rw [hmax]
    calc (Pb x r0) ^ 3
        = (A x r0 + Ab x r0 + Bb x r0) ^ 3 := by simp only [Pb]
      _ ≤ 81 * ((A x r0) ^ 3 * (if theta < 3 * A x r0 then (1 : ℝ) else 0)
            + (Ab x r0) ^ 3 * (if theta < 3 * Ab x r0 then (1 : ℝ) else 0)
            + (Bb x r0) ^ 3 * (if theta < 3 * Bb x r0 then (1 : ℝ) else 0)) := hkey
      _ ≤ 81 * ∑ r : Fin p,
          ((A x r) ^ 3 * (if theta < 3 * A x r then (1 : ℝ) else 0)
            + (Ab x r) ^ 3 * (if theta < 3 * Ab x r then (1 : ℝ) else 0)
            + (Bb x r) ^ 3 * (if theta < 3 * Bb x r then (1 : ℝ) else 0)) := by
          apply mul_le_mul_of_nonneg_left hsingle
          norm_num
  have h3 : ∫ x, (if Lam x then (maxPb x) ^ 3 else 0) ∂(P.prod P) ≤
      27 * ∑ r : Fin p,
        (∫ ω, |Y i ω r - muY r| ^ 3 ∂P + 2 * ∫ ω, |G i ω r - muY r| ^ 3 ∂P) := by
    have hPbnonneg : ∀ (x : Ω × Ω) (r : Fin p), 0 ≤ Pb x r := by
      intro x r
      have e1 : 0 ≤ A x r := abs_nonneg (Y i x.1 r - muY r)
      have e2 : 0 ≤ Ab x r := abs_nonneg (G i x.1 r - muY r)
      have e3 : 0 ≤ Bb x r := abs_nonneg (G i x.2 r - muY r)
      simp only [Pb]
      linarith
    have hmaxPb_nonneg : ∀ x : Ω × Ω, 0 ≤ maxPb x := by
      intro x
      haveI : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
      obtain ⟨r0, -, hrsup⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun r : Fin p => Pb x r)
      have hmax : maxPb x = Pb x r0 := by
        show (⨆ r : Fin p, Pb x r) = Pb x r0
        rw [← Finset.sup'_univ_eq_ciSup (fun r : Fin p => Pb x r)]
        exact hrsup
      rw [hmax]
      exact hPbnonneg x r0
    have hAint : ∀ r : Fin p, Integrable (fun x : Ω × Ω => (A x r) ^ 3) (P.prod P) :=
      fun r => (hY3 i r).comp_fst P
    have hBint : ∀ r : Fin p, Integrable (fun x : Ω × Ω => (Ab x r) ^ 3) (P.prod P) :=
      fun r => (hG3 i r).comp_fst P
    have hCint : ∀ r : Fin p, Integrable (fun x : Ω × Ω => (Bb x r) ^ 3) (P.prod P) :=
      fun r => (hG3 i r).comp_snd P
    have hϕint : ∀ r : Fin p,
        Integrable (fun x : Ω × Ω => (A x r) ^ 3 + (Ab x r) ^ 3 + (Bb x r) ^ 3) (P.prod P) :=
      fun r => ((hAint r).add (hBint r)).add (hCint r)
    have hAval : ∀ r : Fin p, ∫ x : Ω × Ω, (A x r) ^ 3 ∂(P.prod P) = ∫ ω, |Y i ω r - muY r| ^ 3 ∂P := by
      intro r
      rw [MeasureTheory.integral_prod (fun x : Ω × Ω => (A x r) ^ 3) (hAint r)]
      have inner : ∀ a : Ω, ∫ b : Ω, (A (a, b) r) ^ 3 ∂P = |Y i a r - muY r| ^ 3 := by
        intro a
        have hconst : (fun b : Ω => (A (a, b) r) ^ 3) = (fun _ : Ω => |Y i a r - muY r| ^ 3) := by
          funext b
          simp [A]
        rw [hconst, MeasureTheory.integral_const,
          (MeasureTheory.isProbabilityMeasure_iff_real (μ := P)).mp (inferInstance)]
        simp
      simp only [inner]
    have hBval : ∀ r : Fin p, ∫ x : Ω × Ω, (Ab x r) ^ 3 ∂(P.prod P) = ∫ ω, |G i ω r - muY r| ^ 3 ∂P := by
      intro r
      rw [MeasureTheory.integral_prod (fun x : Ω × Ω => (Ab x r) ^ 3) (hBint r)]
      have inner : ∀ a : Ω, ∫ b : Ω, (Ab (a, b) r) ^ 3 ∂P = |G i a r - muY r| ^ 3 := by
        intro a
        have hconst : (fun b : Ω => (Ab (a, b) r) ^ 3) = (fun _ : Ω => |G i a r - muY r| ^ 3) := by
          funext b
          simp [Ab]
        rw [hconst, MeasureTheory.integral_const,
          (MeasureTheory.isProbabilityMeasure_iff_real (μ := P)).mp (inferInstance)]
        simp
      simp only [inner]
    have hCval : ∀ r : Fin p, ∫ x : Ω × Ω, (Bb x r) ^ 3 ∂(P.prod P) = ∫ ω, |G i ω r - muY r| ^ 3 ∂P := by
      intro r
      rw [MeasureTheory.integral_prod (fun x : Ω × Ω => (Bb x r) ^ 3) (hCint r)]
      have inner : ∀ a : Ω, ∫ b : Ω, (Bb (a, b) r) ^ 3 ∂P = ∫ b : Ω, |G i b r - muY r| ^ 3 ∂P := by
        intro a
        have hconst : (fun b : Ω => (Bb (a, b) r) ^ 3) = (fun b : Ω => |G i b r - muY r| ^ 3) := by
          funext b
          simp [Bb]
        rw [hconst]
      simp only [inner]
      rw [MeasureTheory.integral_const,
        (MeasureTheory.isProbabilityMeasure_iff_real (μ := P)).mp (inferInstance)]
      simp
    have hϕval : ∀ r : Fin p,
        ∫ x : Ω × Ω, ((A x r) ^ 3 + (Ab x r) ^ 3 + (Bb x r) ^ 3) ∂(P.prod P)
        = ∫ ω, |Y i ω r - muY r| ^ 3 ∂P
            + (∫ ω, |G i ω r - muY r| ^ 3 ∂P + ∫ ω, |G i ω r - muY r| ^ 3 ∂P) := by
      intro r
      have hAB : Integrable (fun x : Ω × Ω => (A x r) ^ 3 + (Ab x r) ^ 3) (P.prod P) :=
        (hAint r).add (hBint r)
      have e1 : ∫ x : Ω × Ω, ((A x r) ^ 3 + (Ab x r) ^ 3 + (Bb x r) ^ 3) ∂(P.prod P)
          = (∫ x : Ω × Ω, ((A x r) ^ 3 + (Ab x r) ^ 3) ∂(P.prod P))
              + ∫ x : Ω × Ω, (Bb x r) ^ 3 ∂(P.prod P) := by
        have h := MeasureTheory.integral_add hAB (hCint r)
        simpa using h
      have e2 : ∫ x : Ω × Ω, ((A x r) ^ 3 + (Ab x r) ^ 3) ∂(P.prod P)
          = (∫ x : Ω × Ω, (A x r) ^ 3 ∂(P.prod P))
              + ∫ x : Ω × Ω, (Ab x r) ^ 3 ∂(P.prod P) := by
        have h := MeasureTheory.integral_add (hAint r) (hBint r)
        simpa using h
      rw [e1, e2, hAval r, hBval r, hCval r]
      ring
    have hFint : Integrable
        (fun x : Ω × Ω => 27 * ∑ r : Fin p, ((A x r) ^ 3 + (Ab x r) ^ 3 + (Bb x r) ^ 3)) (P.prod P) := by
      have hsum : Integrable
          (fun x : Ω × Ω => ∑ r : Fin p, ((A x r) ^ 3 + (Ab x r) ^ 3 + (Bb x r) ^ 3)) (P.prod P) :=
        MeasureTheory.integrable_finset_sum Finset.univ (fun r _ => hϕint r)
      exact hsum.const_mul 27
    have hInonneg : ∀ x : Ω × Ω, 0 ≤ (if Lam x then (maxPb x) ^ 3 else 0) := by
      intro x
      by_cases hL : Lam x
      · rw [if_pos hL]; exact pow_nonneg (hmaxPb_nonneg x) 3
      · simp only [if_neg hL, le_refl]
    have hfg : ∀ᵐ x ∂(P.prod P),
        (if Lam x then (maxPb x) ^ 3 else 0)
          ≤ 27 * ∑ r : Fin p, ((A x r) ^ 3 + (Ab x r) ^ 3 + (Bb x r) ^ 3) := by
      apply Filter.Eventually.of_forall
      intro x
      by_cases hL : Lam x
      · rw [if_pos hL]; exact h1 x hL
      · rw [if_neg hL]
        apply mul_nonneg (by norm_num)
        apply Finset.sum_nonneg
        intro r _
        have e1 : 0 ≤ (A x r) ^ 3 := pow_nonneg (abs_nonneg (Y i x.1 r - muY r)) 3
        have e2 : 0 ≤ (Ab x r) ^ 3 := pow_nonneg (abs_nonneg (G i x.1 r - muY r)) 3
        have e3 : 0 ≤ (Bb x r) ^ 3 := pow_nonneg (abs_nonneg (G i x.2 r - muY r)) 3
        linarith
    have hIle : ∫ x, (if Lam x then (maxPb x) ^ 3 else 0) ∂(P.prod P)
        ≤ ∫ x, (27 * ∑ r : Fin p, ((A x r) ^ 3 + (Ab x r) ^ 3 + (Bb x r) ^ 3)) ∂(P.prod P) :=
      MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall hInonneg) hFint hfg
    have hsumval : ∫ x : Ω × Ω, (∑ r : Fin p, ((A x r) ^ 3 + (Ab x r) ^ 3 + (Bb x r) ^ 3)) ∂(P.prod P)
        = ∑ r : Fin p,
          (∫ ω, |Y i ω r - muY r| ^ 3 ∂P + 2 * ∫ ω, |G i ω r - muY r| ^ 3 ∂P) := by
      rw [MeasureTheory.integral_finset_sum Finset.univ (fun r _ => hϕint r)]
      apply Finset.sum_congr rfl
      intro r _
      rw [hϕval r]
      ring
    have hFeq : ∫ x, (27 * ∑ r : Fin p, ((A x r) ^ 3 + (Ab x r) ^ 3 + (Bb x r) ^ 3)) ∂(P.prod P)
        = 27 * ∑ r : Fin p,
          (∫ ω, |Y i ω r - muY r| ^ 3 ∂P + 2 * ∫ ω, |G i ω r - muY r| ^ 3 ∂P) := by
      rw [MeasureTheory.integral_const_mul, hsumval]
    rw [hFeq] at hIle
    exact hIle
  have h4 : ∫ x, (if Lam x then 0 else (maxPb x) ^ 3) ∂(P.prod P) ≤
      81 * ∑ r : Fin p,
        (∫ ω, |Y i ω r - muY r| ^ 3 * (if theta < 3 * |Y i ω r - muY r| then (1 : ℝ) else 0) ∂P
          + 2 * ∫ ω, |G i ω r - muY r| ^ 3 * (if theta < 3 * |G i ω r - muY r| then (1 : ℝ) else 0) ∂P) := by
    have hAmeas : ∀ r : Fin p, Measurable (fun x : Ω × Ω => A x r) := by
      intro r
      have h1 : Measurable (fun ω : Ω => Y i ω r) := (measurable_pi_apply r).comp (hYm i)
      have h2 : Measurable (fun x : Ω × Ω => Y i x.1 r) := h1.comp measurable_fst
      have h3 : Measurable (fun x : Ω × Ω => Y i x.1 r - muY r) := h2.sub measurable_const
      have h4 : Measurable (fun x : Ω × Ω => |Y i x.1 r - muY r|) := h3.abs
      simpa only [A] using h4
    have hintA : ∀ r : Fin p, Integrable
        (fun x : Ω × Ω => (A x r) ^ 3 * (if theta < 3 * A x r then (1 : ℝ) else 0)) (P.prod P) := by
      intro r
      have hSet : MeasurableSet {x : Ω × Ω | theta < 3 * A x r} :=
        ((hAmeas r).const_mul 3) measurableSet_Ioi
      have hcube : Measurable (fun x : Ω × Ω => (A x r) ^ 3) := by
        have h2 : Measurable (fun x : Ω × Ω => A x r * A x r) :=
          Measurable.mul (hAmeas r) (hAmeas r)
        have h3 : Measurable (fun x : Ω × Ω => A x r * A x r * A x r) :=
          Measurable.mul h2 (hAmeas r)
        have heq : (fun x : Ω × Ω => (A x r) ^ 3)
            = (fun x : Ω × Ω => A x r * A x r * A x r) := by
          funext x
          ring
        rw [heq]
        exact h3
      have hind : Measurable (fun x : Ω × Ω => (if theta < 3 * A x r then (1 : ℝ) else 0)) :=
        Measurable.ite hSet measurable_const measurable_const
      have hm : Measurable
          (fun x : Ω × Ω => (A x r) ^ 3 * (if theta < 3 * A x r then (1 : ℝ) else 0)) :=
        Measurable.mul hcube hind
      refine MeasureTheory.Integrable.mono' ((hY3 i r).comp_fst P) hm.aestronglyMeasurable ?_
      apply Filter.Eventually.of_forall
      intro x
      have h1 : (0 : ℝ) ≤ (A x r) ^ 3 := pow_nonneg (abs_nonneg (Y i x.1 r - muY r)) 3
      have hin0 : (0 : ℝ) ≤ (if theta < 3 * A x r then (1 : ℝ) else 0) := by split_ifs <;> norm_num
      have hin1 : (if theta < 3 * A x r then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 hin0)]
      calc (A x r) ^ 3 * (if theta < 3 * A x r then (1 : ℝ) else 0)
          ≤ (A x r) ^ 3 * 1 := mul_le_mul_of_nonneg_left hin1 h1
        _ = (A x r) ^ 3 := by ring
    have hBmeas : ∀ r : Fin p, Measurable (fun x : Ω × Ω => Ab x r) := by
      intro r
      have h1 : Measurable (fun ω : Ω => G i ω r) := (measurable_pi_apply r).comp (hGm i)
      have h2 : Measurable (fun x : Ω × Ω => G i x.1 r) := h1.comp measurable_fst
      have h3 : Measurable (fun x : Ω × Ω => G i x.1 r - muY r) := h2.sub measurable_const
      have h4 : Measurable (fun x : Ω × Ω => |G i x.1 r - muY r|) := h3.abs
      simpa only [Ab] using h4
    have hCmeas : ∀ r : Fin p, Measurable (fun x : Ω × Ω => Bb x r) := by
      intro r
      have h1 : Measurable (fun ω : Ω => G i ω r) := (measurable_pi_apply r).comp (hGm i)
      have h2 : Measurable (fun x : Ω × Ω => G i x.2 r) := h1.comp measurable_snd
      have h3 : Measurable (fun x : Ω × Ω => G i x.2 r - muY r) := h2.sub measurable_const
      have h4 : Measurable (fun x : Ω × Ω => |G i x.2 r - muY r|) := h3.abs
      simpa only [Bb] using h4
    have hintB : ∀ r : Fin p, Integrable
        (fun x : Ω × Ω => (Ab x r) ^ 3 * (if theta < 3 * Ab x r then (1 : ℝ) else 0)) (P.prod P) := by
      intro r
      have hSet : MeasurableSet {x : Ω × Ω | theta < 3 * Ab x r} :=
        ((hBmeas r).const_mul 3) measurableSet_Ioi
      have hcube : Measurable (fun x : Ω × Ω => (Ab x r) ^ 3) := by
        have h2 : Measurable (fun x : Ω × Ω => Ab x r * Ab x r) :=
          Measurable.mul (hBmeas r) (hBmeas r)
        have h3 : Measurable (fun x : Ω × Ω => Ab x r * Ab x r * Ab x r) :=
          Measurable.mul h2 (hBmeas r)
        have heq : (fun x : Ω × Ω => (Ab x r) ^ 3)
            = (fun x : Ω × Ω => Ab x r * Ab x r * Ab x r) := by
          funext x
          ring
        rw [heq]
        exact h3
      have hind : Measurable (fun x : Ω × Ω => (if theta < 3 * Ab x r then (1 : ℝ) else 0)) :=
        Measurable.ite hSet measurable_const measurable_const
      have hm : Measurable
          (fun x : Ω × Ω => (Ab x r) ^ 3 * (if theta < 3 * Ab x r then (1 : ℝ) else 0)) :=
        Measurable.mul hcube hind
      refine MeasureTheory.Integrable.mono' ((hG3 i r).comp_fst P) hm.aestronglyMeasurable ?_
      apply Filter.Eventually.of_forall
      intro x
      have h1 : (0 : ℝ) ≤ (Ab x r) ^ 3 := pow_nonneg (abs_nonneg (G i x.1 r - muY r)) 3
      have hin0 : (0 : ℝ) ≤ (if theta < 3 * Ab x r then (1 : ℝ) else 0) := by split_ifs <;> norm_num
      have hin1 : (if theta < 3 * Ab x r then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 hin0)]
      calc (Ab x r) ^ 3 * (if theta < 3 * Ab x r then (1 : ℝ) else 0)
          ≤ (Ab x r) ^ 3 * 1 := mul_le_mul_of_nonneg_left hin1 h1
        _ = (Ab x r) ^ 3 := by ring
    have hintC : ∀ r : Fin p, Integrable
        (fun x : Ω × Ω => (Bb x r) ^ 3 * (if theta < 3 * Bb x r then (1 : ℝ) else 0)) (P.prod P) := by
      intro r
      have hSet : MeasurableSet {x : Ω × Ω | theta < 3 * Bb x r} :=
        ((hCmeas r).const_mul 3) measurableSet_Ioi
      have hcube : Measurable (fun x : Ω × Ω => (Bb x r) ^ 3) := by
        have h2 : Measurable (fun x : Ω × Ω => Bb x r * Bb x r) :=
          Measurable.mul (hCmeas r) (hCmeas r)
        have h3 : Measurable (fun x : Ω × Ω => Bb x r * Bb x r * Bb x r) :=
          Measurable.mul h2 (hCmeas r)
        have heq : (fun x : Ω × Ω => (Bb x r) ^ 3)
            = (fun x : Ω × Ω => Bb x r * Bb x r * Bb x r) := by
          funext x
          ring
        rw [heq]
        exact h3
      have hind : Measurable (fun x : Ω × Ω => (if theta < 3 * Bb x r then (1 : ℝ) else 0)) :=
        Measurable.ite hSet measurable_const measurable_const
      have hm : Measurable
          (fun x : Ω × Ω => (Bb x r) ^ 3 * (if theta < 3 * Bb x r then (1 : ℝ) else 0)) :=
        Measurable.mul hcube hind
      refine MeasureTheory.Integrable.mono' ((hG3 i r).comp_snd P) hm.aestronglyMeasurable ?_
      apply Filter.Eventually.of_forall
      intro x
      have h1 : (0 : ℝ) ≤ (Bb x r) ^ 3 := pow_nonneg (abs_nonneg (G i x.2 r - muY r)) 3
      have hin0 : (0 : ℝ) ≤ (if theta < 3 * Bb x r then (1 : ℝ) else 0) := by split_ifs <;> norm_num
      have hin1 : (if theta < 3 * Bb x r then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 hin0)]
      calc (Bb x r) ^ 3 * (if theta < 3 * Bb x r then (1 : ℝ) else 0)
          ≤ (Bb x r) ^ 3 * 1 := mul_le_mul_of_nonneg_left hin1 h1
        _ = (Bb x r) ^ 3 := by ring
    have hmaxPb_nonneg : ∀ x : Ω × Ω, 0 ≤ maxPb x := by
      intro x
      have hPbnn : ∀ r : Fin p, 0 ≤ Pb x r := by
        intro r
        have e1 : 0 ≤ A x r := abs_nonneg (Y i x.1 r - muY r)
        have e2 : 0 ≤ Ab x r := abs_nonneg (G i x.1 r - muY r)
        have e3 : 0 ≤ Bb x r := abs_nonneg (G i x.2 r - muY r)
        simp only [Pb]
        linarith
      haveI : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
      obtain ⟨r0, -, hrsup⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun r : Fin p => Pb x r)
      have hmax : maxPb x = Pb x r0 := by
        show (⨆ r : Fin p, Pb x r) = Pb x r0
        rw [← Finset.sup'_univ_eq_ciSup (fun r : Fin p => Pb x r)]
        exact hrsup
      rw [hmax]
      exact hPbnn r0
    have hAval' : ∀ r : Fin p,
        ∫ x : Ω × Ω, (A x r) ^ 3 * (if theta < 3 * A x r then (1 : ℝ) else 0) ∂(P.prod P)
        = ∫ ω, |Y i ω r - muY r| ^ 3 * (if theta < 3 * |Y i ω r - muY r| then (1 : ℝ) else 0) ∂P := by
      intro r
      rw [MeasureTheory.integral_prod
        (fun x : Ω × Ω => (A x r) ^ 3 * (if theta < 3 * A x r then (1 : ℝ) else 0)) (hintA r)]
      have inner : ∀ a : Ω,
          ∫ b : Ω, ((A (a, b) r) ^ 3 * (if theta < 3 * A (a, b) r then (1 : ℝ) else 0)) ∂P
          = |Y i a r - muY r| ^ 3 * (if theta < 3 * |Y i a r - muY r| then (1 : ℝ) else 0) := by
        intro a
        have hconst :
            (fun b : Ω => (A (a, b) r) ^ 3 * (if theta < 3 * A (a, b) r then (1 : ℝ) else 0))
            = (fun _ : Ω => |Y i a r - muY r| ^ 3 * (if theta < 3 * |Y i a r - muY r| then (1 : ℝ) else 0)) := by
          funext b
          simp [A]
        rw [hconst, MeasureTheory.integral_const,
          (MeasureTheory.isProbabilityMeasure_iff_real (μ := P)).mp (inferInstance)]
        simp
      simp only [inner]
    have hBval' : ∀ r : Fin p,
        ∫ x : Ω × Ω, (Ab x r) ^ 3 * (if theta < 3 * Ab x r then (1 : ℝ) else 0) ∂(P.prod P)
        = ∫ ω, |G i ω r - muY r| ^ 3 * (if theta < 3 * |G i ω r - muY r| then (1 : ℝ) else 0) ∂P := by
      intro r
      rw [MeasureTheory.integral_prod
        (fun x : Ω × Ω => (Ab x r) ^ 3 * (if theta < 3 * Ab x r then (1 : ℝ) else 0)) (hintB r)]
      have inner : ∀ a : Ω,
          ∫ b : Ω, ((Ab (a, b) r) ^ 3 * (if theta < 3 * Ab (a, b) r then (1 : ℝ) else 0)) ∂P
          = |G i a r - muY r| ^ 3 * (if theta < 3 * |G i a r - muY r| then (1 : ℝ) else 0) := by
        intro a
        have hconst :
            (fun b : Ω => (Ab (a, b) r) ^ 3 * (if theta < 3 * Ab (a, b) r then (1 : ℝ) else 0))
            = (fun _ : Ω => |G i a r - muY r| ^ 3 * (if theta < 3 * |G i a r - muY r| then (1 : ℝ) else 0)) := by
          funext b
          simp [Ab]
        rw [hconst, MeasureTheory.integral_const,
          (MeasureTheory.isProbabilityMeasure_iff_real (μ := P)).mp (inferInstance)]
        simp
      simp only [inner]
    have hCval' : ∀ r : Fin p,
        ∫ x : Ω × Ω, (Bb x r) ^ 3 * (if theta < 3 * Bb x r then (1 : ℝ) else 0) ∂(P.prod P)
        = ∫ ω, |G i ω r - muY r| ^ 3 * (if theta < 3 * |G i ω r - muY r| then (1 : ℝ) else 0) ∂P := by
      intro r
      rw [MeasureTheory.integral_prod
        (fun x : Ω × Ω => (Bb x r) ^ 3 * (if theta < 3 * Bb x r then (1 : ℝ) else 0)) (hintC r)]
      have inner : ∀ a : Ω,
          ∫ b : Ω, ((Bb (a, b) r) ^ 3 * (if theta < 3 * Bb (a, b) r then (1 : ℝ) else 0)) ∂P
          = ∫ b : Ω, (|G i b r - muY r| ^ 3 * (if theta < 3 * |G i b r - muY r| then (1 : ℝ) else 0)) ∂P := by
        intro a
        have hconst :
            (fun b : Ω => (Bb (a, b) r) ^ 3 * (if theta < 3 * Bb (a, b) r then (1 : ℝ) else 0))
            = (fun b : Ω => |G i b r - muY r| ^ 3 * (if theta < 3 * |G i b r - muY r| then (1 : ℝ) else 0)) := by
          funext b
          simp [Bb]
        rw [hconst]
      simp only [inner]
      rw [MeasureTheory.integral_const,
        (MeasureTheory.isProbabilityMeasure_iff_real (μ := P)).mp (inferInstance)]
      simp
    have hϕint' : ∀ r : Fin p, Integrable
        (fun x : Ω × Ω => (A x r) ^ 3 * (if theta < 3 * A x r then (1 : ℝ) else 0)
          + (Ab x r) ^ 3 * (if theta < 3 * Ab x r then (1 : ℝ) else 0)
          + (Bb x r) ^ 3 * (if theta < 3 * Bb x r then (1 : ℝ) else 0)) (P.prod P) :=
      fun r => ((hintA r).add (hintB r)).add (hintC r)
    have hϕval' : ∀ r : Fin p,
        ∫ x : Ω × Ω, ((A x r) ^ 3 * (if theta < 3 * A x r then (1 : ℝ) else 0)
          + (Ab x r) ^ 3 * (if theta < 3 * Ab x r then (1 : ℝ) else 0)
          + (Bb x r) ^ 3 * (if theta < 3 * Bb x r then (1 : ℝ) else 0)) ∂(P.prod P)
        = (∫ ω, |Y i ω r - muY r| ^ 3 * (if theta < 3 * |Y i ω r - muY r| then (1 : ℝ) else 0) ∂P)
          + ((∫ ω, |G i ω r - muY r| ^ 3 * (if theta < 3 * |G i ω r - muY r| then (1 : ℝ) else 0) ∂P)
            + (∫ ω, |G i ω r - muY r| ^ 3 * (if theta < 3 * |G i ω r - muY r| then (1 : ℝ) else 0) ∂P)) := by
      intro r
      have hAB : Integrable
          (fun x : Ω × Ω => (A x r) ^ 3 * (if theta < 3 * A x r then (1 : ℝ) else 0)
            + (Ab x r) ^ 3 * (if theta < 3 * Ab x r then (1 : ℝ) else 0)) (P.prod P) :=
        (hintA r).add (hintB r)
      have e1 : ∫ x : Ω × Ω, ((A x r) ^ 3 * (if theta < 3 * A x r then (1 : ℝ) else 0)
          + (Ab x r) ^ 3 * (if theta < 3 * Ab x r then (1 : ℝ) else 0)
          + (Bb x r) ^ 3 * (if theta < 3 * Bb x r then (1 : ℝ) else 0)) ∂(P.prod P)
          = (∫ x : Ω × Ω, ((A x r) ^ 3 * (if theta < 3 * A x r then (1 : ℝ) else 0)
              + (Ab x r) ^ 3 * (if theta < 3 * Ab x r then (1 : ℝ) else 0)) ∂(P.prod P))
            + ∫ x : Ω × Ω, (Bb x r) ^ 3 * (if theta < 3 * Bb x r then (1 : ℝ) else 0) ∂(P.prod P) := by
        have h := MeasureTheory.integral_add hAB (hintC r)
        simpa using h
      have e2 : ∫ x : Ω × Ω, ((A x r) ^ 3 * (if theta < 3 * A x r then (1 : ℝ) else 0)
          + (Ab x r) ^ 3 * (if theta < 3 * Ab x r then (1 : ℝ) else 0)) ∂(P.prod P)
          = (∫ x : Ω × Ω, (A x r) ^ 3 * (if theta < 3 * A x r then (1 : ℝ) else 0) ∂(P.prod P))
            + ∫ x : Ω × Ω, (Ab x r) ^ 3 * (if theta < 3 * Ab x r then (1 : ℝ) else 0) ∂(P.prod P) := by
        have h := MeasureTheory.integral_add (hintA r) (hintB r)
        simpa using h
      rw [e1, e2, hAval' r, hBval' r, hCval' r]
      ring
    have hFint' : Integrable
        (fun x : Ω × Ω => 81 * ∑ r : Fin p,
          ((A x r) ^ 3 * (if theta < 3 * A x r then (1 : ℝ) else 0)
            + (Ab x r) ^ 3 * (if theta < 3 * Ab x r then (1 : ℝ) else 0)
            + (Bb x r) ^ 3 * (if theta < 3 * Bb x r then (1 : ℝ) else 0))) (P.prod P) := by
      have hsum : Integrable
          (fun x : Ω × Ω => ∑ r : Fin p,
            ((A x r) ^ 3 * (if theta < 3 * A x r then (1 : ℝ) else 0)
              + (Ab x r) ^ 3 * (if theta < 3 * Ab x r then (1 : ℝ) else 0)
              + (Bb x r) ^ 3 * (if theta < 3 * Bb x r then (1 : ℝ) else 0))) (P.prod P) :=
        MeasureTheory.integrable_finset_sum Finset.univ (fun r _ => hϕint' r)
      exact hsum.const_mul 81
    have hInonneg' : ∀ x : Ω × Ω, 0 ≤ (if Lam x then 0 else (maxPb x) ^ 3) := by
      intro x
      by_cases hL : Lam x
      · simp only [if_pos hL, le_refl]
      · rw [if_neg hL]; exact pow_nonneg (hmaxPb_nonneg x) 3
    have hfg' : ∀ᵐ x ∂(P.prod P),
        (if Lam x then 0 else (maxPb x) ^ 3)
          ≤ 81 * ∑ r : Fin p,
            ((A x r) ^ 3 * (if theta < 3 * A x r then (1 : ℝ) else 0)
              + (Ab x r) ^ 3 * (if theta < 3 * Ab x r then (1 : ℝ) else 0)
              + (Bb x r) ^ 3 * (if theta < 3 * Bb x r then (1 : ℝ) else 0)) := by
      apply Filter.Eventually.of_forall
      intro x
      by_cases hL : Lam x
      · rw [if_pos hL]
        apply mul_nonneg (by norm_num)
        apply Finset.sum_nonneg
        intro r _
        have i1 : (0 : ℝ) ≤ (if theta < 3 * A x r then (1 : ℝ) else 0) := by split_ifs <;> norm_num
        have i2 : (0 : ℝ) ≤ (if theta < 3 * Ab x r then (1 : ℝ) else 0) := by split_ifs <;> norm_num
        have i3 : (0 : ℝ) ≤ (if theta < 3 * Bb x r then (1 : ℝ) else 0) := by split_ifs <;> norm_num
        have e1 : (0 : ℝ) ≤ (A x r) ^ 3 := pow_nonneg (abs_nonneg (Y i x.1 r - muY r)) 3
        have e2 : (0 : ℝ) ≤ (Ab x r) ^ 3 := pow_nonneg (abs_nonneg (G i x.1 r - muY r)) 3
        have e3 : (0 : ℝ) ≤ (Bb x r) ^ 3 := pow_nonneg (abs_nonneg (G i x.2 r - muY r)) 3
        have m1 := mul_nonneg e1 i1
        have m2 := mul_nonneg e2 i2
        have m3 := mul_nonneg e3 i3
        linarith
      · rw [if_neg hL]
        exact h2 x hL
    have hIle' : ∫ x, (if Lam x then 0 else (maxPb x) ^ 3) ∂(P.prod P)
        ≤ ∫ x, (81 * ∑ r : Fin p,
            ((A x r) ^ 3 * (if theta < 3 * A x r then (1 : ℝ) else 0)
              + (Ab x r) ^ 3 * (if theta < 3 * Ab x r then (1 : ℝ) else 0)
              + (Bb x r) ^ 3 * (if theta < 3 * Bb x r then (1 : ℝ) else 0))) ∂(P.prod P) :=
      MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall hInonneg') hFint' hfg'
    have hsumval' : ∫ x : Ω × Ω, (∑ r : Fin p,
            ((A x r) ^ 3 * (if theta < 3 * A x r then (1 : ℝ) else 0)
              + (Ab x r) ^ 3 * (if theta < 3 * Ab x r then (1 : ℝ) else 0)
              + (Bb x r) ^ 3 * (if theta < 3 * Bb x r then (1 : ℝ) else 0))) ∂(P.prod P)
        = ∑ r : Fin p,
          ((∫ ω, |Y i ω r - muY r| ^ 3 * (if theta < 3 * |Y i ω r - muY r| then (1 : ℝ) else 0) ∂P)
            + 2 * (∫ ω, |G i ω r - muY r| ^ 3 * (if theta < 3 * |G i ω r - muY r| then (1 : ℝ) else 0) ∂P)) := by
      rw [MeasureTheory.integral_finset_sum Finset.univ (fun r _ => hϕint' r)]
      apply Finset.sum_congr rfl
      intro r _
      rw [hϕval' r]
      ring
    have hFeq' : ∫ x, (81 * ∑ r : Fin p,
            ((A x r) ^ 3 * (if theta < 3 * A x r then (1 : ℝ) else 0)
              + (Ab x r) ^ 3 * (if theta < 3 * Ab x r then (1 : ℝ) else 0)
              + (Bb x r) ^ 3 * (if theta < 3 * Bb x r then (1 : ℝ) else 0))) ∂(P.prod P)
        = 81 * ∑ r : Fin p,
          ((∫ ω, |Y i ω r - muY r| ^ 3 * (if theta < 3 * |Y i ω r - muY r| then (1 : ℝ) else 0) ∂P)
            + 2 * (∫ ω, |G i ω r - muY r| ^ 3 * (if theta < 3 * |G i ω r - muY r| then (1 : ℝ) else 0) ∂P)) := by
      rw [MeasureTheory.integral_const_mul, hsumval']
    rw [hFeq'] at hIle'
    exact hIle'
  exact ⟨h1, h2, h3, h4⟩
  /- @proof-region region.target-node.session.e3409c75933e4897 end -/

end

end Statlib.Imported

