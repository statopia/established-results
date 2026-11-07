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
theorem statopia_math_node_957869045_16437b4b : ∀ (p : ℕ) (hp : 2 ≤ p) (phi : ℝ)
    (hphi : 1 ≤ phi) (phi0 : ℝ → ℝ) (hphi0 : ContDiff ℝ 3 phi0) (y : Fin p → ℝ)
    (w : Fin p → ℝ) (j : Fin p),
    HasDerivAt
      (fun t : ℝ =>
        phi0 (phi * ((phi * Real.log (p : ℝ))⁻¹ *
          Real.log (∑ k : Fin p,
            Real.exp ((phi * Real.log (p : ℝ)) *
              ((w + t • (Pi.single j (1 : ℝ) : Fin p → ℝ)) k - y k))))))
      (deriv phi0 (phi * ((phi * Real.log (p : ℝ))⁻¹ *
          Real.log (∑ k : Fin p,
            Real.exp ((phi * Real.log (p : ℝ)) * (w k - y k))))) *
        (phi * (Real.exp ((phi * Real.log (p : ℝ)) * (w j - y j)) /
          (∑ k : Fin p, Real.exp ((phi * Real.log (p : ℝ)) * (w k - y k))))))
      0 := by
  /- @proof-region region.target-node.session.a2df34ac31e13b6d begin -/
  intro p hp phi hphi phi0 hphi0 y w j
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hphi_pos : 0 < phi := lt_of_lt_of_le zero_lt_one hphi
  set beta : ℝ := phi * Real.log (p : ℝ) with hbeta
  have hbeta_ne : beta ≠ 0 := by
    rw [hbeta]
    exact ne_of_gt (mul_pos hphi_pos (Real.log_pos hp1))
  set e : Fin p → ℝ := Pi.single j (1 : ℝ) with he
  have hpt : ∀ (k : Fin p) (t : ℝ), (w + t • e) k = w k + t * e k := by
    intro k t
    simp
  have hej : e j = 1 := by
    rw [he]
    simp
  have hek : ∀ k : Fin p, k ≠ j → e k = 0 := by
    intro k hk
    rw [he]
    simp [hk]
  have hsingle : Real.exp (beta * (w j - y j)) ≤ ∑ k : Fin p, Real.exp (beta * (w k - y k)) :=
    Finset.single_le_sum (fun i _ => (Real.exp_pos (beta * (w i - y i))).le) (Finset.mem_univ j)
  have hSw_pos : 0 < ∑ k : Fin p, Real.exp (beta * (w k - y k)) :=
    lt_of_lt_of_le (Real.exp_pos (beta * (w j - y j))) hsingle
  have hSw_ne : (∑ k : Fin p, Real.exp (beta * (w k - y k))) ≠ 0 := ne_of_gt hSw_pos
  have hterm : ∀ k : Fin p,
      HasDerivAt (fun t : ℝ => Real.exp (beta * ((w + t • e) k - y k)))
        (Real.exp (beta * (w k - y k)) * (beta * e k)) 0 := by
    intro k
    have h1 : HasDerivAt (fun t : ℝ => t * e k) (e k) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const (e k)
    have h2 : HasDerivAt (fun t : ℝ => w k + t * e k) (e k) 0 := by
      simpa using h1.const_add (w k)
    have h3 : HasDerivAt (fun t : ℝ => w k + t * e k - y k) (e k) 0 := by
      simpa using h2.sub_const (y k)
    have h4 : HasDerivAt (fun t : ℝ => beta * (w k + t * e k - y k)) (beta * e k) 0 := by
      simpa using h3.const_mul beta
    simpa [hpt k] using h4.exp
  have hSsum := HasDerivAt.sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin p))) => hterm k)
  have hfun : (∑ k : Fin p, fun t : ℝ => Real.exp (beta * ((w + t • e) k - y k)))
      = fun t : ℝ => ∑ k : Fin p, Real.exp (beta * ((w + t • e) k - y k)) := by
    ext t
    simp [Finset.sum_apply]
  have hS : HasDerivAt (fun t : ℝ => ∑ k : Fin p, Real.exp (beta * ((w + t • e) k - y k)))
      (∑ k : Fin p, Real.exp (beta * (w k - y k)) * (beta * e k)) 0 := by
    rw [hfun] at hSsum
    exact hSsum
  have hsum_eq : (∑ k : Fin p, Real.exp (beta * (w k - y k)) * (beta * e k))
      = Real.exp (beta * (w j - y j)) * beta := by
    have h0 : ∀ b ∈ (Finset.univ : Finset (Fin p)), b ≠ j →
        Real.exp (beta * (w b - y b)) * (beta * e b) = 0 := by
      intro b _ hb
      simp [hek b hb]
    have h1 : j ∉ (Finset.univ : Finset (Fin p)) →
        Real.exp (beta * (w j - y j)) * (beta * e j) = 0 := by
      intro hj
      exact absurd (Finset.mem_univ j) hj
    rw [Finset.sum_eq_single j h0 h1, hej, mul_one]
  have hS0 : (∑ k : Fin p, Real.exp (beta * ((w + (0 : ℝ) • e) k - y k)))
      = ∑ k : Fin p, Real.exp (beta * (w k - y k)) := by
    simp
  have hS' : HasDerivAt (fun t : ℝ => ∑ k : Fin p, Real.exp (beta * ((w + t • e) k - y k)))
      (Real.exp (beta * (w j - y j)) * beta) 0 := hsum_eq ▸ hS
  have hlog := hS'.log (by rw [hS0]; exact hSw_ne)
  have hT : HasDerivAt
      (fun t : ℝ => Real.log (∑ k : Fin p, Real.exp (beta * ((w + t • e) k - y k))))
      ((Real.exp (beta * (w j - y j)) * beta) / (∑ k : Fin p, Real.exp (beta * (w k - y k)))) 0 := by
    simpa [hS0] using hlog
  have hU : HasDerivAt
      (fun t : ℝ => phi * (beta⁻¹ * Real.log (∑ k : Fin p, Real.exp (beta * ((w + t • e) k - y k)))))
      (phi * (beta⁻¹ * ((Real.exp (beta * (w j - y j)) * beta) /
        (∑ k : Fin p, Real.exp (beta * (w k - y k)))))) 0 := by
    have hc1 : HasDerivAt
        (fun t : ℝ => beta⁻¹ * Real.log (∑ k : Fin p, Real.exp (beta * ((w + t • e) k - y k))))
        (beta⁻¹ * ((Real.exp (beta * (w j - y j)) * beta) /
          (∑ k : Fin p, Real.exp (beta * (w k - y k))))) 0 :=
      hT.const_mul beta⁻¹
    simpa using hc1.const_mul phi
  have hinner : beta⁻¹ * ((Real.exp (beta * (w j - y j)) * beta) /
        (∑ k : Fin p, Real.exp (beta * (w k - y k))))
      = Real.exp (beta * (w j - y j)) / (∑ k : Fin p, Real.exp (beta * (w k - y k))) := by
    have hnum : beta⁻¹ * (Real.exp (beta * (w j - y j)) * beta)
        = Real.exp (beta * (w j - y j)) := by
      rw [mul_comm (Real.exp (beta * (w j - y j))) beta, ← mul_assoc,
        inv_mul_cancel₀ hbeta_ne, one_mul]
    rw [← mul_div_assoc, hnum]
  have hy : phi * (beta⁻¹ * Real.log (∑ k : Fin p, Real.exp (beta * (w k - y k))))
      = (fun t : ℝ => phi * (beta⁻¹ *
          Real.log (∑ k : Fin p, Real.exp (beta * ((w + t • e) k - y k))))) 0 := by
    simp [hS0]
  have hphi0_at : HasDerivAt phi0
      (deriv phi0 (phi * (beta⁻¹ * Real.log (∑ k : Fin p, Real.exp (beta * (w k - y k))))))
      (phi * (beta⁻¹ * Real.log (∑ k : Fin p, Real.exp (beta * (w k - y k))))) :=
    (hphi0.contDiffAt.differentiableAt (by decide)).hasDerivAt
  have hcomp := HasDerivAt.comp_of_eq 0 hphi0_at hU hy
  simpa [hinner] using hcomp
  /- @proof-region region.target-node.session.a2df34ac31e13b6d end -/

end

end Statlib.Imported

