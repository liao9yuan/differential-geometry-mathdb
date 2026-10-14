import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.ChainRule.Defs
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.Multiply
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Closedness
import Submission.DifferentialGeometry.External.DeGiorgi.BallExtension.RoughInput
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.MeasureTheory.Function.Jacobian

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology
open scoped _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

namespace SmoothDiffeoBounded

def derivBoundMaxOne {Ω Ω' : Set E} (Φ : SmoothDiffeoBounded d Ω Ω') : ℝ :=
  _root_.Max.max Φ.derivBound 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.SmoothDiffeoBounded.derivBoundMaxOne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.SmoothDiffeoBounded.derivBoundMaxOne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.SmoothDiffeoBounded.derivBoundMaxOne ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.SmoothDiffeoBounded.derivBoundMaxOne

lemma derivBoundMaxOne_pos {Ω Ω' : Set E} (Φ : SmoothDiffeoBounded d Ω Ω') :
    0 < Φ.derivBoundMaxOne := by
  unfold derivBoundMaxOne
  have h1 : (0 : ℝ) < 1 := by norm_num
  exact lt_of_lt_of_le h1 (le_max_right _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.SmoothDiffeoBounded.derivBoundMaxOne_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.SmoothDiffeoBounded.derivBoundMaxOne_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.SmoothDiffeoBounded.derivBoundMaxOne_pos ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.SmoothDiffeoBounded.derivBoundMaxOne_pos

lemma derivBoundMaxOne_ge_one {Ω Ω' : Set E}
    (Φ : SmoothDiffeoBounded d Ω Ω') :
    1 ≤ Φ.derivBoundMaxOne :=
  le_max_right _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.SmoothDiffeoBounded.derivBoundMaxOne_ge_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.SmoothDiffeoBounded.derivBoundMaxOne_ge_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.SmoothDiffeoBounded.derivBoundMaxOne_ge_one ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.SmoothDiffeoBounded.derivBoundMaxOne_ge_one

lemma deriv_bound_le_derivBoundMaxOne {Ω Ω' : Set E}
    (Φ : SmoothDiffeoBounded d Ω Ω') :
    Φ.derivBound ≤ Φ.derivBoundMaxOne :=
  le_max_left _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.SmoothDiffeoBounded.deriv_bound_le_derivBoundMaxOne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.SmoothDiffeoBounded.deriv_bound_le_derivBoundMaxOne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.SmoothDiffeoBounded.deriv_bound_le_derivBoundMaxOne ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.SmoothDiffeoBounded.deriv_bound_le_derivBoundMaxOne

lemma norm_iteratedFDeriv_comp_toFun_le
    {Ω Ω' : Set E} (Φ : SmoothDiffeoBounded d Ω Ω')
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (n : ℕ) (x : E) {C : ℝ}
    (hC : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i u (Φ.toFun x)‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (fun y => u (Φ.toFun y)) x‖ ≤
      n.factorial * C * Φ.derivBoundMaxOne ^ n := by
  classical
  set D := Φ.derivBoundMaxOne with hD_def
  have hD_ge_1 : 1 ≤ D := Φ.derivBoundMaxOne_ge_one
  have hD_pos : 0 < D := Φ.derivBoundMaxOne_pos
  have hΦ_smooth_top : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ.toFun := by
    simpa using Φ.toFun_smooth
  have hu_smooth_top : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u := by
    simpa using hu
  have hn_le : (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    have h1 : (n : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
    exact_mod_cast h1
  have hfun_eq : (fun y => u (Φ.toFun y)) = (u ∘ Φ.toFun) := rfl
  rw [hfun_eq]
  have hΦ_iter : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv ℝ i Φ.toFun x‖ ≤ D ^ i := by
    intro i hi1 _hin
    have hbound := Φ.iter_deriv_bounded i x
    have hbnd' : ‖iteratedFDeriv ℝ i Φ.toFun x‖ ≤ D :=
      hbound.trans Φ.deriv_bound_le_derivBoundMaxOne
    rcases i with _ | i
    · exact (Nat.lt_irrefl 0 hi1).elim
    · have h_pow_mono : D ≤ D ^ (i + 1) := by
        have hpw : 1 ≤ D ^ i := one_le_pow₀ hD_ge_1
        calc D = D * 1 := by ring
          _ ≤ D * D ^ i := mul_le_mul_of_nonneg_left hpw (by linarith)
          _ = D ^ (i + 1) := by ring
      exact hbnd'.trans h_pow_mono
  exact norm_iteratedFDeriv_comp_le (𝕜 := ℝ)
    (g := u) (f := Φ.toFun) (n := n) (N := ((⊤ : ℕ∞) : WithTop ℕ∞))
    (x := x) hu_smooth_top hΦ_smooth_top hn_le
    (C := C) (D := D) (fun i hi => hC i hi) hΦ_iter

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.SmoothDiffeoBounded.norm_iteratedFDeriv_comp_toFun_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.SmoothDiffeoBounded.norm_iteratedFDeriv_comp_toFun_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.SmoothDiffeoBounded.norm_iteratedFDeriv_comp_toFun_le ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.SmoothDiffeoBounded.norm_iteratedFDeriv_comp_toFun_le

lemma comp_toFun_contDiff
    {Ω Ω' : Set E} (Φ : SmoothDiffeoBounded d Ω Ω')
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => u (Φ.toFun x)) :=
  hu.comp Φ.toFun_smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.SmoothDiffeoBounded.comp_toFun_contDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.SmoothDiffeoBounded.comp_toFun_contDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.SmoothDiffeoBounded.comp_toFun_contDiff ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.SmoothDiffeoBounded.comp_toFun_contDiff

end SmoothDiffeoBounded

end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry
