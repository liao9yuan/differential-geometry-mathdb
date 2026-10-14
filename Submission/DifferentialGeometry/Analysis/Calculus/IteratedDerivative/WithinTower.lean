import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.Set
open scoped _root_.ContDiff

namespace DifferentialGeometry.Analysis

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]

theorem contDiffWithinAt_derivWithin_tower
    {f : ℕ → 𝕜 → V} {s : Set 𝕜} {x : 𝕜} (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s)
    (hzero : ContDiffWithinAt 𝕜 ∞ (f 0) s x)
    (hstep : ∀ q y, y ∈ s → f (q + 1) y = derivWithin (f q) s y)
    (q : ℕ) : ContDiffWithinAt 𝕜 ∞ (f q) s x := by
  induction q with
  | zero => exact hzero
  | succ q ih =>
    exact (ih.derivWithin hs (by simp) hx).congr_of_mem (hstep q) hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.contDiffWithinAt_derivWithin_tower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.contDiffWithinAt_derivWithin_tower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.contDiffWithinAt_derivWithin_tower ``Submission.DifferentialGeometry.Analysis.contDiffWithinAt_derivWithin_tower

theorem derivWithin_tower_eq {s : Set 𝕜} (f g : ℕ → 𝕜 → V)
    (hf : ∀ q x, x ∈ s → f (q + 1) x = derivWithin (f q) s x)
    (hg : ∀ q x, x ∈ s → g (q + 1) x = derivWithin (g q) s x)
    (hzero : _root_.Set.EqOn (f 0) (g 0) s) : ∀ q, _root_.Set.EqOn (f q) (g q) s := by
  intro q
  induction q with
  | zero => exact hzero
  | succ q ih =>
    intro x hx
    rw [hf q x hx, hg q x hx]
    exact derivWithin_congr ih (ih hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.derivWithin_tower_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.derivWithin_tower_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.derivWithin_tower_eq ``Submission.DifferentialGeometry.Analysis.derivWithin_tower_eq

theorem iteratedDerivWithin_eq_of_hasDerivWithinAt {s : Set 𝕜}
    (hs : UniqueDiffOn 𝕜 s) (f : 𝕜 → V) (g : ℕ → 𝕜 → V)
    (hg : ∀ q x, x ∈ s → HasDerivWithinAt (g q) (g (q + 1) x) s x)
    (hzero : _root_.Set.EqOn f (g 0) s) : ∀ q, _root_.Set.EqOn (iteratedDerivWithin q f s) (g q) s := by
  apply derivWithin_tower_eq (fun q => iteratedDerivWithin q f s) g
    (fun q x _ => congrFun (iteratedDerivWithin_succ (n := q)) x)
    (fun q x hx => ((hg q x hx).derivWithin (hs x hx)).symm)
  exact hzero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.iteratedDerivWithin_eq_of_hasDerivWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.iteratedDerivWithin_eq_of_hasDerivWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.iteratedDerivWithin_eq_of_hasDerivWithinAt ``Submission.DifferentialGeometry.Analysis.iteratedDerivWithin_eq_of_hasDerivWithinAt

end DifferentialGeometry.Analysis
