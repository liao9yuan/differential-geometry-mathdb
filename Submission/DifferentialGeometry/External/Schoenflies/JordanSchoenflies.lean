/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
/-
Modified for this project; see MODIFICATIONS.md for the local changes.
-/
import Submission.DifferentialGeometry.External.Schoenflies.BoundaryAnchors

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# The Jordan–Schönflies theorem

The quantitative stage recursion supplies the interior homeomorphism.  Its fresh target nets
give a dense source anchor set; radial mesh spokes supply the boundary germs, and finite-stage
nonboundary edge paths supply matched crosscuts. These data prove `HasLimitHomeomorphism`, then
`SquareExtension`, and finally the relative Jordan–Schönflies theorem.

## Blueprint

The declarations below close `thm:square-extension` and `thm:main`; the intervening square
reduction, closed-interior, pointed, and exterior extensions are supplied by `Endgame.lean`.
-/

open _root_.Set

namespace Schoenflies

/-- All four inputs to boundary continuity are supplied by the prescribed quantitative stage
sequence. -/
theorem hasLimitHomeomorphism : HasLimitHomeomorphism := by
  intro C u v hC hu
  let T := prescribedJordanStageSequence hC u v hu
  exact ⟨prescribedSourceAnchorSet hC hu, T.limitTower.F, T.limitTower.inv,
    prescribedSourceAnchorSet_subset hC hu,
    prescribedSourceAnchorSet_dense hC hu,
    T.isHomeoOn_F,
    prescribedSourceAnchorSet_hasAnchorCrosscuts hC hu,
    prescribedSourceAnchorSet_hasSpokes hC hu⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.hasLimitHomeomorphism then
    throwError "Refusing to shadow existing declaration Schoenflies.hasLimitHomeomorphism"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.hasLimitHomeomorphism ``Submission.Schoenflies.hasLimitHomeomorphism

/-- **`thm:square-extension`.** Every homeomorphism from a Jordan curve to the boundary of the
model square extends over the corresponding closed domains. -/
theorem squareExtension : SquareExtension :=
  squareExtension_of_hasLimitHomeomorphism hasLimitHomeomorphism

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.squareExtension then
    throwError "Refusing to shadow existing declaration Schoenflies.squareExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.squareExtension ``Submission.Schoenflies.squareExtension

variable {C C' : Set Plane}

/-- **The relative Jordan–Schönflies theorem**, in the unbundled `IsHomeoOn` form. -/
theorem jordan_schoenflies {f g : Plane → Plane}
    (hC : IsJordanCurve C) (hC' : IsJordanCurve C') (hfg : IsHomeoOn f g C C') :
    ∃ F G : Plane → Plane, IsHomeoOn F G _root_.Set.univ _root_.Set.univ ∧ _root_.Set.EqOn F f C :=
  jordan_schoenflies_of_squareExtension squareExtension hC hC' hfg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.jordan_schoenflies then
    throwError "Refusing to shadow existing declaration Schoenflies.jordan_schoenflies"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.jordan_schoenflies ``Submission.Schoenflies.jordan_schoenflies

/-- **The relative Jordan–Schönflies theorem**, packaged as a plane
self-homeomorphism. -/
theorem jordan_schoenflies_homeomorph {f g : Plane → Plane}
    (hC : IsJordanCurve C) (hC' : IsJordanCurve C') (hfg : IsHomeoOn f g C C') :
    ∃ F : Plane ≃ₜ Plane, _root_.Set.EqOn F f C :=
  jordan_schoenflies_homeomorph_of_squareExtension squareExtension hC hC' hfg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.jordan_schoenflies_homeomorph then
    throwError "Refusing to shadow existing declaration Schoenflies.jordan_schoenflies_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.jordan_schoenflies_homeomorph ``Submission.Schoenflies.jordan_schoenflies_homeomorph

/-- **The blueprint's bundled statement.** Every homeomorphism between two
Jordan curves extends to a self-homeomorphism of the plane. -/
theorem jordan_schoenflies_of_homeomorph
    (hC : IsJordanCurve C) (hC' : IsJordanCurve C') (e : ↥C ≃ₜ ↥C') :
    ∃ F : Plane ≃ₜ Plane, ∀ z : ↥C, F z = e z :=
  jordan_schoenflies_of_homeomorph_of_squareExtension squareExtension hC hC' e

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.jordan_schoenflies_of_homeomorph then
    throwError "Refusing to shadow existing declaration Schoenflies.jordan_schoenflies_of_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.jordan_schoenflies_of_homeomorph ``Submission.Schoenflies.jordan_schoenflies_of_homeomorph

end Schoenflies
