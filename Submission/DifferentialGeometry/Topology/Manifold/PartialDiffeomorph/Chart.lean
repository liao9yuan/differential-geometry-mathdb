import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.PartialDiffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable (I : ModelWithCorners 𝕜 E H) [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

noncomputable def extChartAt (n : WithTop ℕ∞) [IsManifold I n M] (x : M) :
    PartialDiffeomorph I 𝓘(𝕜, E) M E n where
  toPartialEquiv := _root_.extChartAt I x
  open_source := isOpen_extChartAt_source x
  open_target := isOpen_extChartAt_target x
  contMDiffOn_toFun := by
    simpa only [_root_.extChartAt_source] using
      (contMDiffOn_extChartAt (I := I) (n := n) (x := x))
  contMDiffOn_invFun := contMDiffOn_extChartAt_symm x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PartialDiffeomorph.extChartAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PartialDiffeomorph.extChartAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PartialDiffeomorph.extChartAt ``Submission.DifferentialGeometry.PartialDiffeomorph.extChartAt

@[simp]
theorem extChartAt_toPartialEquiv (n : WithTop ℕ∞) [IsManifold I n M] (x : M) :
    (extChartAt I n x).toPartialEquiv = _root_.extChartAt I x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PartialDiffeomorph.extChartAt_toPartialEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PartialDiffeomorph.extChartAt_toPartialEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PartialDiffeomorph.extChartAt_toPartialEquiv ``Submission.DifferentialGeometry.PartialDiffeomorph.extChartAt_toPartialEquiv

end DifferentialGeometry.PartialDiffeomorph
