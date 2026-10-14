import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.LocalDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open scoped _root_.Manifold _root_.ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

def extChartAtPartialDiffeomorph (n : ℕ∞ω) [IsManifold I n M] (x : M) :
    PartialDiffeomorph I 𝓘(𝕜, E) M E n where
  toFun := extChartAt I x
  invFun := (extChartAt I x).symm
  source := (extChartAt I x).source
  target := (extChartAt I x).target
  map_source' := fun {y} hy => (extChartAt I x).map_source hy
  map_target' := fun {y} hy => (extChartAt I x).map_target hy
  left_inv' := fun {y} hy => (extChartAt I x).left_inv hy
  right_inv' := fun {y} hy => (extChartAt I x).right_inv hy
  open_source := isOpen_extChartAt_source (I := I) x
  open_target := isOpen_extChartAt_target (I := I) x
  contMDiffOn_toFun := by
    simpa only [extChartAt_source] using contMDiffOn_extChartAt (I := I) (n := n) (x := x)
  contMDiffOn_invFun := contMDiffOn_extChartAt_symm (I := I) (n := n) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `extChartAtPartialDiffeomorph then
    throwError "Refusing to shadow existing declaration extChartAtPartialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `extChartAtPartialDiffeomorph ``Submission.extChartAtPartialDiffeomorph
