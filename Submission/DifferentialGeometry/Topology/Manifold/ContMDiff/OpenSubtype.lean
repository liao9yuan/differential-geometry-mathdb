import Mathlib.Geometry.Manifold.ContMDiff.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Function _root_.Manifold _root_.TopologicalSpace
open scoped _root_.ContDiff
set_option autoImplicit false
namespace DifferentialGeometry.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {F G N : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace G] [TopologicalSpace N] [ChartedSpace G N]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G} {n : ℕ∞ω}


theorem contMDiffWithinAt_subtypeVal_comp_iff (U : _root_.TopologicalSpace.Opens N) (f : M → U) (s : Set M) (x : M) :
    ContMDiffWithinAt I J n (Subtype.val ∘ f) s x ↔ ContMDiffWithinAt I J n f s x :=
  ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.contMDiffWithinAt_subtypeVal_comp_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.contMDiffWithinAt_subtypeVal_comp_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.contMDiffWithinAt_subtypeVal_comp_iff ``Submission.DifferentialGeometry.Manifold.contMDiffWithinAt_subtypeVal_comp_iff


theorem contMDiffAt_subtypeVal_comp_iff (U : _root_.TopologicalSpace.Opens N) (f : M → U) (x : M) :
    ContMDiffAt I J n (Subtype.val ∘ f) x ↔ ContMDiffAt I J n f x :=
  contMDiffWithinAt_subtypeVal_comp_iff U f _root_.Set.univ x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.contMDiffAt_subtypeVal_comp_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.contMDiffAt_subtypeVal_comp_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.contMDiffAt_subtypeVal_comp_iff ``Submission.DifferentialGeometry.Manifold.contMDiffAt_subtypeVal_comp_iff


theorem contMDiffOn_subtypeVal_comp_iff (U : _root_.TopologicalSpace.Opens N) (f : M → U) (s : Set M) :
    ContMDiffOn I J n (Subtype.val ∘ f) s ↔ ContMDiffOn I J n f s := by
  simp only [ContMDiffOn, contMDiffWithinAt_subtypeVal_comp_iff]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.contMDiffOn_subtypeVal_comp_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.contMDiffOn_subtypeVal_comp_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.contMDiffOn_subtypeVal_comp_iff ``Submission.DifferentialGeometry.Manifold.contMDiffOn_subtypeVal_comp_iff


theorem contMDiff_subtypeVal_comp_iff (U : _root_.TopologicalSpace.Opens N) (f : M → U) :
    ContMDiff I J n (Subtype.val ∘ f) ↔ ContMDiff I J n f := by
  simp only [ContMDiff, contMDiffAt_subtypeVal_comp_iff]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.contMDiff_subtypeVal_comp_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.contMDiff_subtypeVal_comp_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.contMDiff_subtypeVal_comp_iff ``Submission.DifferentialGeometry.Manifold.contMDiff_subtypeVal_comp_iff

end DifferentialGeometry.Manifold
