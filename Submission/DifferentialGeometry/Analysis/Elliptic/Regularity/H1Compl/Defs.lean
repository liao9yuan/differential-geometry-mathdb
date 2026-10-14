import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothScalar.PreH1
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.InnerProductSpace.Completion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

abbrev H1Compl (g : SmoothRiemannianMetric I M) : Type _ :=
  UniformSpace.Completion (SmoothScalar g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1Compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1Compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1Compl ``Submission.DifferentialGeometry.Analysis.Laplacian.H1Compl

noncomputable def smoothToH1Compl (g : SmoothRiemannianMetric I M) :
    SmoothScalar g →L[ℝ] H1Compl g :=
  UniformSpace.Completion.toComplL

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.smoothToH1Compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.smoothToH1Compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.smoothToH1Compl ``Submission.DifferentialGeometry.Analysis.Laplacian.smoothToH1Compl

@[simp] lemma smoothToH1Compl_apply (g : SmoothRiemannianMetric I M)
    (f : SmoothScalar g) :
    smoothToH1Compl (I := I) (M := M) g f = (f : H1Compl g) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.smoothToH1Compl_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.smoothToH1Compl_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.smoothToH1Compl_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.smoothToH1Compl_apply

end Laplacian
end Analysis
end DifferentialGeometry

end
