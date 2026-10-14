import Submission.DifferentialGeometry.Tensor.Exterior.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.ContinuousAlternatingMap _root_.Submission.ContinuousAlternatingMap _root_.Bundle.ContinuousAlternatingMap _root_.Function _root_.Filter
open scoped _root_.Topology _root_.Manifold _root_.ContDiff _root_.Bundle _root_.Submission.Bundle

namespace DifferentialGeometry
namespace DifferentialForm

attribute [local instance] seminormedAddCommGroupTangentSpace
attribute [local instance] normedAddCommGroupTangentSpace
attribute [local instance] normedSpaceTangentSpace

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ∞ M]
  {k : ℕ}

def isClosed [BoundarylessManifold IM M] (α : DifferentialForm IM M k) : Prop :=
  exteriorDerivative α = 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.isClosed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.isClosed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.isClosed ``Submission.DifferentialGeometry.DifferentialForm.isClosed

def isExact [BoundarylessManifold IM M] (α : DifferentialForm IM M (k + 1)) : Prop :=
  ∃ β : DifferentialForm IM M k, exteriorDerivative β = α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.isExact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.isExact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.isExact ``Submission.DifferentialGeometry.DifferentialForm.isExact

theorem exact_closed [BoundarylessManifold IM M] {α : DifferentialForm IM M (k + 1)}
    (h : isExact α) : isClosed α := by
  rcases h with ⟨β, hβ⟩
  rw [isClosed, ← hβ]
  exact exteriorDerivative_sq β

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.exact_closed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.exact_closed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.exact_closed ``Submission.DifferentialGeometry.DifferentialForm.exact_closed

theorem isClosed_iff_mem_ker [BoundarylessManifold IM M] (α : DifferentialForm IM M k) :
    isClosed α ↔ α ∈ LinearMap.ker (exteriorDerivativeLinearMap (IM := IM) (M := M) k) := by
  simp [isClosed, exteriorDerivativeLinearMap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.isClosed_iff_mem_ker then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.isClosed_iff_mem_ker"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.isClosed_iff_mem_ker ``Submission.DifferentialGeometry.DifferentialForm.isClosed_iff_mem_ker

theorem isExact_iff_mem_range [BoundarylessManifold IM M] (α : DifferentialForm IM M (k + 1)) :
    isExact α ↔ α ∈ LinearMap.range (exteriorDerivativeLinearMap (IM := IM) (M := M) k) := by
  simp [isExact, exteriorDerivativeLinearMap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.isExact_iff_mem_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.isExact_iff_mem_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.isExact_iff_mem_range ``Submission.DifferentialGeometry.DifferentialForm.isExact_iff_mem_range

end DifferentialForm
end DifferentialGeometry

end
