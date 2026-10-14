import Submission.DifferentialGeometry.Topology.Manifold.OpenSubtype

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.TopologicalSpace _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.Manifold
variable {E F H H' M N : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [TopologicalSpace H] [TopologicalSpace H']
variable (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F H')
variable [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]

theorem mfderiv_comp_open_val (U : _root_.TopologicalSpace.Opens N) (f : M → U)
    (hf : ContMDiff I J ∞ f) (x : M) :
    mfderiv I J (Subtype.val ∘ f) x = mfderiv I J f x := by
  have h := mfderiv_comp x
    ((contMDiff_subtype_val (I := J) (U := U) (n := ∞)).mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp))
  rw [DifferentialGeometry.mfderiv_subtype_val] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.mfderiv_comp_open_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.mfderiv_comp_open_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.mfderiv_comp_open_val ``Submission.DifferentialGeometry.Topology.Manifold.mfderiv_comp_open_val

theorem mfderiv_restrict_open (U : _root_.TopologicalSpace.Opens M) (f : M → N)
    (hf : ContMDiff I J ∞ f) (x : U) :
    mfderiv I J (f ∘ (Subtype.val : U → M)) x = mfderiv I J f x.val := by
  have h := mfderiv_comp x (hf.mdifferentiableAt (by simp))
    ((contMDiff_subtype_val (I := I) (U := U) (n := ∞)).mdifferentiableAt (by simp))
  rw [DifferentialGeometry.mfderiv_subtype_val] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.mfderiv_restrict_open then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.mfderiv_restrict_open"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.mfderiv_restrict_open ``Submission.DifferentialGeometry.Topology.Manifold.mfderiv_restrict_open
end DifferentialGeometry.Topology.Manifold
