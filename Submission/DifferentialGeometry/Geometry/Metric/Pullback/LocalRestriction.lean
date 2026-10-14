import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Local
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Manifold _root_.Submission.Manifold _root_.TopologicalSpace
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry
variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

omit [FiniteDimensional ℝ F] in
theorem localPullMetric_restrictOpenOfSubset_eq
    (g : SmoothRiemannianMetric J N) {U V : _root_.TopologicalSpace.Opens M} (hUV : U ≤ V)
    (f : V → N) (hf : IsLocalDiffeomorph I J ∞ f)
    (fU : U → N) (hfU : IsLocalDiffeomorph I J ∞ fU)
    (heq : fU = f ∘ Opens.inclusion hUV) :
    (localPullMetric g f hf).restrictOpenOfSubset hUV = localPullMetric g fU hfU := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have hinc : IsLocalDiffeomorph I I ∞ (Opens.inclusion hUV) := fun y =>
    isLocalDiffeomorphAt_subtypeCodRestrict (fun z : U => hUV z.property)
      (isLocalDiffeomorph_subtype_val U y)
  have hd : mfderiv I J fU x = mfderiv I J f (Opens.inclusion hUV x) := by
    rw [heq, mfderiv_comp x (hf.contMDiff.mdifferentiableAt (by decide))
      (hinc.contMDiff.mdifferentiableAt (by decide)), mfderiv_opens_incl]
    exact ContinuousLinearMap.comp_id _
  change g.inner (f (Opens.inclusion hUV x))
    (mfderiv I J f (Opens.inclusion hUV x) v)
    (mfderiv I J f (Opens.inclusion hUV x) w) = _
  rw [localPullMetric_inner, hd, heq]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.localPullMetric_restrictOpenOfSubset_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.localPullMetric_restrictOpenOfSubset_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.localPullMetric_restrictOpenOfSubset_eq ``Submission.DifferentialGeometry.localPullMetric_restrictOpenOfSubset_eq

omit [FiniteDimensional ℝ F] in
theorem localPullMetric_restrictOpenOfSubset_eq_of_comp_eq
    (g : SmoothRiemannianMetric J N) {U V W : _root_.TopologicalSpace.Opens M} (hWU : W ≤ U) (hWV : W ≤ V)
    (f : U → N) (hf : IsLocalDiffeomorph I J ∞ f)
    (f' : V → N) (hf' : IsLocalDiffeomorph I J ∞ f')
    (heq : f ∘ Opens.inclusion hWU = f' ∘ Opens.inclusion hWV) :
    (localPullMetric g f hf).restrictOpenOfSubset hWU =
      (localPullMetric g f' hf').restrictOpenOfSubset hWV := by
  have hincU : IsLocalDiffeomorph I I ∞ (Opens.inclusion hWU) := fun y =>
    isLocalDiffeomorphAt_subtypeCodRestrict (fun z : W => hWU z.property)
      (isLocalDiffeomorph_subtype_val W y)
  have hincV : IsLocalDiffeomorph I I ∞ (Opens.inclusion hWV) := fun y =>
    isLocalDiffeomorphAt_subtypeCodRestrict (fun z : W => hWV z.property)
      (isLocalDiffeomorph_subtype_val W y)
  rw [localPullMetric_restrictOpenOfSubset_eq g hWU f hf _
    (isLocalDiffeomorph_comp hf hincU) rfl,
    localPullMetric_restrictOpenOfSubset_eq g hWV f' hf' _
    (isLocalDiffeomorph_comp hf' hincV) rfl]
  congr 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.localPullMetric_restrictOpenOfSubset_eq_of_comp_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.localPullMetric_restrictOpenOfSubset_eq_of_comp_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.localPullMetric_restrictOpenOfSubset_eq_of_comp_eq ``Submission.DifferentialGeometry.localPullMetric_restrictOpenOfSubset_eq_of_comp_eq

end DifferentialGeometry
