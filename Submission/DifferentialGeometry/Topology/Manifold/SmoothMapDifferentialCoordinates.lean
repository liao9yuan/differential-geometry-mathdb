import Submission.DifferentialGeometry.Topology.Manifold.SmoothOrientation
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Filter _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.Manifold
variable {E H M F K N : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable [TopologicalSpace M] [ChartedSpace H M]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable [TopologicalSpace K] (J : ModelWithCorners ℝ F K)
variable [TopologicalSpace N] [ChartedSpace K N]

def differentialEquivOfBijective (f : M → N)
    (hf : ∀ x : M, _root_.Function.Bijective (mfderiv I J f x)) (x : M) : E ≃L[ℝ] F := by
  let D : E →L[ℝ] F := mfderiv I J f x
  exact (LinearEquiv.ofBijective D.toLinearMap (hf x)).toContinuousLinearEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.differentialEquivOfBijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.differentialEquivOfBijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.differentialEquivOfBijective ``Submission.DifferentialGeometry.Topology.Manifold.differentialEquivOfBijective

omit [FiniteDimensional ℝ F] in
theorem differentialEquivOfBijective_apply (f : M → N)
    (hf : ∀ x : M, _root_.Function.Bijective (mfderiv I J f x)) (x : M) (v : E) :
    differentialEquivOfBijective I J f hf x v = mfderiv I J f x v := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.differentialEquivOfBijective_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.differentialEquivOfBijective_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.differentialEquivOfBijective_apply ``Submission.DifferentialGeometry.Topology.Manifold.differentialEquivOfBijective_apply

variable [IsManifold I ∞ M] [IsManifold J ∞ N]

theorem preferredChartTangentEquiv_symm_apply (p x : M)
    (hx : x ∈ (chartAt H p).source) (v : E) :
    (preferredChartTangentEquiv I p x hx).symm v =
      mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (_root_.Set.range I) (extChartAt I p x) v := by
  apply (preferredChartTangentEquiv I p x hx).injective
  have h := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' (I := I)
    (by simpa only [extChartAt_source] using hx)
  have hv : preferredChartTangentEquiv I p x hx
      (mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (_root_.Set.range I) (extChartAt I p x) v) = v :=
    congrArg (fun A : E →L[ℝ] E => A v) h
  exact ((preferredChartTangentEquiv I p x hx).apply_symm_apply v).trans hv.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.preferredChartTangentEquiv_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.preferredChartTangentEquiv_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.preferredChartTangentEquiv_symm_apply ``Submission.DifferentialGeometry.Topology.Manifold.preferredChartTangentEquiv_symm_apply

def coordinateDifferentialEquiv (f : M → N)
    (hf : ∀ x : M, _root_.Function.Bijective (mfderiv I J f x)) (p : M)
    (x : ↥((chartAt H p).source ∩ f ⁻¹' (chartAt K (f p)).source)) : E ≃L[ℝ] F :=
  ((preferredChartTangentEquiv I p x.val x.property.1).symm.trans
    (differentialEquivOfBijective I J f hf x.val)).trans
    (preferredChartTangentEquiv J (f p) (f x.val) x.property.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.coordinateDifferentialEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.coordinateDifferentialEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.coordinateDifferentialEquiv ``Submission.DifferentialGeometry.Topology.Manifold.coordinateDifferentialEquiv

theorem coordinateDifferentialEquiv_eq (f : M → N)
    (hf : ∀ x : M, _root_.Function.Bijective (mfderiv I J f x)) (p : M)
    (x : ↥((chartAt H p).source ∩ f ⁻¹' (chartAt K (f p)).source)) :
    (coordinateDifferentialEquiv I J f hf p x : E →L[ℝ] F) =
      inTangentCoordinates I J id f (mfderiv I J f) p x.val := by
  rw [inTangentCoordinates_eq_mfderiv_comp x.property.1 x.property.2]
  apply ContinuousLinearMap.ext
  intro v
  change preferredChartTangentEquiv J (f p) (f x.val) x.property.2
    (differentialEquivOfBijective I J f hf x.val
      ((preferredChartTangentEquiv I p x.val x.property.1).symm v)) = _
  rw [preferredChartTangentEquiv_apply, differentialEquivOfBijective_apply,
    preferredChartTangentEquiv_symm_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.coordinateDifferentialEquiv_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.coordinateDifferentialEquiv_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.coordinateDifferentialEquiv_eq ``Submission.DifferentialGeometry.Topology.Manifold.coordinateDifferentialEquiv_eq

theorem continuousAt_coordinateDifferentialEquiv (f : M → N)
    (hf : ContMDiff I J ∞ f) (hbij : ∀ x : M, _root_.Function.Bijective (mfderiv I J f x)) (p : M) :
    ContinuousAt (fun x : ↥((chartAt H p).source ∩ f ⁻¹' (chartAt K (f p)).source) =>
      (coordinateDifferentialEquiv I J f hbij p x : E →L[ℝ] F))
        ⟨p, mem_chart_source H p, mem_chart_source K (f p)⟩ := by
  have h : ContinuousAt (inTangentCoordinates I J id f (mfderiv I J f) p) p :=
    (hf.contMDiffAt.mfderiv_const (m := 0) (by simp)).continuousAt
  have h' := h.comp (continuous_subtype_val.continuousAt (x :=
    (⟨p, mem_chart_source H p, mem_chart_source K (f p)⟩ :
      ↥((chartAt H p).source ∩ f ⁻¹' (chartAt K (f p)).source))))
  have he : (fun x : ↥((chartAt H p).source ∩ f ⁻¹' (chartAt K (f p)).source) =>
      (coordinateDifferentialEquiv I J f hbij p x : E →L[ℝ] F)) =
      (fun x => inTangentCoordinates I J id f (mfderiv I J f) p x.val) := by
    funext x
    exact coordinateDifferentialEquiv_eq I J f hbij p x
  rw [he]
  exact h'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.continuousAt_coordinateDifferentialEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.continuousAt_coordinateDifferentialEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.continuousAt_coordinateDifferentialEquiv ``Submission.DifferentialGeometry.Topology.Manifold.continuousAt_coordinateDifferentialEquiv
end DifferentialGeometry.Topology.Manifold
