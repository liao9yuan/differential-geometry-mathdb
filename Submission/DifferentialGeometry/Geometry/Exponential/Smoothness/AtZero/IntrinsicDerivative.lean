import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.NormDiamond
import Submission.DifferentialGeometry.Geometry.Exponential.Smoothness.AtZero.Derivative
import Submission.DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Set _root_.Function _root_.Filter _root_.Metric _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Real _root_.Submission.Real
open scoped _root_.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

omit [ConnectedSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem mfderiv_expMapIntrinsic_at_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M] [CompleteSpace E]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    mfderiv 𝓘(ℝ, E) I
      (fun v : E => (expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from v) : M))
      (0 : E) =
      ContinuousLinearMap.id ℝ E := by
  classical
  obtain ⟨ρ, hρ_pos, hagree⟩ :=
    exists_expMapIntrinsic_eq_expMap_radius (I := I) g hEnorm p
  have hcont : Continuous (fun v : E => Real.sqrt (g.inner p (show TangentSpace I p from v)
      (show TangentSpace I p from v))) :=
    continuous_sqrt_gInner_self (I := I) g p
  set S : Set E :=
    {v : E | Real.sqrt (g.inner p (show TangentSpace I p from v)
      (show TangentSpace I p from v)) < ρ} with hS_def
  have hS_open : IsOpen S := hcont.isOpen_preimage (Set.Iio ρ) isOpen_Iio
  have hzero_mem : (0 : E) ∈ S := by
    have h0 : Real.sqrt (g.inner p (show TangentSpace I p from (0 : E))
        (show TangentSpace I p from (0 : E))) = 0 := by
      have hgz : g.inner p (show TangentSpace I p from (0 : E))
          (show TangentSpace I p from (0 : E)) = 0 := by
        change g.inner p (0 : TangentSpace I p) (0 : TangentSpace I p) = 0
        simp
      rw [hgz, Real.sqrt_zero]
    change Real.sqrt (g.inner p (show TangentSpace I p from (0 : E))
      (show TangentSpace I p from (0 : E))) < ρ
    rw [h0]; exact hρ_pos
  have hEvEq :
      (fun v : E => (expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from v) : M))
        =ᶠ[𝓝 (0 : E)]
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M)) := by
    refine Filter.eventuallyEq_of_mem (hS_open.mem_nhds hzero_mem) ?_
    intro v hv
    exact hagree hv
  rw [hEvEq.mfderiv_eq]
  exact mfderiv_expMap_at_zero (I := I) g p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.mfderiv_expMapIntrinsic_at_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.mfderiv_expMapIntrinsic_at_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.mfderiv_expMapIntrinsic_at_zero ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.mfderiv_expMapIntrinsic_at_zero

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
