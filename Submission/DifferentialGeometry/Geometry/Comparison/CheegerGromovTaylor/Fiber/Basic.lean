import Submission.DifferentialGeometry.Geometry.Exponential.NormalCoordinates.Fiber
import Submission.DifferentialGeometry.Geometry.Exponential.Intrinsic.Framed.Coordinates
import Submission.DifferentialGeometry.Geometry.Exponential.Intrinsic.Agreement
import Submission.DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Function _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold _root_.Submission.Manifold _root_.Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CheegerGromovTaylor

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential _root_.Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

def intrinsicFiber
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p q : M) (r : Real) : Set E :=
  {u | u ∈ Metric.ball (0 : E) r ∧
    intrinsicFramedExp (I := I) g hEnorm p u = q}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicFiber then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicFiber"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicFiber ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicFiber

theorem exists_fiber_inj
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    {p q : M} {R r₀ s : Real}
    (hqs :
      _root_.Manifold.riemannianEDist I p q < ENNReal.ofReal s)
    (hfit : r₀ + s < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R)) :
    ∃ f :
        intrinsicFiber (I := I) g hEnorm p p r₀ →
          intrinsicFiber (I := I) g hEnorm p q (r₀ + s),
      Function.Injective f := by
  have hagree : framedExpMap (I := I) g p =
      intrinsicFramedExp (I := I) g hEnorm p := by
    funext z
    rw [framedExpMap_apply, intrinsicFrame_apply, expMap_eq_expMapIntrinsic g hEnorm p]
  have hdom : ∀ z ∈ Metric.ball (0 : E) R,
      normalFrame (I := I) g p z ∈ expDomain (I := I) g p := by
    intro z _
    rw [expDomain_eq_univ_of_completeSpace g hEnorm p]
    exact _root_.Set.mem_univ _
  have hloc' : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R) := by
    rw [hagree]
    exact hloc
  have hd : riemannianEDistOf g p q < ENNReal.ofReal s := by
    rw [riemannianEDistOf_eq_riemannianEDist g hEnorm]
    exact hqs
  obtain ⟨f⟩ := nonempty_embedding_fiber_framedExpMap g hd hfit hdom hloc'
  unfold intrinsicFiber
  rw [← hagree]
  exact ⟨f, f.injective⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.exists_fiber_inj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.exists_fiber_inj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.exists_fiber_inj ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.exists_fiber_inj

theorem fiber_encard_le
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    {p q : M} {R r₀ s : Real}
    (hqs :
      _root_.Manifold.riemannianEDist I p q < ENNReal.ofReal s)
    (hfit : r₀ + s < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R)) :
    (intrinsicFiber (I := I) g hEnorm p p r₀).encard ≤
      (intrinsicFiber (I := I) g hEnorm p q (r₀ + s)).encard := by
  obtain ⟨f, hf⟩ :=
    exists_fiber_inj (I := I) g hEnorm hqs hfit hloc
  exact (Function.Embedding.mk f hf).encard_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.fiber_encard_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.fiber_encard_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.fiber_encard_le ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.fiber_encard_le

end CheegerGromovTaylor
end Riemannian
end Geometry
end DifferentialGeometry
