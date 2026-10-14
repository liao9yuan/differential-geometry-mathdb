import Submission.DifferentialGeometry.Topology.Covering.DeckAction
import Submission.DifferentialGeometry.Geometry.Metric.UniversalCover.Metric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Set _root_.Function _root_.Manifold
open scoped _root_.Topology _root_.ContDiff _root_.Manifold

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology
namespace UniversalCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [ConnectedSpace M] [LocallyPathConnectedSpace M]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
  [Inhabited M]

omit [FiniteDimensional ℝ E] [I.Boundaryless]
  [IsManifold I ∞ M]
  [T2Space M]
  [SigmaCompactSpace M]
  [ConnectedSpace M] in
theorem hasMFDerivAt_deck
    (a : FundamentalGroup M (_root_.Inhabited.default : M))
    (p : UniversalCover M) :
    HasMFDerivAt I I (fun q : UniversalCover M => a • q) p
      (ContinuousLinearMap.id ℝ E) := by
  let f : UniversalCover M → UniversalCover M := fun q => a • q
  have hproj : ∀ q, proj (f q) = proj q := fun q => proj_deckAct a q
  refine ⟨(deckAct_contMDiff (I := I) a).continuous.continuousAt, ?_⟩
  have hEq :
      writtenInExtChartAt I I p f
        =ᶠ[𝓝[_root_.Set.range I] (extChartAt I p p)] (id : E → E) := by
    have hmem : (extChartAt I p).target ∈
        𝓝[_root_.Set.range I] (extChartAt I p p) :=
      extChartAt_target_mem_nhdsWithin p
    refine Filter.eventuallyEq_of_mem hmem ?_
    intro y hy
    change extChartAt I (f p) (f ((extChartAt I p).symm y)) = y
    rw [extChartAt_proj_eq (I := I) (M := M),
      hproj p, hproj ((extChartAt I p).symm y),
      ← extChartAt_proj_eq (I := I) (M := M)]
    exact (extChartAt I p).right_inv hy
  have hId : HasFDerivWithinAt (id : E → E)
      (ContinuousLinearMap.id ℝ E) (_root_.Set.range I) (extChartAt I p p) :=
    (hasFDerivAt_id _).hasFDerivWithinAt
  have hx0 :
      writtenInExtChartAt I I p f (extChartAt I p p) =
        (id : E → E) (extChartAt I p p) := by
    change extChartAt I (f p) (f ((extChartAt I p).symm (extChartAt I p p))) =
      extChartAt I p p
    rw [extChartAt_proj_eq (I := I) (M := M),
      hproj p, hproj ((extChartAt I p).symm (extChartAt I p p)),
      ← extChartAt_proj_eq (I := I) (M := M), extChartAt_to_inv]
  exact hId.congr_of_eventuallyEq hEq hx0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.hasMFDerivAt_deck then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.hasMFDerivAt_deck"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.hasMFDerivAt_deck ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.hasMFDerivAt_deck

omit [FiniteDimensional ℝ E]
  [I.Boundaryless]
  [T2Space M]
  [SigmaCompactSpace M]
  [ConnectedSpace M] in
theorem deck_inner
    (g : SmoothRiemannianMetric I M)
    (a : FundamentalGroup M (_root_.Inhabited.default : M))
    (p : UniversalCover M) (v w : TangentSpace I p) :
    (liftedMetric (I := I) g).inner (a • p)
        (mfderiv I I (fun q : UniversalCover M => a • q) p v)
        (mfderiv I I (fun q : UniversalCover M => a • q) p w) =
      (liftedMetric (I := I) g).inner p v w := by
  rw [(hasMFDerivAt_deck (I := I) a p).mfderiv]
  change g.inner (proj (a • p)) v w = g.inner (proj p) v w
  rw [proj_deckAct]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.deck_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.deck_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.deck_inner ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.deck_inner

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry
