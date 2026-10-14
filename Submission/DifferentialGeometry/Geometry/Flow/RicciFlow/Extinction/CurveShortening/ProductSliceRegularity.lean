import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalRegularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductSolution

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set
open scoped _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [I.Boundaryless]

theorem sliceRegularity_of_immersedOn (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) :
    c.SliceRegularity g lambda t := by
  let A : QuotientProductAtlas I M := quotientProductAtlas
  let _ := A.charts
  let _ := A.smoothManifold
  let ghat := fun τ => quotientProductMetric A (g τ) lambda hlambda
  have hs := c.smoothOn_map A hc
  have him := (c.map_immersedOn_iff A hc).mpr hi
  have hreg := c.map.sliceRegularity ghat J hs him t ht
  have hspeed (x : ℝ) : c.map.speed ghat x t = c.speed g lambda x t :=
    c.map_speed_eq A g lambda hlambda hc x t ht
  have hcurv (x : ℝ) : c.map.curvatureSq ghat x t = c.curvatureSq g lambda x t :=
    c.map_curvatureSq_eq A g lambda hlambda hc hi x t ht
  exact ⟨by simpa only [hspeed] using hreg.speed_continuous,
    by simpa only [hcurv] using hreg.curvatureSq_continuous,
    by simpa only [hcurv, hspeed] using hreg.curvatureSq_speed_periodic⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.sliceRegularity_of_immersedOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.sliceRegularity_of_immersedOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.sliceRegularity_of_immersedOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.sliceRegularity_of_immersedOn

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve
