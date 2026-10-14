import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSplitting
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RiemannianProduct
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalCoverCurvatureNorm
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CrossModelCurvatureTransport
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceProductCurvature
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceScalarPositive

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Topology
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.BigOperators

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
  (G : PointedFlowData.{u, 0, 0} (I := 𝓡 2) ancientTimeInterval)

local instance splitSurfaceGeometryBaseTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseTopology
local instance splitSurfaceGeometryBaseCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseCharted
local instance splitSurfaceGeometryBaseSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseSmooth
local instance splitSurfaceGeometryBaseC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseC1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseC1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseC1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseC1
local instance splitSurfaceGeometryBaseT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseT2
local instance splitSurfaceGeometryBaseSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseSigma
local instance splitSurfaceGeometryBaseInhabited : Inhabited F.M := ⟨F.basepoint⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseInhabited then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseInhabited"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseInhabited ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseInhabited
local instance splitSurfaceGeometryBaseLocallyPathConnected : LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseLocallyPathConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseLocallyPathConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseLocallyPathConnected ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseLocallyPathConnected
local instance splitSurfaceGeometryBaseSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseSemilocallySimplyConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseSemilocallySimplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseSemilocallySimplyConnected ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometryBaseSemilocallySimplyConnected

local instance splitSurfaceGeometrySurfaceTopology : TopologicalSpace G.M := G.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometrySurfaceTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometrySurfaceTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometrySurfaceTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometrySurfaceTopology
local instance splitSurfaceGeometrySurfaceCharted :
    ChartedSpace (EuclideanSpace ℝ (Fin 2)) G.M := G.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometrySurfaceCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometrySurfaceCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometrySurfaceCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometrySurfaceCharted
local instance splitSurfaceGeometrySurfaceSmooth : IsManifold (𝓡 2) ∞ G.M := G.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometrySurfaceSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometrySurfaceSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometrySurfaceSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometrySurfaceSmooth
local instance splitSurfaceGeometrySurfaceC1 : IsManifold (𝓡 2) 1 G.M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometrySurfaceC1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometrySurfaceC1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometrySurfaceC1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometrySurfaceC1
local instance splitSurfaceGeometrySurfaceT2 : T2Space G.M := G.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometrySurfaceT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometrySurfaceT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometrySurfaceT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometrySurfaceT2
local instance splitSurfaceGeometrySurfaceSigma : SigmaCompactSpace G.M := G.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometrySurfaceSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometrySurfaceSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometrySurfaceSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceGeometrySurfaceSigma

variable (Phi : (G.M × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover F.M)
  (hproduct : ∀ t : ℝ, t ≤ 0 → ∀ (y : G.M) (s : ℝ)
    (v w : TangentSpace (𝓡 2) y) (a c : ℝ),
    (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Phi (y, s))
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (v, a))
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (w, c)) =
      (G.S.family.metric t).inner y v w + a * c)

include hproduct

theorem splitSurface_nonnegativeCurvatureOperator {kappa : ℝ}
    (hF : IsAncientKappaSolution (I := I) kappa F) (t : ℝ) (ht : t ≤ 0) :
    PointedFlowNonnegativeCurvatureOperator (I := 𝓡 2) G t := by
  intro y n c v w
  let gP := Diffeomorph.pullbackMetricCross
    (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)) Phi
  have hP (q : G.M) (s : ℝ) (a b : TangentSpace (𝓡 2) q) (c d : ℝ) :
      gP.inner (q, s) (a, c) (b, d) = (G.S.family.metric t).inner q a b + c * d := by
    exact (Diffeomorph.pullbackMetricCross_inner
      (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)) Phi
      (q, s) (a, c) (b, d)).trans (hproduct t ht q s a b c d)
  have hbase : metricAlgebraicCurvatureTensorAt (I := I) (F.S.family.metric t)
      (UniversalCover.proj (Phi (y, 0))) ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) := by
    apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (I := I) (F.S.family.metric t) (UniversalCover.proj (Phi (y, 0)))).mpr
    intro m d a b
    simpa only [metricRm04StandardAt_apply, SolutionFamily.rm04, metricRm04_apply,
      SolutionOn.family] using
      hF.nonnegativeCurvatureOperator t (by simpa using ht)
        (UniversalCover.proj (Phi (y, 0))) m d a b
  have hlift :=
    (metricAlgebraicCurvatureTensorAt_lifted_mem_operatorNonnegativeCone_iff
      (F.S.family.metric t) (Phi (y, 0))).mpr hbase
  have hcross := metricCurvatureOperatorNonnegative_pullbackCross
    (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)) Phi (y, 0) hlift
  have hsurface :=
    (metricAlgebraicCurvatureTensorAt_product_real_mem_operatorCone_iff
      (G.S.family.metric t) gP hP y 0).mp hcross
  have htest :=
    (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (I := 𝓡 2) (G.S.family.metric t) y).mp hsurface n c v w
  simpa only [metricRm04StandardAt_apply, SolutionFamily.rm04, metricRm04_apply,
    SolutionOn.family] using htest

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurface_nonnegativeCurvatureOperator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurface_nonnegativeCurvatureOperator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurface_nonnegativeCurvatureOperator ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurface_nonnegativeCurvatureOperator

theorem splitSurface_rmNormSq_eq
    (t : ℝ) (ht : t ≤ 0) (y : G.M) :
    G.rmNormSq (I := 𝓡 2) t y =
      F.rmNormSq (I := I) t (UniversalCover.proj (Phi (y, 0))) := by
  let gP := Diffeomorph.pullbackMetricCross
    (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)) Phi
  have hP (q : G.M) (s : ℝ) (a b : TangentSpace (𝓡 2) q) (c d : ℝ) :
      gP.inner (q, s) (a, c) (b, d) = (G.S.family.metric t).inner q a b + c * d := by
    exact (Diffeomorph.pullbackMetricCross_inner
      (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)) Phi
      (q, s) (a, c) (b, d)).trans (hproduct t ht q s a b c d)
  have hp := metricRmNormSq_product_real_of_inner_eq (G.S.family.metric t) gP hP y 0
  have hc := metricRmNormSq_pullbackCross
    (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)) Phi (y, 0)
  have hl := UniversalCover.normSq0S_metricRm04At_liftedMetric
    (F.S.family.metric t) (Phi (y, 0))
  change normSq0S (I := 𝓡 2) (G.S.family.metric t) y 4
      (metricRm04At (I := 𝓡 2) (G.S.family.metric t) y) =
    normSq0S (I := I) (F.S.family.metric t) (UniversalCover.proj (Phi (y, 0))) 4
      (metricRm04At (I := I) (F.S.family.metric t) (UniversalCover.proj (Phi (y, 0))))
  exact hp.symm.trans (hc.trans hl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurface_rmNormSq_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurface_rmNormSq_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurface_rmNormSq_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurface_rmNormSq_eq

theorem splitSurface_scalarBounded_of_baseBound {kappa : ℝ}
    (hF : IsAncientKappaSolution (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (C : ℝ) (hC : PointedFlowScalarBounded (I := I) F C)
    (hpositive : ∀ t : ℝ, t ≤ 0 → ∀ y : G.M, 0 < G.S.scalar t y) :
    PointedFlowScalarBounded (I := 𝓡 2) G (Real.sqrt 3 * C) := by
  intro t ht y
  have htzero : t ≤ 0 := by simpa using ht
  refine ⟨(hpositive t htzero y).le, ?_⟩
  have hnorm := ancientKappa_rmNormLeScalar F hdim hF t ht
    (UniversalCover.proj (Phi (y, 0)))
  have hscalar : G.S.scalar t y =
      Real.sqrt (F.rmNormSq (I := I) t (UniversalCover.proj (Phi (y, 0)))) := by
    rw [← splitSurface_rmNormSq_eq F G Phi hproduct t htzero y,
      pointedSurface_rmNormSq_eq_scalar_sq G (by simp),
      Real.sqrt_sq (hpositive t htzero y).le]
  rw [hscalar]
  exact hnorm.trans (mul_le_mul_of_nonneg_left
    (hC t ht (UniversalCover.proj (Phi (y, 0)))).2 (Real.sqrt_nonneg 3))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurface_scalarBounded_of_baseBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurface_scalarBounded_of_baseBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurface_scalarBounded_of_baseBound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurface_scalarBounded_of_baseBound

theorem splitSurface_ancient_geometry {kappa : ℝ}
    (hF : IsAncientKappaSolution (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (hpositive : ∀ t : ℝ, t ≤ 0 → ∀ y : G.M, 0 < G.S.scalar t y) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ t : ℝ, t ≤ 0 → PointedFlowNonnegativeCurvatureOperator (I := 𝓡 2) G t) ∧
      PointedFlowScalarBounded (I := 𝓡 2) G C ∧
      PointedFlowRmNormSqBounded (I := 𝓡 2) G (C ^ 2) ∧
      PointedFlowNotFlat (I := 𝓡 2) G := by
  obtain ⟨C, hC, hRm⟩ := ancientKappa_rmNormSqBounded F hdim hF
  have hCnonneg : 0 ≤ C :=
    (hC 0 (by simp) F.basepoint).1.trans (hC 0 (by simp) F.basepoint).2
  refine ⟨Real.sqrt 3 * C, mul_nonneg (Real.sqrt_nonneg 3) hCnonneg, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact splitSurface_nonnegativeCurvatureOperator F G Phi hproduct hF t ht
  · exact splitSurface_scalarBounded_of_baseBound F G Phi hproduct hF hdim C hC hpositive
  · intro t ht y
    rw [splitSurface_rmNormSq_eq F G Phi hproduct t (by simpa using ht) y]
    exact hRm t ht (UniversalCover.proj (Phi (y, 0)))
  · exact pointedFlowNotFlat_of_scalar_ne_zero (I := 𝓡 2) G (by simp) G.basepoint
      (ne_of_gt (hpositive 0 le_rfl G.basepoint))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurface_ancient_geometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurface_ancient_geometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurface_ancient_geometry ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurface_ancient_geometry

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
