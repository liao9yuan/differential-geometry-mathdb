import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.Regularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientTerminalBounds

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.Submission.Manifold _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData (I := I) ancientTimeInterval)

local instance movingDistanceTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.movingDistanceTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.movingDistanceTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.movingDistanceTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.movingDistanceTopology
local instance movingDistanceCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.movingDistanceCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.movingDistanceCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.movingDistanceCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.movingDistanceCharted
local instance movingDistanceSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.movingDistanceSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.movingDistanceSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.movingDistanceSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.movingDistanceSmooth
local instance movingDistanceT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.movingDistanceT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.movingDistanceT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.movingDistanceT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.movingDistanceT2
local instance movingDistanceSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.movingDistanceSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.movingDistanceSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.movingDistanceSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.movingDistanceSigma

theorem IsAncientKappaSolution.absolutelyContinuousOnInterval_moving_distance
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (x y : ℝ → F.M)
    (hx : ContMDiffOn 𝓘(ℝ, ℝ) I 1 x (_root_.Set.Icc a b))
    (hy : ContMDiffOn 𝓘(ℝ, ℝ) I 1 y (_root_.Set.Icc a b)) :
    AbsolutelyContinuousOnInterval
      (fun t => (riemannianEDistOf (F.S.base.metric (-t)) (x t) (y t)).toReal) a b := by
  let _ : ConnectedSpace F.M := hF.connected
  obtain ⟨K, hK⟩ := ancientKappa_rmNormSqBounded_finrank F hF
  have hreg : _root_.Set.Icc ((0 : ℝ) - b) (0 - a) ⊆ ancientTimeInterval.regular := by
    intro t ht
    simpa only [ancientTimeInterval_regular, _root_.Set.mem_Iio] using ht.2.trans_lt (by linarith : 0 - a < 0)
  have hRm (t : ℝ) (ht : t ∈ _root_.Set.Icc ((0 : ℝ) - b) (0 - a)) (z : F.M) :
      Tensor0SBundle.normSq0S (F.S.base.metric t) z 4 (F.S.base.rm04 t z) ≤ K :=
    hK t (ancientTimeInterval.regular_subset (hreg ht)) z
  simpa only [zero_sub] using
    absolutelyContinuousOnInterval_riemannianEDistOf_toReal_of_normSq0S_rm04_le
      F.S F.isSolution hab hreg hRm x y hx hy

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.IsAncientKappaSolution
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.IsAncientKappaSolution.absolutelyContinuousOnInterval_moving_distance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.IsAncientKappaSolution.absolutelyContinuousOnInterval_moving_distance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.IsAncientKappaSolution.absolutelyContinuousOnInterval_moving_distance ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.IsAncientKappaSolution.absolutelyContinuousOnInterval_moving_distance

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
