import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CurvatureNormalization
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Subsequence

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
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance backwardSliceTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceTopology
local instance backwardSliceCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceCharted
local instance backwardSliceSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSmooth
local instance backwardSliceC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceC1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceC1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceC1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceC1
local instance backwardSliceSigmaCompact : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSigmaCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSigmaCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSigmaCompact ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSigmaCompact
local instance backwardSliceT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceT2
local instance backwardSliceTangentT2 : T2Space (TangentBundle I F.M) := F.t2TangentBundle

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceTangentT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceTangentT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceTangentT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceTangentT2

abbrev backwardSliceSequence (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M) :
    PointedRiemannianSeq.{u, uE, uH} (I := I) where
  obj i := {
    M := F.M
    topology := F.topology
    charted := F.charted
    smooth := F.smooth
    sigmaCompact := F.sigmaCompact
    t2 := F.t2
    t2TangentBundle := F.t2TangentBundle
    basepoint := q i
    metric := scaleMetric (tau i)⁻¹ (inv_pos.mpr (htau i)) (F.S.base.metric (-tau i)) }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence


theorem backwardSliceSequence_metric
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M) (i : ℕ) :
    ((backwardSliceSequence F tau htau q).obj i).metric =
      scaleMetric (tau i)⁻¹ (inv_pos.mpr (htau i)) (F.S.base.metric (-tau i)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_metric


theorem backwardSliceSequence_basepoint
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M) (i : ℕ) :
    (backwardSliceSequence F tau htau q).basepoint i = q i := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_basepoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_basepoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_basepoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_basepoint


theorem backwardSliceSequence_edist
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    (i : ℕ) (x y : F.M) :
    riemannianEDistOf (I := I) (M := F.M)
      ((backwardSliceSequence F tau htau q).obj i).metric x y =
      (ENNReal.ofReal (Real.sqrt (tau i)))⁻¹ *
        riemannianEDistOf (I := I) (F.S.base.metric (-tau i)) x y := by
  change riemannianEDistOf (I := I)
    (scaleMetric (tau i)⁻¹ (inv_pos.mpr (htau i)) (F.S.base.metric (-tau i))) x y = _
  rw [edistOf_scale, Real.sqrt_inv, ENNReal.ofReal_inv_of_pos (Real.sqrt_pos.mpr (htau i))]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_edist then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_edist"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_edist ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_edist


theorem backwardSliceSequence_dist
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    (i : ℕ) (x y : F.M) :
    (riemannianEDistOf (I := I) (M := F.M)
      ((backwardSliceSequence F tau htau q).obj i).metric x y).toReal =
      (Real.sqrt (tau i))⁻¹ *
        (riemannianEDistOf (I := I) (F.S.base.metric (-tau i)) x y).toReal := by
  rw [backwardSliceSequence_edist, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg (tau i))]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_dist then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_dist"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_dist ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_dist


theorem backwardSliceSequence_scalar
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M) (i : ℕ) (x : F.M) :
    metricScalarAt (I := I) (M := F.M)
      ((backwardSliceSequence F tau htau q).obj i).metric x =
      tau i * F.S.scalar (-tau i) x := by
  let S : SolutionOn (I := I) (M := F.M) ancientTimeInterval :=
    ⟨⟨fun _ => F.S.base.metric (-tau i)⟩⟩
  have h := congrFun (congrFun (parabolicSolution_scalar (I := I) S 0 (tau i)⁻¹
    (inv_pos.mpr (htau i)) (by change (0 : ℝ) ≤ 0; exact le_rfl)) 0) x
  change metricScalarAt (I := I)
      (scaleMetric (tau i)⁻¹ (inv_pos.mpr (htau i)) (F.S.base.metric (-tau i))) x =
    ((tau i)⁻¹)⁻¹ * metricScalarAt (I := I) (F.S.base.metric (-tau i)) x at h
  change metricScalarAt (I := I)
      (scaleMetric (tau i)⁻¹ (inv_pos.mpr (htau i)) (F.S.base.metric (-tau i))) x =
    tau i * metricScalarAt (I := I) (F.S.base.metric (-tau i)) x
  simpa only [inv_inv] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_scalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_scalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_scalar ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_scalar


theorem backwardSliceSequence_complete {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M) :
    SeqMetricComplete (I := I) (backwardSliceSequence F tau htau q) := by
  constructor
  intro i
  have ht : -tau i ∈ D.carrier := by
    simpa only [hF.carrier_eq, Set.mem_Iic] using (neg_nonpos.mpr (htau i).le)
  have hslice : RiemannianMetricComplete (I := I) (F.S.base.metric (-tau i)) :=
    ⟨hF.complete (-tau i) ht⟩
  have hscaled : RiemannianMetricComplete (I := I)
      (scaleMetric (tau i)⁻¹ (inv_pos.mpr (htau i)) (F.S.base.metric (-tau i))) :=
    hslice.of_lower (inv_pos.mpr (htau i)) (fun _ _ => le_rfl)
  exact hscaled.complete

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_complete then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_complete"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_complete ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_complete


theorem backwardSliceSequence_connected {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M) (i : ℕ) :
    @ConnectedSpace ((backwardSliceSequence F tau htau q).obj i).M
      ((backwardSliceSequence F tau htau q).obj i).topology := hF.connected

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_connected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_connected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_connected ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_connected


theorem backwardSliceSequence_subseq
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M) (phi : ℕ → ℕ) :
    (backwardSliceSequence F tau htau q).subseq phi =
      backwardSliceSequence F (tau ∘ phi) (fun i => htau (phi i)) (q ∘ phi) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_subseq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_subseq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_subseq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_subseq

variable [NeZero (Module.finrank ℝ E)] [I.Boundaryless]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem backwardSliceSequence_basepoint_map
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps (I := I) (backwardSliceSequence F tau htau q) L phi)
    (k : ℕ) : Phi.map k L.basepoint = q (phi k) := Phi.basepoint_map k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_basepoint_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_basepoint_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_basepoint_map ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_basepoint_map

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
