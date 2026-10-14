import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BoundedAtDistanceFromRmBallBound
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonComposition
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.EscapeReindexingReduction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornStructureReduction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CurvatureOperator
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Scalar

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

structure ConeBlowupLimit {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) where
  delta : ℝ
  delta_pos : 0 < delta
  flow : PointedFlowData.{u, 0, 0} I3 (RealTimeInterval.closed (-delta) 0 (by linarith))
  limit_complete : MetricComplete (flow.atTime 0)
  patch : Set flow.M
  open_patch : IsOpen patch
  compact_patch : IsCompact (closure patch)
  connected_patch : IsConnected patch
  base_mem : flow.basepoint ∈ patch
  cone : ConeChart (flow.S.base.metric 0) patch
  nonflat : ∃ x ∈ patch, metricScalarAt (flow.S.base.metric 0) x ≠ 0
  nonnegative : ∀ s ∈ Set.Icc (-delta) 0, SecLower (flow.S.base.metric s) 0 patch
  normalized : PointedFlowScalarAtBase flow 1
  subseq : ℕ → ℕ
  strictMono : StrictMono subseq
  scale : ℕ → ℝ
  scale_pos : ∀ i, 0 < scale i
  scale_tendsto : Filter.Tendsto scale Filter.atTop Filter.atTop
  map : ∀ i, PartialDiffeomorph I3 I3 flow.M (X.term (subseq i)).M ∞
  contains_patch : ∀ i, patch ⊆ (map i).source
  window : ∀ᶠ i in Filter.atTop,
    Set.Icc (-delta / scale i) 0 ⊆ (X.interval (subseq i)).carrier
  rate : ℕ → ℝ
  rate_pos : ∀ i, 0 < rate i
  rate_tendsto : Filter.Tendsto rate Filter.atTop (nhds 0)
  annular_convergence : ∀ K : Set flow.M, IsCompact K → K ⊆ patch → ∀ m : ℕ,
    ∀ᶠ i in Filter.atTop, Nonempty (MetricComparisonOn (fun s => flow.S.base.metric s)
      (rescaledMetric (X.term (subseq i)).S 0 (scale i) (scale_pos i))
      (map i) K (Set.Icc (-delta) 0) m (rate i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConeBlowupLimit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConeBlowupLimit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConeBlowupLimit ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConeBlowupLimit

namespace ConeBlowupLimit

variable {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
  {X : NormalizedSequence.{u} eps kappa sigma Phi}

def toConeFlowLimit (L : ConeBlowupLimit X) : ConeFlowLimit X.toFlowSequence where
  delta := L.delta
  delta_pos := L.delta_pos
  flow := L.flow
  patch := L.patch
  open_patch := L.open_patch
  compact_patch := L.compact_patch
  connected_patch := L.connected_patch
  base_mem := L.base_mem
  cone := L.cone
  nonnegative := L.nonnegative
  normalized := L.normalized
  subseq := L.subseq
  strictMono := L.strictMono
  scale := L.scale
  scale_pos := L.scale_pos
  scale_tendsto := L.scale_tendsto
  map := L.map
  contains_patch := L.contains_patch
  window := L.window
  converges := by
    intro K hK hKU m eps heps
    filter_upwards [L.annular_convergence K hK hKU m,
      L.rate_tendsto.eventually (eventually_lt_nhds heps)] with i hi hri
    exact ⟨(hi.some).mono (subset_refl K) le_rfl hri.le⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConeBlowupLimit.toConeFlowLimit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConeBlowupLimit.toConeFlowLimit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConeBlowupLimit.toConeFlowLimit ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConeBlowupLimit.toConeFlowLimit

theorem false (L : ConeBlowupLimit X) : False :=
  solution_cone_terminal_exclusion L.flow.S L.flow.isSolution (by linarith [L.delta_pos])
    (by intro t ht; exact ht) (by intro t ht; exact ht) L.patch L.cone L.nonnegative L.nonflat

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConeBlowupLimit.false then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConeBlowupLimit.false"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConeBlowupLimit.false ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConeBlowupLimit.false

theorem not_subsequenceCurvatureEscape (L : ConeBlowupLimit X) :
    ¬ SubsequenceCurvatureEscape X :=
  fun _ => L.false

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConeBlowupLimit.not_subsequenceCurvatureEscape then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConeBlowupLimit.not_subsequenceCurvatureEscape"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConeBlowupLimit.not_subsequenceCurvatureEscape ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConeBlowupLimit.not_subsequenceCurvatureEscape

end ConeBlowupLimit

theorem not_nonempty_coneBlowupLimit {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} :
    ¬ Nonempty (ConeBlowupLimit X) :=
  fun h => h.elim fun L => L.false

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_nonempty_coneBlowupLimit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_nonempty_coneBlowupLimit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_nonempty_coneBlowupLimit ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_nonempty_coneBlowupLimit

def ConeBlowupLimitRealization.{v} (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{v} eps kappa sigma Phi,
      SubsequenceCurvatureEscape X → Nonempty (ConeBlowupLimit X)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConeBlowupLimitRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConeBlowupLimitRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConeBlowupLimitRealization ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConeBlowupLimitRealization

theorem coneLimitEscapeShell_of_coneBlowupLimitRealization
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : ConeBlowupLimitRealization.{u} kappa sigma Phi) :
    ConeLimitEscapeShell.{u} kappa sigma Phi := by
  obtain ⟨e, he, hb⟩ := h
  exact ⟨e, he, fun eps hp hle X hsub =>
    (hb eps hp hle X hsub).map fun L => L.toConeFlowLimit⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneLimitEscapeShell_of_coneBlowupLimitRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneLimitEscapeShell_of_coneBlowupLimitRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneLimitEscapeShell_of_coneBlowupLimitRealization ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneLimitEscapeShell_of_coneBlowupLimitRealization

theorem noSubsequenceCurvatureEscapeShell_of_coneBlowupLimitRealization
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : ConeBlowupLimitRealization.{u} kappa sigma Phi) :
    NoSubsequenceCurvatureEscapeShell.{u} kappa sigma Phi := by
  obtain ⟨e, he, hb⟩ := h
  exact ⟨e, he, fun eps hp hle X =>
    fun hsub => (hb eps hp hle X hsub).elim fun L => L.not_subsequenceCurvatureEscape hsub⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.noSubsequenceCurvatureEscapeShell_of_coneBlowupLimitRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.noSubsequenceCurvatureEscapeShell_of_coneBlowupLimitRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.noSubsequenceCurvatureEscapeShell_of_coneBlowupLimitRealization ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.noSubsequenceCurvatureEscapeShell_of_coneBlowupLimitRealization

theorem coneBlowupLimitRealization_iff_noSubsequenceCurvatureEscapeShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} :
    ConeBlowupLimitRealization.{u} kappa sigma Phi ↔
      NoSubsequenceCurvatureEscapeShell.{u} kappa sigma Phi :=
  ⟨noSubsequenceCurvatureEscapeShell_of_coneBlowupLimitRealization,
    fun ⟨e, he, hn⟩ => ⟨e, he, fun eps hp hle X hsub => (hn eps hp hle X hsub).elim⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneBlowupLimitRealization_iff_noSubsequenceCurvatureEscapeShell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneBlowupLimitRealization_iff_noSubsequenceCurvatureEscapeShell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneBlowupLimitRealization_iff_noSubsequenceCurvatureEscapeShell ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneBlowupLimitRealization_iff_noSubsequenceCurvatureEscapeShell

theorem coneLimitEscapeShell_iff_coneBlowupLimitRealization
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} :
    ConeLimitEscapeShell.{u} kappa sigma Phi ↔
      ConeBlowupLimitRealization.{u} kappa sigma Phi :=
  ⟨fun h => coneBlowupLimitRealization_iff_noSubsequenceCurvatureEscapeShell.mpr
      (coneLimitEscapeShell_iff_noSubsequenceCurvatureEscapeShell.mp h),
    coneLimitEscapeShell_of_coneBlowupLimitRealization⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneLimitEscapeShell_iff_coneBlowupLimitRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneLimitEscapeShell_iff_coneBlowupLimitRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneLimitEscapeShell_iff_coneBlowupLimitRealization ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneLimitEscapeShell_iff_coneBlowupLimitRealization

theorem boundedAtDistanceShell_of_smallScale_of_coneBlowupLimitRealization
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hsmall : ∃ epsStar r : ℝ, 0 < epsStar ∧ 0 < r ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, CurvatureBoundedWithin X r)
    (h : ConeBlowupLimitRealization.{u} kappa sigma Phi) :
    BoundedAtDistanceShell.{u} kappa sigma Phi :=
  boundedAtDistanceShell_of_smallScale_of_coneLimitEscapeShell hsmall
    (coneLimitEscapeShell_of_coneBlowupLimitRealization h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.boundedAtDistanceShell_of_smallScale_of_coneBlowupLimitRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.boundedAtDistanceShell_of_smallScale_of_coneBlowupLimitRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.boundedAtDistanceShell_of_smallScale_of_coneBlowupLimitRealization ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.boundedAtDistanceShell_of_smallScale_of_coneBlowupLimitRealization

theorem curvatureEscapeRealization_of_smallScale_of_coneBlowupLimitRealization
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hsmall : ∃ epsStar r : ℝ, 0 < epsStar ∧ 0 < r ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, CurvatureBoundedWithin X r)
    (h : ConeBlowupLimitRealization.{u} kappa sigma Phi) :
    CurvatureEscapeRealization.{u} kappa sigma Phi :=
  curvatureEscapeRealization_of_boundedAtDistance
    (boundedAtDistanceShell_of_smallScale_of_coneBlowupLimitRealization hsmall h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.curvatureEscapeRealization_of_smallScale_of_coneBlowupLimitRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.curvatureEscapeRealization_of_smallScale_of_coneBlowupLimitRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.curvatureEscapeRealization_of_smallScale_of_coneBlowupLimitRealization ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.curvatureEscapeRealization_of_smallScale_of_coneBlowupLimitRealization

theorem bounded_curvature_at_distance_of_smallScale_of_coneBlowupLimitRealization
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hsmall : ∃ epsStar r : ℝ, 0 < epsStar ∧ 0 < r ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, CurvatureBoundedWithin X r)
    (h : ConeBlowupLimitRealization.{u} kappa sigma Phi)
    (hder : TerminalDerivativeBoundProducer.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X ∧ TerminalDerivativeBounds X :=
  bounded_curvature_at_distance_of_noSubsequenceCurvatureEscapeShell_and_terminalDerivativeBoundProducer
    hsmall (noSubsequenceCurvatureEscapeShell_of_coneBlowupLimitRealization h) hder

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bounded_curvature_at_distance_of_smallScale_of_coneBlowupLimitRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bounded_curvature_at_distance_of_smallScale_of_coneBlowupLimitRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bounded_curvature_at_distance_of_smallScale_of_coneBlowupLimitRealization ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bounded_curvature_at_distance_of_smallScale_of_coneBlowupLimitRealization

theorem boundedAtDistanceShell_of_modelCurvatureBound_of_coneBlowupLimitRealization
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) (hsigma : 0 < sigma)
    (hPhi : AdmissiblePinchingFunction Phi)
    (h : ConeBlowupLimitRealization.{u} kappa sigma Phi) :
    BoundedAtDistanceShell.{u} kappa sigma Phi := by
  obtain ⟨e, r, he, hr, hb⟩ := exists_pos_curvatureBoundedWithin_of_modelScale hmod
  exact boundedAtDistanceShell_of_smallScale_of_coneBlowupLimitRealization
    ⟨e, r, he, hr, fun eps hp hle X => hb eps hp hle sigma hsigma Phi hPhi X⟩ h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.boundedAtDistanceShell_of_modelCurvatureBound_of_coneBlowupLimitRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.boundedAtDistanceShell_of_modelCurvatureBound_of_coneBlowupLimitRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.boundedAtDistanceShell_of_modelCurvatureBound_of_coneBlowupLimitRealization ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.boundedAtDistanceShell_of_modelCurvatureBound_of_coneBlowupLimitRealization

theorem bounded_curvature_at_distance_of_modelCurvatureBound_of_coneBlowupLimitRealization
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) (hsigma : 0 < sigma)
    (hPhi : AdmissiblePinchingFunction Phi)
    (h : ConeBlowupLimitRealization.{u} kappa sigma Phi)
    (hder : TerminalDerivativeBoundProducer.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X ∧ TerminalDerivativeBounds X := by
  obtain ⟨e, r, he, hr, hb⟩ := exists_pos_curvatureBoundedWithin_of_modelScale hmod
  exact bounded_curvature_at_distance_of_smallScale_of_coneBlowupLimitRealization
    ⟨e, r, he, hr, fun eps hp hle X => hb eps hp hle sigma hsigma Phi hPhi X⟩ h hder

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bounded_curvature_at_distance_of_modelCurvatureBound_of_coneBlowupLimitRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bounded_curvature_at_distance_of_modelCurvatureBound_of_coneBlowupLimitRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bounded_curvature_at_distance_of_modelCurvatureBound_of_coneBlowupLimitRealization ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bounded_curvature_at_distance_of_modelCurvatureBound_of_coneBlowupLimitRealization

private def emptyConeChart : ConeChart (euclideanMetric (E := ThreeSpace)) (∅ : Set ThreeSpace) where
  surface := EuclideanSpace ℝ (Fin 2)
  metric := euclideanMetric (E := EuclideanSpace ℝ (Fin 2))
  map :=
    { toPartialEquiv :=
        { toFun := fun _ => (0 : ThreeSpace)
          invFun := fun _ => (0, 0)
          source := ∅
          target := ∅
          map_source' := fun x hx => absurd hx (by simp)
          map_target' := fun x hx => absurd hx (by simp)
          left_inv' := fun x hx => absurd hx (by simp)
          right_inv' := fun x hx => absurd hx (by simp) }
      open_source := isOpen_empty
      open_target := isOpen_empty
      contMDiffOn_toFun := fun x hx => absurd hx (by simp)
      contMDiffOn_invFun := fun x hx => absurd hx (by simp) }
  positive_radius := fun z hz => absurd hz (by simp)
  target_eq := rfl
  radial_metric := fun z hz => absurd hz (by simp)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.emptyConeChart
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.emptyConeChart target :: scope.openDecls } }

theorem exists_coneChart_not_exists_metricScalarAt_ne_zero :
    ∃ (g : SmoothRiemannianMetric I3 ThreeSpace) (U : Set ThreeSpace),
      Nonempty (ConeChart g U) ∧ ¬ ∃ x ∈ U, metricScalarAt g x ≠ 0 :=
  ⟨euclideanMetric (E := ThreeSpace), ∅, ⟨⟨emptyConeChart⟩, by simp⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_coneChart_not_exists_metricScalarAt_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_coneChart_not_exists_metricScalarAt_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_coneChart_not_exists_metricScalarAt_ne_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_coneChart_not_exists_metricScalarAt_ne_zero

theorem exists_metricScalarAt_ne_zero :
    ∃ g : SmoothRiemannianMetric I3 ThreeSpace, ∃ x : ThreeSpace, metricScalarAt g x ≠ 0 :=
  ⟨DifferentialGeometry.PDE.RicciFlow.StandardCap.metric, 0, by
    rw [DifferentialGeometry.PDE.RicciFlow.StandardCap.metricScalarAt_zero]
    norm_num⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_metricScalarAt_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_metricScalarAt_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_metricScalarAt_ne_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_metricScalarAt_ne_zero

theorem exists_curvatureOperatorNonnegative_and_metricScalarAt_ne_zero :
    ∃ g : SmoothRiemannianMetric I3 ThreeSpace,
      (∀ x : ThreeSpace, metricAlgebraicCurvatureTensorAt (I := I3) (M := ThreeSpace) g x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I3) (M := ThreeSpace)) ∧
      ∃ x : ThreeSpace, metricScalarAt g x ≠ 0 :=
  ⟨DifferentialGeometry.PDE.RicciFlow.StandardCap.metric,
    fun x => DifferentialGeometry.PDE.RicciFlow.StandardCap.metric_curvatureOperator_nonnegative x,
    0, by
      rw [DifferentialGeometry.PDE.RicciFlow.StandardCap.metricScalarAt_zero]
      norm_num⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_curvatureOperatorNonnegative_and_metricScalarAt_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_curvatureOperatorNonnegative_and_metricScalarAt_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_curvatureOperatorNonnegative_and_metricScalarAt_ne_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_curvatureOperatorNonnegative_and_metricScalarAt_ne_zero

theorem exists_metricScalarAt_ne_zero_of_finiteHorn {W : Type u} [MetricSpace W]
    [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W] [SigmaCompactSpace W]
    {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) :
    ∃ x : W, metricScalarAt g x ≠ 0 := by
  obtain ⟨i, hi⟩ := H.curvature_diverges 0
  obtain ⟨d, hd, _hdle, hmem⟩ := H.cofinal_axial i
  exact ⟨H.axial.point (d / 2),
    ne_of_gt (hi _ (hmem (d / 2) ⟨by linarith, by linarith⟩))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_metricScalarAt_ne_zero_of_finiteHorn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_metricScalarAt_ne_zero_of_finiteHorn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_metricScalarAt_ne_zero_of_finiteHorn ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_metricScalarAt_ne_zero_of_finiteHorn

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
