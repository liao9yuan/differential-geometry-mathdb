import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.DistanceCurvatureEscape
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornBarriersMinimalFrontier
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornBoundedCurvatureFrontier

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
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact
  RealizedFiniteHorn.metric_space RealizedFiniteHorn.charted RealizedFiniteHorn.smooth
  RealizedFiniteHorn.sigmaCompact

def EscapeFiniteHornRealization.{v} (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{v} eps kappa sigma Phi,
      RealizedDistanceCurvatureEscape X → Nonempty (RealizedFiniteHorn X.toFlowSequence)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EscapeFiniteHornRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EscapeFiniteHornRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EscapeFiniteHornRealization ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EscapeFiniteHornRealization

def FiniteControlledRadiusFiniteHornRealization.{v} (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{v} eps kappa sigma Phi,
      Nonempty (FiniteControlledRadius X) → Nonempty (RealizedFiniteHorn X.toFlowSequence)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FiniteControlledRadiusFiniteHornRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FiniteControlledRadiusFiniteHornRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FiniteControlledRadiusFiniteHornRealization ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FiniteControlledRadiusFiniteHornRealization

theorem escapeFiniteHornRealization_iff_finiteControlledRadiusFiniteHornRealization
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} :
    EscapeFiniteHornRealization.{u} kappa sigma Phi ↔
      FiniteControlledRadiusFiniteHornRealization.{u} kappa sigma Phi := by
  constructor
  · rintro ⟨e, he, hmain⟩
    exact ⟨e, he, fun eps hp hle X hX =>
      hmain eps hp hle X (realizedDistanceCurvatureEscape_of_finiteControlledRadius hX.some)⟩
  · rintro ⟨e, he, hmain⟩
    exact ⟨e, he, fun eps hp hle X hX =>
      hmain eps hp hle X
        ((nonempty_finiteControlledRadius_iff_realizedDistanceCurvatureEscape X).mpr hX)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.escapeFiniteHornRealization_iff_finiteControlledRadiusFiniteHornRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.escapeFiniteHornRealization_iff_finiteControlledRadiusFiniteHornRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.escapeFiniteHornRealization_iff_finiteControlledRadiusFiniteHornRealization ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.escapeFiniteHornRealization_iff_finiteControlledRadiusFiniteHornRealization

theorem escapeFiniteHornRealization_of_finiteHornConstruction
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : ∃ alphaMax collarMin : ℝ, 0 < alphaMax ∧ alphaMax < 1 / 11 ∧ 0 < collarMin ∧
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaMax → ∀ collar : ℝ, collarMin ≤ collar →
        ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            FiniteControlledRadius X → ∃ H : RealizedFiniteHorn X.toFlowSequence,
              H.horn.neck_precision = alpha ∧ collar ≤ H.horn.collar_depth) :
    EscapeFiniteHornRealization.{u} kappa sigma Phi := by
  obtain ⟨alphaMax, collarMin, haMax, haMax', hcMin, hmain⟩ := h
  obtain ⟨e, he, hstep⟩ :=
    hmain (alphaMax / 2) (half_pos haMax) (by linarith) (_root_.Max.max collarMin 1) (le_max_left _ _)
  refine ⟨e, he, fun eps hp hle X hX => ?_⟩
  obtain ⟨H, _⟩ := hstep eps hp hle X
    ((nonempty_finiteControlledRadius_iff_realizedDistanceCurvatureEscape X).mpr hX).some
  exact ⟨H⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.escapeFiniteHornRealization_of_finiteHornConstruction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.escapeFiniteHornRealization_of_finiteHornConstruction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.escapeFiniteHornRealization_of_finiteHornConstruction ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.escapeFiniteHornRealization_of_finiteHornConstruction

theorem finiteControlledRadiusFiniteHornRealization_of_boundedAtDistanceShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} (h : BoundedAtDistanceShell.{u} kappa sigma Phi) :
    FiniteControlledRadiusFiniteHornRealization.{u} kappa sigma Phi := by
  obtain ⟨e, he, hb⟩ := h
  refine ⟨e, he, fun eps hp hle X hX => ?_⟩
  exact absurd hX (not_nonempty_finiteControlledRadius_of_boundedAtDistance X (hb eps hp hle X))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteControlledRadiusFiniteHornRealization_of_boundedAtDistanceShell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteControlledRadiusFiniteHornRealization_of_boundedAtDistanceShell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteControlledRadiusFiniteHornRealization_of_boundedAtDistanceShell ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteControlledRadiusFiniteHornRealization_of_boundedAtDistanceShell

theorem nonempty_realizedFiniteHorn_of_curvatureEscapeRealization_of_escapeFiniteHornRealization
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hesc : CurvatureEscapeRealization.{u} kappa sigma Phi)
    (hhorn : EscapeFiniteHornRealization.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        ¬ BoundedAtDistance X → Nonempty (RealizedFiniteHorn X.toFlowSequence) := by
  obtain ⟨e₁, he₁, h₁⟩ := hesc
  obtain ⟨e₂, he₂, h₂⟩ := hhorn
  exact ⟨min e₁ e₂, lt_min he₁ he₂, fun eps hp hle X hne =>
    h₂ eps hp (le_trans hle (min_le_right e₁ e₂)) X
      ((nonempty_finiteControlledRadius_iff_realizedDistanceCurvatureEscape X).mp
        (h₁ eps hp (le_trans hle (min_le_left e₁ e₂)) X hne))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_realizedFiniteHorn_of_curvatureEscapeRealization_of_escapeFiniteHornRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_realizedFiniteHorn_of_curvatureEscapeRealization_of_escapeFiniteHornRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_realizedFiniteHorn_of_curvatureEscapeRealization_of_escapeFiniteHornRealization ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_realizedFiniteHorn_of_curvatureEscapeRealization_of_escapeFiniteHornRealization

theorem boundedAtDistanceShell_of_escapeFiniteHornRealization_of_coneLimitProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hesc : CurvatureEscapeRealization.{u} kappa sigma Phi)
    (hhorn : EscapeFiniteHornRealization.{u} kappa sigma Phi)
    (hcone : FiniteHornConeLimitProducer.{u} kappa sigma Phi) :
    BoundedAtDistanceShell.{u} kappa sigma Phi :=
  boundedAtDistance_of_curvatureEscapeRealization_of_finiteHornConstruction_of_coneLimitProducer
    hesc (escapeFiniteHornRealization_iff_finiteControlledRadiusFiniteHornRealization.mp hhorn)
    hcone

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.boundedAtDistanceShell_of_escapeFiniteHornRealization_of_coneLimitProducer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.boundedAtDistanceShell_of_escapeFiniteHornRealization_of_coneLimitProducer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.boundedAtDistanceShell_of_escapeFiniteHornRealization_of_coneLimitProducer ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.boundedAtDistanceShell_of_escapeFiniteHornRealization_of_coneLimitProducer

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
