import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence

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
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

namespace NormalizedSequence

variable {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}

def reindex (X : NormalizedSequence.{u} eps kappa sigma Phi) (k : ℕ → ℕ)
    (hk : StrictMono k) : NormalizedSequence.{u} eps kappa sigma Phi where
  interval i := X.interval (k i)
  term i := X.term (k i)
  depth i := X.depth (k i)
  scale i := X.scale (k i)
  depth_pos i := X.depth_pos (k i)
  depth_buffer i := X.depth_buffer (k i)
  scale_pos i := X.scale_pos (k i)
  depth_tendsto := X.depth_tendsto.comp hk.tendsto_atTop
  scale_tendsto := X.scale_tendsto.comp hk.tendsto_atTop
  carrier_eq i := X.carrier_eq (k i)
  regular_eq i := X.regular_eq (k i)
  connected i := X.connected (k i)
  orientation i := X.orientation (k i)
  complete i t ht := X.complete (k i) t ht
  source_bound i := X.source_bound (k i)
  base_one i := X.base_one (k i)
  noncollapse i := X.noncollapse (k i)
  pinching i := X.pinching (k i)
  higher_good i t ht x h := X.higher_good (k i) t ht x h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NormalizedSequence.reindex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NormalizedSequence.reindex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NormalizedSequence.reindex ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NormalizedSequence.reindex

@[simp] theorem reindex_term (X : NormalizedSequence.{u} eps kappa sigma Phi) (k : ℕ → ℕ)
    (hk : StrictMono k) (i : ℕ) : (X.reindex k hk).term i = X.term (k i) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NormalizedSequence.reindex_term then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NormalizedSequence.reindex_term"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NormalizedSequence.reindex_term ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NormalizedSequence.reindex_term

@[simp] theorem reindex_interval (X : NormalizedSequence.{u} eps kappa sigma Phi) (k : ℕ → ℕ)
    (hk : StrictMono k) (i : ℕ) : (X.reindex k hk).interval i = X.interval (k i) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NormalizedSequence.reindex_interval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NormalizedSequence.reindex_interval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NormalizedSequence.reindex_interval ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NormalizedSequence.reindex_interval

@[simp] theorem reindex_depth (X : NormalizedSequence.{u} eps kappa sigma Phi) (k : ℕ → ℕ)
    (hk : StrictMono k) (i : ℕ) : (X.reindex k hk).depth i = X.depth (k i) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NormalizedSequence.reindex_depth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NormalizedSequence.reindex_depth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NormalizedSequence.reindex_depth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NormalizedSequence.reindex_depth

@[simp] theorem reindex_scale (X : NormalizedSequence.{u} eps kappa sigma Phi) (k : ℕ → ℕ)
    (hk : StrictMono k) (i : ℕ) : (X.reindex k hk).scale i = X.scale (k i) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NormalizedSequence.reindex_scale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NormalizedSequence.reindex_scale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NormalizedSequence.reindex_scale ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NormalizedSequence.reindex_scale

theorem reindex_id (X : NormalizedSequence.{u} eps kappa sigma Phi) :
    X.reindex id strictMono_id = X := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NormalizedSequence.reindex_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NormalizedSequence.reindex_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NormalizedSequence.reindex_id ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NormalizedSequence.reindex_id

end NormalizedSequence

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
