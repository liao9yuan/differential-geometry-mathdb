import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Restriction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.PointedMaps

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Set _root_.Submission.Set _root_.Filter
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

def FlowSequence.timeRestrict (X : FlowSequence.{u}) (D : RealTimeInterval)
    (hcarrier : ∀ i, D.carrier ⊆ (X.interval i).carrier)
    (hregular : ∀ i, D.regular ⊆ (X.interval i).regular) : PointedFlowSeq.{u, 0, 0} I3 where
  D := D
  term i := (X.term i).timeRestrict D (hcarrier i) (hregular i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.timeRestrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.timeRestrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.timeRestrict ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.timeRestrict

@[simp] theorem FlowSequence.timeRestrict_atTime (X : FlowSequence.{u}) (D : RealTimeInterval)
    (hcarrier : ∀ i, D.carrier ⊆ (X.interval i).carrier)
    (hregular : ∀ i, D.regular ⊆ (X.interval i).regular) (t : ℝ) :
    (X.timeRestrict D hcarrier hregular).atTime t = X.atTime t := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.timeRestrict_atTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.timeRestrict_atTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.timeRestrict_atTime ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.timeRestrict_atTime

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted

variable (X : FlowSequence.{u})

def reindex (k : ℕ → ℕ) : FlowSequence.{u} where
  interval i := X.interval (k i)
  term i := X.term (k i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.reindex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.reindex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.reindex ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.reindex

@[simp] theorem reindex_atTime (k : ℕ → ℕ) (t : ℝ) :
    (X.reindex k).atTime t = (X.atTime t).subseq k := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.reindex_atTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.reindex_atTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.reindex_atTime ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.reindex_atTime

@[simp] theorem timeRestrict_term_metric (D : RealTimeInterval)
    (hcarrier : ∀ i, D.carrier ⊆ (X.interval i).carrier)
    (hregular : ∀ i, D.regular ⊆ (X.interval i).regular) (i : ℕ) :
    ((X.timeRestrict D hcarrier hregular).term i).S.base.metric =
      (X.term i).S.base.metric := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.timeRestrict_term_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.timeRestrict_term_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.timeRestrict_term_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.timeRestrict_term_metric

def singletonTime (t : ℝ) (ht : ∀ i, t ∈ (X.interval i).carrier) : PointedFlowSeq I3 :=
  X.timeRestrict (RealTimeInterval.closed t t le_rfl)
    (fun i s hs => by
      have hst : s = t := le_antisymm hs.2 hs.1
      simpa only [hst] using ht i)
    (fun _ s hs => False.elim (lt_irrefl t (hs.1.trans hs.2)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.singletonTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.singletonTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.singletonTime ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.singletonTime

@[simp] theorem singletonTime_atTime (t : ℝ) (ht : ∀ i, t ∈ (X.interval i).carrier)
    (s : ℝ) : (X.singletonTime t ht).atTime s = X.atTime s := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.singletonTime_atTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.singletonTime_atTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.singletonTime_atTime ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.singletonTime_atTime

@[simp] theorem singletonTime_term_metric (t : ℝ)
    (ht : ∀ i, t ∈ (X.interval i).carrier) (i : ℕ) :
    ((X.singletonTime t ht).term i).S.base.metric = (X.term i).S.base.metric := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.singletonTime_term_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.singletonTime_term_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.singletonTime_term_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.singletonTime_term_metric

variable {X}

def timeRestrictMaps {P : PointedRiemannianManifold.{u, 0, 0} I3} {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps (X.atTime 0) P f)
    (D : RealTimeInterval)
    (hcarrier : ∀ i, D.carrier ⊆ (X.interval i).carrier)
    (hregular : ∀ i, D.regular ⊆ (X.interval i).regular) :
    PointedCGHMaps (X.timeRestrict D hcarrier hregular) P f where
  partialDiffeomorph := F.partialDiffeomorph
  source_exhausts := F.source_exhausts
  base_mem := F.base_mem
  basepoint_map := F.basepoint_map

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.timeRestrictMaps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.timeRestrictMaps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.timeRestrictMaps ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.timeRestrictMaps

@[simp] theorem timeRestrictMaps_partialDiffeomorph
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps (X.atTime 0) P f)
    (D : RealTimeInterval)
    (hcarrier : ∀ i, D.carrier ⊆ (X.interval i).carrier)
    (hregular : ∀ i, D.regular ⊆ (X.interval i).regular) (i : ℕ) :
    (timeRestrictMaps F D hcarrier hregular).partialDiffeomorph i =
      F.partialDiffeomorph i := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.timeRestrictMaps_partialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.timeRestrictMaps_partialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.timeRestrictMaps_partialDiffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.timeRestrictMaps_partialDiffeomorph

def singletonTimeMaps {P : PointedRiemannianManifold.{u, 0, 0} I3} {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps (X.atTime 0) P f)
    (t : ℝ) (ht : ∀ i, t ∈ (X.interval i).carrier) :
    PointedCGHMaps (X.singletonTime t ht) P f where
  partialDiffeomorph := F.partialDiffeomorph
  source_exhausts := F.source_exhausts
  base_mem := F.base_mem
  basepoint_map := F.basepoint_map

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.singletonTimeMaps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.singletonTimeMaps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.singletonTimeMaps ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.singletonTimeMaps

@[simp] theorem singletonTimeMaps_partialDiffeomorph
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps (X.atTime 0) P f)
    (t : ℝ) (ht : ∀ i, t ∈ (X.interval i).carrier) (i : ℕ) :
    (singletonTimeMaps F t ht).partialDiffeomorph i = F.partialDiffeomorph i := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.singletonTimeMaps_partialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.singletonTimeMaps_partialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.singletonTimeMaps_partialDiffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.singletonTimeMaps_partialDiffeomorph

def reindexMaps {P : PointedRiemannianManifold.{u, 0, 0} I3} {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps (X.atTime 0) P f)
    (k : ℕ → ℕ) (hk : StrictMono k) :
    PointedRiemannianConvergenceMaps ((X.reindex (f ∘ k)).atTime 0) P id where
  partialDiffeomorph i := F.partialDiffeomorph (k i)
  source_exhausts := F.source_exhausts.comp_subseq hk
  base_mem i := F.base_mem (k i)
  basepoint_map i := F.basepoint_map (k i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.reindexMaps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.reindexMaps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.reindexMaps ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.reindexMaps

@[simp] theorem reindexMaps_partialDiffeomorph
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps (X.atTime 0) P f)
    (k : ℕ → ℕ) (hk : StrictMono k) (i : ℕ) :
    (reindexMaps F k hk).partialDiffeomorph i = F.partialDiffeomorph (k i) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.reindexMaps_partialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.reindexMaps_partialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.reindexMaps_partialDiffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.reindexMaps_partialDiffeomorph

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence

end

end
