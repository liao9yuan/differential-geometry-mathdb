import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalCapCollar
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckLocalTransport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.ContDiff _root_.Submission.ContDiff

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] {D : RealTimeInterval}
  {S : SolutionOn (I := I3) (M := M) D} {eps C C1 C2 alpha t : ℝ} {x : M} {U : Set M}

def OrderedNeckChain.toSpatial (c : OrderedNeckChain S eps t U) :
    SpatialOrderedNeckChain (S.base.metric t) eps U where
  count := c.count
  count_pos := c.count_pos
  centers := c.centers
  necks i := (c.necks i).toSpatialNeck
  lo := c.lo
  hi := c.hi
  lo_lt_hi := c.lo_lt_hi
  inside := c.inside
  swept_eq := c.swept_eq
  transition_increasing := c.transition_increasing

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.OrderedNeckChain.toSpatial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.OrderedNeckChain.toSpatial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.OrderedNeckChain.toSpatial ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.OrderedNeckChain.toSpatial

def LocalNeck.toSpatial (n : LocalNeck S eps x t U) :
    SpatialLocalNeck (S.base.metric t) eps x U where
  neck := n.strong.toSpatialNeck
  region_eq := n.region_eq
  boundary_eq := n.boundary_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalNeck.toSpatial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalNeck.toSpatial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalNeck.toSpatial ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalNeck.toSpatial

def LocalCap.toSpatial (c : LocalCap S eps x t U) : SpatialLocalCap (S.base.metric t) eps x U where
  core := c.core
  core_inside := c.core_inside
  center_inside := c.center_inside
  coreModel := c.core_model
  tube := c.tube
  tubeMap := c.tube_map
  tube_domain := c.tube_domain
  tube_eq := c.tube_eq
  union_eq := c.union_eq
  overlap_eq := c.overlap_eq
  inner_boundary := c.inner_boundary
  outer_boundary := c.outer_boundary
  boundary_eq := c.boundary_eq
  boundaries_disjoint := c.boundaries_disjoint
  chain := c.chain.toSpatial
  coreBoundaryMap := c.core_boundary_map
  core_boundary_eq := c.core_boundary_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.toSpatial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.toSpatial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.toSpatial ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.toSpatial

def RoundComponent.toSpatial (R : RoundComponent S eps x t U) :
    SpatialRoundComponent (S.base.metric t) eps x U where
  Z := R.Z
  topology := R.topology
  charted := R.charted
  smooth := R.smooth
  t2 := R.t2
  compact := R.compact
  connected := R.connected
  metric := R.metric
  p := R.p
  scalar_one := R.scalar_one
  constant_curvature := R.constant_curvature
  map := R.map
  source_eq := R.source_eq
  target_eq := R.target_eq
  center_eq := R.center_eq
  Q_pos := R.Q_pos
  comparison := R.comparison
  metric_bounds := R.metric_bounds

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RoundComponent.toSpatial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RoundComponent.toSpatial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RoundComponent.toSpatial ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RoundComponent.toSpatial

def CanonicalAlternative.toSpatial :
    CanonicalAlternative S eps C x t U → SpatialCanonicalAlternative (S.base.metric t) eps C x U
  | .neck data => .neck data.toSpatial
  | .cap data deep => .cap data.toSpatial deep
  | .positive whole data sec => .positive whole data sec
  | .round whole data => .round whole data.toSpatial

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalAlternative.toSpatial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalAlternative.toSpatial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalAlternative.toSpatial ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalAlternative.toSpatial

omit [T2Space M] [SigmaCompactSpace M] in
theorem CanonicalAlternative.requiresVolume_toSpatial (A : CanonicalAlternative S eps C x t U) :
    A.toSpatial.requiresVolume ↔ A.requiresVolume := by
  cases A <;> rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalAlternative.requiresVolume_toSpatial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalAlternative.requiresVolume_toSpatial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalAlternative.requiresVolume_toSpatial ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalAlternative.requiresVolume_toSpatial

def CanonicalWitness.toSpatial (W : CanonicalWitness S eps C1 C2 x t) :
    SpatialCanonicalWitness (S.base.metric t) eps C1 C2 x where
  Q_pos := W.Q_pos
  eps_pos := W.eps_pos
  eps_lt_one := W.eps_lt_one
  domain := W.domain
  center_inside := W.center_inside
  radius := W.radius
  radius_lower := W.radius_lower
  radius_upper := W.radius_upper
  ball_inside := W.ball_inside
  inside_ball := W.inside_ball
  scalar_bounds := W.scalar_bounds
  rm_bound := W.rm_bound
  alternative := W.alternative.toSpatial
  volume h := W.volume (W.alternative.requiresVolume_toSpatial.mp h)
  gradient := W.gradient

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.toSpatial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.toSpatial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.toSpatial ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.toSpatial

theorem CanonicalWitness.capTubeHasNeckChart_toSpatial {W : CanonicalWitness S eps C1 C2 x t}
    (h : W.capTubeHasNeckChart alpha) : W.toSpatial.capTubeHasNeckChart alpha := by
  intro cap depth heq
  change W.alternative.toSpatial = SpatialCanonicalAlternative.cap cap depth at heq
  cases halt : W.alternative with
  | neck data =>
    rw [halt] at heq
    cases heq
  | cap data deep =>
    rw [halt] at heq
    change SpatialCanonicalAlternative.cap data.toSpatial deep = _ at heq
    cases heq
    obtain ⟨v, nk, hnk⟩ := h data deep halt
    exact ⟨v, nk.toSpatialNeck, hnk⟩
  | positive whole data sec =>
    rw [halt] at heq
    cases heq
  | round whole data =>
    rw [halt] at heq
    cases heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.capTubeHasNeckChart_toSpatial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.capTubeHasNeckChart_toSpatial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.capTubeHasNeckChart_toSpatial ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.capTubeHasNeckChart_toSpatial

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
