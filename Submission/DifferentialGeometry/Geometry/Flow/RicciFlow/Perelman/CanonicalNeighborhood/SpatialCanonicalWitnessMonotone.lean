import Submission.DifferentialGeometry.Geometry.Neck.SpatialTolerance
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {g : SmoothRiemannianMetric I3 M}

def SpatialOrderedNeckChain.monoEps {eps eps' : ℝ} {V : Set M}
    (c : SpatialOrderedNeckChain g eps V) (heps : eps ≤ eps') (hsmall : eps' < 1 / 11) :
    SpatialOrderedNeckChain g eps' V where
  count := c.count
  count_pos := c.count_pos
  centers := c.centers
  necks := fun i => (c.necks i).mono heps hsmall
  lo := c.lo
  hi := c.hi
  lo_lt_hi := c.lo_lt_hi
  inside := c.inside
  swept_eq := c.swept_eq
  transition_increasing := c.transition_increasing

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialOrderedNeckChain.monoEps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialOrderedNeckChain.monoEps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialOrderedNeckChain.monoEps ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialOrderedNeckChain.monoEps

def SpatialLocalNeck.monoEps {eps eps' : ℝ} {x : M} {U : Set M}
    (L : SpatialLocalNeck g eps x U) (heps : eps ≤ eps') (hsmall : eps' < 1 / 11) :
    SpatialLocalNeck g eps' x U where
  neck := L.neck.mono heps hsmall
  region_eq := L.region_eq
  boundary_eq := L.boundary_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialLocalNeck.monoEps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialLocalNeck.monoEps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialLocalNeck.monoEps ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialLocalNeck.monoEps

def SpatialLocalCap.monoEps {eps eps' : ℝ} {x : M} {U : Set M}
    (C : SpatialLocalCap g eps x U) (heps : eps ≤ eps') (hsmall : eps' < 1 / 11) :
    SpatialLocalCap g eps' x U where
  core := C.core
  core_inside := C.core_inside
  center_inside := C.center_inside
  coreModel := C.coreModel
  tube := C.tube
  tubeMap := C.tubeMap
  tube_domain := C.tube_domain
  tube_eq := C.tube_eq
  union_eq := C.union_eq
  overlap_eq := C.overlap_eq
  inner_boundary := C.inner_boundary
  outer_boundary := C.outer_boundary
  boundary_eq := C.boundary_eq
  boundaries_disjoint := C.boundaries_disjoint
  chain := C.chain.monoEps heps hsmall
  coreBoundaryMap := C.coreBoundaryMap
  core_boundary_eq := C.core_boundary_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialLocalCap.monoEps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialLocalCap.monoEps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialLocalCap.monoEps ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialLocalCap.monoEps

def SpatialRoundComponent.monoEps {eps eps' : ℝ} {x : M} {U : Set M}
    (R : SpatialRoundComponent g eps x U) (hpos : 0 < eps) (heps : eps ≤ eps') :
    SpatialRoundComponent g eps' x U := by
  letI : TopologicalSpace R.Z := R.topology
  letI : ChartedSpace ThreeSpace R.Z := R.charted
  letI : IsManifold I3 ∞ R.Z := R.smooth
  letI : T2Space R.Z := R.t2
  letI : CompactSpace R.Z := R.compact
  letI : ConnectedSpace R.Z := R.connected
  exact
    { Z := R.Z
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
      comparison := R.comparison.mono (subset_refl _)
        (Nat.ceil_mono (inv_anti₀ hpos heps)) heps
      metric_bounds := R.metric_bounds }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialRoundComponent.monoEps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialRoundComponent.monoEps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialRoundComponent.monoEps ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialRoundComponent.monoEps

def SpatialCanonicalAlternative.monoEps {eps eps' C : ℝ} {x : M} {U : Set M}
    (A : SpatialCanonicalAlternative g eps C x U) (hpos : 0 < eps) (heps : eps ≤ eps')
    (hsmall : eps' < 1 / 11) : SpatialCanonicalAlternative g eps' C x U := by
  cases A with
  | neck data => exact .neck (data.monoEps heps hsmall)
  | cap data deep => exact .cap (data.monoEps heps hsmall) deep
  | positive whole data sec => exact .positive whole data sec
  | round whole data => exact .round whole (data.monoEps hpos heps)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialCanonicalAlternative.monoEps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialCanonicalAlternative.monoEps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialCanonicalAlternative.monoEps ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialCanonicalAlternative.monoEps

omit [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem SpatialCanonicalAlternative.monoEps_requiresVolume {eps eps' C : ℝ} {x : M}
    {U : Set M} (A : SpatialCanonicalAlternative g eps C x U) (hpos : 0 < eps)
    (heps : eps ≤ eps') (hsmall : eps' < 1 / 11) :
    (A.monoEps hpos heps hsmall).requiresVolume = A.requiresVolume := by
  cases A <;> rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialCanonicalAlternative.monoEps_requiresVolume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialCanonicalAlternative.monoEps_requiresVolume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialCanonicalAlternative.monoEps_requiresVolume ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialCanonicalAlternative.monoEps_requiresVolume

def SpatialCanonicalWitness.monoEps {eps eps' C1 C2 : ℝ} {x : M}
    (W : SpatialCanonicalWitness g eps C1 C2 x) (heps : eps ≤ eps') (hsmall : eps' < 1 / 11) :
    SpatialCanonicalWitness g eps' C1 C2 x where
  Q_pos := W.Q_pos
  eps_pos := W.eps_pos.trans_le heps
  eps_lt_one := lt_trans hsmall (by norm_num)
  domain := W.domain
  center_inside := W.center_inside
  radius := W.radius
  radius_lower := W.radius_lower
  radius_upper := W.radius_upper
  ball_inside := W.ball_inside
  inside_ball := W.inside_ball
  scalar_bounds := W.scalar_bounds
  rm_bound := W.rm_bound
  alternative := W.alternative.monoEps W.eps_pos heps hsmall
  volume := by
    intro hv
    exact W.volume (by
      simpa only [SpatialCanonicalAlternative.monoEps_requiresVolume] using hv)
  gradient := W.gradient

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialCanonicalWitness.monoEps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialCanonicalWitness.monoEps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialCanonicalWitness.monoEps ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialCanonicalWitness.monoEps

theorem SpatialCanonicalWitness.capTubeHasNeckChart.mono_eps {eps eps' C1 C2 alpha alpha' : ℝ}
    {x : M} {W : SpatialCanonicalWitness g eps C1 C2 x} (h : W.capTubeHasNeckChart alpha)
    (heps : eps ≤ eps') (hsmall : eps' < 1 / 11) (halpha : alpha ≤ alpha')
    (halpha' : alpha' < 1 / 11) :
    (W.monoEps heps hsmall).capTubeHasNeckChart alpha' := by
  intro cap depth heq
  change W.alternative.monoEps W.eps_pos heps hsmall = SpatialCanonicalAlternative.cap cap depth
    at heq
  cases halt : W.alternative with
  | neck data =>
    rw [halt] at heq
    cases heq
  | cap data deep =>
    rw [halt] at heq
    change SpatialCanonicalAlternative.cap (data.monoEps heps hsmall) deep =
      SpatialCanonicalAlternative.cap cap depth at heq
    cases heq
    obtain ⟨v, nk, hnk⟩ := h data deep halt
    exact ⟨v, nk.mono halpha halpha', hnk⟩
  | positive whole data sec =>
    rw [halt] at heq
    cases heq
  | round whole data =>
    rw [halt] at heq
    cases heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialCanonicalWitness.capTubeHasNeckChart.mono_eps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialCanonicalWitness.capTubeHasNeckChart.mono_eps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialCanonicalWitness.capTubeHasNeckChart.mono_eps ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialCanonicalWitness.capTubeHasNeckChart.mono_eps

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

namespace OrientedThreeStage.IncomingSlab

variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

theorem spatiallyCanonicalBefore_mono_eps {ε ε' C1 C2 q t : ℝ} (hε : ε ≤ ε')
    (hε' : ε' < 1 / 11) : G.SpatiallyCanonicalBefore ε C1 C2 q t →
    G.SpatiallyCanonicalBefore ε' C1 C2 q t := by
  intro hG y t' ht hR
  obtain ⟨W, hW⟩ := hG y t' ht hR
  exact ⟨W.monoEps hε hε', hW.mono_eps hε hε' hε hε'⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.spatiallyCanonicalBefore_mono_eps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.spatiallyCanonicalBefore_mono_eps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.spatiallyCanonicalBefore_mono_eps ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.spatiallyCanonicalBefore_mono_eps

theorem spatiallyCanonicalOn_mono_eps {ε ε' C1 C2 q t η : ℝ} (hε : ε ≤ ε')
    (hε' : ε' < 1 / 11) : G.SpatiallyCanonicalOn ε C1 C2 q t η →
    G.SpatiallyCanonicalOn ε' C1 C2 q t η := by
  intro hG y t' ha ht hη hs hR
  obtain ⟨W, hW⟩ := hG y t' ha ht hη hs hR
  exact ⟨W.monoEps hε hε', hW.mono_eps hε hε' hε hε'⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.spatiallyCanonicalOn_mono_eps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.spatiallyCanonicalOn_mono_eps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.spatiallyCanonicalOn_mono_eps ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.spatiallyCanonicalOn_mono_eps

end OrientedThreeStage.IncomingSlab

namespace RetainedCoreHistory

variable {P₀ : OrientedThreeStage.{u}} (H : RetainedCoreHistory P₀)

theorem eventSlabsSpatiallyCanonical_mono_eps {ε ε' C1 C2 q : ℝ}
    {k : Fin (H.eventCount + 1)} (hε : ε ≤ ε') (hε' : ε' < 1 / 11) :
    H.EventSlabsSpatiallyCanonical ε C1 C2 q k → H.EventSlabsSpatiallyCanonical ε' C1 C2 q k :=
  fun hH j hj => (H.toHistory.event j).incoming.spatiallyCanonicalBefore_mono_eps hε hε' (hH j hj)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.eventSlabsSpatiallyCanonical_mono_eps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.eventSlabsSpatiallyCanonical_mono_eps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.eventSlabsSpatiallyCanonical_mono_eps ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.eventSlabsSpatiallyCanonical_mono_eps

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
