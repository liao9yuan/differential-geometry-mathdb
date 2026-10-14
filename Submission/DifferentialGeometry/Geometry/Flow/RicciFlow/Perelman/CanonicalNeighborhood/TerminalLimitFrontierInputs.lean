import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientExtension
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalBackwardExtension
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SlabFlowBootstrap

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
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open scoped _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

def TerminalLimitCompactnessFrontier (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
      BoundedAtDistance X → TerminalDerivativeBounds X →
        ∃ P : MetricCompactLimit.{u, 0, 0} (I := I3) (X.toFlowSequence.atTime 0),
          (∀ k, P.convergence.metrics.domain k =
            CanonicalMetricCompactness.canonicalSourceData P.maps k) ∧
          ConnectedSpace P.limit.M ∧ MetricSourceCapture P.maps ∧
          (∀ i, IsCompact (closure (P.maps.partialDiffeomorph i).source)) ∧
          (∀ i, IsConnected (P.maps.partialDiffeomorph i).source) ∧
          (∀ i, closure (P.maps.partialDiffeomorph i).source ⊆
            (P.maps.partialDiffeomorph (i + 1)).source) ∧
          (∃ o : TangentOrientationSection P.limit.M,
            ∀ i y, y ∈ (P.maps.partialDiffeomorph i).source →
              ∃ hf : Function.Bijective (mfderiv I3 I3 (P.maps.partialDiffeomorph i) y),
                PreservesTangentOrientationAt o (X.orientation (P.subseq i))
                  (P.maps.partialDiffeomorph i) y hf) ∧
          (∃ kappa' : ℝ, 0 < kappa' ∧ MetricNoncollapsed P.limit kappa' (Set.Ioc 0 1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalLimitCompactnessFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalLimitCompactnessFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalLimitCompactnessFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalLimitCompactnessFrontier

def TerminalLimitScalarBoundFrontier (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
      BoundedAtDistance X → TerminalDerivativeBounds X →
        ∀ P : MetricCompactLimit.{u, 0, 0} (I := I3) (X.toFlowSequence.atTime 0),
          (∀ k, P.convergence.metrics.domain k =
            CanonicalMetricCompactness.canonicalSourceData P.maps k) →
          (hconn : ConnectedSpace P.limit.M) → MetricSourceCapture P.maps →
          (∀ i, IsCompact (closure (P.maps.partialDiffeomorph i).source)) →
          (∀ i, IsConnected (P.maps.partialDiffeomorph i).source) →
          (∀ i, closure (P.maps.partialDiffeomorph i).source ⊆
            (P.maps.partialDiffeomorph (i + 1)).source) →
          (∃ o : TangentOrientationSection P.limit.M,
            ∀ i y, y ∈ (P.maps.partialDiffeomorph i).source →
              ∃ hf : Function.Bijective (mfderiv I3 I3 (P.maps.partialDiffeomorph i) y),
                PreservesTangentOrientationAt o (X.orientation (P.subseq i))
                  (P.maps.partialDiffeomorph i) y hf) →
          (∃ kappa' : ℝ, 0 < kappa' ∧ MetricNoncollapsed P.limit kappa' (Set.Ioc 0 1)) →
            ∃ C : ℝ, ∀ x, metricScalarAt P.limit.metric x ≤ C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalLimitScalarBoundFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalLimitScalarBoundFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalLimitScalarBoundFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalLimitScalarBoundFrontier

theorem terminal_limit_global_bound_of_frontiers {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hPhi : AdmissiblePinchingFunction Phi)
    (hcompact : TerminalLimitCompactnessFrontier.{u} kappa sigma Phi)
    (hbounded : TerminalLimitScalarBoundFrontier.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X → TerminalDerivativeBounds X → Nonempty (TerminalLimit X) := by
  obtain ⟨e₁, he₁, h₁⟩ := hcompact
  obtain ⟨e₂, he₂, h₂⟩ := hbounded
  refine ⟨min e₁ e₂, lt_min he₁ he₂, fun eps heps hle X hb hd => ?_⟩
  obtain ⟨P, hcanon, hconn, hcap, hpre, hcd, hnested, hor, hnc⟩ :=
    h₁ eps heps (hle.trans (min_le_left e₁ e₂)) X hb hd
  obtain ⟨o, hor'⟩ := hor
  have hsb := h₂ eps heps (hle.trans (min_le_right e₁ e₂)) X hb hd P hcanon hconn hcap hpre
    hcd hnested ⟨o, hor'⟩ hnc
  exact terminal_limit_of_metric_compact_limit hPhi P hcanon hcap hpre hcd hnested o hor' hsb hnc
    hconn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminal_limit_global_bound_of_frontiers then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminal_limit_global_bound_of_frontiers"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminal_limit_global_bound_of_frontiers ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminal_limit_global_bound_of_frontiers

theorem terminal_limit_compactness_frontier_of_terminal_limit_exists {kappa sigma : ℝ}
    {Phi : ℝ → ℝ}
    (h : ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X → TerminalDerivativeBounds X → Nonempty (TerminalLimit X)) :
    TerminalLimitCompactnessFrontier.{u} kappa sigma Phi := by
  obtain ⟨e, he, hmain⟩ := h
  refine ⟨e, he, fun eps heps hle X hb hd => ?_⟩
  obtain ⟨L⟩ := hmain eps heps hle X hb hd
  let P : MetricCompactLimit.{u, 0, 0} (I := I3) (X.toFlowSequence.atTime 0) :=
    { subseq := L.subseq
      strictMono := L.strictMono
      limit := L.space
      limit_complete := L.complete
      maps := L.maps
      convergence := { metrics := L.converges } }
  exact ⟨P, L.canonical_domains, L.connected, L.capture, L.precompact, L.connected_domains,
    L.nested, ⟨L.orientation, L.orientation_preserved⟩, L.noncollapse⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminal_limit_compactness_frontier_of_terminal_limit_exists then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminal_limit_compactness_frontier_of_terminal_limit_exists"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminal_limit_compactness_frontier_of_terminal_limit_exists ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminal_limit_compactness_frontier_of_terminal_limit_exists

theorem exists_metricScalarAt_upper_bound_of_compactSpace
    (P : PointedRiemannianManifold.{u, 0, 0} I3) [CompactSpace P.M] :
    ∃ C : ℝ, ∀ x : P.M, metricScalarAt P.metric x ≤ C := by
  obtain ⟨x₀, -, hmax⟩ := isCompact_univ.exists_isMaxOn ⟨P.basepoint, Set.mem_univ _⟩
    (metricScalar_smooth (I := I3) P.metric).continuous.continuousOn
  exact ⟨metricScalarAt P.metric x₀, fun x => hmax (Set.mem_univ x)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_metricScalarAt_upper_bound_of_compactSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_metricScalarAt_upper_bound_of_compactSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_metricScalarAt_upper_bound_of_compactSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_metricScalarAt_upper_bound_of_compactSpace

def TerminalLimitCompactLimitSpaceFrontier (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
      BoundedAtDistance X → TerminalDerivativeBounds X →
        ∀ P : MetricCompactLimit.{u, 0, 0} (I := I3) (X.toFlowSequence.atTime 0),
          (∀ k, P.convergence.metrics.domain k =
            CanonicalMetricCompactness.canonicalSourceData P.maps k) →
          (hconn : ConnectedSpace P.limit.M) → MetricSourceCapture P.maps →
          (∀ i, IsCompact (closure (P.maps.partialDiffeomorph i).source)) →
          (∀ i, IsConnected (P.maps.partialDiffeomorph i).source) →
          (∀ i, closure (P.maps.partialDiffeomorph i).source ⊆
            (P.maps.partialDiffeomorph (i + 1)).source) →
          (∃ o : TangentOrientationSection P.limit.M,
            ∀ i y, y ∈ (P.maps.partialDiffeomorph i).source →
              ∃ hf : Function.Bijective (mfderiv I3 I3 (P.maps.partialDiffeomorph i) y),
                PreservesTangentOrientationAt o (X.orientation (P.subseq i))
                  (P.maps.partialDiffeomorph i) y hf) →
          (∃ kappa' : ℝ, 0 < kappa' ∧ MetricNoncollapsed P.limit kappa' (Set.Ioc 0 1)) →
            CompactSpace P.limit.M

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalLimitCompactLimitSpaceFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalLimitCompactLimitSpaceFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalLimitCompactLimitSpaceFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalLimitCompactLimitSpaceFrontier

def TerminalLimitNoncompactScalarBoundFrontier (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
      BoundedAtDistance X → TerminalDerivativeBounds X →
        ∀ P : MetricCompactLimit.{u, 0, 0} (I := I3) (X.toFlowSequence.atTime 0),
          (∀ k, P.convergence.metrics.domain k =
            CanonicalMetricCompactness.canonicalSourceData P.maps k) →
          (hconn : ConnectedSpace P.limit.M) → MetricSourceCapture P.maps →
          (∀ i, IsCompact (closure (P.maps.partialDiffeomorph i).source)) →
          (∀ i, IsConnected (P.maps.partialDiffeomorph i).source) →
          (∀ i, closure (P.maps.partialDiffeomorph i).source ⊆
            (P.maps.partialDiffeomorph (i + 1)).source) →
          (∃ o : TangentOrientationSection P.limit.M,
            ∀ i y, y ∈ (P.maps.partialDiffeomorph i).source →
              ∃ hf : Function.Bijective (mfderiv I3 I3 (P.maps.partialDiffeomorph i) y),
                PreservesTangentOrientationAt o (X.orientation (P.subseq i))
                  (P.maps.partialDiffeomorph i) y hf) →
          (∃ kappa' : ℝ, 0 < kappa' ∧ MetricNoncollapsed P.limit kappa' (Set.Ioc 0 1)) →
          ¬ CompactSpace P.limit.M →
            ∃ C : ℝ, ∀ x, metricScalarAt P.limit.metric x ≤ C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalLimitNoncompactScalarBoundFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalLimitNoncompactScalarBoundFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalLimitNoncompactScalarBoundFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalLimitNoncompactScalarBoundFrontier

theorem terminal_limit_scalar_bound_frontier_of_compact_limits {kappa sigma : ℝ}
    {Phi : ℝ → ℝ} (h : TerminalLimitCompactLimitSpaceFrontier.{u} kappa sigma Phi) :
    TerminalLimitScalarBoundFrontier.{u} kappa sigma Phi := by
  obtain ⟨e, he, hmain⟩ := h
  exact ⟨e, he, fun eps heps hle X hb hd P hcanon hconn hcap hpre hcd hnested hor hnc =>
    @exists_metricScalarAt_upper_bound_of_compactSpace P.limit
      (hmain eps heps hle X hb hd P hcanon hconn hcap hpre hcd hnested hor hnc)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminal_limit_scalar_bound_frontier_of_compact_limits then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminal_limit_scalar_bound_frontier_of_compact_limits"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminal_limit_scalar_bound_frontier_of_compact_limits ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminal_limit_scalar_bound_frontier_of_compact_limits

theorem terminal_limit_scalar_bound_frontier_of_noncompact {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : TerminalLimitNoncompactScalarBoundFrontier.{u} kappa sigma Phi) :
    TerminalLimitScalarBoundFrontier.{u} kappa sigma Phi := by
  obtain ⟨e, he, hmain⟩ := h
  refine ⟨e, he, fun eps heps hle X hb hd P hcanon hconn hcap hpre hcd hnested hor hnc => ?_⟩
  by_cases hcompact : CompactSpace P.limit.M
  · exact @exists_metricScalarAt_upper_bound_of_compactSpace P.limit hcompact
  · exact hmain eps heps hle X hb hd P hcanon hconn hcap hpre hcd hnested hor hnc hcompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminal_limit_scalar_bound_frontier_of_noncompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminal_limit_scalar_bound_frontier_of_noncompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminal_limit_scalar_bound_frontier_of_noncompact ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminal_limit_scalar_bound_frontier_of_noncompact

theorem terminal_limit_global_bound_of_noncompact_frontier {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hPhi : AdmissiblePinchingFunction Phi)
    (hcompact : TerminalLimitCompactnessFrontier.{u} kappa sigma Phi)
    (hnoncompact : TerminalLimitNoncompactScalarBoundFrontier.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X → TerminalDerivativeBounds X → Nonempty (TerminalLimit X) :=
  terminal_limit_global_bound_of_frontiers hPhi hcompact
    (terminal_limit_scalar_bound_frontier_of_noncompact hnoncompact)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminal_limit_global_bound_of_noncompact_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminal_limit_global_bound_of_noncompact_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminal_limit_global_bound_of_noncompact_frontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminal_limit_global_bound_of_noncompact_frontier

def SlabLimitSpatialJets {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) (delta : ℝ) (hd : 0 < delta) : Prop :=
  ∀ g : ℝ → SmoothRiemannianMetric I3 L.space.M, IsSlabLimit L delta hd g →
    ∀ (p : L.space.M) (r : ℕ) (i j : Fin (Module.finrank ℝ ThreeSpace)),
      ContinuousOn (fun q : ℝ × ThreeSpace => iteratedFDeriv ℝ r
        (chartGramOnE (I := I3) (g q.1) p i j) q.2)
        (Set.Icc (-delta) 0 ×ˢ (extChartAt I3 p).target)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SlabLimitSpatialJets then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SlabLimitSpatialJets"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SlabLimitSpatialJets ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SlabLimitSpatialJets

theorem slabLimit_isSolutionOn_of_spatialJets {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) {delta : ℝ} {hd : 0 < delta}
    (hle : delta ≤ depthBound) (hjets : SlabLimitSpatialJets L delta hd) :
    SlabLimitIsFlow L delta hd :=
  fun g hlim => IsSlabLimit.isSolutionOn_of_spatialJets L hle hlim (hjets g hlim)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabLimit_isSolutionOn_of_spatialJets then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabLimit_isSolutionOn_of_spatialJets"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabLimit_isSolutionOn_of_spatialJets ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabLimit_isSolutionOn_of_spatialJets

def TerminalSlabJetInputs (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X),
      ∃ (depthBound delta : ℝ) (hdepth : depthBound ≤ 2 * modelDepth eps)
        (hb : TerminalSlabBounds L depthBound) (hd : 0 < delta),
        0 < depthBound ∧ delta ≤ depthBound ∧
          SlabLimitExists (L.toStatic hdepth hb) delta ∧
          SlabLimitSpatialJets (L.toStatic hdepth hb) delta hd ∧
          SlabLimitSliceGeometry (L.toStatic hdepth hb) delta hd ∧
          SlabLimitCurvatureBound (L.toStatic hdepth hb) delta hd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalSlabJetInputs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalSlabJetInputs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalSlabJetInputs ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalSlabJetInputs

theorem first_backward_slab_of_terminal_slab_jetInputs {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : TerminalSlabJetInputs.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X),
        ∃ delta : ℝ, ∃ hd : 0 < delta,
          Nonempty (BackwardExtension L (RealTimeInterval.closed (-delta) 0 (by linarith))) := by
  obtain ⟨e, he, hI⟩ := h
  refine ⟨e, he, fun eps heps hle X L => ?_⟩
  obtain ⟨depthBound, delta, hdepth, hb, hd, hdpos, hdle, hexists, hjets, hgeom, hcurv⟩ :=
    hI eps heps hle X L
  have hflow : SlabLimitIsFlow (L.toStatic hdepth hb) delta hd :=
    slabLimit_isSolutionOn_of_spatialJets _ hdle hjets
  exact first_backward_slab_of_terminal L hdepth hb
    ⟨delta, hd, hdle, hexists, hflow, hgeom, hcurv⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.first_backward_slab_of_terminal_slab_jetInputs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.first_backward_slab_of_terminal_slab_jetInputs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.first_backward_slab_of_terminal_slab_jetInputs ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.first_backward_slab_of_terminal_slab_jetInputs

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
