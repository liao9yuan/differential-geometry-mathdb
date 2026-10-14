import Submission.DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.ENNReal _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Toponogov

open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]

structure RealizedMinimizingConnector
    (g : SmoothRiemannianMetric I M) (p q : M) where
  curve : ℝ → M
  length : ℝ
  length_nonneg : 0 ≤ length
  source : curve 0 = p
  target : curve length = q
  smooth : ContMDiffOn 𝓘(ℝ, ℝ) I 1 curve (Set.Icc 0 length)
  geodesic : IsGeodesicOn (I := I) g curve (Set.Icc 0 length)
  unitSpeed : ∀ t ∈ Set.Ioo (0 : ℝ) length,
    g.inner (curve t) (mfderiv 𝓘(ℝ, ℝ) I curve t 1)
        (mfderiv 𝓘(ℝ, ℝ) I curve t 1) = 1
  realizes : riemannianEDistOf (I := I) g p q = ENNReal.ofReal length

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.RealizedMinimizingConnector then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.RealizedMinimizingConnector"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.RealizedMinimizingConnector ``Submission.DifferentialGeometry.Toponogov.RealizedMinimizingConnector

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem RealizedMinimizingConnector.constant_on_of_length_eq_zero
    {g : SmoothRiemannianMetric I M} {p q : M}
    (c : RealizedMinimizingConnector (I := I) g p q)
    (hc : c.length = 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) c.length, c.curve t = p := by
  intro t ht
  have ht0 : t = 0 := by
    rw [hc] at ht
    exact le_antisymm ht.2 ht.1
  simpa [ht0] using c.source

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Toponogov.RealizedMinimizingConnector
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.RealizedMinimizingConnector.constant_on_of_length_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.RealizedMinimizingConnector.constant_on_of_length_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.RealizedMinimizingConnector.constant_on_of_length_eq_zero ``Submission.DifferentialGeometry.Toponogov.RealizedMinimizingConnector.constant_on_of_length_eq_zero

def RealizedConnectors (g : SmoothRiemannianMetric I M) (p : M)
    (β : ℝ → M) (J : Set ℝ) : Prop :=
  ∀ r ∈ J, Nonempty (RealizedMinimizingConnector (I := I) g p (β r))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.RealizedConnectors then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.RealizedConnectors"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.RealizedConnectors ``Submission.DifferentialGeometry.Toponogov.RealizedConnectors

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem RealizedConnectors.exists_connector
    {g : SmoothRiemannianMetric I M} {p : M} {β : ℝ → M} {J : Set ℝ}
    (h : RealizedConnectors (I := I) g p β J) {r : ℝ} (hr : r ∈ J) :
    Nonempty (RealizedMinimizingConnector (I := I) g p (β r)) :=
  h r hr

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Toponogov.RealizedConnectors
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.RealizedConnectors.exists_connector then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.RealizedConnectors.exists_connector"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.RealizedConnectors.exists_connector ``Submission.DifferentialGeometry.Toponogov.RealizedConnectors.exists_connector

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem RealizedConnectors.mono
    {g : SmoothRiemannianMetric I M} {p : M} {β : ℝ → M} {J K : Set ℝ}
    (h : RealizedConnectors (I := I) g p β J) (hKJ : K ⊆ J) :
    RealizedConnectors (I := I) g p β K := by
  intro r hr
  exact h r (hKJ hr)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.RealizedConnectors.mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.RealizedConnectors.mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.RealizedConnectors.mono ``Submission.DifferentialGeometry.Toponogov.RealizedConnectors.mono

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem nonempty_realizedMinimizingConnector_of_complete
    [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (p q : M) :
    Nonempty (RealizedMinimizingConnector (I := I) g p q) := by
  let : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let : TopologicalSpace.MetrizableSpace M :=
    Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : _root_.Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : PseudoEMetricSpace M :=
    (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
  let : CompleteSpace M := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) (M := M) g := by
    intro x v
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  obtain ⟨γ, L, hL, hγ0, hγL, hγsmooth, hγgeo, hγunit, hdist⟩ :=
    exists_unit_speed_minimizing_geodesic_between_points
      (I := I) (M := M) g hEnorm p q
  refine ⟨⟨γ, L, hL, hγ0, hγL, hγsmooth, hγgeo, hγunit, ?_⟩⟩
  simpa only [riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm] using hdist

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.nonempty_realizedMinimizingConnector_of_complete then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.nonempty_realizedMinimizingConnector_of_complete"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.nonempty_realizedMinimizingConnector_of_complete ``Submission.DifferentialGeometry.Toponogov.nonempty_realizedMinimizingConnector_of_complete

theorem realizedConnectors_of_complete
    [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (p : M) (β : ℝ → M) (J : Set ℝ) :
    RealizedConnectors (I := I) g p β J := by
  intro r _
  exact nonempty_realizedMinimizingConnector_of_complete
    (I := I) g hcomplete p (β r)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.realizedConnectors_of_complete then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.realizedConnectors_of_complete"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.realizedConnectors_of_complete ``Submission.DifferentialGeometry.Toponogov.realizedConnectors_of_complete

end DifferentialGeometry.Toponogov
