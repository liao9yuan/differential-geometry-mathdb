import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StaticSurfaceSelectedInjectivity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StaticSurfaceLineContradiction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalMetricCompactness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.Measure _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

private local instance staticCompactnessC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.staticCompactnessC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.staticCompactnessC1 target :: scope.openDecls } }
private local instance staticCompactnessMeasurable : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.staticCompactnessMeasurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.staticCompactnessMeasurable target :: scope.openDecls } }
private local instance staticCompactnessBorel : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.staticCompactnessBorel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.staticCompactnessBorel target :: scope.openDecls } }

variable (g : SmoothRiemannianMetric I M)
  (hjets : ∀ A : ℝ, 0 < A → ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (q : M) (r : ℝ) (hQ : 0 < metricScalarAt (I := I) g q),
      (∀ z, (riemannianEDistOf (I := I) g z q).toReal < r →
        metricScalarAt (I := I) g z ≤ 4 * metricScalarAt (I := I) g q) →
      A + 1 / 2 < r * Real.sqrt (metricScalarAt (I := I) g q) →
      ∀ y : M,
        riemannianEDistOf (I := I) (scaleMetric (metricScalarAt (I := I) g q) hQ g)
          q y ≤ ENNReal.ofReal A →
        curvDerivNorm (I := I) m (scaleMetric (metricScalarAt (I := I) g q) hQ g) y ≤ C)

include hjets


theorem exists_staticScalarNormalized_metric_compactness
    (hg : RiemannianMetricComplete (I := I) g)
    (x : ℕ → M) (r : ℕ → ℝ) (hQ : ∀ i, 0 < metricScalarAt (I := I) g (x i))
    (hlocal : ∀ i z, (riemannianEDistOf (I := I) g z (x i)).toReal < r i →
      metricScalarAt (I := I) g z ≤ 4 * metricScalarAt (I := I) g (x i))
    (hexpand : _root_.Filter.Tendsto (fun i => r i * Real.sqrt (metricScalarAt (I := I) g (x i)))
      _root_.Filter.atTop _root_.Filter.atTop)
    (hinj : BaseInjBound (I := I)
      (spatialRescaledPointedSeq g x
        (fun i => Real.sqrt (metricScalarAt (I := I) g (x i)))
        (fun i => Real.sqrt_pos.mpr (hQ i)))) :
    ∃ P : MetricCompactLimit (I := I)
      (spatialRescaledPointedSeq g x
        (fun i => Real.sqrt (metricScalarAt (I := I) g (x i)))
        (fun i => Real.sqrt_pos.mpr (hQ i))),
      (∀ k, P.convergence.metrics.domain k =
        CanonicalMetricCompactness.canonicalSourceData P.maps k) ∧
      (let _ : TopologicalSpace P.limit.M := P.limit.topology
       ConnectedSpace P.limit.M) := by
  let lam := fun i => Real.sqrt (metricScalarAt (I := I) g (x i))
  let hlam : ∀ i, 0 < lam i := fun i => Real.sqrt_pos.mpr (hQ i)
  let X := spatialRescaledPointedSeq g x lam hlam
  have hcomplete : SeqMetricComplete (I := I) X :=
    spatialRescaledPointedSeq_complete g hg x lam hlam
  have hlocalJets : ∀ A : ℝ, 0 < A → ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ i in _root_.Filter.atTop, ∀ y : M,
        riemannianEDistOf (I := I) (X.obj i).metric (x i) y ≤ ENNReal.ofReal A →
        curvDerivNorm (I := I) m (X.obj i).metric y ≤ C := by
    intro A hA m
    obtain ⟨C, hC, hbound⟩ := hjets A hA m
    refine ⟨C, hC, ?_⟩
    filter_upwards [hexpand.eventually_gt_atTop (A + 1 / 2)] with i hi
    intro y hy
    have hmetric : (X.obj i).metric = scaleMetric (metricScalarAt (I := I) g (x i))
        (hQ i) g := by
      change scaleMetric (Real.sqrt (metricScalarAt (I := I) g (x i)) ^ 2)
        (sq_pos_of_pos (Real.sqrt_pos.mpr (hQ i))) g = _
      congr 1
      exact Real.sq_sqrt (hQ i).le
    rw [hmetric] at hy ⊢
    exact hbound (x i) (r i) (hQ i) (hlocal i) hi y hy
  obtain ⟨P, hcanonical, _hreference, hconnected⟩ :=
    exists_local_pointed_metric_compactness X hcomplete
      (spatialRescaledPointedSeq_connected g x lam hlam) hinj hlocalJets
  exact ⟨P, hcanonical, hconnected⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_staticScalarNormalized_metric_compactness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_staticScalarNormalized_metric_compactness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_staticScalarNormalized_metric_compactness ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_staticScalarNormalized_metric_compactness


theorem static_surface_scalar_bddAbove_of_local_normalized_jets
    (hg : RiemannianMetricComplete (I := I) g) (hdim : Module.finrank ℝ E = 2)
    (hnonneg : ∀ z, 0 ≤ metricScalarAt (I := I) g z)
    (hsec : ∀ z, metricRm04At (I := I) g z ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (kappa : ℝ) (hkappa : 0 < kappa)
    (hnc : ∀ (p : M) (rho : ℝ), 0 < rho →
      (∀ z ∈ riemannianBallOf (I := I) g p rho,
        rho ^ 4 * Tensor0SBundle.normSq0S (I := I) g z 4
          (metricRm04At (I := I) g z) ≤ 1) →
      ENNReal.ofReal kappa * ENNReal.ofReal rho ^ Module.finrank ℝ E ≤
        riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf (I := I) g p rho)) :
    BddAbove (Set.range (metricScalarAt (I := I) g)) := by
  classical
  by_contra hunbounded
  let p : M := Classical.choice (inferInstance : Nonempty M)
  obtain ⟨x, r, hQ, _hr, _hQescape, hexpand, hdist, hscaled, hlocal, ⟨hinj⟩, _hbase⟩ :=
    exists_static_surface_blowup_with_baseInjBound g hg hdim hnonneg hsec
      kappa hkappa hnc hunbounded p
  obtain ⟨P, hcanonical, hconnected⟩ := exists_staticScalarNormalized_metric_compactness
    g hjets hg x r hQ hlocal hexpand hinj
  exact false_of_static_surface_scalar_normalized_compactness g hg hdim hsec
    p x hQ hdist hscaled P hcanonical hconnected

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.static_surface_scalar_bddAbove_of_local_normalized_jets then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.static_surface_scalar_bddAbove_of_local_normalized_jets"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.static_surface_scalar_bddAbove_of_local_normalized_jets ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.static_surface_scalar_bddAbove_of_local_normalized_jets

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
