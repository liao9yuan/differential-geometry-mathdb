import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.MinimizingLensAngle
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Topology
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.Filter _root_.Set _root_.Submission.Set
open scoped _root_.Topology _root_.Submission.Topology _root_.ContDiff
namespace DifferentialGeometry.Geometry.Comparison.Toponogov

private theorem eventually_lt_comparisonAngle_of_compact_distance_lenses
    {M : Type*} [PseudoMetricSpace M] {K : Set M} (hK : IsCompact K)
    (y p z : M) (u v : ℕ → M) (c : ℕ → ℝ) {r θ θ' : ℝ} (hr : 0 < r)
    (hmem : ∀ᶠ i in _root_.Filter.atTop, u i ∈ K ∧ v i ∈ K)
    (hyu : _root_.Filter.Tendsto (fun i => _root_.Dist.dist y (u i)) _root_.Filter.atTop (𝓝 r))
    (hyv : _root_.Filter.Tendsto (fun i => _root_.Dist.dist y (v i)) _root_.Filter.atTop (𝓝 r))
    (hup : _root_.Filter.Tendsto (fun i => _root_.Dist.dist (u i) p) _root_.Filter.atTop (𝓝 (_root_.Dist.dist y p - r)))
    (hvz : _root_.Filter.Tendsto (fun i => _root_.Dist.dist (v i) z) _root_.Filter.atTop (𝓝 (_root_.Dist.dist y z - r)))
    (hc : _root_.Filter.Tendsto (fun i => c i - _root_.Dist.dist (u i) (v i)) _root_.Filter.atTop (𝓝 0))
    (hcompare : ∀ q ∈ K, ∀ w ∈ K,
      _root_.Dist.dist y q = r → _root_.Dist.dist y w = r →
      _root_.Dist.dist q p = _root_.Dist.dist y p - r → _root_.Dist.dist w z = _root_.Dist.dist y z - r →
      θ ≤ comparisonAngle r r (_root_.Dist.dist q w))
    (hθ : θ' < θ) :
    ∀ᶠ i in _root_.Filter.atTop, θ' < comparisonAngle r r (c i) := by
  by_contra h
  have hbad : ∃ᶠ i in _root_.Filter.atTop, comparisonAngle r r (c i) ≤ θ' := by
    simpa only [_root_.Filter.not_eventually, not_lt] using h
  obtain ⟨ψ, hψ, hψbad⟩ := _root_.Filter.extraction_of_frequently_atTop hbad
  have hpair : ∀ᶠ i in _root_.Filter.atTop, (u (ψ i), v (ψ i)) ∈ K ×ˢ K :=
    hψ.tendsto_atTop.eventually hmem
  obtain ⟨qw, hqw, φ, hφ, hlim⟩ := (hK.prod hK).tendsto_subseq' hpair.frequently
  let χ := ψ ∘ φ
  have hχ : _root_.Filter.Tendsto χ _root_.Filter.atTop atTop := hψ.tendsto_atTop.comp hφ.tendsto_atTop
  have hu : _root_.Filter.Tendsto (u ∘ χ) _root_.Filter.atTop (𝓝 qw.1) :=
    (continuous_fst.tendsto qw).comp hlim
  have hv : _root_.Filter.Tendsto (v ∘ χ) _root_.Filter.atTop (𝓝 qw.2) :=
    (continuous_snd.tendsto qw).comp hlim
  have hyq : _root_.Dist.dist y qw.1 = r :=
    tendsto_nhds_unique (tendsto_const_nhds.dist hu) (hyu.comp hχ)
  have hyw : _root_.Dist.dist y qw.2 = r :=
    tendsto_nhds_unique (tendsto_const_nhds.dist hv) (hyv.comp hχ)
  have hqp : _root_.Dist.dist qw.1 p = _root_.Dist.dist y p - r :=
    tendsto_nhds_unique (hu.dist tendsto_const_nhds) (hup.comp hχ)
  have hwz : _root_.Dist.dist qw.2 z = _root_.Dist.dist y z - r :=
    tendsto_nhds_unique (hv.dist tendsto_const_nhds) (hvz.comp hχ)
  have hcχ : _root_.Filter.Tendsto (c ∘ χ) _root_.Filter.atTop (𝓝 (_root_.Dist.dist qw.1 qw.2)) := by
    have hh := (hc.comp hχ).add (hu.dist hv)
    simpa only [Function.comp_def, sub_add_cancel, zero_add] using hh
  have hangle := tendsto_comparisonAngle tendsto_const_nhds tendsto_const_nhds hcχ hr hr
  have hle : comparisonAngle r r (_root_.Dist.dist qw.1 qw.2) ≤ θ' := by
    apply le_of_tendsto hangle
    exact Eventually.of_forall fun i => hψbad (φ i)
  exact (not_lt_of_ge ((hcompare qw.1 hqw.1 qw.2 hqw.2 hyq hyw hqp hwz).trans hle)) hθ

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.eventually_lt_comparisonAngle_of_compact_distance_lenses
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Comparison.Toponogov.eventually_lt_comparisonAngle_of_compact_distance_lenses target :: scope.openDecls } }


theorem eventually_lt_comparisonAngle_of_compact_riemannian_distance_lenses
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ThreeSpace M]
    [IsManifold DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.I3 ∞ M]
    [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.I3 M)
    (hcomplete : RiemannianMetricComplete g)
    (hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature g)
    {K : Set M} (hK : IsCompact K)
    (y p z : M) (u v : ℕ → M) (c : ℕ → ℝ) {r θ : ℝ} (hr : 0 < r)
    (hrp : r < (riemannianEDistOf g y p).toReal)
    (hrz : r < (riemannianEDistOf g y z).toReal)
    (hmem : ∀ᶠ i in _root_.Filter.atTop, u i ∈ K ∧ v i ∈ K)
    (hyu : _root_.Filter.Tendsto (fun i => (riemannianEDistOf g y (u i)).toReal) _root_.Filter.atTop (𝓝 r))
    (hyv : _root_.Filter.Tendsto (fun i => (riemannianEDistOf g y (v i)).toReal) _root_.Filter.atTop (𝓝 r))
    (hup : _root_.Filter.Tendsto (fun i => (riemannianEDistOf g (u i) p).toReal)
      _root_.Filter.atTop (𝓝 ((riemannianEDistOf g y p).toReal - r)))
    (hvz : _root_.Filter.Tendsto (fun i => (riemannianEDistOf g (v i) z).toReal)
      _root_.Filter.atTop (𝓝 ((riemannianEDistOf g y z).toReal - r)))
    (hc : _root_.Filter.Tendsto (fun i => c i - (riemannianEDistOf g (u i) (v i)).toReal) _root_.Filter.atTop (𝓝 0))
    (hθ : θ < comparisonAngle (riemannianEDistOf g y p).toReal
      (riemannianEDistOf g y z).toReal (riemannianEDistOf g p z).toReal) :
    ∀ᶠ i in _root_.Filter.atTop, θ < comparisonAngle r r (c i) := by
  let : TopologicalSpace.MetrizableSpace M :=
    Manifold.metrizableSpace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.I3 M
  let : RegularSpace M := inferInstance
  let : PseudoMetricSpace M := g.toPseudoMetricSpace
  exact eventually_lt_comparisonAngle_of_compact_distance_lenses hK y p z u v c hr
    hmem hyu hyv hup hvz hc (fun q _ w _ hq hw hqp hwz =>
      DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.comparisonAngle_le_of_equal_radius_minimizing_lenses
        g hcomplete hsec y p z q w hr hrp hrz hq hw hqp hwz) hθ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Comparison.Toponogov.eventually_lt_comparisonAngle_of_compact_riemannian_distance_lenses then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Comparison.Toponogov.eventually_lt_comparisonAngle_of_compact_riemannian_distance_lenses"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Comparison.Toponogov.eventually_lt_comparisonAngle_of_compact_riemannian_distance_lenses ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.eventually_lt_comparisonAngle_of_compact_riemannian_distance_lenses

end DifferentialGeometry.Geometry.Comparison.Toponogov
