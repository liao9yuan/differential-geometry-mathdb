import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildComparisonMetric
import Submission.DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import Submission.DifferentialGeometry.Topology.Manifold.OpenEmbedding
import Submission.DifferentialGeometry.Geometry.Metric.DistancePullback

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace G N] [IsManifold I ∞ M] [IsManifold J ∞ N]

theorem riemannianCurveLength_comp_le_of_mapsTo
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N) (f : M → N)
    (U : Set M) {ell : ℝ}
    (hf : ∀ y ∈ U, ∀ z ∈ U, riemannianEDistOf h (f y) (f z) ≤
      ENNReal.ofReal ell * riemannianEDistOf g y z)
    (γ : ℝ → M) (a b : ℝ) (hγ : _root_.Set.MapsTo γ (_root_.Set.Icc a b) U) :
    riemannianCurveLength h (fun t => f (γ t)) a b ≤
      ENNReal.ofReal ell * riemannianCurveLength g γ a b := by
  exact DifferentialGeometry.Geometry.riemannianCurveVariation_comp_le_of_mapsTo g h f U hf γ a b hγ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_comp_le_of_mapsTo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_comp_le_of_mapsTo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_comp_le_of_mapsTo ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_comp_le_of_mapsTo

theorem curveLengthComparison_scaleMetric
    (g : SmoothRiemannianMetric I M) {ell : ℝ} (hell : 1 ≤ ell) (γ : ℝ → M) (a b : ℝ) :
    riemannianCurveLength (scaleMetric (I := I) (ell ^ 2)
        (pow_pos (lt_of_lt_of_le zero_lt_one hell) 2) g) γ a b ≤
      ENNReal.ofReal ell * riemannianCurveLength g γ a b := by
  rw [riemannianCurveLength_scaleMetric (ell ^ 2)
    (pow_pos (lt_of_lt_of_le zero_lt_one hell) 2) g γ a b, Real.sqrt_sq (zero_le_one.trans hell)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.curveLengthComparison_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.curveLengthComparison_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.curveLengthComparison_scaleMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.curveLengthComparison_scaleMetric

theorem edistComparison_scaleMetric
    (g : SmoothRiemannianMetric I M) {ell : ℝ} (hell : 1 ≤ ell) (y z : M) :
    riemannianEDistOf (scaleMetric (I := I) (ell ^ 2)
        (pow_pos (lt_of_lt_of_le zero_lt_one hell) 2) g) y z =
      ENNReal.ofReal ell * riemannianEDistOf g y z := by
  rw [DifferentialGeometry.edistOf_scale (ell ^ 2)
    (pow_pos (lt_of_lt_of_le zero_lt_one hell) 2) g y z, Real.sqrt_sq (zero_le_one.trans hell)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.edistComparison_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.edistComparison_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.edistComparison_scaleMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.edistComparison_scaleMetric

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)

theorem inclusion_edist_le (c : ConnectedComponents (H.stage i.succ).Carrier)
    (b : G.ChildBoundary c) (u v : (G.static b.1).witness.Output) :
    riemannianEDistOf (H.event i).outputMetric
        ((G.static b.1).inclusion u) ((G.static b.1).inclusion v) ≤
      riemannianEDistOf (G.static b.1).witness.metric u v := by
  have hld : IsLocalDiffeomorph ThreeModel ThreeModel ∞
      ((G.static b.1).inclusion : (G.static b.1).witness.Output →
        (H.stage i.succ).Carrier) := by
    obtain ⟨Q, hQng, hQns, hQimm⟩ := (G.static b.1).inclusion_smooth.isImmersion
    refine DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
      (G.static b.1).inclusion_smooth.contMDiff (fun x => ?_) (by simp)
    exact DifferentialGeometry.Topology.Manifold.injective_mfderiv_of_isImmersionAt
      ThreeModel ThreeModel _ x ⟨Q, hQng, hQns, hQimm x⟩
  have h := DifferentialGeometry.Geometry.Metric.edistOf_le_of_quad_of_localDiffeomorph
    (G.static b.1).witness.metric
    (H.event i).outputMetric
    ((G.static b.1).inclusion : (G.static b.1).witness.Output →
      (H.stage i.succ).Carrier) hld
    (c := 1) one_pos (fun x v => by
      simpa only [one_mul] using ((G.static b.1).inclusion_metric x v v).ge) u v
  simpa using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.inclusion_edist_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.inclusion_edist_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.inclusion_edist_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.inclusion_edist_le

def LocalEDistComparison
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    (s₀ : ℝ) (ell : ℝ → ℝ) : Prop :=
  ∀ c, ∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), ∀ x ∈ (Kc c).support.region,
    ∃ U ∈ 𝓝 x, ∀ y ∈ U, ∀ z ∈ U,
      riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
        ((Kc c).rfs_whole_parent_map y) ((Kc c).rfs_whole_parent_map z) ≤
      ENNReal.ofReal (ell s) * riemannianEDistOf
        ((H.stage i.castSucc).componentMetric
          ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) y z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.LocalEDistComparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.LocalEDistComparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.LocalEDistComparison ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.LocalEDistComparison

def LocalTerminalEDistComparison
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c) : Prop :=
  ∀ c, ∀ x ∈ (Kc c).support.region, ∃ U ∈ 𝓝 x,
    (∀ y ∈ U, y.1 ∈ (H.event i).incoming.terminalRegularRegion) ∧
    ∀ y ∈ U, ∀ z ∈ U,
      ∀ hy : y.1 ∈ (H.event i).incoming.terminalRegularRegion,
      ∀ hz : z.1 ∈ (H.event i).incoming.terminalRegularRegion,
      riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
        ((Kc c).rfs_whole_parent_map y) ((Kc c).rfs_whole_parent_map z) ≤
      riemannianEDistOf (H.event i).terminal.metric ⟨y.1, hy⟩ ⟨z.1, hz⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.LocalTerminalEDistComparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.LocalTerminalEDistComparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.LocalTerminalEDistComparison ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.LocalTerminalEDistComparison

def LocalTerminalParentEDistComparison
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    (s₀ : ℝ) (ell : ℝ → ℝ) : Prop :=
  ∀ c, ∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), ∀ x ∈ (Kc c).support.region, ∃ U ∈ 𝓝 x,
    (∀ y ∈ U, y.1 ∈ (H.event i).incoming.terminalRegularRegion) ∧
    ∀ y ∈ U, ∀ z ∈ U,
      ∀ hy : y.1 ∈ (H.event i).incoming.terminalRegularRegion,
      ∀ hz : z.1 ∈ (H.event i).incoming.terminalRegularRegion,
      riemannianEDistOf (H.event i).terminal.metric ⟨y.1, hy⟩ ⟨z.1, hz⟩ ≤
      ENNReal.ofReal (ell s) * riemannianEDistOf
        ((H.stage i.castSucc).componentMetric
          ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) y z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.LocalTerminalParentEDistComparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.LocalTerminalParentEDistComparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.LocalTerminalParentEDistComparison ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.LocalTerminalParentEDistComparison

theorem localEDistComparison_of_terminal_comparisons
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    {s₀ : ℝ} {ell : ℝ → ℝ}
    (hcollapse : G.LocalTerminalEDistComparison Kc)
    (hconvergence : G.LocalTerminalParentEDistComparison Kc s₀ ell) :
    G.LocalEDistComparison Kc s₀ ell := by
  intro c s hs x hx
  obtain ⟨U, hU, hterm, hU'⟩ := hcollapse c x hx
  obtain ⟨V, hV, hterm', hV'⟩ := hconvergence c s hs x hx
  exact ⟨U ∩ V, Filter.inter_mem hU hV, fun y hy z hz =>
    (hU' y hy.1 z hz.1 (hterm y hy.1) (hterm z hz.1)).trans
      (hV' y hy.2 z hz.2 (hterm' y hy.2) (hterm' z hz.2))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.localEDistComparison_of_terminal_comparisons then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.localEDistComparison_of_terminal_comparisons"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.localEDistComparison_of_terminal_comparisons ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.localEDistComparison_of_terminal_comparisons

theorem localLengthComparison_of_localEDistComparison
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    {s₀ : ℝ} (hs₀ : s₀ ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ)) {ell : ℝ → ℝ}
    (hlocal : G.LocalEDistComparison Kc s₀ ell)
    (hell : ∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), 1 ≤ ell s)
    (htend : Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1)) :
    G.LocalLengthComparison Kc := by
  refine ⟨s₀, hs₀, ell, hell, htend, ?_⟩
  intro c s hs x hx
  obtain ⟨U, hU, hU'⟩ := hlocal c s hs x hx
  exact ⟨U, hU, fun a b γ _ _ hmap _ =>
    riemannianCurveLength_comp_le_of_mapsTo _ _ _ U hU' γ a b hmap⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.localLengthComparison_of_localEDistComparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.localLengthComparison_of_localEDistComparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.localLengthComparison_of_localEDistComparison ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.localLengthComparison_of_localEDistComparison

theorem localLengthComparison_of_terminal_comparisons
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    {s₀ : ℝ} (hs₀ : s₀ ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ)) {ell : ℝ → ℝ}
    (hcollapse : G.LocalTerminalEDistComparison Kc)
    (hconvergence : G.LocalTerminalParentEDistComparison Kc s₀ ell)
    (hell : ∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), 1 ≤ ell s)
    (htend : Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1)) :
    G.LocalLengthComparison Kc :=
  G.localLengthComparison_of_localEDistComparison Kc hs₀
    (G.localEDistComparison_of_terminal_comparisons Kc hcollapse hconvergence) hell htend

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.localLengthComparison_of_terminal_comparisons then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.localLengthComparison_of_terminal_comparisons"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.localLengthComparison_of_terminal_comparisons ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.localLengthComparison_of_terminal_comparisons

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
