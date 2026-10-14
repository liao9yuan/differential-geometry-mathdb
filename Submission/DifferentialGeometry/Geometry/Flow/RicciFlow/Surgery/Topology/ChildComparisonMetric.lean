import Submission.DifferentialGeometry.Geometry.Metric.CurveVariation.Comparison
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Comparison

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem riemannianCurveLength_le_of_quad (g h : SmoothRiemannianMetric I M) {c : ℝ}
    (hc : 0 < c) (hgh : ∀ x v, h.inner x v v ≤ c * g.inner x v v)
    (γ : ℝ → M) (a b : ℝ) :
    riemannianCurveLength h γ a b ≤
      ENNReal.ofReal (Real.sqrt c) * riemannianCurveLength g γ a b := by
  exact DifferentialGeometry.Geometry.riemannianCurveVariation_le_of_quad g h hc hgh γ a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_le_of_quad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_le_of_quad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_le_of_quad ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_le_of_quad
theorem le_riemannianCurveLength_of_quad (g h : SmoothRiemannianMetric I M) {c : ℝ}
    (hc : 0 < c) (hl : ∀ x v, c * g.inner x v v ≤ h.inner x v v)
    (γ : ℝ → M) (a b : ℝ) :
    ENNReal.ofReal (Real.sqrt c) * riemannianCurveLength g γ a b ≤
      riemannianCurveLength h γ a b := by
  exact DifferentialGeometry.Geometry.le_riemannianCurveVariation_of_quad g h hc hl γ a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.le_riemannianCurveLength_of_quad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.le_riemannianCurveLength_of_quad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.le_riemannianCurveLength_of_quad ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.le_riemannianCurveLength_of_quad
theorem riemannianCurveLength_scaleMetric (c : ℝ) (hc : 0 < c)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (a b : ℝ) :
    riemannianCurveLength (scaleMetric (I := I) c hc g) γ a b =
      ENNReal.ofReal (Real.sqrt c) * riemannianCurveLength g γ a b := by
  exact DifferentialGeometry.Geometry.riemannianCurveVariation_scaleMetric c hc g γ a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_scaleMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_scaleMetric

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)

def LocalLengthComparison
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c) : Prop :=
  ∃ s₀ ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
    (∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
    Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
    ∀ c, ∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), ∀ x ∈ (Kc c).support.region,
      ∃ U ∈ 𝓝 x, ∀ (a b : ℝ) (γ : ℝ → (G.Parent c).Carrier),
        a ≤ b → ContinuousOn γ (_root_.Set.Icc a b) → _root_.Set.MapsTo γ (_root_.Set.Icc a b) U →
        riemannianCurveLength ((H.stage i.castSucc).componentMetric
          ((H.event i).incoming.flow.base.metric s)
          (G.transition.childParent c)) γ a b ≠ ⊤ →
        riemannianCurveLength
          ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
          (fun t => (Kc c).rfs_whole_parent_map (γ t)) a b ≤
        ENNReal.ofReal (ell s) * riemannianCurveLength
          ((H.stage i.castSucc).componentMetric
            ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) γ a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.LocalLengthComparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.LocalLengthComparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.LocalLengthComparison ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.LocalLengthComparison

theorem rfs_child_comparison_metric_of_local_length_comparison
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    (hlocal : G.LocalLengthComparison Kc) :
    ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
        C((G.Parent c).Carrier, (G.Child c).Carrier),
      (∀ c, f c = (Kc c).rfs_whole_parent_map) ∧
      ∃ s₀ ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
        (∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
        Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
        ∀ c, ∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
          riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
            (f c x) (f c y) ≤ ENNReal.ofReal (ell s) *
            riemannianEDistOf ((H.stage i.castSucc).componentMetric
              ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y := by
  obtain ⟨s₀, hs₀, ell, hell, htend, hloc⟩ := hlocal
  refine ⟨fun c => (Kc c).rfs_whole_parent_map, fun c => rfl, s₀, hs₀, ell, hell, htend, ?_⟩
  intro c s hs x y
  let gs : SmoothRiemannianMetric ThreeModel (G.Parent c).Carrier :=
    (H.stage i.castSucc).componentMetric ((H.event i).incoming.flow.base.metric s)
      (G.transition.childParent c)
  let hc : SmoothRiemannianMetric ThreeModel (G.Child c).Carrier :=
    (H.stage i.succ).componentMetric (H.event i).outputMetric c
  have hL : (0 : ℝ) ≤ ell s := le_trans zero_le_one (hell s hs)
  have hlocFull : ∀ x : (G.Parent c).Carrier, ∃ U ∈ 𝓝 x,
      ∀ (a b : ℝ) (γ : ℝ → (G.Parent c).Carrier),
        a ≤ b → ContinuousOn γ (_root_.Set.Icc a b) → _root_.Set.MapsTo γ (_root_.Set.Icc a b) U →
        riemannianCurveLength gs γ a b ≠ ⊤ →
        riemannianCurveLength hc (fun t => (Kc c).rfs_whole_parent_map (γ t)) a b ≤
          ENNReal.ofReal (ell s) * riemannianCurveLength gs γ a b := by
    intro x
    by_cases hx : x ∈ (Kc c).support.region
    · obtain ⟨U, hU, hU'⟩ := hloc c s hs x hx
      exact ⟨U, hU, hU'⟩
    · obtain ⟨U, hU, hconst⟩ := (Kc c).rfs_whole_parent_map_locallyConstant_of_notMem hx
      refine ⟨U, hU, fun a b γ hab hγ hmap hfin => ?_⟩
      have hone : ∀ t ∈ _root_.Set.Icc a b, (fun t => (Kc c).rfs_whole_parent_map (γ t)) t =
          (Kc c).rfs_whole_parent_map x :=
        fun t ht => hconst (γ t) (hmap ht)
      have hzero := riemannianCurveLength_eq_zero_of_apply_eq_const (g := hc)
        (γ := fun t => (Kc c).rfs_whole_parent_map (γ t))
        (a := a) (b := b) (q := (Kc c).rfs_whole_parent_map x) hone
      rw [hzero]
      exact bot_le
  let : SecondCountableTopology (G.Parent c).Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace (G.Parent c).Carrier
  let : SecondCountableTopology (G.Child c).Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace (G.Child c).Carrier
  by_cases hfin : riemannianEDistOf gs x y = ⊤
  · rw [hfin, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr
      (lt_of_lt_of_le (zero_lt_one : (0 : ℝ) < 1) (hell s hs))))]
    exact le_top
  · have hlocCoe : ∀ x : (G.Parent c).Carrier, ∃ U ∈ 𝓝 x,
        ∀ (a b : ℝ) (γ : ℝ → (G.Parent c).Carrier),
          a ≤ b → ContinuousOn γ (_root_.Set.Icc a b) → _root_.Set.MapsTo γ (_root_.Set.Icc a b) U →
          riemannianCurveLength gs γ a b ≠ ⊤ →
          riemannianCurveLength hc (fun t => (Kc c).rfs_whole_parent_map (γ t)) a b ≤
            ↑(NNReal.mk (ell s) hL) * riemannianCurveLength gs γ a b :=
      fun x => by
        obtain ⟨U, hU, hU'⟩ := hlocFull x
        exact ⟨U, hU, fun a b γ hab hγ hmap hfin => by
          simpa only [ENNReal.ofReal_eq_coe_nnreal hL] using hU' a b γ hab hγ hmap hfin⟩
    have h := rfs_local_to_global_length_of_ne_top gs hc
      ((Kc c).rfs_whole_parent_map) (NNReal.mk (ell s) hL) hlocCoe hfin
    rwa [ENNReal.ofReal_eq_coe_nnreal hL]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_metric_of_local_length_comparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_metric_of_local_length_comparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_metric_of_local_length_comparison ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_metric_of_local_length_comparison

theorem rfs_child_comparison_metric_of_exists_local_length_comparison
    (h : ∃ Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c,
      G.LocalLengthComparison Kc) :
    ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
        C((G.Parent c).Carrier, (G.Child c).Carrier),
      (∀ c, ∃ K : G.ComparisonSupport c, f c = K.rfs_whole_parent_map) ∧
      ∃ s₀ ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
        (∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
        Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
        ∀ c, ∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
          riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
            (f c x) (f c y) ≤ ENNReal.ofReal (ell s) *
            riemannianEDistOf ((H.stage i.castSucc).componentMetric
              ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y := by
  obtain ⟨Kc, hKc⟩ := h
  obtain ⟨f, hf, hrest⟩ := rfs_child_comparison_metric_of_local_length_comparison G Kc hKc
  exact ⟨f, fun c => ⟨Kc c, hf c⟩, hrest⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_metric_of_exists_local_length_comparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_metric_of_exists_local_length_comparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_metric_of_exists_local_length_comparison ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_metric_of_exists_local_length_comparison

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
