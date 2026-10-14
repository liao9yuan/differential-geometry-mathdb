import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildComparisonCompactSupport
import Submission.DifferentialGeometry.Geometry.Metric.CurveVariation.Restriction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildTerminalDistance
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalRegionConvexity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)

private theorem local_length_comparison_of_local_terminal_edist_comparison
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    (hcollapse : G.LocalTerminalEDistComparison Kc) :
    G.LocalLengthComparison Kc := by
  obtain ⟨K, hK, hsupport, d, hd, ell, hell, htend, hquad⟩ :=
    G.exists_compact_comparison_support_quad_modulus Kc
  refine ⟨d, hd, ell, hell, htend, ?_⟩
  intro c s hs x hx
  obtain ⟨V, hV, hterm, hcollapseV⟩ := hcollapse c x hx
  let U : Set (G.Parent c).Carrier :=
    Subtype.val ⁻¹' (Subtype.val '' interior K)
  have hU : IsOpen U :=
    ((H.event i).incoming.terminalRegularRegion_isOpen.isOpenMap_subtype_val
      (interior K) isOpen_interior).preimage continuous_subtype_val
  have hxU : x ∈ U := ⟨⟨x.1, (Kc c).support_terminal x hx⟩, hsupport c x hx, rfl⟩
  refine ⟨U ∩ V, Filter.inter_mem (hU.mem_nhds hxU) hV, ?_⟩
  intro a b γ hab hγ hmap hfin
  let γT : ℝ → (H.event i).incoming.terminalRegularOpen := fun t =>
    ⟨(γ (_root_.Set.projIcc a b hab t)).1,
      hterm (γ (_root_.Set.projIcc a b hab t)) (hmap (_root_.Set.projIcc a b hab t).property).2⟩
  have hγT : Continuous γT := by
    apply Continuous.subtype_mk
    exact ((continuous_subtype_val.comp_continuousOn hγ).domRestrict).comp
      continuous_projIcc
  have hγeq (t : ℝ) (ht : t ∈ _root_.Set.Icc a b) : (γT t).1 = (γ t).1 := by
    simp only [γT, _root_.Set.projIcc_of_mem, ht]
  have hγK : _root_.Set.MapsTo γT (_root_.Set.Icc a b) (interior K) := by
    intro t ht
    obtain ⟨z, hz, heq⟩ := (hmap ht).1
    have heq' : γT t = z := Subtype.ext ((hγeq t ht).trans heq.symm)
    exact heq' ▸ hz
  have hlength : riemannianCurveLength
      ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
      (fun t => (Kc c).rfs_whole_parent_map (γ t)) a b ≤
        riemannianCurveLength (H.event i).terminal.metric γT a b := by
    unfold riemannianCurveLength
    apply iSup_le
    intro p
    refine (Finset.sum_le_sum fun j hj => ?_).trans
      (le_iSup (f := fun q : ℕ × {v : ℕ → ℝ // Monotone v ∧ ∀ j, v j ∈ _root_.Set.Icc a b} =>
        ∑ j ∈ Finset.range q.1,
          riemannianEDistOf (H.event i).terminal.metric
            (γT (q.2.1 (j + 1))) (γT (q.2.1 j))) p)
    have ht₁ := p.2.2.2 (j + 1)
    have ht₀ := p.2.2.2 j
    have hb := hcollapseV (γ (p.2.1 (j + 1))) (hmap ht₁).2
      (γ (p.2.1 j)) (hmap ht₀).2
      (hterm _ (hmap ht₁).2) (hterm _ (hmap ht₀).2)
    convert hb using 1 <;> congr 1 <;> apply Subtype.ext <;>
      simp only [γT, _root_.Set.projIcc_of_mem, ht₀, ht₁]
  have hmetric : riemannianCurveLength (H.event i).terminal.metric γT a b ≤
      ENNReal.ofReal (ell s) * riemannianCurveLength
        (((H.event i).incoming.flow.base.metric s).restrictOpen
          (H.event i).incoming.terminalRegularOpen) γT a b := by
    have hb := DifferentialGeometry.Geometry.riemannianCurveVariation_le_of_quad_on
      (((H.event i).incoming.flow.base.metric s).restrictOpen
        (H.event i).incoming.terminalRegularOpen) (H.event i).terminal.metric
      (⟨interior K, isOpen_interior⟩ : TopologicalSpace.Opens
        (H.event i).incoming.terminalRegularOpen)
      (c := (ell s) ^ 2) (sq_pos_of_pos (lt_of_lt_of_le zero_lt_one (hell s hs)))
      (fun y hy v => hquad s hs y (interior_subset hy) v)
      hγT.continuousOn hγK
    simpa only [riemannianCurveLength, DifferentialGeometry.Geometry.riemannianCurveVariation,
      Real.sqrt_sq (zero_le_one.trans (hell s hs))] using hb
  have hincoming : riemannianCurveLength
      (((H.event i).incoming.flow.base.metric s).restrictOpen
        (H.event i).incoming.terminalRegularOpen) γT a b =
      riemannianCurveLength ((H.stage i.castSucc).componentMetric
        ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) γ a b := by
    change DifferentialGeometry.Geometry.riemannianCurveVariation
      (((H.event i).incoming.flow.base.metric s).restrictOpen
        (H.event i).incoming.terminalRegularOpen) γT a b =
      DifferentialGeometry.Geometry.riemannianCurveVariation ((H.stage i.castSucc).componentMetric
        ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) γ a b
    rw [DifferentialGeometry.Geometry.riemannianCurveVariation_restrictOpen _ _ _ _ _ hγT.continuousOn]
    have hcongr := DifferentialGeometry.Geometry.riemannianCurveVariation_congr ((H.event i).incoming.flow.base.metric s)
      (show _root_.Set.EqOn (Subtype.val ∘ γT) (Subtype.val ∘ γ) (_root_.Set.Icc a b) from hγeq)
    rw [hcongr]
    unfold DifferentialGeometry.Geometry.riemannianCurveVariation
    simp only [OrientedThreeStage.edistOf_componentMetric]
    rfl
  exact hlength.trans (by simpa only [hincoming] using hmetric)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.local_length_comparison_of_local_terminal_edist_comparison
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.local_length_comparison_of_local_terminal_edist_comparison target :: scope.openDecls } }


theorem local_length_comparison
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c) :
    G.LocalLengthComparison Kc :=
  G.local_length_comparison_of_local_terminal_edist_comparison Kc
    (G.local_terminal_edist_comparison Kc)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.local_length_comparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.local_length_comparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.local_length_comparison ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.local_length_comparison

theorem child_comparison_metric
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c) :
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
              ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y :=
  G.rfs_child_comparison_metric_of_local_length_comparison Kc (G.local_length_comparison Kc)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.child_comparison_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.child_comparison_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.child_comparison_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.child_comparison_metric

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
