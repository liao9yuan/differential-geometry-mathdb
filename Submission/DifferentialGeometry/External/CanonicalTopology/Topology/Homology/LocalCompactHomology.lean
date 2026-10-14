import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.LocalCharts
import Mathlib.Topology.MetricSpace.ProperSpace
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.OpenExcision
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.LocalBallHomology

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.ContinuousMap _root_.Set _root_.Metric
open scoped _root_.Topology

universe u

namespace DifferentialGeometry.Topology

private theorem exists_chart_closedBall_neighborhood
    {X Y : Type u} [TopologicalSpace X] [MetricSpace Y] [ProperSpace Y]
    (e : OpenPartialHomeomorph X Y) (p : X) (hp : p ∈ e.source) :
    ∃ r : ℝ, 0 < r ∧ _root_.Metric.closedBall (e p) r ⊆ e.target ∧
      IsCompact (e.symm '' _root_.Metric.closedBall (e p) r) ∧
      e.symm '' _root_.Metric.closedBall (e p) r ⊆ e.source ∧
      p ∈ interior (e.symm '' _root_.Metric.closedBall (e p) r) := by
  obtain ⟨r, hr, hball⟩ := nhds_basis_closedBall.mem_iff.mp
    (e.open_target.mem_nhds (e.map_source hp))
  have hcompact : IsCompact (e.symm '' _root_.Metric.closedBall (e p) r) :=
    (_root_.ProperSpace.isCompact_closedBall (e p) r).image_of_continuousOn (e.symm.continuousOn.mono hball)
  have hsource : e.symm '' _root_.Metric.closedBall (e p) r ⊆ e.source := by
    rintro x ⟨y, hy, rfl⟩
    exact e.map_target (hball hy)
  have hopen : IsOpen (e.symm '' _root_.Metric.ball (e p) r) :=
    e.isOpen_image_symm_of_subset_target _root_.Metric.isOpen_ball (ball_subset_closedBall.trans hball)
  have hpball : p ∈ e.symm '' _root_.Metric.ball (e p) r :=
    ⟨e p, _root_.Metric.mem_ball_self hr, e.left_inv hp⟩
  exact ⟨r, hr, hball, hcompact, hsource,
    interior_maximal (_root_.Set.image_mono _root_.Metric.ball_subset_closedBall) hopen hpball⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.exists_chart_closedBall_neighborhood
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.exists_chart_closedBall_neighborhood target :: scope.openDecls } }

end DifferentialGeometry.Topology

end

noncomputable section

open _root_.CategoryTheory _root_.ContinuousMap _root_.Set

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

private theorem chart_inverse_image_subset_source (e : OpenPartialHomeomorph X Y)
    (L : Set Y) (hL : L ⊆ e.target) : e.symm '' L ⊆ e.source := by
  rintro x ⟨y, hy, rfl⟩
  exact e.map_target (hL hy)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.chart_inverse_image_subset_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.chart_inverse_image_subset_source target :: scope.openDecls } }

omit [TopologicalSpace X] in
private theorem complement_union_eq_univ_of_subset {K U : Set X} (h : K ⊆ U) :
    Kᶜ ∪ U = univ := by
  ext x
  simp only [_root_.Set.mem_union, _root_.Set.mem_compl_iff, _root_.Set.mem_univ, iff_true]
  by_cases hx : x ∈ K
  · exact Or.inr (h hx)
  · exact Or.inl hx

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.complement_union_eq_univ_of_subset
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.complement_union_eq_univ_of_subset target :: scope.openDecls } }

private theorem chart_pair_complement_mapsTo (e : OpenPartialHomeomorph X Y) (L : Set Y) :
    _root_.Set.MapsTo e.toHomeomorphSourceTarget
      (subspaceIntersection (e.symm '' L)ᶜ e.source)
      (subspaceIntersection Lᶜ e.target) := by
  intro x hx
  change x.val ∉ e.symm '' L at hx
  change e x.val ∉ L
  intro he
  exact hx ⟨e x.val, he, e.left_inv x.property⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.chart_pair_complement_mapsTo
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.chart_pair_complement_mapsTo target :: scope.openDecls } }

private theorem chart_pair_complement_symm_mapsTo (e : OpenPartialHomeomorph X Y)
    (L : Set Y) (hL : L ⊆ e.target) :
    _root_.Set.MapsTo e.toHomeomorphSourceTarget.symm
      (subspaceIntersection Lᶜ e.target)
      (subspaceIntersection (e.symm '' L)ᶜ e.source) := by
  intro y hy
  change y.val ∉ L at hy
  change e.symm y.val ∉ e.symm '' L
  rintro ⟨z, hz, heq⟩
  exact hy ((e.symm.injOn (hL hz) y.property heq) ▸ hz)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.chart_pair_complement_symm_mapsTo
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.chart_pair_complement_symm_mapsTo target :: scope.openDecls } }

variable [T2Space X] [T2Space Y]

def integralRelativeHomologyOpenPartialHomeomorphIso (n : ℕ)
    (e : OpenPartialHomeomorph X Y) (L : Set Y) (hL : IsCompact L) (hLt : L ⊆ e.target) :
    integralRelativeHomology n (e.symm '' L)ᶜ ≅ integralRelativeHomology n Lᶜ :=
  (integralRelativeOpenExcisionIso n (e.symm '' L)ᶜ e.source
    (hL.image_of_continuousOn (e.symm.continuousOn.mono hLt)).isClosed.isOpen_compl
    e.open_source
    (complement_union_eq_univ_of_subset (chart_inverse_image_subset_source e L hLt))).symm ≪≫
  integralRelativeHomologyHomeomorphIso n e.toHomeomorphSourceTarget
    (subspaceIntersection (e.symm '' L)ᶜ e.source)
    (subspaceIntersection Lᶜ e.target)
    (chart_pair_complement_mapsTo e L) (chart_pair_complement_symm_mapsTo e L hLt) ≪≫
  integralRelativeOpenExcisionIso n Lᶜ e.target hL.isClosed.isOpen_compl e.open_target
    (complement_union_eq_univ_of_subset hLt)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeHomologyOpenPartialHomeomorphIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeHomologyOpenPartialHomeomorphIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeHomologyOpenPartialHomeomorphIso ``Submission.DifferentialGeometry.Topology.integralRelativeHomologyOpenPartialHomeomorphIso

theorem integralRelativeHomologyOpenPartialHomeomorphIso_comp_excision (n : ℕ)
    (e : OpenPartialHomeomorph X Y) (L : Set Y) (hL : IsCompact L) (hLt : L ⊆ e.target) :
    (integralRelativeHomologyOpenPartialHomeomorphIso n e L hL hLt).hom.hom.comp
      (integralRelativeOpenExcisionIso n (e.symm '' L)ᶜ e.source
        (hL.image_of_continuousOn (e.symm.continuousOn.mono hLt)).isClosed.isOpen_compl
        e.open_source
        (complement_union_eq_univ_of_subset (chart_inverse_image_subset_source e L hLt))).hom.hom =
    integralRelativeHomologyMap n
      (⟨fun x : e.source => e x, e.continuousOn.domRestrict⟩ : C(e.source, Y))
      (show _root_.Set.MapsTo (fun x : e.source => e x)
        (subspaceIntersection (e.symm '' L)ᶜ e.source) Lᶜ from
          fun x hx he => hx ⟨e x.val, he, e.left_inv x.property⟩) := by
  let J := integralRelativeOpenExcisionIso n (e.symm '' L)ᶜ e.source
    (hL.image_of_continuousOn (e.symm.continuousOn.mono hLt)).isClosed.isOpen_compl
    e.open_source
    (complement_union_eq_univ_of_subset (chart_inverse_image_subset_source e L hLt))
  let H := integralRelativeHomologyHomeomorphIso n e.toHomeomorphSourceTarget
    (subspaceIntersection (e.symm '' L)ᶜ e.source)
    (subspaceIntersection Lᶜ e.target)
    (chart_pair_complement_mapsTo e L) (chart_pair_complement_symm_mapsTo e L hLt)
  let T := integralRelativeOpenExcisionIso n Lᶜ e.target hL.isClosed.isOpen_compl e.open_target
    (complement_union_eq_univ_of_subset hLt)
  have hnat : J.hom ≫ (integralRelativeHomologyOpenPartialHomeomorphIso n e L hL hLt).hom =
      H.hom ≫ T.hom := by
    simp [integralRelativeHomologyOpenPartialHomeomorphIso, J, H, T]
  have hlin := congrArg (fun f => f.hom) hnat
  change (integralRelativeHomologyOpenPartialHomeomorphIso n e L hL hLt).hom.hom.comp J.hom.hom =
    T.hom.hom.comp H.hom.hom at hlin
  change (integralRelativeHomologyOpenPartialHomeomorphIso n e L hL hLt).hom.hom.comp J.hom.hom = _
  rw [hlin]
  change (integralRelativeHomologyMap n (singularSubspaceInclusion e.target)
      (subspaceIntersection_mapsTo Lᶜ e.target)).comp
    (integralRelativeHomologyMap n
      ⟨e.toHomeomorphSourceTarget, e.toHomeomorphSourceTarget.continuous⟩
      (chart_pair_complement_mapsTo e L)) = _
  rw [← integralRelativeHomologyMap_comp]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeHomologyOpenPartialHomeomorphIso_comp_excision then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeHomologyOpenPartialHomeomorphIso_comp_excision"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeHomologyOpenPartialHomeomorphIso_comp_excision ``Submission.DifferentialGeometry.Topology.integralRelativeHomologyOpenPartialHomeomorphIso_comp_excision

end DifferentialGeometry.Topology

end

noncomputable section

open _root_.CategoryTheory _root_.ContinuousMap _root_.Set

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

private theorem chart_inverse_image_mem (e : OpenPartialHomeomorph X Y)
    (L : Set Y) (hLt : L ⊆ e.target) {x : X} (hx : x ∈ e.symm '' L) : e x ∈ L := by
  obtain ⟨y, hy, rfl⟩ := hx
  simpa only [e.right_inv (hLt hy)] using hy

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.chart_inverse_image_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.chart_inverse_image_mem target :: scope.openDecls } }

variable [T2Space X] [T2Space Y]

theorem integralRelativeHomologyOpenPartialHomeomorphIso_local_restriction (n : ℕ)
    (e : OpenPartialHomeomorph X Y) (L : Set Y) (hL : IsCompact L) (hLt : L ⊆ e.target)
    (x : X) (hx : x ∈ e.symm '' L) :
    (integralLocalHomologyOpenPartialHomeomorphIso n e x
      (chart_inverse_image_subset_source e L hLt hx)).hom.hom.comp
      (integralRelativeHomologyMap n (ContinuousMap.id X)
        (show (e.symm '' L)ᶜ ⊆ ({x}ᶜ : Set X) from
          fun _ hz heq => hz (heq.symm ▸ hx))) =
    (integralRelativeHomologyMap n (ContinuousMap.id Y)
      (show Lᶜ ⊆ ({e x}ᶜ : Set Y) from
        fun _ hz heq => hz (heq.symm ▸ chart_inverse_image_mem e L hLt hx))).comp
      (integralRelativeHomologyOpenPartialHomeomorphIso n e L hL hLt).hom.hom := by
  have hxs := chart_inverse_image_subset_source e L hLt hx
  let J := integralRelativeOpenExcisionIso n (e.symm '' L)ᶜ e.source
    (hL.image_of_continuousOn (e.symm.continuousOn.mono hLt)).isClosed.isOpen_compl
    e.open_source
    (complement_union_eq_univ_of_subset (chart_inverse_image_subset_source e L hLt))
  let Jx := integralLocalHomologyNeighborhoodIso n x e.source e.open_source hxs
  let I := integralLocalHomologyOpenPartialHomeomorphIso n e x hxs
  let C := integralRelativeHomologyOpenPartialHomeomorphIso n e L hL hLt
  have hRX : _root_.Set.MapsTo (ContinuousMap.id X) (e.symm '' L)ᶜ ({x}ᶜ : Set X) := by
    intro z hz heq
    change z = x at heq
    exact hz (heq.symm ▸ hx)
  have hRY : _root_.Set.MapsTo (ContinuousMap.id Y) Lᶜ ({e x}ᶜ : Set Y) := by
    intro z hz heq
    change z = e x at heq
    exact hz (heq.symm ▸ chart_inverse_image_mem e L hLt hx)
  have hRS : _root_.Set.MapsTo (ContinuousMap.id e.source)
      (subspaceIntersection (e.symm '' L)ᶜ e.source)
      ({(⟨x, hxs⟩ : e.source)}ᶜ : Set e.source) := by
    intro z hz heq
    apply hz
    change z = (⟨x, hxs⟩ : e.source) at heq
    have hval := congrArg (fun w : e.source => w.val) heq
    exact hval.symm ▸ hx
  have hleft : (integralRelativeHomologyMap n (ContinuousMap.id X) hRX).comp J.hom.hom =
      Jx.hom.hom.comp (integralRelativeHomologyMap n (ContinuousMap.id e.source) hRS) := by
    change (integralRelativeHomologyMap n (ContinuousMap.id X) hRX).comp
      (integralRelativeHomologyMap n (singularSubspaceInclusion e.source)
        (subspaceIntersection_mapsTo (e.symm '' L)ᶜ e.source)) =
      (integralRelativeHomologyMap n (singularSubspaceInclusion e.source)
        (neighborhoodPointComplement_mapsTo x e.source hxs)).comp
      (integralRelativeHomologyMap n (ContinuousMap.id e.source) hRS)
    rw [← integralRelativeHomologyMap_comp, ← integralRelativeHomologyMap_comp]
    rfl
  have hcomp : I.hom.hom.comp
      ((integralRelativeHomologyMap n (ContinuousMap.id X) hRX).comp J.hom.hom) =
    (integralRelativeHomologyMap n (ContinuousMap.id Y) hRY).comp
      (C.hom.hom.comp J.hom.hom) := by
    rw [hleft, ← LinearMap.comp_assoc]
    rw [integralLocalHomologyOpenPartialHomeomorphIso_comp_neighborhood
      n e x e.source e.open_source hxs Subset.rfl]
    rw [integralRelativeHomologyOpenPartialHomeomorphIso_comp_excision]
    rw [← integralRelativeHomologyMap_comp, ← integralRelativeHomologyMap_comp]
    rfl
  apply LinearMap.ext
  intro z
  have h := LinearMap.congr_fun hcomp (J.inv.hom z)
  change I.hom.hom (integralRelativeHomologyMap n (ContinuousMap.id X) hRX
      (J.hom.hom (J.inv.hom z))) =
    integralRelativeHomologyMap n (ContinuousMap.id Y) hRY
      (C.hom.hom (J.hom.hom (J.inv.hom z))) at h
  have hz : J.hom.hom (J.inv.hom z) = z := congrArg (fun f => f.hom z) J.inv_hom_id
  rw [hz] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeHomologyOpenPartialHomeomorphIso_local_restriction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeHomologyOpenPartialHomeomorphIso_local_restriction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeHomologyOpenPartialHomeomorphIso_local_restriction ``Submission.DifferentialGeometry.Topology.integralRelativeHomologyOpenPartialHomeomorphIso_local_restriction

end DifferentialGeometry.Topology

end

noncomputable section

open _root_.CategoryTheory _root_.ContinuousMap _root_.Set _root_.Metric

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E]

private theorem chart_point_normalization_mapsTo (c y : E) :
    MapsTo (Homeomorph.addRight (c - y)) ({y}ᶜ : Set E) ({c}ᶜ : Set E) := by
  intro z hz h
  apply hz
  apply (Homeomorph.addRight (c - y)).injective
  have hy : Homeomorph.addRight (c - y) y = c := by
    change y + (c - y) = c
    abel
  exact h.trans hy.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.chart_point_normalization_mapsTo
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.chart_point_normalization_mapsTo target :: scope.openDecls } }

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  [NormedSpace ℝ E] [ProperSpace E]

private theorem exists_chart_closedBall_class_with_normalized_local_maps
    (n : ℕ) (e : OpenPartialHomeomorph X E) (p : X) (hp : p ∈ e.source)
    (r : ℝ) (hr : 0 ≤ r) (hball : _root_.Metric.closedBall (e p) r ⊆ e.target)
    (ζ : integralLocalHomology n p) :
    ∃ a : integralRelativeHomology n (e.symm '' _root_.Metric.closedBall (e p) r)ᶜ,
      ∀ (x : X) (hx : x ∈ e.symm '' _root_.Metric.closedBall (e p) r),
        integralRelativeHomologyMap n (toContinuousMap (Homeomorph.addRight (e p - e x)))
          (chart_point_normalization_mapsTo (e p) (e x))
          ((integralLocalHomologyOpenPartialHomeomorphIso n e x
            (chart_inverse_image_subset_source e (_root_.Metric.closedBall (e p) r) hball hx)).hom.hom
            (integralRelativeHomologyMap n (ContinuousMap.id X)
              (show (e.symm '' _root_.Metric.closedBall (e p) r)ᶜ ⊆ ({x}ᶜ : Set X) from
                fun _ hz heq => hz (heq.symm ▸ hx)) a)) =
          (integralLocalHomologyOpenPartialHomeomorphIso n e p hp).hom.hom ζ := by
  let C := integralRelativeHomologyOpenPartialHomeomorphIso n e (_root_.Metric.closedBall (e p) r)
    (_root_.ProperSpace.isCompact_closedBall (e p) r) hball
  let μ := (integralLocalHomologyOpenPartialHomeomorphIso n e p hp).hom.hom ζ
  obtain ⟨b, hb, _⟩ := existsUnique_closedBall_class_with_normalized_local_maps n (e p) r hr μ
  refine ⟨C.inv.hom b, ?_⟩
  intro x hx
  have hxball := chart_inverse_image_mem e (_root_.Metric.closedBall (e p) r) hball hx
  have hRX : _root_.Set.MapsTo (ContinuousMap.id X) (e.symm '' _root_.Metric.closedBall (e p) r)ᶜ ({x}ᶜ : Set X) := by
    intro z hz heq
    change z = x at heq
    exact hz (heq.symm ▸ hx)
  have hRY : _root_.Set.MapsTo (ContinuousMap.id E) (_root_.Metric.closedBall (e p) r)ᶜ ({e x}ᶜ : Set E) := by
    intro z hz heq
    change z = e x at heq
    exact hz (heq.symm ▸ hxball)
  let T := integralRelativeHomologyMap n (toContinuousMap (Homeomorph.addRight (e p - e x)))
    (chart_point_normalization_mapsTo (e p) (e x))
  have hsquare := LinearMap.congr_fun
    (integralRelativeHomologyOpenPartialHomeomorphIso_local_restriction n e (_root_.Metric.closedBall (e p) r)
      (_root_.ProperSpace.isCompact_closedBall (e p) r) hball x hx) (C.inv.hom b)
  change (integralLocalHomologyOpenPartialHomeomorphIso n e x
      (chart_inverse_image_subset_source e (_root_.Metric.closedBall (e p) r) hball hx)).hom.hom
      (integralRelativeHomologyMap n (ContinuousMap.id X) hRX (C.inv.hom b)) =
    integralRelativeHomologyMap n (ContinuousMap.id E) hRY (C.hom.hom (C.inv.hom b)) at hsquare
  have hC : C.hom.hom (C.inv.hom b) = b := congrArg (fun f => f.hom b) C.inv_hom_id
  rw [hC] at hsquare
  exact (congrArg T hsquare).trans (hb (e x) hxball)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.exists_chart_closedBall_class_with_normalized_local_maps
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.exists_chart_closedBall_class_with_normalized_local_maps target :: scope.openDecls } }

end DifferentialGeometry.Topology

end

noncomputable section

open _root_.CategoryTheory _root_.ContinuousMap _root_.Set _root_.Metric

universe u

namespace DifferentialGeometry.Topology

variable {E X : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [TopologicalSpace X] [T2Space X]

private theorem existsUnique_chart_closedBall_class_with_normalized_local_maps
    (n : ℕ) (e : OpenPartialHomeomorph X E) (p : X) (hp : p ∈ e.source)
    (r : ℝ) (hr : 0 ≤ r) (hball : _root_.Metric.closedBall (e p) r ⊆ e.target)
    (ζ : integralLocalHomology n p) :
    ∃! a : integralRelativeHomology n (e.symm '' _root_.Metric.closedBall (e p) r)ᶜ,
      ∀ (x : X) (hx : x ∈ e.symm '' _root_.Metric.closedBall (e p) r),
        integralRelativeHomologyMap n (toContinuousMap (Homeomorph.addRight (e p - e x)))
          (chart_point_normalization_mapsTo (e p) (e x))
          ((integralLocalHomologyOpenPartialHomeomorphIso n e x
            (chart_inverse_image_subset_source e (_root_.Metric.closedBall (e p) r) hball hx)).hom.hom
            (integralRelativeHomologyMap n (ContinuousMap.id X)
              (show (e.symm '' _root_.Metric.closedBall (e p) r)ᶜ ⊆ ({x}ᶜ : Set X) from
                fun _ hz heq => hz (heq.symm ▸ hx)) a)) =
          (integralLocalHomologyOpenPartialHomeomorphIso n e p hp).hom.hom ζ := by
  obtain ⟨a, ha⟩ := exists_chart_closedBall_class_with_normalized_local_maps n e p hp r hr hball ζ
  refine ⟨a, ha, ?_⟩
  intro b hb
  have hpK : p ∈ e.symm '' _root_.Metric.closedBall (e p) r :=
    ⟨e p, _root_.Metric.mem_closedBall_self hr, e.left_inv hp⟩
  have hmapcenter : (toContinuousMap (Homeomorph.addRight (e p - e p)) : C(E, E)) =
      ContinuousMap.id E := by
    ext x
    simp
  have hba := hb p hpK
  have haa := ha p hpK
  simp only [hmapcenter, integralRelativeHomologyMap_id, LinearMap.id_apply] at hba haa
  let C := integralRelativeHomologyOpenPartialHomeomorphIso n e (_root_.Metric.closedBall (e p) r)
    (_root_.ProperSpace.isCompact_closedBall (e p) r) hball
  let B := integralClosedBallLocalHomologyIso n (e p) r hr
  have hsquare := integralRelativeHomologyOpenPartialHomeomorphIso_local_restriction n e
    (_root_.Metric.closedBall (e p) r) (_root_.ProperSpace.isCompact_closedBall (e p) r) hball p hpK
  have hb' := LinearMap.congr_fun hsquare b
  have ha' := LinearMap.congr_fun hsquare a
  apply C.toLinearEquiv.injective
  apply B.toLinearEquiv.injective
  change B.hom.hom (C.hom.hom b) = B.hom.hom (C.hom.hom a)
  dsimp only [B]
  rw [integralClosedBallLocalHomologyIso_hom]
  exact hb'.symm.trans ((hba.trans haa.symm).trans ha')

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.existsUnique_chart_closedBall_class_with_normalized_local_maps
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.existsUnique_chart_closedBall_class_with_normalized_local_maps target :: scope.openDecls } }

end DifferentialGeometry.Topology

end

noncomputable section

open _root_.CategoryTheory _root_.ContinuousMap _root_.Set _root_.Metric
open scoped _root_.Topology

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E]

private def integralLocalHomologyTranslationZeroIso (n : ℕ) (c : E) :
    integralLocalHomology n c ≅ integralLocalHomology n (0 : E) :=
  integralRelativeHomologyHomeomorphIso n (Homeomorph.subRight c) ({c}ᶜ : Set E) {0}ᶜ
    (fun _ hz => sub_ne_zero.mpr hz)
    (fun z hz heq => by
      apply hz
      change z + c = c at heq
      exact add_right_cancel (heq.trans (zero_add c).symm))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralLocalHomologyTranslationZeroIso
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralLocalHomologyTranslationZeroIso target :: scope.openDecls } }

private theorem integralRelativeHomologyMap_translation_zero_comp
    (n : ℕ) (c y : E) :
    (integralRelativeHomologyMap n (toContinuousMap (Homeomorph.subRight c))
        (show _root_.Set.MapsTo (Homeomorph.subRight c) ({c}ᶜ : Set E) ({0}ᶜ : Set E)
          from fun _ hz => sub_ne_zero.mpr hz)).comp
      (integralRelativeHomologyMap n (toContinuousMap (Homeomorph.addRight (c - y)))
        (chart_point_normalization_mapsTo c y)) =
    integralRelativeHomologyMap n (toContinuousMap (Homeomorph.subRight y))
      (show _root_.Set.MapsTo (Homeomorph.subRight y) ({y}ᶜ : Set E) ({0}ᶜ : Set E)
        from fun _ hz => sub_ne_zero.mpr hz) := by
  rw [← integralRelativeHomologyMap_comp]
  have hmaps : (toContinuousMap (Homeomorph.subRight c)).comp
      (toContinuousMap (Homeomorph.addRight (c - y))) =
      toContinuousMap (Homeomorph.subRight y) := by
    ext z
    change z + (c - y) - c = z - y
    abel
  simp only [hmaps]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralRelativeHomologyMap_translation_zero_comp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralRelativeHomologyMap_translation_zero_comp target :: scope.openDecls } }

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  [NormedSpace ℝ E] [ProperSpace E]

private theorem existsUnique_chart_closedBall_class_with_zero_normalization
    (n : ℕ) (e : OpenPartialHomeomorph X E) (p : X) (hp : p ∈ e.source)
    (r : ℝ) (hr : 0 ≤ r) (hball : _root_.Metric.closedBall (e p) r ⊆ e.target)
    (μ : integralLocalHomology n (0 : E)) :
    ∃! a : integralRelativeHomology n (e.symm '' _root_.Metric.closedBall (e p) r)ᶜ,
      ∀ (x : X) (hx : x ∈ e.symm '' _root_.Metric.closedBall (e p) r),
        integralRelativeHomologyMap n (toContinuousMap (Homeomorph.subRight (e x)))
          (show _root_.Set.MapsTo (Homeomorph.subRight (e x)) ({e x}ᶜ : Set E) ({0}ᶜ : Set E)
            from fun _ hz => sub_ne_zero.mpr hz)
          ((integralLocalHomologyOpenPartialHomeomorphIso n e x
            (chart_inverse_image_subset_source e (_root_.Metric.closedBall (e p) r) hball hx)).hom.hom
            (integralRelativeHomologyMap n (ContinuousMap.id X)
              (show (e.symm '' _root_.Metric.closedBall (e p) r)ᶜ ⊆ ({x}ᶜ : Set X) from
                fun _ hz heq => hz (heq.symm ▸ hx)) a)) = μ := by
  let I := integralLocalHomologyOpenPartialHomeomorphIso n e p hp
  let Z := integralLocalHomologyTranslationZeroIso n (e p)
  obtain ⟨a, ha, huniq⟩ := existsUnique_chart_closedBall_class_with_normalized_local_maps n e p hp r hr hball
    (I.inv.hom (Z.inv.hom μ))
  have hI : I.hom.hom (I.inv.hom (Z.inv.hom μ)) = Z.inv.hom μ :=
    congrArg (fun f => f.hom (Z.inv.hom μ)) I.inv_hom_id
  have hZ : Z.hom.hom (Z.inv.hom μ) = μ :=
    congrArg (fun f => f.hom μ) Z.inv_hom_id
  refine ⟨a, ?_, ?_⟩
  · intro x hx
    have h := congrArg Z.hom.hom (ha x hx)
    rw [hI, hZ] at h
    have hcomp := integralRelativeHomologyMap_translation_zero_comp n (e p) (e x)
    have hv := LinearMap.congr_fun hcomp
      ((integralLocalHomologyOpenPartialHomeomorphIso n e x
        (chart_inverse_image_subset_source e (_root_.Metric.closedBall (e p) r) hball hx)).hom.hom
        (integralRelativeHomologyMap n (ContinuousMap.id X)
          (show (e.symm '' _root_.Metric.closedBall (e p) r)ᶜ ⊆ ({x}ᶜ : Set X) from
            fun _ hz heq => hz (heq.symm ▸ hx)) a))
    exact hv.symm.trans h
  · intro b hb
    apply huniq b
    intro x hx
    apply Z.toLinearEquiv.injective
    change Z.hom.hom _ = Z.hom.hom (I.hom.hom (I.inv.hom (Z.inv.hom μ)))
    rw [hI, hZ]
    have hv := LinearMap.congr_fun
      (integralRelativeHomologyMap_translation_zero_comp n (e p) (e x))
      ((integralLocalHomologyOpenPartialHomeomorphIso n e x
        (chart_inverse_image_subset_source e (_root_.Metric.closedBall (e p) r) hball hx)).hom.hom
        (integralRelativeHomologyMap n (ContinuousMap.id X)
          (show (e.symm '' _root_.Metric.closedBall (e p) r)ᶜ ⊆ ({x}ᶜ : Set X) from
            fun _ hz heq => hz (heq.symm ▸ hx)) b))
    exact hv.trans (hb x hx)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.existsUnique_chart_closedBall_class_with_zero_normalization
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.existsUnique_chart_closedBall_class_with_zero_normalization target :: scope.openDecls } }

end DifferentialGeometry.Topology

end

noncomputable section

open _root_.CategoryTheory _root_.ContinuousMap _root_.Set _root_.Metric
open scoped _root_.Topology

universe u

namespace DifferentialGeometry.Topology

theorem exists_compact_chart_neighborhood_class
    {E X : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [TopologicalSpace X] [T2Space X]
    (n : ℕ) (e : OpenPartialHomeomorph X E) (p : X) (hp : p ∈ e.source)
    (μ : integralLocalHomology n (0 : E)) :
    ∃ (K : Set X) (hK : K ⊆ e.source), IsCompact K ∧ p ∈ interior K ∧
      ∃! a : integralRelativeHomology n Kᶜ,
        ∀ (x : X) (hx : x ∈ K),
          integralRelativeHomologyMap n (toContinuousMap (Homeomorph.subRight (e x)))
            (show _root_.Set.MapsTo (Homeomorph.subRight (e x)) ({e x}ᶜ : Set E) ({0}ᶜ : Set E)
              from fun _ hz => sub_ne_zero.mpr hz)
            ((integralLocalHomologyOpenPartialHomeomorphIso n e x (hK hx)).hom.hom
              (integralRelativeHomologyMap n (ContinuousMap.id X)
                (show Kᶜ ⊆ ({x}ᶜ : Set X) from
                  fun _ hz heq => hz (heq.symm ▸ hx)) a)) = μ := by
  obtain ⟨r, hr, hball, hcompact, hsource, hpint⟩ :=
    exists_chart_closedBall_neighborhood e p hp
  exact ⟨e.symm '' _root_.Metric.closedBall (e p) r, hsource, hcompact, hpint,
    existsUnique_chart_closedBall_class_with_zero_normalization n e p hp r hr.le hball μ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_compact_chart_neighborhood_class then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_compact_chart_neighborhood_class"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_compact_chart_neighborhood_class ``Submission.DifferentialGeometry.Topology.exists_compact_chart_neighborhood_class

end DifferentialGeometry.Topology

end
