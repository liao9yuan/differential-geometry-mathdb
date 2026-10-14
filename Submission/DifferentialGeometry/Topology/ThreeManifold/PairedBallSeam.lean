import Submission.DifferentialGeometry.Topology.ThreeManifold.PairedBallPuncturedAtlas
import Submission.DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.DirectSmooth
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Pullback
import Submission.DifferentialGeometry.Topology.Manifold.Sigma
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Cover

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Metric _root_.Submission.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.E3 target :: scope.openDecls } }
variable {V : Type v} {E : Type w}
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
      (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
  (s : E) (a : BoundaryAttachment)

def seamCore : TopologicalSpace.Opens (Σ v, PuncturedFactor N endpoint chart v) :=
  ⟨(_root_.Set.range (fun z => (⟨endpoint s _root_.Bool.false, boundaryPoint N endpoint chart hdisj s _root_.Bool.false z⟩ :
      Σ v, PuncturedFactor N endpoint chart v)) ∪
    _root_.Set.range (fun z => (⟨endpoint s _root_.Bool.true, boundaryPoint N endpoint chart hdisj s _root_.Bool.true z⟩ :
      Σ v, PuncturedFactor N endpoint chart v)))ᶜ,
    ((isCompact_range (continuous_sigmaMk.comp (continuous_boundaryPoint N endpoint chart hdisj s _root_.Bool.false))).isClosed.union
      (isCompact_range (continuous_sigmaMk.comp (continuous_boundaryPoint N endpoint chart hdisj s _root_.Bool.true))).isClosed).isOpen_compl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.seamCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.seamCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.seamCore ``Submission.DifferentialGeometry.Topology.PairedBallGluing.seamCore

def seamCoreInclusion : seamCore N endpoint chart hdisj s → Quot (seamRel N endpoint chart hdisj s a) :=
  fun x => Quot.mk _ x.val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.seamCoreInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.seamCoreInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.seamCoreInclusion ``Submission.DifferentialGeometry.Topology.PairedBallGluing.seamCoreInclusion

include hdisj in
private theorem radial_not_mem_holes (e : E) (b : Bool)
    (z : _root_.Metric.sphere (0 : E3) 1) (r : ℝ) (hr : r ∈ _root_.Set.Icc 1 2) :
    flagMap N endpoint chart (e, b) (r • z.val) ∉
      ⋃ p, flagMap N endpoint chart p '' _root_.Metric.ball (0 : E3) 1 := by
  intro hx
  obtain ⟨p, v, hv, heq⟩ := mem_iUnion.mp hx
  have hrad : r • z.val ∈ _root_.Metric.closedBall (0 : E3) 2 := by
    rw [_root_.Metric.mem_closedBall, dist_zero_right, BallChart.norm_radial z (by linarith [hr.1])]
    exact hr.2
  by_cases hp : p = (e, b)
  · subst p
    have hh : (chart e b).chart v = (chart e b).chart (r • z.val) := eq_of_heq (Sigma.mk.inj heq).2
    have hvsrc := (chart e b).toBallChart.ball_subset_source hv
    have he := (chart e b).chart.injOn hvsrc ((chart e b).closedBall_subset_source hrad) hh
    rw [he, _root_.Metric.mem_ball, dist_zero_right, BallChart.norm_radial z (by linarith [hr.1])] at hv
    exact (not_lt_of_ge hr.1) hv
  · exact disjoint_left.mp (hdisj hp)
      ⟨v, ball_subset_closedBall.trans (_root_.Metric.closedBall_subset_closedBall (by norm_num)) hv, heq⟩
      ⟨r • z.val, hrad, rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.radial_not_mem_holes
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.radial_not_mem_holes target :: scope.openDecls } }

def radialPoint (e : E) (b : Bool) (z : _root_.Metric.sphere (0 : E3) 1)
    (r : ℝ) (hr : r ∈ _root_.Set.Icc 1 2) : PuncturedFactor N endpoint chart (endpoint e b) :=
  ⟨(chart e b).chart (r • z.val), radial_not_mem_holes N endpoint chart hdisj e b z r hr⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.radialPoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.radialPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.radialPoint ``Submission.DifferentialGeometry.Topology.PairedBallGluing.radialPoint

theorem radialPoint_one (e : E) (b : Bool) (z : _root_.Metric.sphere (0 : E3) 1) :
    radialPoint N endpoint chart hdisj e b z 1 (by norm_num) =
      boundaryPoint N endpoint chart hdisj e b z := by
  apply Subtype.ext
  change (chart e b).chart ((1 : ℝ) • z.val) = (chart e b).chart z.val
  rw [one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.radialPoint_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.radialPoint_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.radialPoint_one ``Submission.DifferentialGeometry.Topology.PairedBallGluing.radialPoint_one

def seamChart (p : SelfAttachment.directSeamDomain) : Quot (seamRel N endpoint chart hdisj s a) :=
  if ht : 0 ≤ p.val.2 then
    Quot.mk _ ⟨endpoint s _root_.Bool.false,
      radialPoint N endpoint chart hdisj s _root_.Bool.false p.val.1 (1 + p.val.2)
        ⟨by linarith, by linarith [p.property.2.2]⟩⟩
  else
    Quot.mk _ ⟨endpoint s _root_.Bool.true,
      radialPoint N endpoint chart hdisj s _root_.Bool.true (a.val p.val.1) (1 - p.val.2)
        ⟨by linarith, by linarith [p.property.2.1]⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.seamChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.seamChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.seamChart ``Submission.DifferentialGeometry.Topology.PairedBallGluing.seamChart

theorem seamChart_zero (z : SelfAttachment.Sphere (n := 3)) :
    seamChart N endpoint chart hdisj s a ⟨(z, 0), _root_.Set.mem_univ _, by norm_num [SelfAttachment.directSeamDomain]⟩ =
      Quot.mk _ ⟨endpoint s _root_.Bool.false, boundaryPoint N endpoint chart hdisj s _root_.Bool.false z⟩ := by
  rw [seamChart, dif_pos le_rfl]
  apply congrArg (Quot.mk _)
  apply congrArg (Sigma.mk (endpoint s _root_.Bool.false))
  apply Subtype.ext
  change (chart s _root_.Bool.false).chart ((1 + 0 : ℝ) • z.val) = (chart s _root_.Bool.false).chart z.val
  simp only [add_zero, one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.seamChart_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.seamChart_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.seamChart_zero ``Submission.DifferentialGeometry.Topology.PairedBallGluing.seamChart_zero

theorem seam_local_maps_cover (q : Quot (seamRel N endpoint chart hdisj s a)) :
    (∃ x, seamCoreInclusion N endpoint chart hdisj s a x = q) ∨
      ∃ z, seamChart N endpoint chart hdisj s a
        ⟨(z, 0), _root_.Set.mem_univ _, by norm_num [SelfAttachment.directSeamDomain]⟩ = q := by
  induction q using Quot.inductionOn with
  | h x =>
    by_cases hx : x ∈ seamCore N endpoint chart hdisj s
    · exact Or.inl ⟨⟨x, hx⟩, rfl⟩
    · right
      have hx' : x ∈ _root_.Set.range (fun z => (⟨endpoint s _root_.Bool.false, boundaryPoint N endpoint chart hdisj s _root_.Bool.false z⟩ :
          Σ v, PuncturedFactor N endpoint chart v)) ∪
        _root_.Set.range (fun z => (⟨endpoint s _root_.Bool.true, boundaryPoint N endpoint chart hdisj s _root_.Bool.true z⟩ :
          Σ v, PuncturedFactor N endpoint chart v)) := not_not.mp hx
      rcases hx' with ⟨z, rfl⟩ | ⟨z, rfl⟩
      · exact ⟨z, seamChart_zero N endpoint chart hdisj s a z⟩
      · refine ⟨a.val.symm z, ?_⟩
        rw [seamChart_zero]
        apply Quot.sound
        refine ⟨a.val.symm z, Or.inl ⟨rfl, ?_⟩⟩
        rw [a.val.apply_symm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.seam_local_maps_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.seam_local_maps_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.seam_local_maps_cover ``Submission.DifferentialGeometry.Topology.PairedBallGluing.seam_local_maps_cover

end DifferentialGeometry.Topology.PairedBallGluing

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w
variable {V : Type v} {E : Type w}
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2)
      (flagMap N endpoint chart q '' closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2))
  (s : E) (a : BoundaryAttachment)

theorem mem_seamCore_iff (x : Σ v, PuncturedFactor N endpoint chart v) :
    x ∈ seamCore N endpoint chart hdisj s ↔
      (⟨x.fst, x.snd.val⟩ : Σ v, (N v).Carrier) ∉
        flagMap N endpoint chart (s, _root_.Bool.false) '' _root_.Metric.closedBall 0 1 ∪
          flagMap N endpoint chart (s, _root_.Bool.true) '' _root_.Metric.closedBall 0 1 := by
  have heq (b : Bool) :
      x ∈ _root_.Set.range (fun z => (⟨endpoint s b, boundaryPoint N endpoint chart hdisj s b z⟩ :
        Σ v, PuncturedFactor N endpoint chart v)) ↔
        (⟨x.fst, x.snd.val⟩ : Σ v, (N v).Carrier) ∈ flagMap N endpoint chart (s, b) '' _root_.Metric.closedBall 0 1 := by
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z.val, _root_.Metric.sphere_subset_closedBall z.property, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have hge : 1 ≤ ‖y‖ := by
        by_contra h
        exact x.snd.property (mem_iUnion.mpr ⟨(s, b), y, mem_ball_zero_iff.mpr (not_le.mp h), hyx⟩)
      let z : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
        ⟨y, mem_sphere_zero_iff_norm.mpr (le_antisymm (mem_closedBall_zero_iff.mp hy) hge)⟩
      refine ⟨z, ?_⟩
      have hi : Function.Injective (fun q : Σ v, PuncturedFactor N endpoint chart v =>
          (⟨q.fst, q.snd.val⟩ : Σ v, (N v).Carrier)) := by
        rintro ⟨v, p⟩ ⟨w, q⟩ h
        have hv : v = w := congrArg Sigma.fst h
        subst w
        exact congrArg (Sigma.mk v) (Subtype.ext (eq_of_heq (Sigma.mk.inj h).2))
      exact hi hyx
  exact not_congr (or_congr (heq _root_.Bool.false) (heq _root_.Bool.true))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.mem_seamCore_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.mem_seamCore_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.mem_seamCore_iff ``Submission.DifferentialGeometry.Topology.PairedBallGluing.mem_seamCore_iff

end DifferentialGeometry.Topology.PairedBallGluing

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w
private abbrev IC := (𝓡 2).prod 𝓘(ℝ, ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.IC target :: scope.openDecls } }
variable {V : Type v} {E : Type w}
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
      (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
  (s : E) (a : BoundaryAttachment)

theorem range_seamCoreInclusion_union_range_seamChart :
    _root_.Set.range (seamCoreInclusion N endpoint chart hdisj s a) ∪
      range (seamChart N endpoint chart hdisj s a) = univ := by
  apply _root_.Set.eq_univ_of_forall
  intro q
  rcases seam_local_maps_cover N endpoint chart hdisj s a q with h | ⟨z, hz⟩
  · exact Or.inl h
  · exact Or.inr ⟨_, hz⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.range_seamCoreInclusion_union_range_seamChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.range_seamCoreInclusion_union_range_seamChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.range_seamCoreInclusion_union_range_seamChart ``Submission.DifferentialGeometry.Topology.PairedBallGluing.range_seamCoreInclusion_union_range_seamChart

variable [∀ v, ChartedSpace (EuclideanHalfSpace 3) (PuncturedFactor N endpoint chart v)]

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace (EuclideanHalfSpace 3) Y]

variable [ChartedSpace (EuclideanHalfSpace 3) (Quot (seamRel N endpoint chart hdisj s a))]

theorem isLocalDiffeomorph_seamQuotient_of_comp_local_maps
    (hcore : IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞
      (seamCoreInclusion N endpoint chart hdisj s a))
    (hseam : IsLocalDiffeomorph IC (𝓡∂ 3) ∞ (seamChart N endpoint chart hdisj s a))
    (f : Quot (seamRel N endpoint chart hdisj s a) → Y)
    (hfcore : IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞
      (f ∘ seamCoreInclusion N endpoint chart hdisj s a))
    (hfseam : IsLocalDiffeomorph IC (𝓡∂ 3) ∞ (f ∘ seamChart N endpoint chart hdisj s a)) :
    IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞ f :=
  DifferentialGeometry.isLocalDiffeomorph_of_comp_cover _ _
    (range_seamCoreInclusion_union_range_seamChart N endpoint chart hdisj s a)
    hcore hseam f hfcore hfseam

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.isLocalDiffeomorph_seamQuotient_of_comp_local_maps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.isLocalDiffeomorph_seamQuotient_of_comp_local_maps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.isLocalDiffeomorph_seamQuotient_of_comp_local_maps ``Submission.DifferentialGeometry.Topology.PairedBallGluing.isLocalDiffeomorph_seamQuotient_of_comp_local_maps

def seamDiffeomorphOfLocalMaps
    (h : Quot (seamRel N endpoint chart hdisj s a) ≃ₜ Y)
    (hcore : IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞
      (seamCoreInclusion N endpoint chart hdisj s a))
    (hseam : IsLocalDiffeomorph IC (𝓡∂ 3) ∞ (seamChart N endpoint chart hdisj s a))
    (hhcore : IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞
      (h ∘ seamCoreInclusion N endpoint chart hdisj s a))
    (hhseam : IsLocalDiffeomorph IC (𝓡∂ 3) ∞ (h ∘ seamChart N endpoint chart hdisj s a)) :
    Diffeomorph (𝓡∂ 3) (𝓡∂ 3) (Quot (seamRel N endpoint chart hdisj s a)) Y ∞ :=
  (isLocalDiffeomorph_seamQuotient_of_comp_local_maps N endpoint chart hdisj s a
    hcore hseam h hhcore hhseam).diffeomorphOfBijective h.bijective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.seamDiffeomorphOfLocalMaps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.seamDiffeomorphOfLocalMaps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.seamDiffeomorphOfLocalMaps ``Submission.DifferentialGeometry.Topology.PairedBallGluing.seamDiffeomorphOfLocalMaps

theorem seamDiffeomorphOfLocalMaps_apply
    (h : Quot (seamRel N endpoint chart hdisj s a) ≃ₜ Y)
    (hcore : IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞
      (seamCoreInclusion N endpoint chart hdisj s a))
    (hseam : IsLocalDiffeomorph IC (𝓡∂ 3) ∞ (seamChart N endpoint chart hdisj s a))
    (hhcore : IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞
      (h ∘ seamCoreInclusion N endpoint chart hdisj s a))
    (hhseam : IsLocalDiffeomorph IC (𝓡∂ 3) ∞ (h ∘ seamChart N endpoint chart hdisj s a))
    (x : Quot (seamRel N endpoint chart hdisj s a)) :
    seamDiffeomorphOfLocalMaps N endpoint chart hdisj s a h hcore hseam hhcore hhseam x = h x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.seamDiffeomorphOfLocalMaps_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.seamDiffeomorphOfLocalMaps_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.seamDiffeomorphOfLocalMaps_apply ``Submission.DifferentialGeometry.Topology.PairedBallGluing.seamDiffeomorphOfLocalMaps_apply

omit [ChartedSpace (EuclideanHalfSpace 3) (Quot (seamRel N endpoint chart hdisj s a))] in
theorem exists_smooth_seam_atlas_of_comp_local_maps [IsManifold (𝓡∂ 3) ∞ Y]
    (h : Quot (seamRel N endpoint chart hdisj s a) ≃ₜ Y)
    (hhcore : IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞
      (h ∘ seamCoreInclusion N endpoint chart hdisj s a))
    (hhseam : IsLocalDiffeomorph IC (𝓡∂ 3) ∞ (h ∘ seamChart N endpoint chart hdisj s a)) :
    ∃ C : ChartedSpace (EuclideanHalfSpace 3) (Quot (seamRel N endpoint chart hdisj s a)),
      let _ := C
      IsManifold (𝓡∂ 3) ∞ (Quot (seamRel N endpoint chart hdisj s a)) ∧
        IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞ (seamCoreInclusion N endpoint chart hdisj s a) ∧
        IsLocalDiffeomorph IC (𝓡∂ 3) ∞ (seamChart N endpoint chart hdisj s a) ∧
        ∃ D : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) (Quot (seamRel N endpoint chart hdisj s a)) Y ∞,
          ∀ x, D x = h x := by
  let C := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := EuclideanHalfSpace 3) h
  let _ := C
  let _ := DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback (I := 𝓡∂ 3) (n := ∞) h
  refine ⟨C, inferInstance, ?_, ?_,
    DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph (I := 𝓡∂ 3) (n := ∞) h, fun _ => rfl⟩
  · exact isLocalDiffeomorph_pullback_of_comp h _ hhcore
  · exact isLocalDiffeomorph_pullback_of_comp h _ hhseam

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.exists_smooth_seam_atlas_of_comp_local_maps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.exists_smooth_seam_atlas_of_comp_local_maps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.exists_smooth_seam_atlas_of_comp_local_maps ``Submission.DifferentialGeometry.Topology.PairedBallGluing.exists_smooth_seam_atlas_of_comp_local_maps

end DifferentialGeometry.Topology.PairedBallGluing
