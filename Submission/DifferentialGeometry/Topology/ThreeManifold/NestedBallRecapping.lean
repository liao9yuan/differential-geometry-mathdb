import Submission.DifferentialGeometry.Topology.ThreeManifold.ChartSphereBall
import Submission.DifferentialGeometry.Topology.Manifold.StereographicChart
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Boundary
import Submission.DifferentialGeometry.Topology.ThreeManifold.RelativeBallReplacement
import Submission.DifferentialGeometry.Topology.ThreeManifold.TwoBallCharts
import Batteries.Tactic.OpenPrivate

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set _root_.Metric _root_.Submission.Metric _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.Topology.ThreeManifold

open private standardHemisphereChart oppositeHemisphereChart standardHemisphereChart_source
  oppositeHemisphereChart_source hemisphere_complement from
    Submission.DifferentialGeometry.Topology.ThreeManifold.TwoBallCharts

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.E3 target :: scope.openDecls } }
private abbrev E4 := EuclideanSpace ℝ (Fin 4)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.E4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.E4 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.S2 target :: scope.openDecls } }
private abbrev S3 := Metric.sphere (0 : E4) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.S3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.S3 target :: scope.openDecls } }

private def stereographicPartial (p : S3) : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞ where
  toPartialEquiv := (stereographic' 3 p).symm.toPartialEquiv
  open_source := (stereographic' 3 p).symm.open_source
  open_target := (stereographic' 3 p).symm.open_target
  contMDiffOn_toFun := (DifferentialGeometry.Topology.Manifold.stereographicInverse_isLocalDiffeomorph p).contMDiff.contMDiffOn
  contMDiffOn_invFun := (DifferentialGeometry.Topology.Manifold.stereographic_isLocalDiffeomorphOn p).contMDiffOn

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.stereographicPartial
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.stereographicPartial target :: scope.openDecls } }

private theorem exists_ball_chart_complement_of_sphere_ball_chart
    (C : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞)
    (hC : _root_.Metric.closedBall (0 : E3) 1 ⊆ C.source) :
    ∃ B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞,
      _root_.Metric.closedBall (0 : E3) 1 ⊆ B.source ∧
      B '' _root_.Metric.ball (0 : E3) 1 = (C '' _root_.Metric.closedBall (0 : E3) 1)ᶜ ∧
      B '' _root_.Metric.closedBall (0 : E3) 1 = (C '' _root_.Metric.ball (0 : E3) 1)ᶜ ∧
      B '' _root_.Metric.sphere (0 : E3) 1 = C '' _root_.Metric.sphere (0 : E3) 1 := by
  let p := C 0
  let A := stereographicPartial p
  have hAt : A.target = {p}ᶜ := by change (stereographic' 3 p).source = {p}ᶜ; simp
  have hCcompact : IsCompact (C '' _root_.Metric.closedBall (0 : E3) 1) :=
    (_root_.ProperSpace.isCompact_closedBall _ _).image_of_continuousOn (C.contMDiffOn_toFun.continuousOn.mono hC)
  have hCint : interior (C '' _root_.Metric.closedBall (0 : E3) 1) = C '' _root_.Metric.ball (0 : E3) 1 := by
    have h := C.toOpenPartialHomeomorph.image_interior_of_subset_source hC
    rw [interior_closedBall _ one_ne_zero] at h
    exact h.symm
  have hclosure : closure (C '' _root_.Metric.closedBall (0 : E3) 1)ᶜ = (C '' _root_.Metric.ball (0 : E3) 1)ᶜ := by
    rw [closure_compl, hCint]
  have hp : p ∈ C '' _root_.Metric.ball (0 : E3) 1 := ⟨0, by simp, rfl⟩
  have hsource : closure (C '' _root_.Metric.closedBall (0 : E3) 1)ᶜ ⊆ A.target := by
    rw [hclosure, hAt]
    intro z hz hzp
    exact hz (mem_singleton_iff.mp hzp ▸ hp)
  have hne : ((C '' _root_.Metric.closedBall (0 : E3) 1)ᶜ).Nonempty := by
    by_contra h
    have hall : C '' _root_.Metric.closedBall (0 : E3) 1 = univ := by
      exact eq_univ_iff_forall.mpr (fun z => not_not.mp (fun hz => h ⟨z, hz⟩))
    have hf := C.image_frontier_of_isCompact (_root_.ProperSpace.isCompact_closedBall (0 : E3) 1) hC
    rw [frontier_closedBall _ one_ne_zero, hall, frontier_univ] at hf
    have hn : (C '' _root_.Metric.sphere (0 : E3) 1).Nonempty :=
      ⟨C (EuclideanSpace.single 0 1), EuclideanSpace.single 0 1, by simp, rfl⟩
    rw [hf] at hn
    exact _root_.Set.not_nonempty_empty hn
  let f : S2 → S3 := C ∘ Subtype.val
  have hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f :=
    DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph C
      (isSmoothEmbedding_coe_sphere (E := E3) (n := 2))
      (by rw [Subtype.range_val]; exact sphere_subset_closedBall.trans hC)
  have hfront : frontier (C '' _root_.Metric.closedBall (0 : E3) 1)ᶜ = _root_.Set.range f := by
    rw [frontier_compl, ← C.image_frontier_of_isCompact (_root_.ProperSpace.isCompact_closedBall _ _) hC,
      frontier_closedBall _ one_ne_zero, _root_.Set.range_comp, Subtype.range_val]
  obtain ⟨B, hB, hBo, hBc, hBf⟩ := exists_ball_chart_of_compact_closure_sphere_frontier
    A hCcompact.isClosed.isOpen_compl hne isClosed_closure.isCompact hsource f hf hfront
  exact ⟨B, hB, hBo, hBc.trans hclosure, by simpa only [f, _root_.Set.range_comp, Subtype.range_val] using hBf⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_complement_of_sphere_ball_chart
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_complement_of_sphere_ball_chart target :: scope.openDecls } }

section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]

private theorem exists_ball_chart_of_recapped_sphere_ball_complement
    (C b : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞)
    (P : PartialDiffeomorph (𝓡 3) (𝓡 3) S3 M ∞)
    (G : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (hC : _root_.Metric.closedBall (0 : E3) 1 ⊆ C.source)
    (hb : _root_.Metric.closedBall (0 : E3) 1 ⊆ b.source)
    (hG : _root_.Metric.closedBall (0 : E3) 1 ⊆ G.source)
    (hdis : Disjoint (C '' _root_.Metric.closedBall (0 : E3) 1) (b '' _root_.Metric.closedBall (0 : E3) 1))
    (hP : (C '' _root_.Metric.ball (0 : E3) 1)ᶜ \ b '' _root_.Metric.ball (0 : E3) 1 ⊆ P.source)
    (hboundary : P '' (b '' _root_.Metric.sphere (0 : E3) 1) = G '' _root_.Metric.sphere (0 : E3) 1)
    (hinter : P '' ((C '' _root_.Metric.ball (0 : E3) 1)ᶜ \ b '' _root_.Metric.ball (0 : E3) 1) ∩
      G '' _root_.Metric.closedBall (0 : E3) 1 ⊆ G '' _root_.Metric.sphere (0 : E3) 1) :
    ∃ (J : PartialDiffeomorph (𝓡 3) (𝓡 3) S3 M ∞)
      (A : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞),
      (C '' _root_.Metric.ball (0 : E3) 1)ᶜ ⊆ J.source ∧
      _root_.Metric.closedBall (0 : E3) 1 ⊆ A.source ∧
      A '' _root_.Metric.closedBall (0 : E3) 1 =
        P '' ((C '' _root_.Metric.ball (0 : E3) 1)ᶜ \ b '' _root_.Metric.ball (0 : E3) 1) ∪ G '' _root_.Metric.closedBall (0 : E3) 1 ∧
      A '' _root_.Metric.sphere (0 : E3) 1 = P '' (C '' _root_.Metric.sphere (0 : E3) 1) ∧
      ∃ O : Set S3, IsOpen O ∧ (C '' _root_.Metric.ball (0 : E3) 1)ᶜ \ b '' _root_.Metric.ball (0 : E3) 1 ⊆ O ∧
        O ⊆ P.source ∧ _root_.Set.EqOn J P O := by
  let Ω := (C '' _root_.Metric.ball (0 : E3) 1)ᶜ
  have hΩ : IsCompact Ω :=
    (C.toOpenPartialHomeomorph.isOpen_image_of_subset_source _root_.Metric.isOpen_ball
      (ball_subset_closedBall.trans hC)).isClosed_compl.isCompact
  have hbΩ : b '' _root_.Metric.closedBall (0 : E3) 1 ⊆ interior Ω := by
    rw [interior_compl, DifferentialGeometry.Topology.Manifold.closure_image_ball_of_partialDiffeomorph C hC]
    exact disjoint_left.mp hdis.symm
  obtain ⟨J, D, hJ, hJimage, _, _, O, hO, hKO, hOP, hJP⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_ball_replacement_eqOn_complement
      b P G hb hG hΩ hbΩ hP hboundary hinter
  obtain ⟨B, hB, _, hBc, hBs⟩ := exists_ball_chart_complement_of_sphere_ball_chart C hC
  let A := B.trans J
  have hA : _root_.Metric.closedBall (0 : E3) 1 ⊆ A.source := by
    intro z hz
    refine ⟨hB hz, hJ ?_⟩
    change B z ∈ (C '' _root_.Metric.ball (0 : E3) 1)ᶜ
    exact hBc ▸ _root_.Set.mem_image_of_mem B hz
  have hAi : A '' _root_.Metric.closedBall (0 : E3) 1 = J '' Ω := by
    change (J ∘ B) '' _root_.Metric.closedBall (0 : E3) 1 = _
    rw [_root_.Set.image_comp, hBc]
  have hCboundary : C '' _root_.Metric.sphere (0 : E3) 1 ⊆ Ω \ b '' _root_.Metric.ball (0 : E3) 1 := by
    rintro z ⟨w, hw, rfl⟩
    refine ⟨?_, ?_⟩
    · rintro ⟨v, hv, hvw⟩
      have he := C.toPartialEquiv.injOn (hC (_root_.Metric.ball_subset_closedBall hv))
        (hC (_root_.Metric.sphere_subset_closedBall hw)) hvw
      exact (mem_ball_zero_iff.mp (he ▸ hv)).ne (mem_sphere_zero_iff_norm.mp hw)
    · exact fun hz => disjoint_left.mp hdis ⟨w, _root_.Metric.sphere_subset_closedBall hw, rfl⟩
        (_root_.Set.image_mono _root_.Metric.ball_subset_closedBall hz)
  have hAf : A '' _root_.Metric.sphere (0 : E3) 1 = P '' (C '' _root_.Metric.sphere (0 : E3) 1) := by
    change (J ∘ B) '' _root_.Metric.sphere (0 : E3) 1 = _
    rw [_root_.Set.image_comp, hBs]
    exact (hJP.mono (hCboundary.trans hKO)).image_eq
  exact ⟨J, A, hJ, hA, hAi.trans hJimage, hAf, O, hO, hKO, hOP, hJP⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_of_recapped_sphere_ball_complement
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_of_recapped_sphere_ball_complement target :: scope.openDecls } }

end

section

variable {Z M : Type*} [TopologicalSpace Z] [ChartedSpace E3 Z] [T2Space Z]
  [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]

omit [T2Space Z] in
theorem exists_ball_chart_of_recapped_nested_ball_shell
    (C B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞)
    (F : PartialDiffeomorph (𝓡 3) (𝓡 3) Z M ∞)
    (G : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (hC : _root_.Metric.closedBall (0 : E3) 1 ⊆ C.source)
    (hB : _root_.Metric.closedBall (0 : E3) 1 ⊆ B.source)
    (hG : _root_.Metric.closedBall (0 : E3) 1 ⊆ G.source)
    (hnested : C '' _root_.Metric.closedBall (0 : E3) 1 ⊆ B '' _root_.Metric.ball (0 : E3) 1)
    (hF : B '' _root_.Metric.closedBall (0 : E3) 1 \ C '' _root_.Metric.ball (0 : E3) 1 ⊆ F.source)
    (hboundary : F '' (B '' _root_.Metric.sphere (0 : E3) 1) = G '' _root_.Metric.sphere (0 : E3) 1)
    (hinter : F '' (B '' _root_.Metric.closedBall (0 : E3) 1 \ C '' _root_.Metric.ball (0 : E3) 1) ∩
      G '' _root_.Metric.closedBall (0 : E3) 1 ⊆ G '' _root_.Metric.sphere (0 : E3) 1) :
    ∃ A : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞,
      _root_.Metric.closedBall (0 : E3) 1 ⊆ A.source ∧
      A '' _root_.Metric.closedBall (0 : E3) 1 =
        F '' (B '' _root_.Metric.closedBall (0 : E3) 1 \ C '' _root_.Metric.ball (0 : E3) 1) ∪ G '' _root_.Metric.closedBall (0 : E3) 1 ∧
      A '' _root_.Metric.sphere (0 : E3) 1 = F '' (C '' _root_.Metric.sphere (0 : E3) 1) ∧
      ∃ H : PartialDiffeomorph (𝓡 3) (𝓡 3) Z E3 ∞,
        B '' _root_.Metric.closedBall (0 : E3) 1 \ C '' _root_.Metric.ball (0 : E3) 1 ⊆ H.source ∧
        (∀ z ∈ B '' _root_.Metric.closedBall (0 : E3) 1 \ C '' _root_.Metric.ball (0 : E3) 1, A (H z) = F z) ∧
        ∀ z ∈ C '' _root_.Metric.sphere (0 : E3) 1, H z ∈ _root_.Metric.sphere (0 : E3) 1 := by
  let p : S3 := ⟨EuclideanSpace.single 0 1, by simp⟩
  let a := standardHemisphereChart p
  let b := oppositeHemisphereChart p
  have has : a.source = univ := standardHemisphereChart_source p
  have hbs : b.source = univ := oppositeHemisphereChart_source p
  have hab : b '' _root_.Metric.closedBall (0 : E3) 1 = (a '' _root_.Metric.ball (0 : E3) 1)ᶜ := hemisphere_complement p
  have hab' : b '' _root_.Metric.ball (0 : E3) 1 = (a '' _root_.Metric.closedBall (0 : E3) 1)ᶜ := by
    have h := congrArg interior hab
    have hbi := b.toOpenPartialHomeomorph.image_interior_of_subset_source
      (show _root_.Metric.closedBall (0 : E3) 1 ⊆ b.source by rw [hbs]; exact _root_.Set.subset_univ _)
    change b '' interior (_root_.Metric.closedBall (0 : E3) 1) = interior (b '' _root_.Metric.closedBall (0 : E3) 1) at hbi
    rw [interior_closedBall _ one_ne_zero] at hbi
    rw [← hbi, interior_compl,
      DifferentialGeometry.Topology.Manifold.closure_image_ball_of_partialDiffeomorph a
        (has ▸ _root_.Set.subset_univ _)] at h
    exact h
  let L := B.symm.trans a
  let C' := C.trans L
  let P := (a.symm.trans B).trans F
  have hCB (z : E3) (hz : z ∈ _root_.Metric.closedBall (0 : E3) 1) : C z ∈ B.target := by
    obtain ⟨x, hx, hxc⟩ := hnested ⟨z, hz, rfl⟩
    exact hxc ▸ B.map_source (hB (_root_.Metric.ball_subset_closedBall hx))
  have hC' : _root_.Metric.closedBall (0 : E3) 1 ⊆ C'.source :=
    fun z hz => ⟨hC hz, hCB z hz, has ▸ _root_.Set.mem_univ _⟩
  have hLC (z : E3) (hz : z ∈ _root_.Metric.closedBall (0 : E3) 1) :
      B (B.symm (C z)) = C z := B.right_inv (hCB z hz)
  have hC'a : C' '' _root_.Metric.closedBall (0 : E3) 1 ⊆ a '' _root_.Metric.ball (0 : E3) 1 := by
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨x, hx, hxc⟩ := hnested ⟨z, hz, rfl⟩
    refine ⟨x, hx, ?_⟩
    change a x = a (B.symm (C z))
    rw [← hxc]
    congr 1
    exact (B.left_inv (hB (_root_.Metric.ball_subset_closedBall hx))).symm
  have hdis : Disjoint (C' '' _root_.Metric.closedBall (0 : E3) 1) (b '' _root_.Metric.closedBall (0 : E3) 1) := by
    rw [hab]
    exact disjoint_compl_right.mono_left hC'a
  let S := (C' '' _root_.Metric.ball (0 : E3) 1)ᶜ \ b '' _root_.Metric.ball (0 : E3) 1
  have hSa : S ⊆ a '' _root_.Metric.closedBall (0 : E3) 1 := by
    dsimp only [S]
    rw [hab']
    exact fun x hx => not_not.mp hx.2
  have hcoord (x : S3) (hx : x ∈ S) :
      B (a.symm x) ∈ B '' _root_.Metric.closedBall (0 : E3) 1 \ C '' _root_.Metric.ball (0 : E3) 1 := by
    obtain ⟨z, hz, hzx⟩ := hSa hx
    have ha_inv : a.symm x = z := by rw [← hzx]; exact a.left_inv (has ▸ _root_.Set.mem_univ _)
    rw [ha_inv]
    refine ⟨⟨z, hz, rfl⟩, ?_⟩
    rintro ⟨w, hw, hwB⟩
    apply hx.1
    refine ⟨w, hw, ?_⟩
    change a (B.symm (C w)) = x
    rw [hwB]
    have hb_inv : B.symm (B z) = z := B.left_inv (hB hz)
    rw [hb_inv]
    exact hzx
  have hPs : S ⊆ P.source := by
    intro x hx
    obtain ⟨z, hz, hzx⟩ := hSa hx
    have ha_inv : a.symm x = z := by rw [← hzx]; exact a.left_inv (has ▸ _root_.Set.mem_univ _)
    refine ⟨⟨?_, ?_⟩, hF (hcoord x hx)⟩
    · exact hzx ▸ a.map_source (has ▸ _root_.Set.mem_univ _)
    · change a.symm x ∈ B.source
      rw [ha_inv]
      exact hB hz
  have himage : P '' S = F '' (B '' _root_.Metric.closedBall (0 : E3) 1 \ C '' _root_.Metric.ball (0 : E3) 1) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨B (a.symm x), hcoord x hx, rfl⟩
    · rintro ⟨z, ⟨⟨v, hv, hvz⟩, hzC⟩, rfl⟩
      refine ⟨a v, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · rintro ⟨w, hw, hwa⟩
          have hvw : B.symm (C w) = v := a.toPartialEquiv.injOn
            (has ▸ _root_.Set.mem_univ _) (has ▸ _root_.Set.mem_univ _) hwa
          apply hzC
          exact ⟨w, hw, (hLC w (_root_.Metric.ball_subset_closedBall hw)).symm.trans
            ((congrArg B hvw).trans hvz)⟩
        · rw [hab']
          exact not_not.mpr ⟨v, hv, rfl⟩
      · change F (B (a.symm (a v))) = F z
        have ha_inv : a.symm (a v) = v := a.left_inv (has ▸ _root_.Set.mem_univ _)
        rw [ha_inv, hvz]
  have hbface : b '' _root_.Metric.sphere (0 : E3) 1 = a '' _root_.Metric.sphere (0 : E3) 1 := by
    have h := congrArg frontier hab
    rw [← b.image_frontier_of_isCompact (_root_.ProperSpace.isCompact_closedBall _ _) (hbs ▸ _root_.Set.subset_univ _),
      frontier_closedBall _ one_ne_zero, frontier_compl,
      DifferentialGeometry.Topology.Manifold.frontier_image_ball_of_partialDiffeomorph a
        (has ▸ _root_.Set.subset_univ _)] at h
    exact h
  have hPbs : P '' (b '' _root_.Metric.sphere (0 : E3) 1) = F '' (B '' _root_.Metric.sphere (0 : E3) 1) := by
    rw [hbface, _root_.Set.image_image, _root_.Set.image_image]
    apply _root_.Set.image_congr
    intro z hz
    change F (B (a.symm (a z))) = F (B z)
    have ha_inv : a.symm (a z) = z := a.left_inv (has ▸ _root_.Set.mem_univ _)
    rw [ha_inv]
  have hPC's : P '' (C' '' _root_.Metric.sphere (0 : E3) 1) = F '' (C '' _root_.Metric.sphere (0 : E3) 1) := by
    rw [_root_.Set.image_image, _root_.Set.image_image]
    apply _root_.Set.image_congr
    intro z hz
    change F (B (a.symm (a (B.symm (C z))))) = F (C z)
    have ha_inv : a.symm (a (B.symm (C z))) = B.symm (C z) := a.left_inv (has ▸ _root_.Set.mem_univ _)
    rw [ha_inv, hLC z (_root_.Metric.sphere_subset_closedBall hz)]
  obtain ⟨J, A, _, hA, hAi, hAf, _⟩ := exists_ball_chart_of_recapped_sphere_ball_complement
    C' b P G hC' (hbs ▸ _root_.Set.subset_univ _) hG hdis hPs
    (hPbs.trans hboundary) (by rw [himage]; exact hinter)
  have hAi' : A '' _root_.Metric.closedBall (0 : E3) 1 =
      F '' (B '' _root_.Metric.closedBall (0 : E3) 1 \ C '' _root_.Metric.ball (0 : E3) 1) ∪ G '' _root_.Metric.closedBall (0 : E3) 1 := by
    rw [himage] at hAi
    exact hAi
  have hAf' := hAf.trans hPC's
  let H := F.trans A.symm
  have hFHtarget (z : Z) (hz : z ∈ B '' _root_.Metric.closedBall (0 : E3) 1 \ C '' _root_.Metric.ball (0 : E3) 1) :
      F z ∈ A.target := by
    have hmem : F z ∈ A '' _root_.Metric.closedBall (0 : E3) 1 := by
      rw [hAi']
      exact Or.inl (_root_.Set.mem_image_of_mem F hz)
    obtain ⟨w, hw, heq⟩ := hmem
    exact heq ▸ A.map_source (hA hw)
  refine ⟨A, hA, hAi', hAf', H, ?_, ?_, ?_⟩
  · exact fun z hz => ⟨hF hz, hFHtarget z hz⟩
  · exact fun z hz => A.right_inv (hFHtarget z hz)
  · intro z hz
    obtain ⟨w, hw, heq⟩ := hAf'.symm ▸ _root_.Set.mem_image_of_mem F hz
    change A.symm.toPartialEquiv (F z) ∈ _root_.Metric.sphere (0 : E3) 1
    rw [← heq]
    exact (A.toPartialEquiv.left_inv (hA (_root_.Metric.sphere_subset_closedBall hw))).symm ▸ hw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_of_recapped_nested_ball_shell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_of_recapped_nested_ball_shell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_of_recapped_nested_ball_shell ``Submission.DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_of_recapped_nested_ball_shell

end

section

variable {Z M N : Type*} [TopologicalSpace Z] [ChartedSpace E3 Z]
  [TopologicalSpace M] [ChartedSpace E3 M]
  [TopologicalSpace N] [ChartedSpace E3 N] [T2Space N]

theorem exists_ball_chart_of_recapped_nested_ball_complements
    (C B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞)
    (F : PartialDiffeomorph (𝓡 3) (𝓡 3) Z M ∞)
    (P : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞)
    (G : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 N ∞)
    (hC : _root_.Metric.closedBall (0 : E3) 1 ⊆ C.source)
    (hB : _root_.Metric.closedBall (0 : E3) 1 ⊆ B.source)
    (hG : _root_.Metric.closedBall (0 : E3) 1 ⊆ G.source)
    (hF : (C '' _root_.Metric.ball (0 : E3) 1)ᶜ ⊆ F.source)
    (hside : (B '' _root_.Metric.ball (0 : E3) 1)ᶜ ⊆ (C '' _root_.Metric.closedBall (0 : E3) 1)ᶜ)
    {K : Set M}
    (hKi : F '' (B '' _root_.Metric.closedBall (0 : E3) 1)ᶜ = interior K)
    (hKf : F '' (B '' _root_.Metric.sphere (0 : E3) 1) = frontier K)
    (hP : F '' (C '' _root_.Metric.ball (0 : E3) 1)ᶜ \ interior K ⊆ P.source)
    (hboundary : P '' frontier K = G '' _root_.Metric.sphere (0 : E3) 1)
    (hinter : P '' (F '' (C '' _root_.Metric.ball (0 : E3) 1)ᶜ \ interior K) ∩
      G '' _root_.Metric.closedBall (0 : E3) 1 ⊆ G '' _root_.Metric.sphere (0 : E3) 1) :
    ∃ (A : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 N ∞)
      (H : PartialDiffeomorph (𝓡 3) (𝓡 3) M E3 ∞),
      _root_.Metric.closedBall (0 : E3) 1 ⊆ A.source ∧
      A '' _root_.Metric.closedBall (0 : E3) 1 =
        P '' (F '' (C '' _root_.Metric.ball (0 : E3) 1)ᶜ \ interior K) ∪ G '' _root_.Metric.closedBall (0 : E3) 1 ∧
      A '' _root_.Metric.sphere (0 : E3) 1 = P '' (F '' (C '' _root_.Metric.sphere (0 : E3) 1)) ∧
      F '' (C '' _root_.Metric.ball (0 : E3) 1)ᶜ \ interior K ⊆ H.source ∧
      (∀ x ∈ F '' (C '' _root_.Metric.ball (0 : E3) 1)ᶜ \ interior K, A (H x) = P x) ∧
      ∀ x ∈ F '' (C '' _root_.Metric.sphere (0 : E3) 1), H x ∈ _root_.Metric.sphere (0 : E3) 1 := by
  have hnest : C '' _root_.Metric.closedBall (0 : E3) 1 ⊆ B '' _root_.Metric.ball (0 : E3) 1 := by
    intro x hx
    by_contra hn
    exact hside hn hx
  have hBcomp : (B '' _root_.Metric.closedBall (0 : E3) 1)ᶜ ⊆ (C '' _root_.Metric.ball (0 : E3) 1)ᶜ := by
    intro x hx hxC
    exact hx (_root_.Set.image_mono _root_.Metric.ball_subset_closedBall
      (hnest (_root_.Set.image_mono _root_.Metric.ball_subset_closedBall hxC)))
  have hmodel : F '' (B '' _root_.Metric.closedBall (0 : E3) 1 \ C '' _root_.Metric.ball (0 : E3) 1) =
      F '' (C '' _root_.Metric.ball (0 : E3) 1)ᶜ \ interior K := by
    rw [← hKi]
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨⟨z, hz.2, rfl⟩, ?_⟩
      rintro ⟨y, hy, hyz⟩
      have he := F.toPartialEquiv.injOn (hF (hBcomp hy)) (hF hz.2) hyz
      exact hy (he.symm ▸ hz.1)
    · rintro ⟨⟨z, hz, rfl⟩, hn⟩
      refine ⟨z, ⟨?_, hz⟩, rfl⟩
      by_contra hzB
      exact hn ⟨z, hzB, rfl⟩
  have hFP : B '' _root_.Metric.closedBall (0 : E3) 1 \ C '' _root_.Metric.ball (0 : E3) 1 ⊆ (F.trans P).source := by
    intro z hz
    exact ⟨hF hz.2, hP (hmodel ▸ _root_.Set.mem_image_of_mem F hz)⟩
  have hbound : (F.trans P) '' (B '' _root_.Metric.sphere (0 : E3) 1) = G '' _root_.Metric.sphere (0 : E3) 1 := by
    change (P ∘ F) '' (B '' _root_.Metric.sphere (0 : E3) 1) = _
    rw [_root_.Set.image_comp, hKf, hboundary]
  have hFPimage : (F.trans P) '' (B '' _root_.Metric.closedBall (0 : E3) 1 \ C '' _root_.Metric.ball (0 : E3) 1) =
      P '' (F '' (C '' _root_.Metric.ball (0 : E3) 1)ᶜ \ interior K) := by
    change (P ∘ F) '' _ = _
    rw [_root_.Set.image_comp, hmodel]
  obtain ⟨A, hA, hAc, hAf, J, hJ, hAJ, hJS⟩ :=
    exists_ball_chart_of_recapped_nested_ball_shell C B (F.trans P) G hC hB hG hnest hFP hbound
      (by rw [hFPimage]; exact hinter)
  let H := F.symm.trans J
  have hcoord (x : M) (hx : x ∈ F '' (C '' _root_.Metric.ball (0 : E3) 1)ᶜ \ interior K) :
      F.symm x ∈ B '' _root_.Metric.closedBall (0 : E3) 1 \ C '' _root_.Metric.ball (0 : E3) 1 := by
    obtain ⟨z, hz, hzx⟩ := hmodel.symm ▸ hx
    rw [← hzx]
    have he : F.symm.toPartialEquiv (F.toPartialEquiv z) = z := F.toPartialEquiv.left_inv (hF hz.2)
    change F.symm.toPartialEquiv (F.toPartialEquiv z) ∈ _
    rw [he]
    exact hz
  refine ⟨A, H, hA, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [hFPimage] at hAc
  · change A '' _root_.Metric.sphere (0 : E3) 1 = (P ∘ F) '' (C '' _root_.Metric.sphere (0 : E3) 1) at hAf
    rw [_root_.Set.image_comp] at hAf
    exact hAf
  · intro x hx
    obtain ⟨z, hz, hzx⟩ := hx.1
    exact ⟨hzx ▸ F.map_source (hF hz), hJ (hcoord x hx)⟩
  · intro x hx
    have he := hAJ (F.symm x) (hcoord x hx)
    change A (J (F.symm x)) = P x
    refine he.trans ?_
    change P (F (F.symm x)) = P x
    obtain ⟨z, hz, hzx⟩ := hx.1
    have hcancel : F.toPartialEquiv (F.symm.toPartialEquiv x) = x :=
      F.toPartialEquiv.right_inv (hzx ▸ F.map_source (hF hz))
    rw [hcancel]
  · rintro x ⟨z, hz, rfl⟩
    have hzsource : z ∈ F.source := by
      apply hF
      rintro ⟨w, hw, hwz⟩
      obtain ⟨v, hv, hvz⟩ := hz
      have he := C.toPartialEquiv.injOn (hC (_root_.Metric.ball_subset_closedBall hw))
        (hC (_root_.Metric.sphere_subset_closedBall hv)) (hwz.trans hvz.symm)
      exact (mem_ball_zero_iff.mp (he ▸ hw)).ne (mem_sphere_zero_iff_norm.mp hv)
    change J (F.symm (F z)) ∈ _root_.Metric.sphere (0 : E3) 1
    have he : F.symm.toPartialEquiv (F.toPartialEquiv z) = z := F.toPartialEquiv.left_inv hzsource
    rw [he]
    exact hJS z hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_of_recapped_nested_ball_complements then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_of_recapped_nested_ball_complements"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_of_recapped_nested_ball_complements ``Submission.DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_of_recapped_nested_ball_complements

end

section

variable {Z M N ι : Type*} [TopologicalSpace Z] [ChartedSpace E3 Z] [T2Space Z]
  [TopologicalSpace M] [ChartedSpace E3 M] [T3Space M]
  [TopologicalSpace N] [ChartedSpace E3 N] [T2Space N]

theorem exists_ball_chart_of_finitely_recapped_nested_ball_complements
    (C B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞)
    (F : PartialDiffeomorph (𝓡 3) (𝓡 3) Z M ∞)
    (P : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞)
    (G : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 N ∞)
    (s : Finset ι)
    (b : ι → PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (g : ι → PartialDiffeomorph (𝓡 3) (𝓡 3) E3 N ∞)
    (hC : _root_.Metric.closedBall (0 : E3) 1 ⊆ C.source)
    (hB : _root_.Metric.closedBall (0 : E3) 1 ⊆ B.source)
    (hG : _root_.Metric.closedBall (0 : E3) 1 ⊆ G.source)
    (hb : ∀ i ∈ s, _root_.Metric.closedBall (0 : E3) 1 ⊆ (b i).source)
    (hg : ∀ i ∈ s, _root_.Metric.closedBall (0 : E3) 1 ⊆ (g i).source)
    (hF : (C '' _root_.Metric.ball (0 : E3) 1)ᶜ ⊆ F.source)
    (hside : (B '' _root_.Metric.ball (0 : E3) 1)ᶜ ⊆ (C '' _root_.Metric.closedBall (0 : E3) 1)ᶜ)
    {K W : Set M} (hK : IsClosed K)
    (hKi : F '' (B '' _root_.Metric.closedBall (0 : E3) 1)ᶜ = interior K)
    (hKf : F '' (B '' _root_.Metric.sphere (0 : E3) 1) = frontier K)
    (hKΩ : K ⊆ interior (F '' (C '' _root_.Metric.ball (0 : E3) 1)ᶜ))
    (hbΩ : ∀ i ∈ s, b i '' _root_.Metric.closedBall (0 : E3) 1 ⊆ interior (F '' (C '' _root_.Metric.ball (0 : E3) 1)ᶜ))
    (hbK : ∀ i ∈ s, Disjoint (b i '' _root_.Metric.closedBall (0 : E3) 1) K)
    (hdisb : (s : Set ι).Pairwise (fun i j => Disjoint
      (b i '' _root_.Metric.closedBall (0 : E3) 1) (b j '' _root_.Metric.closedBall (0 : E3) 1)))
    (hdisg : (s : Set ι).Pairwise (fun i j => Disjoint
      (g i '' _root_.Metric.closedBall (0 : E3) 1) (g j '' _root_.Metric.closedBall (0 : E3) 1)))
    (hgG : ∀ i ∈ s, Disjoint (g i '' _root_.Metric.closedBall (0 : E3) 1) (G '' _root_.Metric.closedBall (0 : E3) 1))
    (hW : W = F '' (C '' _root_.Metric.ball (0 : E3) 1)ᶜ \ (interior K ∪ ⋃ i ∈ s, b i '' _root_.Metric.ball (0 : E3) 1))
    (hP : W ⊆ P.source)
    (hboundary : ∀ i ∈ s, P '' (b i '' _root_.Metric.sphere (0 : E3) 1) = g i '' _root_.Metric.sphere (0 : E3) 1)
    (hboundaryG : P '' frontier K = G '' _root_.Metric.sphere (0 : E3) 1)
    (hinter : ∀ i ∈ s, P '' W ∩ g i '' _root_.Metric.closedBall (0 : E3) 1 ⊆ g i '' _root_.Metric.sphere (0 : E3) 1)
    (hinterG : P '' W ∩ G '' _root_.Metric.closedBall (0 : E3) 1 ⊆ G '' _root_.Metric.sphere (0 : E3) 1) :
    ∃ (A : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 N ∞)
      (H : PartialDiffeomorph (𝓡 3) (𝓡 3) M E3 ∞)
      (Q : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞),
      _root_.Metric.closedBall (0 : E3) 1 ⊆ A.source ∧
      H = Q.trans A.symm ∧
      _root_.Set.MapsTo H (F '' (C '' _root_.Metric.ball (0 : E3) 1)ᶜ \ interior K) (_root_.Metric.closedBall (0 : E3) 1) ∧
      A '' _root_.Metric.closedBall (0 : E3) 1 = P '' W ∪
        (⋃ i ∈ s, g i '' _root_.Metric.closedBall (0 : E3) 1) ∪ G '' _root_.Metric.closedBall (0 : E3) 1 ∧
      A '' _root_.Metric.sphere (0 : E3) 1 = P '' (F '' (C '' _root_.Metric.sphere (0 : E3) 1)) ∧
      (F '' (C '' _root_.Metric.ball (0 : E3) 1)ᶜ \ interior K) ⊆ Q.source ∧
      Q '' (F '' (C '' _root_.Metric.ball (0 : E3) 1)ᶜ \ interior K) = P '' W ∪ ⋃ i ∈ s, g i '' _root_.Metric.closedBall (0 : E3) 1 ∧
      (F '' (C '' _root_.Metric.ball (0 : E3) 1)ᶜ \ interior K) ⊆ H.source ∧
      (∀ x ∈ F '' (C '' _root_.Metric.ball (0 : E3) 1)ᶜ \ interior K, A (H x) = Q x) ∧
      (∀ x ∈ W, A (H x) = P x) ∧
      (∀ i ∈ s, ∃ D : E3 ≃ₘ[ℝ] E3,
        D '' _root_.Metric.closedBall (0 : E3) 1 = _root_.Metric.closedBall (0 : E3) 1 ∧
        ∀ z ∈ _root_.Metric.closedBall (0 : E3) 1, A (H (b i z)) = g i (D z)) ∧
      (∀ x ∈ F '' (C '' _root_.Metric.sphere (0 : E3) 1), H x ∈ _root_.Metric.sphere (0 : E3) 1) ∧
      ∃ O : Set M, IsOpen O ∧ W ⊆ O ∧ O ⊆ P.source ∧ _root_.Set.EqOn Q P O := by
  let Ω := F '' (C '' _root_.Metric.ball (0 : E3) 1)ᶜ
  let S := Ω \ interior K
  have hnest : C '' _root_.Metric.closedBall (0 : E3) 1 ⊆ B '' _root_.Metric.ball (0 : E3) 1 := by
    intro x hx
    by_contra hn
    exact hside hn hx
  have hBcomp : (B '' _root_.Metric.closedBall (0 : E3) 1)ᶜ ⊆ (C '' _root_.Metric.ball (0 : E3) 1)ᶜ := by
    intro x hx hxC
    exact hx (_root_.Set.image_mono _root_.Metric.ball_subset_closedBall (hnest (_root_.Set.image_mono _root_.Metric.ball_subset_closedBall hxC)))
  have hmodel : F '' (B '' _root_.Metric.closedBall (0 : E3) 1 \ C '' _root_.Metric.ball (0 : E3) 1) = S := by
    dsimp only [S,Ω]
    rw [← hKi]
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      refine ⟨⟨z,hz.2,rfl⟩,?_⟩
      rintro ⟨y,hy,hyz⟩
      have he := F.injOn (hF (hBcomp hy)) (hF hz.2) hyz
      exact hy (he.symm ▸ hz.1)
    · rintro ⟨⟨z,hz,rfl⟩,hn⟩
      refine ⟨z,⟨?_,hz⟩,rfl⟩
      by_contra hzB
      exact hn ⟨z,hzB,rfl⟩
  have hCopen : IsOpen (C '' _root_.Metric.ball (0 : E3) 1) :=
    C.toOpenPartialHomeomorph.isOpen_image_of_subset_source _root_.Metric.isOpen_ball (ball_subset_closedBall.trans hC)
  have hS : IsCompact S := by
    rw [← hmodel]
    apply IsCompact.image_of_continuousOn
      (((_root_.ProperSpace.isCompact_closedBall (0 : E3) 1).image_of_continuousOn
        (B.contMDiffOn_toFun.continuousOn.mono hB)).diff hCopen)
    exact F.contMDiffOn_toFun.continuousOn.mono (fun x hx => hF hx.2)
  have hbS (i : ι) (hi : i ∈ s) : b i '' _root_.Metric.closedBall (0 : E3) 1 ⊆ interior S := by
    have ho : IsOpen (interior Ω \ K) := isOpen_interior.sdiff hK
    apply subset_trans _ (ho.subset_interior_iff.mpr _)
    · intro x hx
      exact ⟨hbΩ i hi hx,disjoint_left.mp (hbK i hi) hx⟩
    · intro x hx
      exact ⟨interior_subset hx.1,fun h => hx.2 (interior_subset h)⟩
  have hres : S \ ⋃ i ∈ s, b i '' _root_.Metric.ball (0 : E3) 1 = W := by
    rw [hW]
    dsimp [S,Ω]
    ext x
    simp only [_root_.Set.mem_sdiff,_root_.Set.mem_union,not_or]
    tauto
  obtain ⟨Q,hQ,hQi,hQballs,O,hO,hWO,hOP,hQP⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_finite_ball_replacement_eqOn_complement
      s b g hb hg hS hbS hdisb hdisg P (hres.symm ▸ hP) hboundary
      (fun i hi => hres.symm ▸ hinter i hi)
  rw [hres] at hQi hWO
  have hKfW : frontier K ⊆ W := by
    intro x hx
    rw [hW]
    refine ⟨interior_subset (hKΩ (hK.frontier_subset hx)),?_⟩
    rintro (hxK | hxB)
    · exact hx.2 hxK
    · obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp hxB
      exact disjoint_left.mp (hbK i hi) (_root_.Set.image_mono _root_.Metric.ball_subset_closedBall hxi) (hK.frontier_subset hx)
  have hΩint : interior Ω = F '' (C '' _root_.Metric.closedBall (0 : E3) 1)ᶜ := by
    have h := F.toOpenPartialHomeomorph.image_interior_of_subset_source hF
    change F '' interior (C '' _root_.Metric.ball (0 : E3) 1)ᶜ = interior Ω at h
    rw [interior_compl,DifferentialGeometry.Topology.Manifold.closure_image_ball_of_partialDiffeomorph C hC] at h
    exact h.symm
  have houterW : F '' (C '' _root_.Metric.sphere (0 : E3) 1) ⊆ W := by
    rintro x ⟨z,hz,rfl⟩
    have hzΩ : z ∈ (C '' _root_.Metric.ball (0 : E3) 1)ᶜ := by
      obtain ⟨w,hw,rfl⟩ := hz
      rintro ⟨v,hv,heq⟩
      have hvw := C.injOn (hC (_root_.Metric.ball_subset_closedBall hv)) (hC (_root_.Metric.sphere_subset_closedBall hw)) heq
      exact (mem_ball_zero_iff.mp (hvw ▸ hv)).ne (mem_sphere_zero_iff_norm.mp hw)
    have hnotint : F z ∉ interior Ω := by
      rw [hΩint]
      rintro ⟨y,hy,hyz⟩
      have hyΩ : y ∈ (C '' _root_.Metric.ball (0 : E3) 1)ᶜ :=
        fun h => hy (_root_.Set.image_mono _root_.Metric.ball_subset_closedBall h)
      have he := F.injOn (hF hyΩ) (hF hzΩ) hyz
      exact hy (he.symm ▸ _root_.Set.image_mono _root_.Metric.sphere_subset_closedBall hz)
    rw [hW]
    refine ⟨mem_image_of_mem F hzΩ,?_⟩
    rintro (hxK | hxB)
    · exact hnotint (hKΩ (interior_subset hxK))
    · obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp hxB
      exact hnotint (hbΩ i hi (_root_.Set.image_mono _root_.Metric.ball_subset_closedBall hxi))
  have hQboundary : Q '' frontier K = G '' _root_.Metric.sphere (0 : E3) 1 :=
    ((hQP.mono (hKfW.trans hWO)).image_eq).trans hboundaryG
  have hQinter : Q '' S ∩ G '' _root_.Metric.closedBall (0 : E3) 1 ⊆ G '' _root_.Metric.sphere (0 : E3) 1 := by
    rw [hQi]
    rintro x ⟨hx,hxG⟩
    rcases hx with hxP | hxg
    · exact hinterG ⟨hxP,hxG⟩
    · obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp hxg
      exact (disjoint_left.mp (hgG i hi) hxi hxG).elim
  obtain ⟨A,_,hA,hAi,hAf,_,_,_⟩ :=
    exists_ball_chart_of_recapped_nested_ball_complements C B F Q G hC hB hG hF hside
      hKi hKf hQ hQboundary hQinter
  let H := Q.trans A.symm
  have hQt (x : M) (hx : x ∈ S) : Q x ∈ A.target := by
    have hmem : Q x ∈ A '' _root_.Metric.closedBall (0 : E3) 1 := by
      rw [hAi]
      exact Or.inl (_root_.Set.mem_image_of_mem Q hx)
    obtain ⟨z,hz,hzq⟩ := hmem
    exact hzq ▸ A.map_source (hA hz)
  have hH : S ⊆ H.source := fun x hx => ⟨hQ hx,hQt x hx⟩
  have hAH (x : M) (hx : x ∈ S) : A (H x) = Q x := A.right_inv (hQt x hx)
  have hHclosed : _root_.Set.MapsTo H S (_root_.Metric.closedBall (0 : E3) 1) := by
    intro x hx
    have hmem : Q x ∈ A '' _root_.Metric.closedBall (0 : E3) 1 := by
      rw [hAi]
      exact Or.inl (_root_.Set.mem_image_of_mem Q hx)
    obtain ⟨z,hz,hzq⟩ := hmem
    change A.symm (Q x) ∈ _root_.Metric.closedBall (0 : E3) 1
    have hleft : A.symm.toPartialEquiv (A.toPartialEquiv z) = z := A.toPartialEquiv.left_inv (hA hz)
    rw [← hzq,hleft]
    exact hz
  have hHS (x : M) (hx : x ∈ F '' (C '' _root_.Metric.sphere (0 : E3) 1)) : H x ∈ _root_.Metric.sphere (0 : E3) 1 := by
    obtain ⟨z,hz,hzx⟩ := hAf.symm ▸ _root_.Set.mem_image_of_mem Q hx
    change A.symm (Q x) ∈ _root_.Metric.sphere (0 : E3) 1
    have hleft : A.symm.toPartialEquiv (A.toPartialEquiv z) = z := A.toPartialEquiv.left_inv (hA (_root_.Metric.sphere_subset_closedBall hz))
    rw [← hzx,hleft]
    exact hz
  have hAi' : A '' _root_.Metric.closedBall (0 : E3) 1 = P '' W ∪
      (⋃ i ∈ s, g i '' _root_.Metric.closedBall (0 : E3) 1) ∪ G '' _root_.Metric.closedBall (0 : E3) 1 := by
    rw [hQi] at hAi
    exact hAi
  have hAf' : A '' _root_.Metric.sphere (0 : E3) 1 = P '' (F '' (C '' _root_.Metric.sphere (0 : E3) 1)) :=
    hAf.trans ((hQP.mono (houterW.trans hWO)).image_eq)
  refine ⟨A,H,Q,hA,rfl,hHclosed,hAi',hAf',hQ,hQi,hH,hAH,?_,?_,hHS,O,hO,hWO,hOP,hQP⟩
  · intro x hx
    have hxS : x ∈ S := by
      rw [← hres] at hx
      exact hx.1
    exact (hAH x hxS).trans (hQP (hWO hx))
  · intro i hi
    obtain ⟨D,hD,hQD⟩ := hQballs i hi
    refine ⟨D,hD,?_⟩
    intro z hz
    exact (hAH (b i z) (interior_subset (hbS i hi (_root_.Set.mem_image_of_mem (b i) hz)))).trans (hQD z hz)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_of_finitely_recapped_nested_ball_complements then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_of_finitely_recapped_nested_ball_complements"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_of_finitely_recapped_nested_ball_complements ``Submission.DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_of_finitely_recapped_nested_ball_complements

end

end DifferentialGeometry.Topology.ThreeManifold
