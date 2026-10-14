import Submission.DifferentialGeometry.External.Schoenflies.JordanSchoenflies
import Mathlib.Analysis.Convex.GaugeRescale

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Metric _root_.Topology

namespace DifferentialGeometry.Topology.PlanarJordan

private theorem closed_region_homeomorph_ball
    {U : Set Schoenflies.Plane} (hU : IsOpen U) (hconn : IsConnected U)
    (hbounded : Bornology.IsBounded U)
    (hC : Schoenflies.IsJordanCurve (frontier U)) :
    Nonempty (closure U ≃ₜ _root_.Metric.closedBall (0 : Schoenflies.Plane) 1) := by
  obtain ⟨x, hx⟩ := hconn.nonempty
  have hsub : U ⊆ (frontier U)ᶜ := by
    intro z hz hfr
    exact (hU.frontier_eq ▸ hfr).2 hz
  have hcomponent : connectedComponentIn (frontier U)ᶜ x = U :=
    Schoenflies.Plane.connectedComponentIn_eq_of_frontier_disjoint hU
      hconn.isPreconnected hsub (_root_.Set.inter_compl_self _) hx
  have hxinside : x ∈ Schoenflies.inside (frontier U) :=
    ⟨hsub hx, hcomponent.symm ▸ hbounded⟩
  have hinside : Schoenflies.inside (frontier U) = U :=
    ((Schoenflies.jordan_curve_theorem hC).connectedComponentIn_eq_inside hxinside).symm.trans
      hcomponent
  obtain ⟨e⟩ := hC.homeomorph_modelCurve
  obtain ⟨f, g, hfg, _⟩ := Schoenflies.exists_isHomeoOn_of_homeomorph e
  obtain ⟨F, G, hFG, _⟩ := Schoenflies.squareExtension _ f g hC hfg
  have hunion : frontier U ∪ Schoenflies.inside (frontier U) = closure U := by
    rw [hinside, _root_.Set.union_comm, ← closure_eq_self_union_frontier]
  rw [hunion] at hFG
  let d : closure U ≃ₜ Schoenflies.Plane.closedSquare 0 1 := {
    toFun z := ⟨F z, hFG.mapsTo z.property⟩
    invFun z := ⟨G z, hFG.mapsTo_inv z.property⟩
    left_inv z := Subtype.ext (hFG.invOn.1 z.property)
    right_inv z := Subtype.ext (hFG.invOn.2 z.property)
    continuous_toFun := hFG.continuousOn.domRestrict.subtype_mk _
    continuous_invFun := hFG.continuousOn_inv.domRestrict.subtype_mk _ }
  obtain ⟨r, _, hr, _⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (Schoenflies.Plane.convex_closedSquare 0 1)
    (by rw [Schoenflies.Plane.interior_closedSquare]
        exact ⟨0, Schoenflies.Plane.mem_openSquare_self zero_lt_one⟩)
    (Schoenflies.Plane.isBounded_closedSquare 0 1)
  rw [(Schoenflies.Plane.isClosed_closedSquare 0 1).closure_eq] at hr
  exact ⟨d.trans ((r.image _).trans (Homeomorph.setCongr hr))⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PlanarJordan.closed_region_homeomorph_ball
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PlanarJordan.closed_region_homeomorph_ball target :: scope.openDecls } }

theorem nonempty_homeomorph_closedBall_closure
    {U : Set ℂ} (hU : IsOpen U) (hconn : IsConnected U)
    (hcompact : IsCompact (closure U))
    {γ : ℝ → ℂ} (hγ : ContinuousOn γ (_root_.Set.Icc 0 1)) (hclose : γ 0 = γ 1)
    (hinj : _root_.Set.InjOn γ (_root_.Set.Ico 0 1)) (hfrontier : frontier U = γ '' _root_.Set.Icc 0 1) :
    Nonempty (_root_.Metric.closedBall (0 : ℂ) 1 ≃ₜ closure U) := by
  let l := Complex.orthonormalBasisOneI.repr
  let e : ℂ ≃ₜ Schoenflies.Plane := l.toHomeomorph
  let W := e '' U
  have hW : IsOpen W := e.isOpenMap U hU
  have hWconn : IsConnected W := hconn.image e e.continuous.continuousOn
  have hWcompact : IsCompact (closure W) := by
    rw [← e.image_closure]
    exact hcompact.image e.continuous
  have hCW : Schoenflies.IsJordanCurve (frontier W) := by
    refine ⟨fun t ↦ e (γ t), ⟨e.continuous.comp_continuousOn hγ,
      congrArg e hclose, fun _ hx _ hy he ↦ hinj hx hy (e.injective he)⟩, ?_⟩
    rw [← e.image_frontier, hfrontier, _root_.Set.image_image]
  obtain ⟨d⟩ := closed_region_homeomorph_ball hW hWconn
    (hWcompact.isBounded.subset subset_closure) hCW
  let b : _root_.Metric.closedBall (0 : ℂ) 1 ≃ₜ _root_.Metric.closedBall (0 : Schoenflies.Plane) 1 :=
    e.subtype (fun z ↦ by
      simp only [_root_.Metric.mem_closedBall, dist_zero_right]
      change ‖z‖ ≤ 1 ↔ ‖l z‖ ≤ 1
      rw [l.norm_map])
  let a : closure U ≃ₜ closure W :=
    (e.image (closure U)).trans (Homeomorph.setCongr (e.image_closure U))
  exact ⟨b.trans (d.symm.trans a.symm)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.nonempty_homeomorph_closedBall_closure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.nonempty_homeomorph_closedBall_closure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.nonempty_homeomorph_closedBall_closure ``Submission.DifferentialGeometry.Topology.PlanarJordan.nonempty_homeomorph_closedBall_closure

end DifferentialGeometry.Topology.PlanarJordan
