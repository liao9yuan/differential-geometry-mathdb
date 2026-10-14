import Submission.DifferentialGeometry.Topology.ThreeManifold.CapCollarMatching
import Submission.DifferentialGeometry.Topology.ThreeManifold.CapBoundaryExtension
import Submission.DifferentialGeometry.Topology.Manifold.ClosedBall.Diffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Metric _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1
local notation "Half" => _root_.Set.Ico (0 : ℝ) (1 / 2)

private local instance capDimension : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCapping.capDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCapping.capDimension target :: scope.openDecls } }
private local instance capClosedCellCharts : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) := Handle.closedCellChartedSpaceSucc 2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCapping.capClosedCellCharts
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCapping.capClosedCellCharts target :: scope.openDecls } }
private local instance capClosedCellSmooth : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) := Handle.closedCellIsManifold 2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCapping.capClosedCellSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCapping.capClosedCellSmooth target :: scope.openDecls } }

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T) (b : T.Boundary)

private theorem radialPartialDiffeomorph_eq_cap
    (d : SmoothTwoSidedCollar (𝓡 2) (𝓡 3) (C.cap b ∘ sphereToClosedCell)) (v : S2)
    (hdin : ∀ (p : S2 × symmetricOpenInterval d.radius), 0 ≤ p.2.val →
      ∃ x : ClosedCell 3, x.val = (1 - p.2.val) • p.1.val ∧ d.toFun p = C.cap b x)
    (x : ClosedCell 3) (hx : x.val ∈ (d.radialPartialDiffeomorph v).source) :
    d.radialPartialDiffeomorph v x.val = C.cap b x := by
  obtain ⟨hxne, ht⟩ := (d.mem_radialPartialDiffeomorph_source_iff v x.val).mp hx
  let z := Manifold.sphereDirection v x.val
  have h := d.radialPartialDiffeomorph_apply v z ‖x.val‖ (norm_pos_iff.mpr hxne) ht
  rw [Manifold.norm_smul_sphereDirection v hxne] at h
  obtain ⟨y, hy, hd⟩ := hdin (z, ⟨1 - ‖x.val‖, ht⟩) (sub_nonneg.mpr x.property)
  have hyx : y = x := by
    apply Subtype.ext
    rw [hy]
    dsimp only
    rw [sub_sub_cancel]
    exact Manifold.norm_smul_sphereDirection v hxne
  exact h.trans (hyx ▸ hd)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCapping.radialPartialDiffeomorph_eq_cap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCapping.radialPartialDiffeomorph_eq_cap target :: scope.openDecls } }

theorem exists_cap_normalization (v : S2) :
    ∃ (B : ClosedCell 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3)
      (e : SmoothTwoSidedCollar (𝓡 2) (𝓡 3) (C.cap b ∘ sphereToClosedCell)),
      (∀ x : ClosedCell 3, ‖x.val‖ ≤ 1 / 2 → B x = x) ∧
      (∀ z : S2, B (sphereToClosedCell z) = sphereToClosedCell z) ∧
      (∃ he : e.radius ≤ 1 / 2, ∀ (p : S2 × symmetricOpenInterval e.radius) (hp : 0 ≤ p.2.val),
        e.toFun p = C.coreInclusionHalfCollar b
          (p.1, ⟨p.2.val, hp, p.2.property.2.trans_le he⟩)) ∧
      ∃ V : Set E3, IsOpen V ∧ _root_.Metric.sphere (0 : E3) 1 ⊆ V ∧
        (∀ x : ClosedCell 3, x.val ∈ V → x.val ∈ (e.reverse.radialPartialDiffeomorph v).source ∧
          C.cap b (B x) = e.reverse.radialPartialDiffeomorph v x.val) ∧
        (∀ x : ClosedCell 3, x.val ∈ V → C.coreBoundaryExtension b e v (C.cap b (B x)) =
          T.radialTube b.1 (C.attaching b) b.2 v x.val) ∧
        ∀ z : S2, IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (C.coreBoundaryExtension b e v)
          (C.cap b (sphereToClosedCell z)) := by
  obtain ⟨d, e, _, he, hdin, heq, D, V, hV, hSV, hdom, hmatch, hfixS, hball, hfix, _⟩ :=
    C.exists_cap_core_collar_matching b v
  let B := Manifold.closedCellDiffeomorph D hball
  have hcap (x : ClosedCell 3) (hx : x.val ∈ V) :
      C.cap b (B x) = e.reverse.radialPartialDiffeomorph v x.val := by
    have hd : d.radialPartialDiffeomorph v (B x).val = C.cap b (B x) :=
      radialPartialDiffeomorph_eq_cap C b d v hdin (B x) (hdom x.val hx).2
    exact hd.symm.trans (hmatch x.val hx)
  refine ⟨B, e, ?_, ?_, ⟨he, heq⟩, V, hV, hSV, ?_, ?_,
    C.isLocalDiffeomorphAt_coreBoundaryExtension b e v⟩
  · intro x hx
    apply Subtype.ext
    exact (hfix x.val hx).1
  · intro z
    apply Subtype.ext
    exact hfixS z.property
  · intro x hx
    exact ⟨(hdom x.val hx).1, hcap x hx⟩
  · intro x hx
    rw [hcap x hx]
    exact C.coreBoundaryExtension_radial b e v x.val (hdom x.val hx).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.exists_cap_normalization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.exists_cap_normalization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.exists_cap_normalization ``Submission.DifferentialGeometry.Topology.SphericalCapping.exists_cap_normalization

end DifferentialGeometry.Topology.SphericalCapping
