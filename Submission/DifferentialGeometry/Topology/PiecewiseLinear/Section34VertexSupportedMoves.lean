/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.DisjointSupportedHomeomorphs
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34IncidentEdgeFinite

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Function

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type*} [TopologicalSpace M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [PseudoMetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Ω : Section34EdgeIndex 𝒦 𝒦' → Set M₂}
  {δ : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {φ : Section34EdgeIndex 𝒦 𝒦' → M₂ ≃ₜ M₂}

theorem exists_section34_vertex_supported_moves
    (hends : ∀ e, (e.1 : Set Ea) =
      ((ends e).1.1 : Set Ea) ∪ ((ends e).2.1 : Set Ea))
    (hdis : Pairwise (Disjoint on Ω)) (hδ : ∀ w, 0 < δ w)
    (hφ : ∀ e, IsPL 3 3 (φ e)) (hφinv : ∀ e, IsPL 3 3 (φ e).symm)
    (hfix : ∀ e, _root_.Set.EqOn (φ e) id (Ω e)ᶜ)
    (hdist : ∀ e, ∀ y ∈ Ω e, _root_.Dist.dist (φ e y) y < δ (ends e).1) :
    ∃ Φ : Section34VertexIndex 𝒦 𝒦' → M₂ ≃ₜ M₂,
      (∀ w, IsPL 3 3 (Φ w)) ∧ (∀ w, IsPL 3 3 (Φ w).symm) ∧
      (∀ w y, _root_.Dist.dist (Φ w y) y < δ w) ∧
      (∀ e, _root_.Set.EqOn (Φ (ends e).1) (φ e) (Ω e)) ∧
      (∀ w e, w ≠ (ends e).1 → _root_.Set.EqOn (Φ w) id (Ω e)) ∧
      (∀ w e, Φ w '' Ω e = Ω e) ∧
      ∀ w, _root_.Set.EqOn (Φ w) id (⋃ e : Section34EdgeIndex 𝒦 𝒦', ⋃ (_ : (ends e).1 = w), Ω e)ᶜ := by
  classical
  have hfinite (w : Section34VertexIndex 𝒦 𝒦') :
      {e : Section34EdgeIndex 𝒦 𝒦' | (ends e).1 = w}.Finite := by
    have hi : {e : Section34EdgeIndex 𝒦 𝒦' |
        w = (ends e).1 ∨ w = (ends e).2}.Finite :=
      Set.finite_coe_iff.mp (section34_incident_edges_finite hends w)
    exact hi.subset fun _ he => Or.inl he.symm
  let s (w : Section34VertexIndex 𝒦 𝒦') := (hfinite w).toFinset
  have hmem (w : Section34VertexIndex 𝒦 𝒦') (e : Section34EdgeIndex 𝒦 𝒦') :
      e ∈ s w ↔ (ends e).1 = w := (hfinite w).mem_toFinset
  have hw (w : Section34VertexIndex 𝒦 𝒦') :=
    exists_isPL_homeomorph_of_finite_disjoint_support (s w) Ω φ hdis
      (fun e _ => hφ e) (fun e _ => hφinv e) (fun e _ => hfix e)
  choose Φ hΦ hΦinv heq hΦfix using hw
  refine ⟨Φ, hΦ, hΦinv, ?_, ?_, ?_, ?_, ?_⟩
  · intro w
    apply dist_lt_of_disjoint_support (fun _ => hδ w) (heq w) (hΦfix w)
    intro e he y hy
    rw [← (hmem w e).mp he]
    exact hdist e y hy
  · intro e
    exact heq _ e ((hmem _ e).mpr rfl)
  · intro w e hwe
    exact homeomorph_eqOn_of_disjoint_support hdis (hΦfix w)
      (fun he => hwe ((hmem w e).mp he).symm)
  · intro w
    exact homeomorph_image_eq_of_disjoint_support hdis (fun e _ => hfix e) (heq w) (hΦfix w)
  · intro w
    simpa only [hmem] using hΦfix w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_section34_vertex_supported_moves then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_section34_vertex_supported_moves"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_section34_vertex_supported_moves ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_section34_vertex_supported_moves

end DifferentialGeometry.Topology.PiecewiseLinear
