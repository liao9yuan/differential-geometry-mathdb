import Submission.DifferentialGeometry.Topology.SphereSeparation.BicollarAxialOrder
import Submission.DifferentialGeometry.Topology.SphereSeparation.BicollarSliceOrder

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Metric _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

section SimplyConnected

variable {A M : Type*} [TopologicalSpace A] [T2Space A] [CompactSpace A] [ConnectedSpace A]
  [TopologicalSpace M] [T2Space M] [SimplyConnectedSpace M] [LocallyPathConnectedSpace M]
  (r : ℝ) (hr : 0 < r)
  (φ : {p : A × ℝ // -r < p.2 ∧ p.2 < r} → M) (hφ : IsOpenEmbedding φ) (a : A)

include hφ

local notation "Φ" => φ ∘ bicollarLineHomeomorph r hr
local notation "σ" => OpenPartialHomeomorph.symm (OpenPartialHomeomorph.univBall (0 : ℝ) r)

theorem finite_bicollar_ordered_band
    (hzero : IsCompact (closure (bicollarLowerSide Φ a 0)))
    (s t : ℝ) (hs : -r < s ∧ s < r) (ht : -r < t ∧ t < r) (hst : s < t) :
    closure (bicollarLowerSide Φ a (σ s)) ⊆ bicollarLowerSide Φ a (σ t) ∧
      closure (bicollarLowerSide Φ a (σ t)) =
        closure (bicollarLowerSide Φ a (σ s)) ∪ φ '' {q | s ≤ q.val.2 ∧ q.val.2 ≤ t} ∧
      (φ '' {q | s ≤ q.val.2 ∧ q.val.2 ≤ t})ᶜ =
        bicollarLowerSide Φ a (σ s) ∪ bicollarUpperSide Φ a (σ t) := by
  have hΦ : _root_.Topology.IsOpenEmbedding Φ := hφ.comp (bicollarLineHomeomorph r hr).isOpenEmbedding
  have hστ := (bicollar_axial_inverse_lt_iff r hr s t hs ht).mpr hst
  have hband : Φ '' ((_root_.Set.univ : Set A) ×ˢ _root_.Set.Icc (σ s) (σ t)) =
      φ '' {q | s ≤ q.val.2 ∧ q.val.2 ≤ t} := by
    rw [_root_.Set.image_comp, bicollarLineHomeomorph_image_band r hr s t hs ht]
  obtain ⟨hnested, hclosure, hcompl⟩ := bicollar_ordered_band Φ hΦ a hzero hστ
  rw [hband] at hclosure hcompl
  exact ⟨hnested, hclosure, hcompl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.finite_bicollar_ordered_band then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.finite_bicollar_ordered_band"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.finite_bicollar_ordered_band ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.finite_bicollar_ordered_band

theorem finite_bicollar_slice_frontiers (s : ℝ) (hs : -r < s ∧ s < r) :
    frontier (bicollarLowerSide Φ a (σ s)) = _root_.Set.range (fun y => φ ⟨(y, s), hs⟩) ∧
      frontier (bicollarUpperSide Φ a (σ s)) = _root_.Set.range (fun y => φ ⟨(y, s), hs⟩) ∧
      interior (closure (bicollarLowerSide Φ a (σ s))) = bicollarLowerSide Φ a (σ s) := by
  have hΦ : _root_.Topology.IsOpenEmbedding Φ := hφ.comp (bicollarLineHomeomorph r hr).isOpenEmbedding
  have hslice : _root_.Set.range (fun y => Φ (y, σ s)) = _root_.Set.range (fun y => φ ⟨(y, s), hs⟩) := by
    congr 1
    funext y
    change φ (bicollarLineHomeomorph r hr (y, σ s)) = φ ⟨(y, s), hs⟩
    rw [bicollarLineHomeomorph_slice r hr s hs y]
  obtain ⟨_hB, _hE, _hBop, _hEop, _hBE, _hcover, hBfr, hEfr, _hBcl, _hEcl,
    _hn, _hp⟩ := bicollar_slice_components Φ hΦ a (σ s)
  rw [hslice] at hBfr hEfr
  exact ⟨hBfr, hEfr, bicollar_lower_regular_open Φ hΦ a (σ s)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.finite_bicollar_slice_frontiers then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.finite_bicollar_slice_frontiers"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.finite_bicollar_slice_frontiers ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.finite_bicollar_slice_frontiers

theorem finite_bicollar_path_crosses_slice (s : ℝ) (hs : -r < s ∧ s < r)
    {x y : M} (hx : x ∈ bicollarLowerSide Φ a (σ s))
    (hy : y ∈ bicollarUpperSide Φ a (σ s)) (γ : Path x y) :
    ∃ u, γ u ∈ _root_.Set.range (fun z => φ ⟨(z, s), hs⟩) := by
  have hΦ : _root_.Topology.IsOpenEmbedding Φ := hφ.comp (bicollarLineHomeomorph r hr).isOpenEmbedding
  obtain ⟨u, z, hz⟩ := bicollar_path_crosses_slice Φ hΦ a (σ s) hx hy γ
  refine ⟨u, z, ?_⟩
  change φ (bicollarLineHomeomorph r hr (z, σ s)) = γ u at hz
  rwa [bicollarLineHomeomorph_slice r hr s hs z] at hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.finite_bicollar_path_crosses_slice then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.finite_bicollar_path_crosses_slice"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.finite_bicollar_path_crosses_slice ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.finite_bicollar_path_crosses_slice

end SimplyConnected

section HomotopicDisjoint

variable {A M : Type*} [TopologicalSpace A] [T2Space A] [CompactSpace A] [ConnectedSpace A]
  [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [LocallyConnectedSpace M]
  (r : ℝ) (hr : 0 < r)
  (φ : {p : A × ℝ // -r < p.2 ∧ p.2 < r} → M) (hφ : IsOpenEmbedding φ) (a : A)

local notation "Φ" => φ ∘ bicollarLineHomeomorph r hr
local notation "σ" => OpenPartialHomeomorph.symm (OpenPartialHomeomorph.univBall (0 : ℝ) r)

include hφ in
theorem finite_bicollar_ordered_band_of_homotopic_disjoint
    (ρ : C(M, M)) (hρ : ContinuousMap.Homotopic ρ (ContinuousMap.id M))
    (hdisjoint : Disjoint (_root_.Set.range ρ)
      (_root_.Set.range (fun y => φ ⟨(y, 0), by constructor <;> linarith⟩)))
    (hzero : IsCompact (closure (bicollarLowerSide Φ a 0)))
    (s t : ℝ) (hs : -r < s ∧ s < r) (ht : -r < t ∧ t < r) (hst : s < t) :
    closure (bicollarLowerSide Φ a (σ s)) ⊆ bicollarLowerSide Φ a (σ t) ∧
      closure (bicollarLowerSide Φ a (σ t)) =
        closure (bicollarLowerSide Φ a (σ s)) ∪ φ '' {q | s ≤ q.val.2 ∧ q.val.2 ≤ t} ∧
      (φ '' {q | s ≤ q.val.2 ∧ q.val.2 ≤ t})ᶜ =
        bicollarLowerSide Φ a (σ s) ∪ bicollarUpperSide Φ a (σ t) := by
  have hΦ : _root_.Topology.IsOpenEmbedding Φ := hφ.comp (bicollarLineHomeomorph r hr).isOpenEmbedding
  have hcenter : _root_.Set.range (fun y => Φ (y, 0)) =
      range (fun y => φ ⟨(y, 0), by constructor <;> linarith⟩) := by
    congr 1
    funext y
    apply congrArg φ
    exact Subtype.ext (bicollarLineHomeomorph_center r hr y)
  have hdisjointΦ : Disjoint (_root_.Set.range ρ) (_root_.Set.range (fun y => Φ (y, 0))) := by
    rwa [hcenter]
  have hστ := (bicollar_axial_inverse_lt_iff r hr s t hs ht).mpr hst
  have hband : Φ '' ((_root_.Set.univ : Set A) ×ˢ _root_.Set.Icc (σ s) (σ t)) =
      φ '' {q | s ≤ q.val.2 ∧ q.val.2 ≤ t} := by
    rw [_root_.Set.image_comp, bicollarLineHomeomorph_image_band r hr s t hs ht]
  obtain ⟨hnested, hclosure, hcompl⟩ :=
    bicollar_ordered_band_of_homotopic_disjoint Φ hΦ ρ hρ hdisjointΦ a hzero hστ
  rw [hband] at hclosure hcompl
  exact ⟨hnested, hclosure, hcompl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.finite_bicollar_ordered_band_of_homotopic_disjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.finite_bicollar_ordered_band_of_homotopic_disjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.finite_bicollar_ordered_band_of_homotopic_disjoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.finite_bicollar_ordered_band_of_homotopic_disjoint

end HomotopicDisjoint

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
