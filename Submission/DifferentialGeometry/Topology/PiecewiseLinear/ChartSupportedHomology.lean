/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Homeomorph.ConjugateFamily
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BranchSlideEndpoint
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.FirstHomologyCarrying

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem CarriesFirstHomologyOnto.conjugate_image_of_supported_homotopy
    {M E : Type*} [TopologicalSpace M] [T2Space M] [TopologicalSpace E]
    {J Y : Set M} (hJ : CarriesFirstHomologyOnto J Y) (c : OpenPartialHomeomorph M E)
    (Φ : E ≃ₜ E) {K : Set E} (hK : IsCompact K) (hKc : K ⊆ c.target)
    (hfix : _root_.Set.EqOn Φ id Kᶜ) (H : E × unitInterval → E) (hH : Continuous H)
    (hH0 : ∀ z, H (z, 0) = z) (hH1 : ∀ z, H (z, 1) = Φ z)
    (hHfix : ∀ t, _root_.Set.EqOn (fun z => H (z, t)) id Kᶜ)
    (hHK : ∀ t, _root_.Set.MapsTo (fun z => H (z, t)) K K) {Yc : Set E}
    (hYcoord : ∀ x ∈ c.source, x ∈ Y ↔ c x ∈ Yc)
    (hHY : ∀ z t, z ∈ Yc → H (z, t) ∈ Yc) :
    CarriesFirstHomologyOnto ((c.conjugateHomeomorph Φ hK hKc hfix) '' J) Y := by
  let Ψ := c.conjugateHomeomorph Φ hK hKc hfix
  have hmap : ∀ t, _root_.Set.MapsTo (fun z => H (z, t)) c.target c.target := by
    intro t z hz
    by_cases hzK : z ∈ K
    · exact hKc (hHK t hzK)
    · have heq : H (z, t) = z := hHfix t hzK
      change H (z, t) ∈ c.target
      rwa [heq]
  let G : unitInterval × M → M := fun w => c.conjugateMap (fun z => H (z, w.1)) w.2
  have hG : Continuous G := c.continuous_conjugateMap_family
    (hH.comp (continuous_snd.prodMk continuous_fst)) hmap hK hKc hHfix
  have hG0 : ∀ x, G (0, x) = x := by
    intro x
    change c.conjugateMap (fun z => H (z, 0)) x = x
    rw [show (fun z => H (z, 0)) = id from funext hH0]
    by_cases hxs : x ∈ c.source
    · rw [c.conjugateMap_of_mem id hxs, id_eq, c.left_inv hxs]
    · exact c.conjugateMap_of_notMem id hxs
  have hG1 : ∀ x, G (1, x) = Ψ x := by
    intro x
    change c.conjugateMap (fun z => H (z, 1)) x = c.conjugateMap Φ x
    rw [show (fun z => H (z, 1)) = Φ from funext hH1]
  have hGY : ∀ t, _root_.Set.MapsTo (fun x => G (t, x)) Y Y := fun t =>
    c.mapsTo_conjugateMap (hmap t) hYcoord (fun z hz => hHY z t hz.2)
  have himage : Ψ '' J ⊆ Y := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hG1]
    exact hGY 1 (hJ.1 hx)
  let g : C(J, Ψ '' J) :=
    ⟨fun x => ⟨Ψ x, x, x.2, rfl⟩,
      (Ψ.continuous.comp continuous_subtype_val).subtype_mk _⟩
  apply hJ.of_homotopic himage g
  refine ⟨{ toFun := fun q => ⟨G (q.1, q.2.1), hGY q.1 (hJ.1 q.2.2)⟩
            continuous_toFun := ?_
            map_zero_left := fun x => Subtype.ext (hG0 x)
            map_one_left := fun x => Subtype.ext (hG1 x) }⟩
  exact (hG.comp (continuous_fst.prodMk
    (continuous_subtype_val.comp continuous_snd))).subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CarriesFirstHomologyOnto.conjugate_image_of_supported_homotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CarriesFirstHomologyOnto.conjugate_image_of_supported_homotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CarriesFirstHomologyOnto.conjugate_image_of_supported_homotopy ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CarriesFirstHomologyOnto.conjugate_image_of_supported_homotopy

end DifferentialGeometry.Topology.PiecewiseLinear
