/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SimplexSlabPrism
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SimplexCoordinates
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Product
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLPath

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_isPLHomeomorphOn_slab_prism_of_affineIndependent
    {ι : Type} [Finite ι] {v : ι → E} (hv : AffineIndependent ℝ v)
    (ℓ : E →ₗ[ℝ] ℝ) {a b r : ℝ} (hr : r ∈ _root_.Set.Icc a b) (hvertices : ∀ i, ℓ (v i) < a ∨ b < ℓ (v i)) :
    ∃ f : E → E × ℝ,
      IsPLHomeomorphOn f (convexHull ℝ (_root_.Set.range v) ∩ {x | a ≤ ℓ x ∧ ℓ x ≤ b})
        ((convexHull ℝ (_root_.Set.range v) ∩ {x | ℓ x = r}) ×ˢ _root_.Set.Icc a b) ∧
      ∀ x ∈ convexHull ℝ (_root_.Set.range v) ∩ {x | a ≤ ℓ x ∧ ℓ x ≤ b},
        (∀ J : Set ι, (f x).1 ∈ convexHull ℝ (v '' J) ↔ x ∈ convexHull ℝ (v '' J)) ∧
        ((f x).2 = a ↔ ℓ x = a) ∧ ((f x).2 = b ↔ ℓ x = b) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let A := Fintype.linearCombination ℝ v
  let g := ℓ.comp A
  let P := stdSimplex ℝ ι ∩ {x | a ≤ g x ∧ g x ≤ b}
  let Q := stdSimplex ℝ ι ∩ {x | g x = r}
  have hA : IsPLHomeomorphOn A (stdSimplex ℝ ι) (convexHull ℝ (_root_.Set.range v)) :=
    isPLHomeomorphOn_linearCombination_of_affineIndependent hv
  have hP : IsPolyhedron P :=
    ((isHPolytope_stdSimplex ι).inter_preimage isHPolytope_Icc g.toAffineMap).isPolyhedron
  have hsingle : IsHPolytope ({r} : Set ℝ) := by
    simpa only [_root_.Set.Icc_self] using (isHPolytope_Icc (a := r) (b := r))
  have hQ : IsPolyhedron Q :=
    ((isHPolytope_stdSimplex ι).inter_preimage hsingle g.toAffineMap).isPolyhedron
  have hAslab : A '' P = convexHull ℝ (_root_.Set.range v) ∩ {x | a ≤ ℓ x ∧ ℓ x ≤ b} := by
    ext x
    constructor
    · rintro ⟨y, ⟨hy, hya, hyb⟩, rfl⟩
      exact ⟨hA.bijOn.mapsTo hy, hya, hyb⟩
    · rintro ⟨hx, hxa, hxb⟩
      obtain ⟨y, hy, rfl⟩ := hA.bijOn.surjOn hx
      exact ⟨y, ⟨hy, hxa, hxb⟩, rfl⟩
  have hAlevel : A '' Q = convexHull ℝ (_root_.Set.range v) ∩ {x | ℓ x = r} := by
    ext x
    constructor
    · rintro ⟨y, ⟨hy, hya⟩, rfl⟩
      exact ⟨hA.bijOn.mapsTo hy, hya⟩
    · rintro ⟨hx, hxa⟩
      obtain ⟨y, hy, rfl⟩ := hA.bijOn.surjOn hx
      exact ⟨y, ⟨hy, hxa⟩, rfl⟩
  have hfA := hA.restrict hP _root_.Set.inter_subset_left
  have hfQ := hA.restrict hQ _root_.Set.inter_subset_left
  rw [hAslab] at hfA
  rw [hAlevel] at hfQ
  have hgvertices : ∀ i, g (Pi.single i 1) < a ∨ b < g (Pi.single i 1) := by
    intro i
    simpa only [g, LinearMap.comp_apply, A, Fintype.linearCombination_apply_single, one_smul] using
        hvertices i
  obtain ⟨f₀, hf₀, hcontrol⟩ := exists_isPLHomeomorphOn_stdSimplex_slab_prism g hr hgvertices
  let f := Prod.map A id ∘ f₀ ∘ Function.invFunOn A P
  have hprod := hfQ.prodMap (isPLHomeomorphOn_id_of_isHPolytope (isHPolytope_Icc (a := a) (b := b)))
  refine ⟨f, (hfA.symm.trans hf₀).trans hprod, ?_⟩
  intro x hx
  let z := Function.invFunOn A P x
  have hz : z ∈ P := hfA.symm.bijOn.mapsTo hx
  have hAz : A z = x := hfA.bijOn.invOn_invFunOn.2 hx
  have himage := hf₀.bijOn.mapsTo hz
  obtain ⟨hsupport, hlow, hhigh⟩ := hcontrol z hz
  refine ⟨?_, ?_, ?_⟩
  · intro J
    change A (f₀ z).1 ∈ convexHull ℝ (v '' J) ↔ x ∈ convexHull ℝ (v '' J)
    rw [← hAz, linearCombination_mem_convexHull_image_iff_of_affineIndependent hv J himage.1.1,
      linearCombination_mem_convexHull_image_iff_of_affineIndependent hv J hz.1]
    exact forall_congr' fun i => imp_congr_right (fun _ => hsupport i)
  · change (f₀ z).2 = a ↔ ℓ x = a
    simpa only [g, LinearMap.comp_apply, hAz] using hlow
  · change (f₀ z).2 = b ↔ ℓ x = b
    simpa only [g, LinearMap.comp_apply, hAz] using hhigh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_slab_prism_of_affineIndependent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_slab_prism_of_affineIndependent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_slab_prism_of_affineIndependent ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_slab_prism_of_affineIndependent

theorem exists_isPLHomeomorphOn_convexHull_slab_prism
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E))
    (ℓ : E →ₗ[ℝ] ℝ) {a b r : ℝ} (hr : r ∈ _root_.Set.Icc a b) (hvertices : ∀ v ∈ T, ℓ v < a ∨ b < ℓ v) :
    ∃ f : E → E × ℝ,
      IsPLHomeomorphOn f (convexHull ℝ (T : Set E) ∩ {x | a ≤ ℓ x ∧ ℓ x ≤ b})
        ((convexHull ℝ (T : Set E) ∩ {x | ℓ x = r}) ×ˢ _root_.Set.Icc a b) ∧
      ∀ x ∈ convexHull ℝ (T : Set E) ∩ {x | a ≤ ℓ x ∧ ℓ x ≤ b},
        (∀ t ⊆ T, (f x).1 ∈ convexHull ℝ (t : Set E) ↔ x ∈ convexHull ℝ (t : Set E)) ∧
        ((f x).2 = a ↔ ℓ x = a) ∧ ((f x).2 = b ↔ ℓ x = b) := by
  classical
  let e : Fin T.card ≃ T := T.equivFin.symm
  let v : Fin T.card → E := fun i => e i
  have hv : AffineIndependent ℝ v := hT.comp_embedding e.toEmbedding
  have hrange : _root_.Set.range v = (T : Set E) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).property
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)⟩
  obtain ⟨f, hf, hcontrol⟩ := exists_isPLHomeomorphOn_slab_prism_of_affineIndependent hv ℓ hr
    (fun i => hvertices (v i) (e i).property)
  rw [hrange] at hf hcontrol
  refine ⟨f, hf, ?_⟩
  intro x hx
  obtain ⟨hfaces, hlow, hhigh⟩ := hcontrol x hx
  refine ⟨?_, hlow, hhigh⟩
  intro t ht
  have himage : v '' {i | v i ∈ t} = (t : Set E) := by
    apply Subset.antisymm
    · rintro _ ⟨i, hi, rfl⟩
      exact hi
    · intro y hy
      obtain ⟨i, rfl⟩ := hrange.symm.subset (ht hy)
      exact ⟨i, hy, rfl⟩
  simpa only [himage] using hfaces {i | v i ∈ t}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_convexHull_slab_prism then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_convexHull_slab_prism"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_convexHull_slab_prism ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_convexHull_slab_prism

end DifferentialGeometry.Topology.PiecewiseLinear
