import Submission.DifferentialGeometry.Geometry.Boundary.ModelCollarInverse
import Submission.DifferentialGeometry.Topology.Manifold.ModelRestriction
import Mathlib.Geometry.Manifold.Instances.Real

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Filter _root_.Topology
open scoped _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Geometry.Boundary

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I]

set_option backward.isDefEq.respectTransparency false in
theorem exists_modelBoundary_collar_coordinates
    {f : hI.boundaryE × ℝ → E} {V : Set hI.boundaryE} {p : hI.boundaryE} {ρ : ℝ} {v : E}
    (hV : IsOpen V) (hp : p ∈ V) (hρ : 0 < ρ)
    (hf : ContDiffOn ℝ ∞ f (V ×ˢ _root_.Set.Icc 0 ρ))
    (hzero : ∀ x ∈ V, f (x, 0) = modelBoundaryParam I x)
    (hderiv : HasDerivWithinAt (fun t ↦ f (p, t)) v (_root_.Set.Icc 0 ρ) 0)
    (hinward : ∃ (w : hI.boundaryE) (c : ℝ), 0 < c ∧
      v = fderiv ℝ (modelBoundaryParam I) p w + c • hI.inwardCoordE) :
    ∃ d : OpenPartialHomeomorph (hI.boundaryE × EuclideanHalfSpace 1) H,
      (p, 0) ∈ d.source ∧
      d.source ⊆ V ×ˢ {t : EuclideanHalfSpace 1 | t.1 0 < ρ} ∧
      ContMDiffOn ((𝓘(ℝ, hI.boundaryE)).prod (𝓡∂ 1)) I ∞ d d.source ∧
      ContMDiffOn I ((𝓘(ℝ, hI.boundaryE)).prod (𝓡∂ 1)) ∞ d.symm d.target ∧
      d (p, 0) = hI.inclH (hI.boundaryI.symm p) ∧
      ∀ z ∈ d.source, I (d z) = f (z.1, z.2.1 0) := by
  obtain ⟨e, hpe, heV, he, hi, heq, hrange, _, _⟩ :=
    exists_modelBoundary_inverse_of_one_sided I hV hp hρ hf hzero hderiv hinward
  let T : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)
  let L : (hI.boundaryE × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ] (hI.boundaryE × ℝ) :=
    (ContinuousLinearEquiv.refl ℝ hI.boundaryE).prodCongr T
  let e' := L.toHomeomorph.toOpenPartialHomeomorph.trans e
  let J := (𝓘(ℝ, hI.boundaryE)).prod (𝓡∂ 1)
  have hLval : ∀ z, L z = (z.1, z.2 0) := fun _ ↦ rfl
  have he' : ContDiffOn ℝ ∞ e' e'.source :=
    he.comp L.contDiff.contDiffOn (fun z hz ↦ hz.2)
  have hi' : ContDiffOn ℝ ∞ e'.symm e'.target :=
    L.symm.contDiff.contDiffOn.comp (hi.mono _root_.Set.inter_subset_left) (fun _ _ ↦ _root_.Set.mem_univ _)
  have hside : e'.IsImage (_root_.Set.range J) (_root_.Set.range I) := by
    intro z hz
    have hh := hrange (L z) hz.2
    change e (L z) ∈ _root_.Set.range I ↔ z ∈ _root_.Set.range J
    rw [hh, hLval, ModelWithCorners.range_prod, range_modelWithCornersEuclideanHalfSpace]
    simp
  obtain ⟨d, hsource, _, hd, hdi, hdeq, _⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_modelRestriction J I e' he' hi' hside
  have hsource' : ∀ z ∈ d.source, (z.1, z.2.1 0) ∈ e.source := by
    intro z hz
    rw [hsource] at hz
    exact hz.2
  have hpD : (p, (0 : EuclideanHalfSpace 1)) ∈ d.source := by
    rw [hsource]
    exact ⟨mem_univ _, hpe⟩
  have hformula : ∀ z ∈ d.source, I (d z) = f (z.1, z.2.1 0) := by
    intro z hz
    rw [hdeq z hz]
    exact heq (z.1, z.2.1 0) (hsource' z hz) z.2.2
  refine ⟨d, hpD, (fun z hz ↦ ⟨(heV (hsource' z hz)).1, (heV (hsource' z hz)).2.2⟩), ?_, ?_, ?_, hformula⟩
  · rw [chartedSpaceSelf_prod]
    exact hd
  · rw [chartedSpaceSelf_prod]
    exact hdi
  · apply I.injective
    rw [hformula (p, 0) hpD]
    exact hzero p hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Boundary.exists_modelBoundary_collar_coordinates then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Boundary.exists_modelBoundary_collar_coordinates"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Boundary.exists_modelBoundary_collar_coordinates ``Submission.DifferentialGeometry.Geometry.Boundary.exists_modelBoundary_collar_coordinates

end DifferentialGeometry.Geometry.Boundary
