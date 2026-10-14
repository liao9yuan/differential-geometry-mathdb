import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Atlas
import Mathlib.Geometry.Manifold.Immersion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set
open scoped _root_.ContDiff _root_.Manifold

namespace Manifold
open _root_.Manifold

variable {E F G M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace M] [ChartedSpace E M] {n : ℕ∞ω} [IsManifold 𝓘(ℝ, E) n M]

open _root_.Manifold in
theorem isImmersionAtOfComplement_of_flat_patch
    (hn : n ≠ 0) (χ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M n)
    (Ψ : (E × F) ≃ₘ^n⟮𝓘(ℝ, E × F), 𝓘(ℝ, G)⟯ G) {g : M → G}
    (hflat : ∀ y ∈ χ.source, g (χ y) = Ψ (y, 0)) {x : E} (hx : x ∈ χ.source) :
    IsImmersionAtOfComplement F 𝓘(ℝ, E) 𝓘(ℝ, G) n g (χ x) := by
  let L : (E × F) ≃L[ℝ] G := Ψ.mfderivToContinuousLinearEquiv hn (x, 0)
  let A : (E × F) ≃ₘ^n⟮𝓘(ℝ, E × F), 𝓘(ℝ, G)⟯ G :=
    { toEquiv := L.toEquiv
      contMDiff_toFun := L.contDiff.contMDiff
      contMDiff_invFun := L.symm.contDiff.contMDiff }
  let C := Ψ.symm.trans A
  apply IsImmersionAtOfComplement.mk_of_charts L χ.symm.toOpenPartialHomeomorph
    C.toPartialDiffeomorph.toOpenPartialHomeomorph (χ.map_source hx) (_root_.Set.mem_univ _)
    (DifferentialGeometry.PartialDiffeomorph.toOpenPartialHomeomorph_mem_maximalAtlas χ.symm)
    (DifferentialGeometry.PartialDiffeomorph.toOpenPartialHomeomorph_mem_maximalAtlas
      C.toPartialDiffeomorph)
  · exact fun _ _ => _root_.Set.mem_univ _
  · intro y hy
    have hy' : y ∈ χ.source := by simpa using hy
    change L (Ψ.symm (g (χ y))) = L (y, 0)
    rw [hflat y hy', Ψ.symm_apply_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.isImmersionAtOfComplement_of_flat_patch then
    throwError "Refusing to shadow existing declaration Manifold.isImmersionAtOfComplement_of_flat_patch"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.isImmersionAtOfComplement_of_flat_patch ``Submission.Manifold.isImmersionAtOfComplement_of_flat_patch

end Manifold
