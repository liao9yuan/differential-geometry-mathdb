import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Metric
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.Manifold

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1

theorem exists_sphere_diffeomorph_of_partialDiffeomorph
    (A : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hsource : Metric.sphere (0 : E3) 1 ⊆ A.source)
    (himage : A '' Metric.sphere (0 : E3) 1 = Metric.sphere (0 : E3) 1) :
    ∃ f : Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞,
      (∀ z : S2, (f z : E3) = A z) ∧ (∀ z : S2, (f.symm z : E3) = A.symm z) := by
  let _ : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
  have htarget : Metric.sphere (0 : E3) 1 ⊆ A.target := by
    rw [← himage]
    rintro y ⟨z, hz, rfl⟩
    exact A.map_source' (hsource hz)
  have hA (z : S2) : A z ∈ Metric.sphere (0 : E3) 1 :=
    himage.subset (_root_.Set.mem_image_of_mem A z.property)
  have hAi (z : S2) : A.symm z ∈ Metric.sphere (0 : E3) 1 := by
    obtain ⟨w, hw, heq⟩ := himage.symm.subset z.property
    have hleft : A.symm z = w := by
      rw [← heq]
      exact A.left_inv' (hsource hw)
    rwa [hleft]
  have hsmooth : ContMDiff (𝓡 2) (𝓡 3) ∞ (fun z : S2 => A z) := by
    apply contMDiffOn_univ.mp
    exact A.contMDiffOn_toFun.comp (contMDiff_coe_sphere (E := E3) (n := 2)).contMDiffOn (fun z _ => hsource z.property)
  have hsmoothi : ContMDiff (𝓡 2) (𝓡 3) ∞ (fun z : S2 => A.symm z) := by
    apply contMDiffOn_univ.mp
    exact A.contMDiffOn_invFun.comp (contMDiff_coe_sphere (E := E3) (n := 2)).contMDiffOn (fun z _ => htarget z.property)
  let f : Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞ := {
    toFun := fun z => ⟨A z, hA z⟩
    invFun := fun z => ⟨A.symm z, hAi z⟩
    left_inv := fun z => Subtype.ext (A.left_inv' (hsource z.property))
    right_inv := fun z => Subtype.ext (A.right_inv' (htarget z.property))
    contMDiff_toFun := hsmooth.codRestrict_sphere hA
    contMDiff_invFun := hsmoothi.codRestrict_sphere hAi }
  exact ⟨f, fun _ => rfl, fun _ => rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_sphere_diffeomorph_of_partialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_sphere_diffeomorph_of_partialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_sphere_diffeomorph_of_partialDiffeomorph ``Submission.DifferentialGeometry.Topology.Manifold.exists_sphere_diffeomorph_of_partialDiffeomorph

end DifferentialGeometry.Topology.Manifold

end

end
