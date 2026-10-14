import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry

variable {E F G R H K L S A B X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace L]
  [NormedAddCommGroup R] [NormedSpace ℝ R] [TopologicalSpace S]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  {P : ModelWithCorners ℝ G L} {Q : ModelWithCorners ℝ R S}
  [TopologicalSpace A] [ChartedSpace H A]
  [TopologicalSpace B] [ChartedSpace K B]
  [TopologicalSpace X] [ChartedSpace L X]
  [TopologicalSpace Y] [ChartedSpace S Y]
  {n : ℕ∞ω}

theorem isLocalDiffeomorph_of_comp_cover (u : A → X) (v : B → X)
    (hcover : _root_.Set.range u ∪ _root_.Set.range v = _root_.Set.univ)
    (hu : IsLocalDiffeomorph I P n u) (hv : IsLocalDiffeomorph J P n v)
    (f : X → Y)
    (hfu : IsLocalDiffeomorph I Q n (f ∘ u))
    (hfv : IsLocalDiffeomorph J Q n (f ∘ v)) :
    IsLocalDiffeomorph P Q n f := by
  intro x
  have hx : x ∈ _root_.Set.range u ∪ _root_.Set.range v := hcover.symm ▸ _root_.Set.mem_univ x
  rcases hx with ⟨z, rfl⟩ | ⟨z, rfl⟩
  · exact isLocalDiffeomorphAt_of_comp (hfu z) (hu z)
  · exact isLocalDiffeomorphAt_of_comp (hfv z) (hv z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.isLocalDiffeomorph_of_comp_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.isLocalDiffeomorph_of_comp_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.isLocalDiffeomorph_of_comp_cover ``Submission.DifferentialGeometry.isLocalDiffeomorph_of_comp_cover

end DifferentialGeometry
