import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StrongNeck
import Submission.DifferentialGeometry.Topology.Manifold.OpenEmbedding
import Submission.DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

private local instance selectedNeckSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.selectedNeckSphereDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.selectedNeckSphereDimension target :: scope.openDecls } }

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
  {yStar : SpatialNeckSphere} {p : M} {t epsilon : ℝ}

namespace StrongNeckWitness

theorem exists_partialDiffeomorph (W : StrongNeckWitness S yStar p t epsilon) :
    ∃ F : PartialDiffeomorph SpatialNeckCylinderModel I SpatialNeckCylinder M ∞,
      F.source = spatialNeckBuffer epsilon ∧
      F.target = _root_.Set.range W.embedding ∧
      (∀ z : spatialNeckBuffer epsilon, F z.val = W.embedding z) ∧
      F '' (_root_.Set.univ ×ˢ ({0} : Set ℝ)) = W.embedding '' spatialNeckCentralDomain epsilon := by
  let U := spatialNeckBuffer epsilon
  have hUne : Nonempty U := ⟨spatialNeckCentralPoint epsilon W.epsilon_pos yStar⟩
  obtain ⟨V, C, hV, hC, _⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_diffeomorph_onto_range_of_injective_immersion
      W.embedding W.smooth_embedding.contMDiff W.smooth_embedding.isEmbedding.injective
      (fun x => immersionAt_mfderiv_injective (W.smooth_embedding.isImmersion.isImmersionAt x))
      (by simpa [Module.finrank_prod] using W.dimension_three.symm)
  have hVne : Nonempty V := ⟨C (spatialNeckCentralPoint epsilon W.epsilon_pos yStar)⟩
  let iU := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph
    SpatialNeckCylinderModel U hUne
  let iV := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph I V hVne
  let F := (iU.symm.trans C.toPartialDiffeomorph).trans iV
  have hsource : F.source = U := by
    ext x
    change ((x ∈ iU.target ∧ iU.symm x ∈ (_root_.Set.univ : Set U)) ∧
      C (iU.symm x) ∈ (_root_.Set.univ : Set V)) ↔ x ∈ U
    simp only [_root_.Set.mem_univ, and_true, iU,
      DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
    rfl
  have htarget : F.target = V := by
    ext y
    change (y ∈ iV.target ∧ (iV.symm y ∈ (_root_.Set.univ : Set V) ∧
      C.symm (iV.symm y) ∈ (_root_.Set.univ : Set U))) ↔ y ∈ V
    simp only [_root_.Set.mem_univ, and_self, and_true, iV,
      DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
    rfl
  have hmap (z : spatialNeckBuffer epsilon) : F z.val = W.embedding z := by
    change (C (iU.symm z.val) : M) = W.embedding z
    rw [show iU.symm z.val = z from
      DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply
        SpatialNeckCylinderModel U hUne z.property]
    exact hC z
  refine ⟨F, hsource, htarget.trans hV, hmap, ?_⟩
  ext q
  constructor
  · rintro ⟨⟨y, s⟩, hs, rfl⟩
    have hs0 : s = 0 := hs.2
    subst s
    exact ⟨spatialNeckCentralPoint epsilon W.epsilon_pos y, rfl, (hmap _).symm⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.val, ⟨mem_univ _, hz⟩, hmap z⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.StrongNeckWitness.exists_partialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.StrongNeckWitness.exists_partialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.StrongNeckWitness.exists_partialDiffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.StrongNeckWitness.exists_partialDiffeomorph

end StrongNeckWitness

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
