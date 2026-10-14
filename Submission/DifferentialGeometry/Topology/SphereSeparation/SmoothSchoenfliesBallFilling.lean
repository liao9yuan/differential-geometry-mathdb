import Submission.DifferentialGeometry.Topology.SphereSeparation.SourceTheorems
import Submission.DifferentialGeometry.Topology.SphereSeparation.Schoenflies
import Submission.DifferentialGeometry.Topology.SphereSeparation.SchoenfliesSides
import Submission.DifferentialGeometry.Topology.Embedding.Sphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Function _root_.Set _root_.Metric _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

noncomputable section

namespace DifferentialGeometry.Topology.SphereSeparation

local notation "E³" => EuclideanThree
local notation "S²" => _root_.Metric.sphere (0 : E³) 1

private instance _root_.Submission.DifferentialGeometry.Topology.SphereSeparation.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨by norm_num [Module.finrank_fin_fun]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry target :: scope.openDecls } }

private theorem isSmoothEmbedding_coe_sphereThree :
    IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun x : S² => (x : E³)) :=
  isSmoothEmbedding_coe_sphere (E := EuclideanSpace ℝ (Fin 3)) (n := 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.isSmoothEmbedding_coe_sphereThree
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.isSmoothEmbedding_coe_sphereThree target :: scope.openDecls } }

noncomputable def smoothSchoenfliesBallFilling : Prop :=
  ∀ (e : S² → E³) (he : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e),
    ∃ D : E³ ≃ₘ[ℝ] E³,
      D '' _root_.Metric.ball (0 : E³) 1 =
        (jordanBrouwer_openThreeSpace e he (Diffeomorph.refl 𝓘(ℝ, E³) E³ ∞)).compactSide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smoothSchoenfliesBallFilling then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smoothSchoenfliesBallFilling"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smoothSchoenfliesBallFilling ``Submission.DifferentialGeometry.Topology.SphereSeparation.smoothSchoenfliesBallFilling

theorem smoothSchoenfliesThree_iff_smoothSchoenfliesBallFilling :
    smoothSchoenfliesThree ↔ smoothSchoenfliesBallFilling := by
  constructor
  · intro hSch e he
    obtain ⟨D, d, hsphere, hd, hcl⟩ :=
      exists_ball_sphereSides_of_smoothSchoenflies hSch e he
    exact ⟨D, by rw [← hd, SphereSides.unique d _]⟩
  · intro hball e he
    obtain ⟨D, hD⟩ := hball e he
    refine ⟨D.toPartialDiffeomorph, _root_.Set.subset_univ _, ?_⟩
    change (D : E³ → E³) '' S² = _root_.Set.range e
    calc (D : E³ → E³) '' S²
        = (D : E³ → E³) '' frontier (_root_.Metric.ball (0 : E³) 1) := by
          rw [frontier_ball 0 one_ne_zero]
      _ = frontier ((D : E³ → E³) '' _root_.Metric.ball (0 : E³) 1) :=
          Homeomorph.image_frontier D.toHomeomorph _
      _ = frontier (jordanBrouwer_openThreeSpace e he
            (Diffeomorph.refl 𝓘(ℝ, E³) E³ ∞)).compactSide := by rw [hD]
      _ = _root_.Set.range e := SphereSides.frontier_compactSide _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smoothSchoenfliesThree_iff_smoothSchoenfliesBallFilling then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smoothSchoenfliesThree_iff_smoothSchoenfliesBallFilling"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smoothSchoenfliesThree_iff_smoothSchoenfliesBallFilling ``Submission.DifferentialGeometry.Topology.SphereSeparation.smoothSchoenfliesThree_iff_smoothSchoenfliesBallFilling

theorem smoothSchoenfliesThree_iff_exists_ambient_diffeomorph :
    smoothSchoenfliesThree ↔
      ∀ (e : S² → E³), _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e →
        ∃ Φ : E³ ≃ₘ[ℝ] E³, Φ '' S² = _root_.Set.range e := by
  constructor
  · intro hSch e he
    exact exists_global_diffeomorph_of_smoothSchoenflies hSch e he
  · intro h e he
    obtain ⟨Φ, hΦ⟩ := h e he
    refine ⟨Φ.toPartialDiffeomorph, _root_.Set.subset_univ _, ?_⟩
    change (Φ : E³ → E³) '' S² = _root_.Set.range e
    rw [hΦ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smoothSchoenfliesThree_iff_exists_ambient_diffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smoothSchoenfliesThree_iff_exists_ambient_diffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smoothSchoenfliesThree_iff_exists_ambient_diffeomorph ``Submission.DifferentialGeometry.Topology.SphereSeparation.smoothSchoenfliesThree_iff_exists_ambient_diffeomorph

theorem exists_diffeomorph_image_sphere_of_diffeomorph_comp_coe (Φ : E³ ≃ₘ[ℝ] E³) :
    ∃ Ψ : E³ ≃ₘ[ℝ] E³, Ψ '' S² = _root_.Set.range (Φ ∘ (Subtype.val : S² → E³)) := by
  refine ⟨Φ, ?_⟩
  rw [_root_.Set.range_comp, Subtype.range_coe]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_diffeomorph_image_sphere_of_diffeomorph_comp_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_diffeomorph_image_sphere_of_diffeomorph_comp_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_diffeomorph_image_sphere_of_diffeomorph_comp_coe ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_diffeomorph_image_sphere_of_diffeomorph_comp_coe

theorem exists_diffeomorph_image_ball_of_diffeomorph_comp_coe (Φ : E³ ≃ₘ[ℝ] E³) :
    ∃ D : E³ ≃ₘ[ℝ] E³,
      D '' _root_.Metric.ball (0 : E³) 1 =
        (jordanBrouwer_openThreeSpace (Φ ∘ (Subtype.val : S² → E³))
          (isSmoothEmbedding_coe_sphereThree.postcomp_diffeomorph Φ)
          (Diffeomorph.refl 𝓘(ℝ, E³) E³ ∞)).compactSide := by
  let d₀ := standardUnitSphereSides.image Φ.toHomeomorph
  have hidx : _root_.Set.range (Φ ∘ (Subtype.val : S² → E³)) = Φ '' S² := by
    rw [_root_.Set.range_comp, Subtype.range_coe]
  have hB : d₀.compactSide = Φ '' _root_.Metric.ball (0 : E³) 1 := by
    change (standardUnitSphereSides.image Φ.toHomeomorph).compactSide = Φ '' _root_.Metric.ball (0 : E³) 1
    rw [SphereSides.image_compactSide, Diffeomorph.coe_toHomeomorph]
    rfl
  refine ⟨Φ, ?_⟩
  rw [← hB]
  exact (SphereSides.side_sets_unique_of_core_properties
    (jordanBrouwer_openThreeSpace (Φ ∘ (Subtype.val : S² → E³))
      (isSmoothEmbedding_coe_sphereThree.postcomp_diffeomorph Φ)
      (Diffeomorph.refl 𝓘(ℝ, E³) E³ ∞)).toSphereSides
    d₀.compactSide d₀.endSide d₀.isOpen_compactSide d₀.isOpen_endSide
    d₀.isConnected_compactSide d₀.isConnected_endSide d₀.disjoint
    (by rw [hidx]; simpa only [Diffeomorph.coe_toHomeomorph] using d₀.union_eq_compl)
    d₀.isCompact_closure_compactSide
    d₀.not_isCompact_closure_endSide).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_diffeomorph_image_ball_of_diffeomorph_comp_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_diffeomorph_image_ball_of_diffeomorph_comp_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_diffeomorph_image_ball_of_diffeomorph_comp_coe ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_diffeomorph_image_ball_of_diffeomorph_comp_coe

end DifferentialGeometry.Topology.SphereSeparation
