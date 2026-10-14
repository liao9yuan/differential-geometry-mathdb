import Submission.DifferentialGeometry.Topology.SphereSeparation.RadialExtensionDerivative
import Submission.DifferentialGeometry.Topology.Embedding.TangentLift

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Manifold _root_.Submission.Manifold _root_.Matrix
open scoped _root_.ContDiff

namespace DifferentialGeometry.Topology.SphereSeparation

noncomputable def embeddedSphereHeightTangent (e : SphereTwo → EuclideanThree)
    (x : SphereTwo) : EuclideanThree :=
  e3coord.symm ![(embeddedSphereAdjugateNormal e x) 1,
    -(embeddedSphereAdjugateNormal e x) 0, 0]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.embeddedSphereHeightTangent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.embeddedSphereHeightTangent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.embeddedSphereHeightTangent ``Submission.DifferentialGeometry.Topology.SphereSeparation.embeddedSphereHeightTangent

theorem contMDiff_embeddedSphereHeightTangent {e : SphereTwo → EuclideanThree}
    (he : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanThree) ∞ e) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanThree) ∞
      (embeddedSphereHeightTangent e) := by
  apply e3coord.symm.contDiff.contMDiff.comp
  rw [contMDiff_pi_space]
  intro i
  fin_cases i
  · exact (EuclideanSpace.proj 1).contMDiff.comp (contMDiff_embeddedSphereAdjugateNormal he)
  · exact ((EuclideanSpace.proj 0).contMDiff.comp
      (contMDiff_embeddedSphereAdjugateNormal he)).neg
  · exact contMDiff_const

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.contMDiff_embeddedSphereHeightTangent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.contMDiff_embeddedSphereHeightTangent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.contMDiff_embeddedSphereHeightTangent ``Submission.DifferentialGeometry.Topology.SphereSeparation.contMDiff_embeddedSphereHeightTangent

@[simp] theorem embeddedSphereHeightTangent_last (e : SphereTwo → EuclideanThree)
    (x : SphereTwo) : embeddedSphereHeightTangent e x 2 = 0 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.embeddedSphereHeightTangent_last then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.embeddedSphereHeightTangent_last"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.embeddedSphereHeightTangent_last ``Submission.DifferentialGeometry.Topology.SphereSeparation.embeddedSphereHeightTangent_last

theorem embeddedSphereHeightTangent_mem_tangentPlane {e : SphereTwo → EuclideanThree}
    (he : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanThree) ∞ e)
    (x : SphereTwo) : embeddedSphereHeightTangent e x ∈ embeddedSphereTangentPlane e x := by
  obtain ⟨hne, hmem⟩ := embeddedSphereAdjugateNormal_ne_zero_mem he x
  have hspan : ℝ ∙ embeddedSphereAdjugateNormal e x = embeddedSphereNormalLine e x :=
    Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr (by simpa using hmem))
      ((finrank_span_singleton hne).trans (finrank_embeddedSphereNormalLine he).symm)
  rw [← Submodule.orthogonal_orthogonal (embeddedSphereTangentPlane e x),
    ← embeddedSphereNormalLine, ← hspan, Submodule.mem_orthogonal_singleton_iff_inner_left]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [embeddedSphereHeightTangent, e3coord, dotProduct, Fin.sum_univ_succ]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.embeddedSphereHeightTangent_mem_tangentPlane then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.embeddedSphereHeightTangent_mem_tangentPlane"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.embeddedSphereHeightTangent_mem_tangentPlane ``Submission.DifferentialGeometry.Topology.SphereSeparation.embeddedSphereHeightTangent_mem_tangentPlane

theorem mfderiv_embeddedSphere_height {e : SphereTwo → EuclideanThree}
    (he : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanThree) ∞ e)
    (x : SphereTwo) (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) x) :
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ) (fun y => e y 2) x v =
      (mvfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) e x v) 2 := by
  change mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ)
    ((EuclideanSpace.proj 2) ∘ e) x v = _
  rw [mfderiv_comp x (EuclideanSpace.proj 2).mdifferentiableAt
    (he.mdifferentiableAt (by simp))]
  have hp : mfderiv 𝓘(ℝ, EuclideanThree) 𝓘(ℝ, ℝ) (EuclideanSpace.proj 2) (e x) =
      EuclideanSpace.proj 2 := by
    exact (ContinuousLinearMap.hasMFDerivAt
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 2) (x := e x)).mfderiv
  rw [hp]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.mfderiv_embeddedSphere_height then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.mfderiv_embeddedSphere_height"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.mfderiv_embeddedSphere_height ``Submission.DifferentialGeometry.Topology.SphereSeparation.mfderiv_embeddedSphere_height

theorem embeddedSphereHeightTangent_ne_zero {e : SphereTwo → EuclideanThree}
    (he : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanThree) ∞ e)
    (x : SphereTwo)
    (hx : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0) :
    embeddedSphereHeightTangent e x ≠ 0 := by
  intro hz
  have h0 : embeddedSphereAdjugateNormal e x 0 = 0 := by
    have h := congrArg (fun z : EuclideanThree => z 1) hz
    simpa [embeddedSphereHeightTangent, e3coord] using h
  have h1 : embeddedSphereAdjugateNormal e x 1 = 0 := by
    have h := congrArg (fun z : EuclideanThree => z 0) hz
    simpa [embeddedSphereHeightTangent, e3coord] using h
  obtain ⟨hne, hmem⟩ := embeddedSphereAdjugateNormal_ne_zero_mem he x
  have h2 : embeddedSphereAdjugateNormal e x 2 ≠ 0 := by
    intro h2
    apply hne
    ext i
    fin_cases i <;> assumption
  apply hx
  ext v
  rw [mfderiv_embeddedSphere_height he.contMDiff]
  have horth := (mem_embeddedSphereNormalLine_iff e x _).mp hmem
    (mvfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) e x v) ⟨v, rfl⟩
  rw [EuclideanSpace.inner_eq_star_dotProduct] at horth
  simp only [dotProduct, Fin.sum_univ_three, _root_.TrivialStar.star_trivial] at horth
  change embeddedSphereAdjugateNormal e x 0 * _ +
    embeddedSphereAdjugateNormal e x 1 * _ + embeddedSphereAdjugateNormal e x 2 * _ = 0 at horth
  rw [h0, h1, _root_.MulZeroClass.zero_mul, _root_.MulZeroClass.zero_mul, zero_add, zero_add] at horth
  exact (mul_eq_zero.mp horth).resolve_left h2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.embeddedSphereHeightTangent_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.embeddedSphereHeightTangent_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.embeddedSphereHeightTangent_ne_zero ``Submission.DifferentialGeometry.Topology.SphereSeparation.embeddedSphereHeightTangent_ne_zero

theorem exists_contMDiff_embeddedSphere_height_tangent_field {e : SphereTwo → EuclideanThree}
    (he : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanThree) ∞ e) :
    ∃ V : (x : SphereTwo) → TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) x,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).tangent ∞
        (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) SphereTwo)) ∧
      (∀ x, mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanThree) e x (V x) =
        embeddedSphereHeightTangent e x) ∧
      (∀ x, mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ) (fun y => e y 2) x (V x) = 0) ∧
      (∀ x, mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0 →
        V x ≠ 0) := by
  have hW : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (𝓘(ℝ, EuclideanThree)).tangent ∞
      (fun x => (⟨e x, embeddedSphereHeightTangent e x⟩ :
        TangentBundle 𝓘(ℝ, EuclideanThree) EuclideanThree)) := by
    intro x
    rw [Bundle.contMDiffAt_totalSpace]
    refine ⟨he.contMDiff x, ?_⟩
    apply (contMDiff_embeddedSphereHeightTangent he x).congr_of_eventuallyEq
    filter_upwards with y
    rw [trivializationAt_model_space_apply]
  obtain ⟨V, hV, hpush⟩ := he.exists_contMDiff_tangent_lift
    (fun x => embeddedSphereHeightTangent e x) hW
    (fun x => embeddedSphereHeightTangent_mem_tangentPlane he x)
  refine ⟨V, hV, hpush, ?_, ?_⟩
  · intro x
    rw [mfderiv_embeddedSphere_height he.contMDiff]
    change (show EuclideanThree from mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
      𝓘(ℝ, EuclideanThree) e x (V x)) 2 = 0
    rw [hpush]
    exact embeddedSphereHeightTangent_last e x
  · intro x hx hv
    apply embeddedSphereHeightTangent_ne_zero he x hx
    rw [← hpush, hv, map_zero]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_contMDiff_embeddedSphere_height_tangent_field then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_contMDiff_embeddedSphere_height_tangent_field"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_contMDiff_embeddedSphere_height_tangent_field ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_contMDiff_embeddedSphere_height_tangent_field

end DifferentialGeometry.Topology.SphereSeparation
