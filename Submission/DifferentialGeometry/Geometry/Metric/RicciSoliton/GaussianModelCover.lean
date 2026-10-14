import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCoverGaussian
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.GaussianRigidity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry.Geometry.Connection _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

private noncomputable def identityTrivialization (X : Type*) [TopologicalSpace X] :
    Trivialization Unit (id : X → X) :=
  { toOpenPartialHomeomorph := (Homeomorph.prodUnique X Unit).symm.toOpenPartialHomeomorph
    baseSet := Set.univ
    open_baseSet := isOpen_univ
    source_eq := by simp
    target_eq := by simp
    proj_toFun := by intro p hp; rfl }

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.identityTrivialization
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.identityTrivialization target :: scope.openDecls } }

private theorem identity_isCoveringMap (X : Type*) [TopologicalSpace X] :
    IsCoveringMap (id : X → X) := by
  refine IsCoveringMap.mk (f := (id : X → X)) (fun _ : X => Unit)
    (fun _ => identityTrivialization X) ?_
  intro x
  exact Set.mem_univ x

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.identity_isCoveringMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.identity_isCoveringMap target :: scope.openDecls } }

omit [FiniteDimensional Real E] [I.Boundaryless] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] in
private theorem diffeomorph_isCoveringMap
  (Φ : E ≃ₘ⟮modelWithCornersSelf Real E, I⟯ M) :
    IsCoveringMap (Φ : E → M) := by
  have hcomp := (identity_isCoveringMap E).homeomorph_comp Φ.toHomeomorph
  change IsCoveringMap (Φ : E → M) at hcomp
  exact hcomp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.diffeomorph_isCoveringMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.diffeomorph_isCoveringMap target :: scope.openDecls } }

theorem exists_solitonModelCovering_of_isGaussianGradientRicciSoliton
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hGaussian : isGaussianGradientRicciSoliton (I := I) (E := E) g f 1) :
    ∃ cover : E → M,
      solitonModelCovering (euclideanMetric (E := E))
        (gaussianPotential (E := E)) g f cover := by
  rcases hGaussian with ⟨_hσ, Ψ, b, hmetric, hpotential⟩
  let fShift : C^∞⟮I, M; Real⟯ :=
    f + ContMDiffMap.const (I := I)
      (I' := modelWithCornersSelf Real Real) (M := M) (n := ∞) b
  have hmetric' : Diffeomorph.pullbackMetricCross euclideanMetric Ψ = g := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    have hxy := Diffeomorph.pullbackMetricCross_inner euclideanMetric Ψ x v w
    rw [hmetric] at hxy
    rw [Diffeomorph.pullbackMetricCross_inner]
    simpa only [scaleMetric_inner, one_mul] using hxy.symm
  have hpull : localPullMetric g Ψ.symm Ψ.symm.isLocalDiffeomorph =
      euclideanMetric := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [localPullMetric_inner]
    have hxy := Diffeomorph.pullbackMetricCross_inner g Ψ.symm x v w
    rw [Diffeomorph.pullbackMetricCross_symm_eq_iff.mp hmetric'] at hxy
    exact hxy.symm
  have hshift : normalizedGradientRicciSoliton (I := I) g fShift := by
    apply normalizedGradientRicciSoliton_of_surjective_localPullMetric
      (I := modelWithCornersSelf Real E) (J := I)
      (h := euclideanMetric (E := E))
      (Fpot := gaussianPotential (E := E))
      (g := g) (f := fShift) (Phi := Ψ.symm)
      normalizedGradientRicciSoliton_gaussian h.1
      Ψ.symm.isLocalDiffeomorph Ψ.symm.surjective
    · exact hpull
    · intro x
      have hx := congrArg (fun q : C^∞⟮I, M; Real⟯ => q (Ψ.symm x)) hpotential
      change f (Ψ.symm x) + b = gaussianPotential (Ψ (Ψ.symm x)) at hx
      rw [Ψ.apply_symm_apply] at hx
      exact hx.symm
  let nonemptyM : Nonempty M := ⟨Ψ.symm 0⟩
  have hb : b = 0 :=
    @normalizedGradientRicciSoliton_add_const_unique E _ _ _ H _ I _ M _ _ _ _ _
      nonemptyM g f b h hshift
  let cover : E → M := Ψ.symm
  refine ⟨cover, ?_⟩
  refine ⟨normalizedGradientRicciSoliton_gaussian, h,
    Ψ.symm.isLocalDiffeomorph, Ψ.symm.surjective,
    diffeomorph_isCoveringMap Ψ.symm, ?_, ?_⟩
  · intro x v w
    have hxy := Diffeomorph.pullbackMetricCross_inner g Ψ.symm x v w
    rw [Diffeomorph.pullbackMetricCross_symm_eq_iff.mp hmetric'] at hxy
    simpa only [cover] using hxy
  · intro x
    have hx := congrArg (fun q : C^∞⟮I, M; Real⟯ => q (Ψ.symm x)) hpotential
    change f (Ψ.symm x) + b = gaussianPotential (Ψ (Ψ.symm x)) at hx
    rw [Ψ.apply_symm_apply, hb, add_zero] at hx
    exact hx.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_solitonModelCovering_of_isGaussianGradientRicciSoliton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_solitonModelCovering_of_isGaussianGradientRicciSoliton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_solitonModelCovering_of_isGaussianGradientRicciSoliton ``Submission.DifferentialGeometry.Geometry.exists_solitonModelCovering_of_isGaussianGradientRicciSoliton

theorem exists_solitonModelCovering_of_normalizedGradientRicciSoliton_of_scalar_eq_zero
    [NeZero (Module.finrank Real E)]
    [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    {x : M} (hx : metricScalarAt (I := I) g x = 0) :
    ∃ cover : E → M,
      solitonModelCovering (euclideanMetric (E := E))
        (gaussianPotential (E := E)) g f cover := by
  apply exists_solitonModelCovering_of_isGaussianGradientRicciSoliton
    (I := I) h
  exact normalizedGradientRicciSoliton_isGaussian_of_scalar_eq_zero
    (I := I) h hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_solitonModelCovering_of_normalizedGradientRicciSoliton_of_scalar_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_solitonModelCovering_of_normalizedGradientRicciSoliton_of_scalar_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_solitonModelCovering_of_normalizedGradientRicciSoliton_of_scalar_eq_zero ``Submission.DifferentialGeometry.Geometry.exists_solitonModelCovering_of_normalizedGradientRicciSoliton_of_scalar_eq_zero

end DifferentialGeometry.Geometry
