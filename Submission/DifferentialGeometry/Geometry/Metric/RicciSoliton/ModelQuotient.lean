import Submission.DifferentialGeometry.Geometry.Metric.Quotient
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCover

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [LocallyCompactSpace M]
variable {G : Type*} [Group G] [MulAction G M]
  [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M]
  [IsCancelSMul G M] [ContMDiffConstSMul I ∞ G M]

private noncomputable def solitonModelQuotientPotentialFn
    (Fpot : C^∞⟮I, M; Real⟯)
    (hpotential : ∀ gamma : G, ∀ x : M, Fpot (gamma • x) = Fpot x) :
    MulAction.orbitRel.Quotient G M → Real :=
  Quotient.lift Fpot fun x y hxy => by
    obtain ⟨gamma, rfl⟩ := hxy
    exact hpotential gamma y

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.solitonModelQuotientPotentialFn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.solitonModelQuotientPotentialFn target :: scope.openDecls } }

noncomputable def solitonModelQuotientMetric
    (h : SmoothRiemannianMetric I M)
    (hmetric : ∀ gamma : G,
      Diffeomorph.pullbackMetric h
        (MulAction.smulDiffeomorph (n := ∞) I gamma) = h) :
    SmoothRiemannianMetric I (MulAction.orbitRel.Quotient G M) :=
  descendedMetric h (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M)
    (MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
      (n := ∞) I)
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.surjective
    (metricFiberCompatible_quotientMk_of_invariant h hmetric)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.solitonModelQuotientMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.solitonModelQuotientMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.solitonModelQuotientMetric ``Submission.DifferentialGeometry.Geometry.solitonModelQuotientMetric

noncomputable def solitonModelQuotientPotential
    (Fpot : C^∞⟮I, M; Real⟯)
    (hpotential : ∀ gamma : G, ∀ x : M, Fpot (gamma • x) = Fpot x) :
    C^∞⟮I, MulAction.orbitRel.Quotient G M; Real⟯ :=
  ⟨solitonModelQuotientPotentialFn Fpot hpotential,
    (MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
      (n := ∞) I).contMDiff_of_comp_of_surjective
        isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.surjective
        (by
          have heq : solitonModelQuotientPotentialFn Fpot hpotential ∘
              (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M) = Fpot := by
            funext x
            rfl
          rw [heq]
          exact Fpot.contMDiff)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.solitonModelQuotientPotential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.solitonModelQuotientPotential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.solitonModelQuotientPotential ``Submission.DifferentialGeometry.Geometry.solitonModelQuotientPotential

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem localPullMetric_solitonModelQuotientMetric
    (h : SmoothRiemannianMetric I M)
    (hmetric : ∀ gamma : G,
      Diffeomorph.pullbackMetric h
        (MulAction.smulDiffeomorph (n := ∞) I gamma) = h) :
    localPullMetric (solitonModelQuotientMetric h hmetric)
        (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M)
        (MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
          (n := ∞) I) = h :=
  localPullMetric_descendedMetric h
    (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M)
    (MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
      (n := ∞) I)
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.surjective
    (metricFiberCompatible_quotientMk_of_invariant h hmetric)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.localPullMetric_solitonModelQuotientMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.localPullMetric_solitonModelQuotientMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.localPullMetric_solitonModelQuotientMetric ``Submission.DifferentialGeometry.Geometry.localPullMetric_solitonModelQuotientMetric

omit [FiniteDimensional Real E] [I.Boundaryless] [SigmaCompactSpace M] in
theorem solitonModelQuotientPotential_apply
    (Fpot : C^∞⟮I, M; Real⟯)
    (hpotential : ∀ gamma : G, ∀ x : M, Fpot (gamma • x) = Fpot x)
    (x : M) :
    solitonModelQuotientPotential Fpot hpotential (Quotient.mk'' x) = Fpot x :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.solitonModelQuotientPotential_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.solitonModelQuotientPotential_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.solitonModelQuotientPotential_apply ``Submission.DifferentialGeometry.Geometry.solitonModelQuotientPotential_apply

omit [I.Boundaryless] in
theorem solitonModelQuotientMetric_complete
    (h : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) h)
    (hmetric : ∀ gamma : G,
      Diffeomorph.pullbackMetric h
        (MulAction.smulDiffeomorph (n := ∞) I gamma) = h) :
    RiemannianMetricComplete (I := I)
      (solitonModelQuotientMetric h hmetric) :=
  RiemannianMetricComplete.of_coveringMap_localPullMetric h
    (solitonModelQuotientMetric h hmetric)
    (MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
      (n := ∞) I)
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.surjective
    (localPullMetric_solitonModelQuotientMetric h hmetric) hcomplete

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.solitonModelQuotientMetric_complete then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.solitonModelQuotientMetric_complete"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.solitonModelQuotientMetric_complete ``Submission.DifferentialGeometry.Geometry.solitonModelQuotientMetric_complete

theorem normalizedGradientRicciSoliton_solitonModelQuotient
    {h : SmoothRiemannianMetric I M} {Fpot : C^∞⟮I, M; Real⟯}
    (hsol : normalizedGradientRicciSoliton (I := I) h Fpot)
    (hmetric : ∀ gamma : G,
      Diffeomorph.pullbackMetric h
        (MulAction.smulDiffeomorph (n := ∞) I gamma) = h)
    (hpotential : ∀ gamma : G, ∀ x : M, Fpot (gamma • x) = Fpot x) :
    normalizedGradientRicciSoliton (I := I)
      (solitonModelQuotientMetric h hmetric)
      (solitonModelQuotientPotential Fpot hpotential) :=
  normalizedGradientRicciSoliton_of_surjective_localPullMetric hsol
    (solitonModelQuotientMetric_complete h hsol.1 hmetric)
    (MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
      (n := ∞) I)
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.surjective
    (localPullMetric_solitonModelQuotientMetric h hmetric)
    (fun x => (solitonModelQuotientPotential_apply Fpot hpotential x).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_solitonModelQuotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_solitonModelQuotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_solitonModelQuotient ``Submission.DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_solitonModelQuotient

theorem solitonModelCovering_quotient_of_invariant
    {h : SmoothRiemannianMetric I M} {Fpot : C^∞⟮I, M; Real⟯}
    (hsol : normalizedGradientRicciSoliton (I := I) h Fpot)
    (hmetric : ∀ gamma : G,
      Diffeomorph.pullbackMetric h
        (MulAction.smulDiffeomorph (n := ∞) I gamma) = h)
    (hpotential : ∀ gamma : G, ∀ x : M, Fpot (gamma • x) = Fpot x) :
    solitonModelCovering h Fpot
      (solitonModelQuotientMetric h hmetric)
      (solitonModelQuotientPotential Fpot hpotential)
      (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M) := by
  refine ⟨hsol,
    normalizedGradientRicciSoliton_solitonModelQuotient hsol hmetric hpotential,
    MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul I,
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.surjective,
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap,
    ?_, ?_⟩
  · intro x v w
    have hpull := congrArg
      (fun k : SmoothRiemannianMetric I M => k.inner x v w)
      (localPullMetric_solitonModelQuotientMetric h hmetric)
    rw [localPullMetric_inner] at hpull
    exact hpull.symm
  · intro x
    exact (solitonModelQuotientPotential_apply Fpot hpotential x).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.solitonModelCovering_quotient_of_invariant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.solitonModelCovering_quotient_of_invariant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.solitonModelCovering_quotient_of_invariant ``Submission.DifferentialGeometry.Geometry.solitonModelCovering_quotient_of_invariant

theorem solitonModelCovering_quotient_target_unique
    {h : SmoothRiemannianMetric I M} {Fpot : C^∞⟮I, M; Real⟯}
    {g : SmoothRiemannianMetric I (MulAction.orbitRel.Quotient G M)}
    {f : C^∞⟮I, MulAction.orbitRel.Quotient G M; Real⟯}
    (hpi : solitonModelCovering h Fpot g f
      (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M))
    (hmetric : ∀ gamma : G,
      Diffeomorph.pullbackMetric h
        (MulAction.smulDiffeomorph (n := ∞) I gamma) = h)
    (hpotential : ∀ gamma : G, ∀ x : M, Fpot (gamma • x) = Fpot x) :
    g = solitonModelQuotientMetric h hmetric ∧
      f = solitonModelQuotientPotential Fpot hpotential := by
  constructor
  · apply localPullMetric_injective_of_surjective
      (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M)
      (MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul I)
      isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.surjective
    exact (solitonModelCovering_metric_eq_localPull hpi).symm.trans
      (localPullMetric_solitonModelQuotientMetric h hmetric).symm
  · apply ContMDiffMap.ext
    intro y
    obtain ⟨x, rfl⟩ :=
      isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.surjective y
    exact (solitonModelCovering_potential hpi x).symm.trans
      (solitonModelQuotientPotential_apply Fpot hpotential x).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.solitonModelCovering_quotient_target_unique then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.solitonModelCovering_quotient_target_unique"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.solitonModelCovering_quotient_target_unique ``Submission.DifferentialGeometry.Geometry.solitonModelCovering_quotient_target_unique

end DifferentialGeometry.Geometry
