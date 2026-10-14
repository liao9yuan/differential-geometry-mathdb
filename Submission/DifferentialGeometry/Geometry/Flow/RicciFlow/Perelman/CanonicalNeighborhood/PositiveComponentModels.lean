import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PositiveSectionalLowerBound
import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Quotient.SpaceFormGroup
import Submission.DifferentialGeometry.Geometry.Curvature.Sphere.ConstCurvature
import Submission.DifferentialGeometry.Topology.ProjectiveSpace.Manifold
import Mathlib.Geometry.Manifold.Instances.Sphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology
open _root_.Metric _root_.Submission.Metric

namespace DifferentialGeometry.Geometry.RoundSphereQuotient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)] [NeZero n]

theorem proj_injective_of_subsingleton_deckGroup
    (D : RoundSphereQuotient E n) [Subsingleton D.Γ] :
    Function.Injective D.proj := by
  intro a b hab
  obtain ⟨γ, hγ⟩ := D.proj_eq_imp a b hab
  have hγ1 : γ = 1 := Subsingleton.elim γ 1
  have hρ : D.ρ γ = 1 := by rw [hγ1, map_one]
  have ha : sphereDiffeo (n := n) (D.ρ γ) a = a := by
    rw [hρ]
    apply Subtype.ext
    simp
  rw [ha] at hγ
  exact hγ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.RoundSphereQuotient.proj_injective_of_subsingleton_deckGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.RoundSphereQuotient.proj_injective_of_subsingleton_deckGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.RoundSphereQuotient.proj_injective_of_subsingleton_deckGroup ``Submission.DifferentialGeometry.Geometry.RoundSphereQuotient.proj_injective_of_subsingleton_deckGroup

theorem proj_isLocalDiffeomorph_of_subsingleton_deckGroup
    (D : RoundSphereQuotient E n) [Subsingleton D.Γ] :
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ D.proj := by
  classical
  have hinj := D.proj_injective_of_subsingleton_deckGroup
  intro a
  let S := D.sectionAt (D.proj a)
  let ψ : D.Q → _root_.Metric.sphere (0 : E) 1 := fun r =>
    if hr : r ∈ S.baseNeighborhood then S.toSphere ⟨r, hr⟩ else a
  have hψ : ∀ r ∈ (S.baseNeighborhood : Set D.Q), D.proj (ψ r) = r := by
    intro r hr
    dsimp only [ψ]
    split_ifs with h
    · exact S.toSphere_proj ⟨r, h⟩
    · exact absurd hr h
  have hψsmooth : ContMDiff (𝓡 n) (𝓡 n) ∞
      (fun r : S.baseNeighborhood => S.toSphere r) := S.toSphere_contMDiff
  refine ⟨{
    toFun := D.proj
    invFun := ψ
    source := D.proj ⁻¹' (S.baseNeighborhood : Set D.Q)
    target := (S.baseNeighborhood : Set D.Q)
    map_source' := fun y hy => hy
    map_target' := fun r hr => by
      change D.proj (ψ r) ∈ (S.baseNeighborhood : Set D.Q)
      rw [hψ r hr]
      exact hr
    left_inv' := fun y hy => hinj (hψ (D.proj y) hy)
    right_inv' := fun r hr => hψ r hr
    open_source := S.baseNeighborhood.isOpen.preimage D.proj_smooth.continuous
    open_target := S.baseNeighborhood.isOpen
    contMDiffOn_toFun := D.proj_smooth.contMDiffOn
    contMDiffOn_invFun := by
      intro r hr
      apply ContMDiffAt.contMDiffWithinAt
      rw [← contMDiffAt_subtype_iff (U := S.baseNeighborhood) (x := ⟨r, hr⟩)]
      refine hψsmooth.contMDiffAt.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
      funext z
      dsimp only [ψ]
      split_ifs with h
      · exact congrArg (fun z : S.baseNeighborhood => S.toSphere z) (Subtype.ext rfl)
      · exact absurd z.2 h }, ?_, ?_⟩
  · exact S.mem_baseNeighborhood
  · intro y hy
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.RoundSphereQuotient.proj_isLocalDiffeomorph_of_subsingleton_deckGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.RoundSphereQuotient.proj_isLocalDiffeomorph_of_subsingleton_deckGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.RoundSphereQuotient.proj_isLocalDiffeomorph_of_subsingleton_deckGroup ``Submission.DifferentialGeometry.Geometry.RoundSphereQuotient.proj_isLocalDiffeomorph_of_subsingleton_deckGroup

noncomputable def sphereDiffeomorph_of_subsingleton_deckGroup
    (D : RoundSphereQuotient E n) [Subsingleton D.Γ] :
    Diffeomorph (𝓡 n) (𝓡 n) (_root_.Metric.sphere (0 : E) 1) D.Q ∞ :=
  (D.proj_isLocalDiffeomorph_of_subsingleton_deckGroup).diffeomorphOfBijective
    ⟨D.proj_injective_of_subsingleton_deckGroup, D.proj_surjective⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.RoundSphereQuotient.sphereDiffeomorph_of_subsingleton_deckGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.RoundSphereQuotient.sphereDiffeomorph_of_subsingleton_deckGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.RoundSphereQuotient.sphereDiffeomorph_of_subsingleton_deckGroup ``Submission.DifferentialGeometry.Geometry.RoundSphereQuotient.sphereDiffeomorph_of_subsingleton_deckGroup

end DifferentialGeometry.Geometry.RoundSphereQuotient

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry (RealProjectiveThreeSpace)

universe u

private instance roundSphereFourFact :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.roundSphereFourFact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.roundSphereFourFact target :: scope.openDecls } }

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] in
private theorem curvatureFormat_eq_vec4 {x : M} (v w : TangentSpace I3 x) :
    (fun i : Fin 4 => ![v, w, w, v] i) = vec4 v w w v := by
  funext i
  fin_cases i <;> simp [vec4]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.curvatureFormat_eq_vec4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.curvatureFormat_eq_vec4 target :: scope.openDecls } }

theorem secLower_roundMetricSphereThree :
    SecLower (M := Sphere 3)
      (roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3)) 1 Set.univ := by
  intro x _ v w
  rw [one_mul, curvatureFormat_eq_vec4 v w,
    ← metricRm04StandardAt_apply (I := 𝓡 3) (M := Sphere 3)
      (roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3)) x v w w v,
    roundMetric_sec_value (E := EuclideanSpace ℝ (Fin 4)) (n := 3) x v w]
  exact le_of_eq (by ring)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.secLower_roundMetricSphereThree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.secLower_roundMetricSphereThree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.secLower_roundMetricSphereThree ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.secLower_roundMetricSphereThree

def hasPositiveSecLowerBound (g : SmoothRiemannianMetric I3 M) (U : Set M) : Prop :=
  ∃ c : ℝ, 0 < c ∧ SecLower g c U

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hasPositiveSecLowerBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hasPositiveSecLowerBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hasPositiveSecLowerBound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hasPositiveSecLowerBound

omit [SigmaCompactSpace M] in
theorem hasPositiveSecLowerBound_iff_le_leastCurvatureOperatorEigenvalueAt
    (g : SmoothRiemannianMetric I3 M)
    (hdim : Module.finrank ℝ ThreeSpace = 3) (U : Set M) :
    hasPositiveSecLowerBound g U ↔ ∃ c : ℝ, 0 < c ∧ ∀ x ∈ U, c ≤
      leastCurvatureOperatorEigenvalueAt (I := I3) g x
        (metricAlgebraicCurvatureTensorAt (I := I3) (M := M) g x) := by
  constructor
  · rintro ⟨c, hc, h⟩
    exact ⟨c, hc, fun x hx =>
      (secLower_iff_le_leastCurvatureOperatorEigenvalueAt g hdim c U).mp h x hx⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨c, hc, (secLower_iff_le_leastCurvatureOperatorEigenvalueAt g hdim c U).mpr h⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hasPositiveSecLowerBound_iff_le_leastCurvatureOperatorEigenvalueAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hasPositiveSecLowerBound_iff_le_leastCurvatureOperatorEigenvalueAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hasPositiveSecLowerBound_iff_le_leastCurvatureOperatorEigenvalueAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hasPositiveSecLowerBound_iff_le_leastCurvatureOperatorEigenvalueAt

theorem hasPositiveSecLowerBound_roundMetricSphereThree :
    hasPositiveSecLowerBound (M := Sphere 3)
      (roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3)) Set.univ :=
  ⟨1, one_pos, secLower_roundMetricSphereThree⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hasPositiveSecLowerBound_roundMetricSphereThree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hasPositiveSecLowerBound_roundMetricSphereThree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hasPositiveSecLowerBound_roundMetricSphereThree ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hasPositiveSecLowerBound_roundMetricSphereThree

noncomputable def positiveComponentOfDiffeomorphSphereThree
    (e : Diffeomorph (𝓡 3) I3 (Sphere 3) M ∞) :
    PositiveComponent (M := M) Set.univ :=
  PositiveComponent.sphere e.toPartialDiffeomorph rfl rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.positiveComponentOfDiffeomorphSphereThree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.positiveComponentOfDiffeomorphSphereThree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.positiveComponentOfDiffeomorphSphereThree ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.positiveComponentOfDiffeomorphSphereThree

noncomputable def realProjectiveThreePresentation :
    ProjectivePresentation RealProjectiveThreeSpace :=
  let D := realProjectiveSpaceQuotientMap_isLocalDiffeomorph (E := EuclideanSpace ℝ (Fin 4))
  { quotient := realProjectiveSpaceQuotientMap (E := EuclideanSpace ℝ (Fin 4))
    smooth := D.contMDiff
    onto := realProjectiveSpaceQuotientMap_surjective
    fibers := fun a b => realProjectiveSpaceQuotientMap_eq_iff (x := a) (y := b)
    local_diffeo := fun a => (D.mfderivToContinuousLinearEquiv (by simp) a).bijective }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.realProjectiveThreePresentation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.realProjectiveThreePresentation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.realProjectiveThreePresentation ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.realProjectiveThreePresentation

noncomputable def positiveComponentOfDiffeomorphProjective
    (Z : Type u) [TopologicalSpace Z] [ChartedSpace ThreeSpace Z] [IsManifold I3 ∞ Z]
    [T2Space Z] [CompactSpace Z] (P : ProjectivePresentation Z)
    (e : Diffeomorph I3 I3 Z M ∞) :
    PositiveComponent (M := M) Set.univ :=
  PositiveComponent.projective Z P e.toPartialDiffeomorph rfl rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.positiveComponentOfDiffeomorphProjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.positiveComponentOfDiffeomorphProjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.positiveComponentOfDiffeomorphProjective ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.positiveComponentOfDiffeomorphProjective

noncomputable def positiveComponentOfRoundSphereQuotient
    (D : RoundSphereQuotient (EuclideanSpace ℝ (Fin 4)) 3) [Subsingleton D.Γ]
    (e : Diffeomorph (𝓡 3) I3 D.Q M ∞) :
    PositiveComponent (M := M) Set.univ :=
  PositiveComponent.sphere
    ((D.sphereDiffeomorph_of_subsingleton_deckGroup).trans e).toPartialDiffeomorph rfl rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.positiveComponentOfRoundSphereQuotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.positiveComponentOfRoundSphereQuotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.positiveComponentOfRoundSphereQuotient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.positiveComponentOfRoundSphereQuotient

theorem nonempty_positiveComponent_sphereThree :
    Nonempty (PositiveComponent (M := Sphere 3) Set.univ) :=
  ⟨positiveComponentOfDiffeomorphSphereThree
    (Diffeomorph.refl (𝓡 3) (Sphere 3) ∞)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_positiveComponent_sphereThree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_positiveComponent_sphereThree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_positiveComponent_sphereThree ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_positiveComponent_sphereThree

theorem nonempty_positiveComponent_realProjectiveThree :
    Nonempty (PositiveComponent (M := RealProjectiveThreeSpace) Set.univ) :=
  ⟨positiveComponentOfDiffeomorphProjective RealProjectiveThreeSpace
    realProjectiveThreePresentation (Diffeomorph.refl I3 RealProjectiveThreeSpace ∞)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_positiveComponent_realProjectiveThree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_positiveComponent_realProjectiveThree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_positiveComponent_realProjectiveThree ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_positiveComponent_realProjectiveThree

omit [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] in
theorem exists_diffeomorph_sphereThree_of_sphericalSpaceFormQuotientModel
    (P : SphericalSpaceFormQuotientModel I3 M) [Subsingleton P.quotient.Γ] :
    Nonempty (Diffeomorph (𝓡 3) I3 (Sphere 3) M ∞) :=
  ⟨(P.quotient.sphereDiffeomorph_of_subsingleton_deckGroup).trans P.equiv.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_diffeomorph_sphereThree_of_sphericalSpaceFormQuotientModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_diffeomorph_sphereThree_of_sphericalSpaceFormQuotientModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_diffeomorph_sphereThree_of_sphericalSpaceFormQuotientModel ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_diffeomorph_sphereThree_of_sphericalSpaceFormQuotientModel

omit [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] in
theorem nonempty_positiveComponent_of_sphericalSpaceFormQuotientModel
    (P : SphericalSpaceFormQuotientModel I3 M) [Subsingleton P.quotient.Γ] :
    Nonempty (PositiveComponent (M := M) Set.univ) :=
  ⟨positiveComponentOfRoundSphereQuotient P.quotient P.equiv.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_positiveComponent_of_sphericalSpaceFormQuotientModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_positiveComponent_of_sphericalSpaceFormQuotientModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_positiveComponent_of_sphericalSpaceFormQuotientModel ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_positiveComponent_of_sphericalSpaceFormQuotientModel

omit [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] in
theorem nonempty_positiveComponent_of_univ_eq {U : Set M} (h : Set.univ = U)
    (hP : Nonempty (PositiveComponent (M := M) Set.univ)) :
    Nonempty (PositiveComponent (M := M) U) :=
  h ▸ hP

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_positiveComponent_of_univ_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_positiveComponent_of_univ_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_positiveComponent_of_univ_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_positiveComponent_of_univ_eq

omit [SigmaCompactSpace M] in
theorem nonempty_canonicalAlternative_positive_of_diffeomorph_sphereThree
    {D : RealTimeInterval} (S : SolutionOn (I := I3) (M := M) D)
    {eps C c : ℝ} {x : M} {t : ℝ}
    (hwhole : Set.univ = connectedComponent x)
    (e : Diffeomorph (𝓡 3) I3 (Sphere 3) M ∞)
    (hQ : 0 < S.scalar t x) (hc : C⁻¹ ≤ c)
    (h : ∀ y ∈ Set.univ, c ≤ leastCurvatureOperatorEigenvalueAt (I := I3)
      (scaleMetric (I := I3) (S.scalar t x) hQ (S.base.metric t)) y
      (metricAlgebraicCurvatureTensorAt (I := I3) (M := M)
        (scaleMetric (I := I3) (S.scalar t x) hQ (S.base.metric t)) y)) :
    Nonempty (CanonicalAlternative S eps C x t Set.univ) :=
  canonicalAlternative_positive_of_scaleInvariant_lower_bound S hwhole
    (positiveComponentOfDiffeomorphSphereThree e) hQ hc h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_canonicalAlternative_positive_of_diffeomorph_sphereThree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_canonicalAlternative_positive_of_diffeomorph_sphereThree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_canonicalAlternative_positive_of_diffeomorph_sphereThree ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_canonicalAlternative_positive_of_diffeomorph_sphereThree

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

section
set_option autoImplicit false

noncomputable section

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {Z M : Type*} [TopologicalSpace Z] [ChartedSpace ThreeSpace Z]
  [TopologicalSpace M] [ChartedSpace ThreeSpace M]

def ProjectivePresentation.map (pr : ProjectivePresentation Z) (e : Z ≃ₘ⟮I3, I3⟯ M) :
    ProjectivePresentation M where
  quotient := e ∘ pr.quotient
  smooth := e.contMDiff.comp pr.smooth
  onto := e.surjective.comp pr.onto
  fibers := fun a b => e.injective.eq_iff.trans (pr.fibers a b)
  local_diffeo := by
    intro a
    rw [mfderiv_comp a (e.contMDiff.mdifferentiable (by simp) _)
      (pr.smooth.mdifferentiable (by simp) a)]
    exact (e.mfderivToContinuousLinearEquiv (by simp) (pr.quotient a)).bijective.comp (pr.local_diffeo a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ProjectivePresentation.map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ProjectivePresentation.map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ProjectivePresentation.map ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ProjectivePresentation.map

@[simp] theorem ProjectivePresentation.map_quotient (pr : ProjectivePresentation Z)
    (e : Z ≃ₘ⟮I3, I3⟯ M) (a : Sphere 3) :
    (pr.map e).quotient a = e (pr.quotient a) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ProjectivePresentation.map_quotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ProjectivePresentation.map_quotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ProjectivePresentation.map_quotient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ProjectivePresentation.map_quotient

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
