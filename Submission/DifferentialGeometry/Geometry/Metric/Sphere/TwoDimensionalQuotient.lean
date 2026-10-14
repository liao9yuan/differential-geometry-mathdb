import Submission.DifferentialGeometry.Geometry.Metric.Sphere.FreeOrthogonalAction
import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Quotient.PositiveSpaceForm
import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Quotient.Descent
import Submission.DifferentialGeometry.Topology.ProjectiveSpace.Real

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Metric
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable [Fact (Module.finrank ℝ E = 2 + 1)]

private instance euclideanThreeFinrankFact :
    Fact (Module.finrank ℝ
      (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨by norm_num [finrank_euclideanSpace_fin]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.euclideanThreeFinrankFact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.euclideanThreeFinrankFact target :: scope.openDecls } }

private theorem RoundSphereQuotient.proj_injective_or_antipodal_fibers
    (D : RoundSphereQuotient E 2) :
    Function.Injective D.proj ∨
      ∀ x y : _root_.Metric.sphere (0 : E) 1,
        D.proj x = D.proj y ↔ x = y ∨ x = -y := by
  classical
  by_cases hneg : ∃ gamma : D.Γ,
      D.ρ gamma = LinearIsometryEquiv.neg ℝ
  · right
    intro x y
    constructor
    · intro hxy
      obtain ⟨gamma, hgamma⟩ := D.proj_eq_imp x y hxy
      rcases orth_rep_apply_eq_one_or_neg_of_free_sphere_action
          D.ρ D.action_free gamma with hone | hminus
      · left
        apply Subtype.ext
        have h := congrArg Subtype.val hgamma
        simpa [hone] using h
      · right
        apply Subtype.ext
        have h := congrArg Subtype.val hgamma
        have h' := congrArg Neg.neg h
        simpa [hminus] using h'
    · rintro (hxy | hxy)
      · exact congrArg D.proj hxy
      · obtain ⟨gamma, hgamma⟩ := hneg
        have hsmul := D.proj_smul gamma y
        rw [hgamma] at hsmul
        have hnegY :
            sphereDiffeo (n := 2) (LinearIsometryEquiv.neg ℝ) y = -y := by
          apply Subtype.ext
          rfl
        rw [hnegY] at hsmul
        rw [hxy]
        exact hsmul
  · left
    intro x y hxy
    obtain ⟨gamma, hgamma⟩ := D.proj_eq_imp x y hxy
    rcases orth_rep_apply_eq_one_or_neg_of_free_sphere_action
        D.ρ D.action_free gamma with hone | hminus
    · apply Subtype.ext
      have h := congrArg Subtype.val hgamma
      simpa [hone] using h
    · exact (hneg ⟨gamma, hminus⟩).elim

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.RoundSphereQuotient.proj_injective_or_antipodal_fibers
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.RoundSphereQuotient.proj_injective_or_antipodal_fibers target :: scope.openDecls } }

theorem RoundSphereQuotient.proj_fiber_dichotomy
    (D : RoundSphereQuotient E 2) :
    (Function.Injective D.proj ∧
      ¬ ∀ x y : _root_.Metric.sphere (0 : E) 1,
        D.proj x = D.proj y ↔ x = y ∨ x = -y) ∨
    (¬ Function.Injective D.proj ∧
      ∀ x y : _root_.Metric.sphere (0 : E) 1,
        D.proj x = D.proj y ↔ x = y ∨ x = -y) := by
  classical
  have hinjNot : Function.Injective D.proj →
      ¬ ∀ x y : _root_.Metric.sphere (0 : E) 1,
        D.proj x = D.proj y ↔ x = y ∨ x = -y := by
    intro hinj hanti
    have hfinrank : 0 < Module.finrank ℝ E := by
      rw [show Module.finrank ℝ E = 2 + 1 from Fact.out]
      norm_num
    let : Nontrivial E := Module.nontrivial_of_finrank_pos hfinrank
    let x : _root_.Metric.sphere (0 : E) 1 :=
      Classical.choice
        (NormedSpace.sphere_nonempty_rclike ℝ
          (E := E) (r := (1 : ℝ)) zero_le_one)
    have hproj : D.proj x = D.proj (-x) :=
      (hanti x (-x)).mpr (Or.inr (by simp))
    exact ne_neg_of_mem_unit_sphere ℝ x (hinj hproj)
  rcases D.proj_injective_or_antipodal_fibers with hinj | hanti
  · exact Or.inl ⟨hinj, hinjNot hinj⟩
  · exact Or.inr ⟨fun hinj => hinjNot hinj hanti, hanti⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.RoundSphereQuotient.proj_fiber_dichotomy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.RoundSphereQuotient.proj_fiber_dichotomy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.RoundSphereQuotient.proj_fiber_dichotomy ``Submission.DifferentialGeometry.Geometry.RoundSphereQuotient.proj_fiber_dichotomy

noncomputable def RoundSphereQuotient.sphereHomeomorph
    (D : RoundSphereQuotient E 2)
    (hinj : Function.Injective D.proj) :
    sphere (0 : E) 1 ≃ₜ D.Q :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective D.proj ⟨hinj, D.proj_surjective⟩)
    D.proj_smooth.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.RoundSphereQuotient.sphereHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.RoundSphereQuotient.sphereHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.RoundSphereQuotient.sphereHomeomorph ``Submission.DifferentialGeometry.Geometry.RoundSphereQuotient.sphereHomeomorph

theorem RoundSphereQuotient.sphereHomeomorph_apply
    (D : RoundSphereQuotient E 2)
    (hinj : Function.Injective D.proj) (x : _root_.Metric.sphere (0 : E) 1) :
    D.sphereHomeomorph hinj x = D.proj x :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.RoundSphereQuotient.sphereHomeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.RoundSphereQuotient.sphereHomeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.RoundSphereQuotient.sphereHomeomorph_apply ``Submission.DifferentialGeometry.Geometry.RoundSphereQuotient.sphereHomeomorph_apply

private theorem RoundSphereQuotient.proj_respects_antipodal
    (D : RoundSphereQuotient E 2)
    (hanti : ∀ x y : _root_.Metric.sphere (0 : E) 1,
      D.proj x = D.proj y ↔ x = y ∨ x = -y)
    (x y : _root_.Metric.sphere (0 : E) 1)
    (hxy : MulAction.orbitRel
      (realProjectiveSpaceAntipodalGroup E) _ x y) :
    D.proj x = D.proj y := by
  rcases hxy with ⟨psi, rfl⟩
  rcases realProjectiveSpaceAntipodalGroup_smul_eq_self_or_neg psi y with
    hself | hneg
  · exact (hanti (psi • y) y).mpr (Or.inl hself)
  · exact (hanti (psi • y) y).mpr (Or.inr hneg)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.RoundSphereQuotient.proj_respects_antipodal
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.RoundSphereQuotient.proj_respects_antipodal target :: scope.openDecls } }

private def RoundSphereQuotient.realProjectiveSpaceToQuotient
    (D : RoundSphereQuotient E 2)
    (hanti : ∀ x y : _root_.Metric.sphere (0 : E) 1,
      D.proj x = D.proj y ↔ x = y ∨ x = -y) :
    RealProjectiveSpace E → D.Q :=
  Quotient.lift D.proj (D.proj_respects_antipodal hanti)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.RoundSphereQuotient.realProjectiveSpaceToQuotient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.RoundSphereQuotient.realProjectiveSpaceToQuotient target :: scope.openDecls } }

private theorem RoundSphereQuotient.realProjectiveSpaceToQuotient_apply
    (D : RoundSphereQuotient E 2)
    (hanti : ∀ x y : _root_.Metric.sphere (0 : E) 1,
      D.proj x = D.proj y ↔ x = y ∨ x = -y)
    (x : _root_.Metric.sphere (0 : E) 1) :
    D.realProjectiveSpaceToQuotient hanti
        (realProjectiveSpaceQuotientMap x) = D.proj x :=
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.RoundSphereQuotient.realProjectiveSpaceToQuotient_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.RoundSphereQuotient.realProjectiveSpaceToQuotient_apply target :: scope.openDecls } }

private theorem RoundSphereQuotient.realProjectiveSpaceToQuotient_continuous
    (D : RoundSphereQuotient E 2)
    (hanti : ∀ x y : _root_.Metric.sphere (0 : E) 1,
      D.proj x = D.proj y ↔ x = y ∨ x = -y) :
    Continuous (D.realProjectiveSpaceToQuotient hanti) :=
  D.proj_smooth.continuous.quotient_lift
    (D.proj_respects_antipodal hanti)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.RoundSphereQuotient.realProjectiveSpaceToQuotient_continuous
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.RoundSphereQuotient.realProjectiveSpaceToQuotient_continuous target :: scope.openDecls } }

noncomputable def RoundSphereQuotient.realProjectiveSpaceHomeomorph
    (D : RoundSphereQuotient E 2)
    (hanti : ∀ x y : _root_.Metric.sphere (0 : E) 1,
      D.proj x = D.proj y ↔ x = y ∨ x = -y) :
    RealProjectiveSpace E ≃ₜ D.Q := by
  let F := D.realProjectiveSpaceToQuotient hanti
  have hsurj : Function.Surjective F := by
    intro q
    obtain ⟨x, hx⟩ := D.proj_surjective q
    exact ⟨realProjectiveSpaceQuotientMap x, hx⟩
  have hinj : Function.Injective F := by
    intro q r hqr
    induction q using Quotient.inductionOn with
    | _ x =>
      induction r using Quotient.inductionOn with
      | _ y =>
        change D.proj x = D.proj y at hqr
        change realProjectiveSpaceQuotientMap x =
          realProjectiveSpaceQuotientMap y
        apply realProjectiveSpaceQuotientMap_eq_iff.mpr
        rcases (hanti x y).mp hqr with hxy | hxy
        · exact Or.inl hxy
        · exact Or.inr (congrArg Subtype.val hxy)
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective F ⟨hinj, hsurj⟩)
    (D.realProjectiveSpaceToQuotient_continuous hanti)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.RoundSphereQuotient.realProjectiveSpaceHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.RoundSphereQuotient.realProjectiveSpaceHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.RoundSphereQuotient.realProjectiveSpaceHomeomorph ``Submission.DifferentialGeometry.Geometry.RoundSphereQuotient.realProjectiveSpaceHomeomorph

theorem RoundSphereQuotient.realProjectiveSpaceHomeomorph_apply
    (D : RoundSphereQuotient E 2)
    (hanti : ∀ x y : _root_.Metric.sphere (0 : E) 1,
      D.proj x = D.proj y ↔ x = y ∨ x = -y)
    (x : _root_.Metric.sphere (0 : E) 1) :
    D.realProjectiveSpaceHomeomorph hanti
        (realProjectiveSpaceQuotientMap x) = D.proj x :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.RoundSphereQuotient.realProjectiveSpaceHomeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.RoundSphereQuotient.realProjectiveSpaceHomeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.RoundSphereQuotient.realProjectiveSpaceHomeomorph_apply ``Submission.DifferentialGeometry.Geometry.RoundSphereQuotient.realProjectiveSpaceHomeomorph_apply

theorem RoundSphereQuotient.homeomorphic_sphere_or_real_projective_space
    (D : RoundSphereQuotient E 2) :
    (∃ e : _root_.Metric.sphere (0 : E) 1 ≃ₜ D.Q,
      ∀ x, e x = D.proj x) ∨
    (∃ e : RealProjectiveSpace E ≃ₜ D.Q,
      ∀ x, e (realProjectiveSpaceQuotientMap x) = D.proj x) := by
  rcases D.proj_fiber_dichotomy with htriv | hanti
  · exact Or.inl ⟨D.sphereHomeomorph htriv.1,
      D.sphereHomeomorph_apply htriv.1⟩
  · exact Or.inr ⟨D.realProjectiveSpaceHomeomorph hanti.2,
      D.realProjectiveSpaceHomeomorph_apply hanti.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.RoundSphereQuotient.homeomorphic_sphere_or_real_projective_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.RoundSphereQuotient.homeomorphic_sphere_or_real_projective_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.RoundSphereQuotient.homeomorphic_sphere_or_real_projective_space ``Submission.DifferentialGeometry.Geometry.RoundSphereQuotient.homeomorphic_sphere_or_real_projective_space

theorem RoundSphereQuotient.homeomorphic_two_sphere_or_real_projective_plane
    (D : RoundSphereQuotient
      (EuclideanSpace ℝ (Fin 3)) 2) :
    (∃ e : _root_.Metric.sphere
        (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ D.Q,
      ∀ x, e x = D.proj x) ∨
    (∃ e : RealProjectivePlane ≃ₜ D.Q,
      ∀ x, e (realProjectivePlaneQuotientMap x) = D.proj x) := by
  rcases D.homeomorphic_sphere_or_real_projective_space with hsphere | hprojective
  · exact Or.inl hsphere
  · right
    obtain ⟨e, he⟩ := hprojective
    exact ⟨e, fun x => by
      simpa only [realProjectivePlaneQuotientMap] using he x⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.RoundSphereQuotient.homeomorphic_two_sphere_or_real_projective_plane then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.RoundSphereQuotient.homeomorphic_two_sphere_or_real_projective_plane"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.RoundSphereQuotient.homeomorphic_two_sphere_or_real_projective_plane ``Submission.DifferentialGeometry.Geometry.RoundSphereQuotient.homeomorphic_two_sphere_or_real_projective_plane

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [FiniteDimensional Real F]
variable {G : Type*} [TopologicalSpace G]
variable {J : ModelWithCorners Real F G}
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
variable [SigmaCompactSpace N] [T2Space N]

theorem homeomorphic_two_sphere_or_real_projective_plane_of_constant_positive_sectional_curvature
    (hcompact : CompactSpace N) (hconn : ConnectedSpace N)
    (hbdry : J.Boundaryless) (hdim : Module.finrank Real F = 2)
    (g : SmoothRiemannianMetric J N) (c : Real) (hc : 0 < c)
    (hsec : ∀ x : N, ∀ v w : TangentSpace J x,
      metricRm04StandardAt (I := J) (M := N) g x v w w v =
        c * (g.inner x v v * g.inner x w w -
          g.inner x v w * g.inner x v w)) :
    Nonempty (_root_.Metric.sphere
        (0 : EuclideanSpace Real (Fin 3)) 1 ≃ₜ N) ∨
      Nonempty (RealProjectivePlane ≃ₜ N) := by
  let q := roundSphereQuotientOfConstantPositiveSectionalCurvature
    (I := J) (M := N) (n := 2) (by omega)
    hcompact hconn hbdry hdim g c hc hsec
  rcases q.1.homeomorphic_two_sphere_or_real_projective_plane with hsphere | hprojective
  · left
    obtain ⟨e, _he⟩ := hsphere
    exact ⟨e.trans q.2.symm.toHomeomorph⟩
  · right
    obtain ⟨e, _he⟩ := hprojective
    exact ⟨e.trans q.2.symm.toHomeomorph⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.homeomorphic_two_sphere_or_real_projective_plane_of_constant_positive_sectional_curvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.homeomorphic_two_sphere_or_real_projective_plane_of_constant_positive_sectional_curvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.homeomorphic_two_sphere_or_real_projective_plane_of_constant_positive_sectional_curvature ``Submission.DifferentialGeometry.Geometry.homeomorphic_two_sphere_or_real_projective_plane_of_constant_positive_sectional_curvature

end DifferentialGeometry.Geometry
