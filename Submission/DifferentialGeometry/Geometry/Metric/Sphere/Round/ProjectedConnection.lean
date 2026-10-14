import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Manifold _root_.Set _root_.Metric _root_.Module
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.RealInnerProductSpace

namespace DifferentialGeometry
namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 1)]

noncomputable def dInclField (Y : ∀ x : _root_.Metric.sphere (0 : E) 1, TangentSpace (𝓡 n) x) :
    sphere (0 : E) 1 → E :=
  fun x => dIncl (n := n) x (Y x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.dInclField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.dInclField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.dInclField ``Submission.DifferentialGeometry.Geometry.dInclField

omit [FiniteDimensional ℝ E] in
@[simp] theorem dInclField_apply (Y : ∀ x : _root_.Metric.sphere (0 : E) 1, TangentSpace (𝓡 n) x)
    (x : _root_.Metric.sphere (0 : E) 1) : dInclField (n := n) Y x = dIncl (n := n) x (Y x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.dInclField_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.dInclField_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.dInclField_apply ``Submission.DifferentialGeometry.Geometry.dInclField_apply

omit [FiniteDimensional ℝ E] in
theorem dInclField_mdifferentiableAt
    {Y : ∀ x : _root_.Metric.sphere (0 : E) 1, TangentSpace (𝓡 n) x} {x : _root_.Metric.sphere (0 : E) 1}
    (hY : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y => (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y (Y y))) x) :
    MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) (dInclField (n := n) Y) x := by
  have htangent : ContMDiff (𝓡 n).tangent 𝓘(ℝ, E).tangent ∞
      (tangentMap (𝓡 n) 𝓘(ℝ, E) ((↑) : _root_.Metric.sphere (0 : E) 1 → E)) := by
    apply ContMDiff.contMDiff_tangentMap contMDiff_coe_sphere
    exact le_top
  have hcomp : MDifferentiableAt (𝓡 n) (𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (fun y => tangentMap (𝓡 n) 𝓘(ℝ, E) ((↑) : _root_.Metric.sphere (0 : E) 1 → E) ⟨y, Y y⟩) x :=
    (htangent.contMDiffAt.mdifferentiableAt (by simp)).comp x hY
  rw [mdifferentiableAt_totalSpace] at hcomp
  refine hcomp.2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  simp only [dInclField, dIncl, tangentMap, trivializationAt_model_space_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.dInclField_mdifferentiableAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.dInclField_mdifferentiableAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.dInclField_mdifferentiableAt ``Submission.DifferentialGeometry.Geometry.dInclField_mdifferentiableAt

noncomputable def dInclEquiv (x : _root_.Metric.sphere (0 : E) 1) :
    TangentSpace (𝓡 n) x ≃L[ℝ] ((ℝ ∙ (↑x : E))ᗮ) := by
  haveI : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n)))
  haveI : T2Space (TangentSpace (𝓡 n) x) :=
    inferInstanceAs (T2Space (EuclideanSpace ℝ (Fin n)))
  have hmem : ∀ v : TangentSpace (𝓡 n) x, dIncl (n := n) x v ∈ (ℝ ∙ (↑x : E))ᗮ := by
    intro v
    rw [← range_mvfderiv_subtypeVal (n := n) x]
    exact ⟨v, rfl⟩
  refine LinearEquiv.toContinuousLinearEquiv
    (LinearEquiv.ofBijective ((dIncl (n := n) x).codRestrict _ hmem).toLinearMap ⟨?_, ?_⟩)
  · intro a b hab
    exact injective_mvfderiv_subtypeVal_sphere x (congrArg Subtype.val hab)
  · intro w
    obtain ⟨v, hv⟩ := (range_mvfderiv_subtypeVal (n := n) x).ge w.2
    exact ⟨v, Subtype.ext hv⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.dInclEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.dInclEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.dInclEquiv ``Submission.DifferentialGeometry.Geometry.dInclEquiv

omit [FiniteDimensional ℝ E] in
@[simp] theorem dInclEquiv_coe (x : _root_.Metric.sphere (0 : E) 1) (v : TangentSpace (𝓡 n) x) :
    ((dInclEquiv (n := n) x v : (ℝ ∙ (↑x : E))ᗮ) : E) = dIncl (n := n) x v := by
  simp only [dInclEquiv, LinearEquiv.coe_toContinuousLinearEquiv']
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.dInclEquiv_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.dInclEquiv_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.dInclEquiv_coe ``Submission.DifferentialGeometry.Geometry.dInclEquiv_coe

omit [FiniteDimensional ℝ E] in
theorem dInclField_add (Y Y' : ∀ x : _root_.Metric.sphere (0 : E) 1, TangentSpace (𝓡 n) x) :
    dInclField (n := n) (Y + Y') = dInclField (n := n) Y + dInclField (n := n) Y' := by
  funext y
  simp only [dInclField, Pi.add_apply, map_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.dInclField_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.dInclField_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.dInclField_add ``Submission.DifferentialGeometry.Geometry.dInclField_add

omit [FiniteDimensional ℝ E] in
theorem dInclField_smul (g : _root_.Metric.sphere (0 : E) 1 → ℝ)
    (Y : ∀ x : _root_.Metric.sphere (0 : E) 1, TangentSpace (𝓡 n) x) :
    dInclField (n := n) (g • Y) = g • dInclField (n := n) Y := by
  funext y
  change dIncl (n := n) y (g y • Y y) = g y • dIncl (n := n) y (Y y)
  exact map_smul _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.dInclField_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.dInclField_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.dInclField_smul ``Submission.DifferentialGeometry.Geometry.dInclField_smul

noncomputable def ambDeriv (Y : ∀ x : _root_.Metric.sphere (0 : E) 1, TangentSpace (𝓡 n) x)
    (x : _root_.Metric.sphere (0 : E) 1) : TangentSpace (𝓡 n) x →L[ℝ] E :=
  mvfderiv (𝓡 n) (dInclField (n := n) Y) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.ambDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.ambDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.ambDeriv ``Submission.DifferentialGeometry.Geometry.ambDeriv

omit [FiniteDimensional ℝ E] in
@[simp] theorem ambDeriv_apply (Y : ∀ x : _root_.Metric.sphere (0 : E) 1, TangentSpace (𝓡 n) x)
    (x : _root_.Metric.sphere (0 : E) 1) (v : TangentSpace (𝓡 n) x) :
    ambDeriv (n := n) Y x v = mvfderiv (𝓡 n) (dInclField (n := n) Y) x v := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.ambDeriv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.ambDeriv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.ambDeriv_apply ``Submission.DifferentialGeometry.Geometry.ambDeriv_apply

omit [FiniteDimensional ℝ E] in
theorem ambDeriv_add {Y Y' : ∀ x : _root_.Metric.sphere (0 : E) 1, TangentSpace (𝓡 n) x} {x : _root_.Metric.sphere (0 : E) 1}
    (hY : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y => (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y (Y y))) x)
    (hY' : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y => (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y (Y' y))) x)
    (v : TangentSpace (𝓡 n) x) :
    ambDeriv (n := n) (Y + Y') x v
      = ambDeriv (n := n) Y x v + ambDeriv (n := n) Y' x v := by
  have h : ambDeriv (n := n) (Y + Y') x = ambDeriv (n := n) Y x + ambDeriv (n := n) Y' x := by
    have h0 := mvfderiv_add (dInclField_mdifferentiableAt (n := n) hY)
      (dInclField_mdifferentiableAt (n := n) hY')
    rw [← dInclField_add] at h0
    exact h0
  rw [h, add_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.ambDeriv_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.ambDeriv_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.ambDeriv_add ``Submission.DifferentialGeometry.Geometry.ambDeriv_add

omit [FiniteDimensional ℝ E] in
theorem ambDeriv_smul {Y : ∀ x : _root_.Metric.sphere (0 : E) 1, TangentSpace (𝓡 n) x}
    {g : _root_.Metric.sphere (0 : E) 1 → ℝ} {x : _root_.Metric.sphere (0 : E) 1}
    (hY : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y => (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y (Y y))) x)
    (hg : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) g x) (v : TangentSpace (𝓡 n) x) :
    ambDeriv (n := n) (g • Y) x v
      = g x • ambDeriv (n := n) Y x v +
          (mvfderiv (𝓡 n) g x v) • dInclField (n := n) Y x := by
  have key := DFunLike.congr_fun
    (mvfderiv_smul hg (dInclField_mdifferentiableAt (n := n) hY)) v
  rw [← dInclField_smul] at key
  change mvfderiv (𝓡 n) (dInclField (n := n) (g • Y)) x v =
    g x • mvfderiv (𝓡 n) (dInclField (n := n) Y) x v +
      mvfderiv (𝓡 n) g x v • dInclField (n := n) Y x
  exact key

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.ambDeriv_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.ambDeriv_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.ambDeriv_smul ``Submission.DifferentialGeometry.Geometry.ambDeriv_smul

noncomputable def projConn (Y : ∀ x : _root_.Metric.sphere (0 : E) 1, TangentSpace (𝓡 n) x) :
    ∀ x : _root_.Metric.sphere (0 : E) 1, TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x :=
  fun x => (dInclEquiv (n := n) x).symm.toContinuousLinearMap.comp
    (((ℝ ∙ (↑x : E))ᗮ).orthogonalProjectionOnto.comp (ambDeriv (n := n) Y x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.projConn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.projConn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.projConn ``Submission.DifferentialGeometry.Geometry.projConn

omit [FiniteDimensional ℝ E] in
theorem dIncl_projConn (Y : ∀ x : _root_.Metric.sphere (0 : E) 1, TangentSpace (𝓡 n) x)
    (x : _root_.Metric.sphere (0 : E) 1) (v : TangentSpace (𝓡 n) x) :
    dIncl (n := n) x (projConn (n := n) Y x v)
      = (↑(((ℝ ∙ (↑x : E))ᗮ).orthogonalProjectionOnto
          (ambDeriv (n := n) Y x v)) : E) := by
  simp only [projConn, ContinuousLinearMap.comp_apply]
  rw [← dInclEquiv_coe (n := n) x]
  congr 1
  exact (dInclEquiv (n := n) x).apply_symm_apply _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.dIncl_projConn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.dIncl_projConn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.dIncl_projConn ``Submission.DifferentialGeometry.Geometry.dIncl_projConn


noncomputable def projConnCD :
    CovariantDerivative (𝓡 n) (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : _root_.Metric.sphere (0 : E) 1 → Type _) where
  toFun := projConn (n := n)
  isCovariantDerivativeOnUniv := by
    refine { add := ?_, leibniz := ?_ }
    · intro Y Y' x hY hY' _
      ext v
      rw [add_apply]
      refine injective_mvfderiv_subtypeVal_sphere x ?_
      change dIncl (n := n) x (projConn (n := n) (Y + Y') x v)
        = dIncl (n := n) x (projConn (n := n) Y x v + projConn (n := n) Y' x v)
      rw [map_add, dIncl_projConn, dIncl_projConn, dIncl_projConn, ambDeriv_add hY hY',
        map_add, Submodule.coe_add]
    · intro Y g x hY hg _
      ext v
      rw [add_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply]
      refine injective_mvfderiv_subtypeVal_sphere x ?_
      change dIncl (n := n) x (projConn (n := n) (g • Y) x v)
        = dIncl (n := n) x (g x • projConn (n := n) Y x v +
          (mvfderiv (𝓡 n) g x v) • Y x)
      have hmem : dInclField (n := n) Y x ∈ (ℝ ∙ (↑x : E))ᗮ := by
        rw [← range_mvfderiv_subtypeVal (n := n) x]; exact ⟨Y x, rfl⟩
      have hfix : (↑(((ℝ ∙ (↑x : E))ᗮ).orthogonalProjectionOnto
          (dInclField (n := n) Y x)) : E)
          = dInclField (n := n) Y x := by
        rw [← Submodule.starProjection_apply]
        exact Submodule.starProjection_eq_self_iff.mpr hmem
      rw [map_add, map_smul, map_smul, dIncl_projConn, dIncl_projConn, ambDeriv_smul hY hg,
        map_add, map_smul, map_smul, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul,
        hfix, dInclField_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.projConnCD then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.projConnCD"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.projConnCD ``Submission.DifferentialGeometry.Geometry.projConnCD

end Geometry
end DifferentialGeometry
