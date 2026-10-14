import Submission.DifferentialGeometry.Bundle.Hom.Regularity
import Submission.DifferentialGeometry.Tensor.Alternating.BundleCompSmooth
import Submission.DifferentialGeometry.Tensor.Exterior.Defs
import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Round.ProjectedConnection
import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Isometry.OrthogonalAction
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace Real A]
  {n : Nat} [Fact (Module.finrank Real A = n + 1)]

private theorem sphere_inner_self (y : Metric.sphere (0 : A) 1) :
    inner Real (y : A) (y : A) = 1 := by
  rw [real_inner_self_eq_norm_sq, (mem_sphere_zero_iff_norm.mp y.2)]
  norm_num

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.sphere_inner_self
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.sphere_inner_self target :: scope.openDecls } }

private theorem sphere_inner_dIncl (y : Metric.sphere (0 : A) 1)
    (v : TangentSpace (𝓡 n) y) : _root_.Inner.inner Real (y : A) (dIncl (n := n) y v) = 0 := by
  rw [← dInclEquiv_coe (n := n) y]
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (dInclEquiv (n := n) y v).property

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.sphere_inner_dIncl
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.sphere_inner_dIncl target :: scope.openDecls } }

private def cylinderTangentFramingMap (x : Metric.sphere (0 : A) 1 × Real) :
    TangentSpace ((𝓡 n).prod 𝓘(Real, Real)) x →L[Real] A :=
  (dIncl (n := n) x.1).coprod ((ContinuousLinearMap.id Real Real).smulRight (x.1 : A))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.cylinderTangentFramingMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.cylinderTangentFramingMap target :: scope.openDecls } }

private theorem cylinderTangentFramingMap_apply (x : Metric.sphere (0 : A) 1 × Real)
    (v : TangentSpace ((𝓡 n).prod 𝓘(Real, Real)) x) :
    cylinderTangentFramingMap x v = dIncl (n := n) x.1 v.1 + v.2 • (x.1 : A) := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.cylinderTangentFramingMap_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.cylinderTangentFramingMap_apply target :: scope.openDecls } }

private theorem cylinderTangentFramingMap_inner (x : Metric.sphere (0 : A) 1 × Real)
    (v : TangentSpace ((𝓡 n).prod 𝓘(Real, Real)) x) :
    inner Real (x.1 : A) (cylinderTangentFramingMap x v) = v.2 := by
  rw [cylinderTangentFramingMap_apply, inner_add_right, inner_smul_right]
  erw [sphere_inner_dIncl, sphere_inner_self]
  simp only [mul_one, zero_add]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.cylinderTangentFramingMap_inner
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.cylinderTangentFramingMap_inner target :: scope.openDecls } }

private theorem cylinderTangentFramingMap_bijective (x : Metric.sphere (0 : A) 1 × Real) :
    Function.Bijective (cylinderTangentFramingMap (n := n) x) := by
  constructor
  · intro u v huv
    have hs : u.2 = v.2 := by
      rw [← cylinderTangentFramingMap_inner x u, ← cylinderTangentFramingMap_inner x v, huv]
    apply Prod.ext
    · apply injective_mvfderiv_subtypeVal_sphere x.1
      have h := huv
      rw [cylinderTangentFramingMap_apply, cylinderTangentFramingMap_apply, hs] at h
      exact add_right_cancel h
    · exact hs
  · intro w
    let a := _root_.Inner.inner Real (x.1 : A) w
    have hz : w - a • (x.1 : A) ∈ (Real ∙ (x.1 : A))ᗮ := by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right,
        inner_smul_right, sphere_inner_self, mul_one]
      exact sub_self a
    let v := (dInclEquiv (n := n) x.1).symm ⟨w - a • (x.1 : A), hz⟩
    refine ⟨(v, a), ?_⟩
    change dIncl (n := n) x.1 v + a • (x.1 : A) = w
    rw [← dInclEquiv_coe (n := n) x.1]
    have hv : (dInclEquiv (n := n) x.1) v = ⟨w - a • (x.1 : A), hz⟩ :=
      (dInclEquiv (n := n) x.1).apply_symm_apply _
    rw [hv]
    exact sub_add_cancel w (a • (x.1 : A))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.cylinderTangentFramingMap_bijective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.cylinderTangentFramingMap_bijective target :: scope.openDecls } }

def cylinderTangentFraming (x : Metric.sphere (0 : A) 1 × Real) :
    TangentSpace ((𝓡 n).prod 𝓘(Real, Real)) x ≃L[Real] A := by
  let _ : FiniteDimensional Real A :=
    FiniteDimensional.of_finrank_eq_succ (Fact.out : Module.finrank Real A = n + 1)
  let _ : FiniteDimensional Real (TangentSpace ((𝓡 n).prod 𝓘(Real, Real)) x) :=
    inferInstanceAs (FiniteDimensional Real (EuclideanSpace Real (Fin n) × Real))
  let _ : T2Space (TangentSpace ((𝓡 n).prod 𝓘(Real, Real)) x) :=
    inferInstanceAs (T2Space (EuclideanSpace Real (Fin n) × Real))
  exact LinearEquiv.toContinuousLinearEquiv
    (LinearEquiv.ofBijective (cylinderTangentFramingMap x).toLinearMap
      (cylinderTangentFramingMap_bijective x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderTangentFraming then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderTangentFraming"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderTangentFraming ``Submission.DifferentialGeometry.Geometry.cylinderTangentFraming

@[simp] theorem cylinderTangentFraming_apply (x : Metric.sphere (0 : A) 1 × Real)
    (v : TangentSpace ((𝓡 n).prod 𝓘(Real, Real)) x) :
    cylinderTangentFraming x v = dIncl (n := n) x.1 v.1 + v.2 • (x.1 : A) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderTangentFraming_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderTangentFraming_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderTangentFraming_apply ``Submission.DifferentialGeometry.Geometry.cylinderTangentFraming_apply


theorem cylinderTangentFraming_contMDiff :
    ContMDiff ((𝓡 n).prod 𝓘(Real, Real)).tangent 𝓘(Real, A) ∞
      (fun v : TangentBundle ((𝓡 n).prod 𝓘(Real, Real))
          (Metric.sphere (0 : A) 1 × Real) => cylinderTangentFraming v.proj v.2) := by
  have hsplit := contMDiff_equivTangentBundleProd (n := ∞)
    (I := 𝓡 n) (M := Metric.sphere (0 : A) 1) (I' := 𝓘(Real, Real)) (M' := Real)
  have hsphere : ContMDiff ((𝓡 n).prod 𝓘(Real, Real)).tangent (𝓡 n).tangent ∞
      (fun v : TangentBundle ((𝓡 n).prod 𝓘(Real, Real))
        (Metric.sphere (0 : A) 1 × Real) =>
        (⟨v.proj.1, v.2.1⟩ : TangentBundle (𝓡 n) (Metric.sphere (0 : A) 1))) :=
    contMDiff_fst.comp hsplit
  have hreal : ContMDiff ((𝓡 n).prod 𝓘(Real, Real)).tangent 𝓘(Real, Real).tangent ∞
      (fun v : TangentBundle ((𝓡 n).prod 𝓘(Real, Real))
        (Metric.sphere (0 : A) 1 × Real) =>
        (⟨v.proj.2, v.2.2⟩ : TangentBundle 𝓘(Real, Real) Real)) :=
    contMDiff_snd.comp hsplit
  have hinc := (show ContMDiff (𝓡 n) 𝓘(Real, A) ∞
      (Subtype.val : Metric.sphere (0 : A) 1 → A) from contMDiff_coe_sphere).contMDiff_tangentMap
    (m := ∞) (by simp)
  have hhor : ContMDiff ((𝓡 n).prod 𝓘(Real, Real)).tangent 𝓘(Real, A) ∞
      (fun v : TangentBundle ((𝓡 n).prod 𝓘(Real, Real))
        (Metric.sphere (0 : A) 1 × Real) => dIncl (n := n) v.proj.1 v.2.1) := by
    exact (contMDiff_snd_tangentBundle_modelSpace A 𝓘(Real, A)).comp
      (hinc.comp hsphere)
  have hver : ContMDiff ((𝓡 n).prod 𝓘(Real, Real)).tangent 𝓘(Real, Real) ∞
      (fun v : TangentBundle ((𝓡 n).prod 𝓘(Real, Real))
        (Metric.sphere (0 : A) 1 × Real) => v.2.2) :=
    (contMDiff_snd_tangentBundle_modelSpace Real 𝓘(Real, Real)).comp hreal
  have hbase : ContMDiff ((𝓡 n).prod 𝓘(Real, Real)).tangent 𝓘(Real, A) ∞
      (fun v : TangentBundle ((𝓡 n).prod 𝓘(Real, Real))
        (Metric.sphere (0 : A) 1 × Real) => (v.proj.1 : A)) :=
    contMDiff_coe_sphere.comp ((_root_.Bundle.contMDiff_proj (TangentSpace (𝓡 n))).comp hsphere)
  exact hhor.add (hver.smul hbase)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderTangentFraming_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderTangentFraming_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderTangentFraming_contMDiff ``Submission.DifferentialGeometry.Geometry.cylinderTangentFraming_contMDiff


theorem cylinderTangentFraming_prodCongr (e : A ≃ₗᵢ[Real] A)
    (psi : Real ≃ₘ⟮𝓘(Real, Real), 𝓘(Real, Real)⟯ Real)
    (x : Metric.sphere (0 : A) 1 × Real)
    (v : TangentSpace ((𝓡 n).prod 𝓘(Real, Real)) x) :
    let _ : FiniteDimensional Real A :=
      FiniteDimensional.of_finrank_eq_succ (Fact.out : Module.finrank Real A = n + 1)
    cylinderTangentFraming ((sphereDiffeo (n := n) e).prodCongr psi x)
      (mfderiv ((𝓡 n).prod 𝓘(Real, Real)) ((𝓡 n).prod 𝓘(Real, Real))
        ((sphereDiffeo (n := n) e).prodCongr psi) x v) =
      e (dIncl (n := n) x.1 v.1 +
        (show Real from mfderiv 𝓘(Real, Real) 𝓘(Real, Real) psi x.2 v.2) • (x.1 : A)) := by
  let _ : FiniteDimensional Real A :=
    FiniteDimensional.of_finrank_eq_succ (Fact.out : Module.finrank Real A = n + 1)
  dsimp only
  rw [cylinderTangentFraming_apply]
  change dIncl (n := n) (sphereDiffeo (n := n) e x.1)
    (mfderiv ((𝓡 n).prod 𝓘(Real, Real)) ((𝓡 n).prod 𝓘(Real, Real))
      (Prod.map (sphereDiffeo (n := n) e) psi) x v).1 +
    (mfderiv ((𝓡 n).prod 𝓘(Real, Real)) ((𝓡 n).prod 𝓘(Real, Real))
      (Prod.map (sphereDiffeo (n := n) e) psi) x v).2 •
      (sphereDiffeo (n := n) e x.1 : A) = _
  rw [mfderiv_prodMap ((sphereDiffeo (n := n) e).contMDiff.mdifferentiableAt (by simp))
    (psi.contMDiff.mdifferentiableAt (by simp))]
  erw [mfderiv_incl_sphereDiffeo]
  rw [sphereDiffeo_coe, map_add]
  erw [map_smul]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderTangentFraming_prodCongr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderTangentFraming_prodCongr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderTangentFraming_prodCongr ``Submission.DifferentialGeometry.Geometry.cylinderTangentFraming_prodCongr

theorem cylinderTangentFraming_hom_contMDiff :
    ContMDiff ((𝓡 n).prod 𝓘(Real, Real))
      (((𝓡 n).prod 𝓘(Real, Real)).prod
        𝓘(Real, (EuclideanSpace Real (Fin n) × Real) →L[Real] A)) ∞
      (fun x : Metric.sphere (0 : A) 1 × Real =>
        (⟨x, (cylinderTangentFraming x).toContinuousLinearMap⟩ :
          _root_.Bundle.TotalSpace ((EuclideanSpace Real (Fin n) × Real) →L[Real] A)
            (fun x => TangentSpace ((𝓡 n).prod 𝓘(Real, Real)) x →L[Real]
              Bundle.Trivial (Metric.sphere (0 : A) 1 × Real) A x))) := by
  apply ContMDiff.clm_bundle_of_map
  intro v
  rw [_root_.Bundle.contMDiffAt_totalSpace]
  refine ⟨contMDiff_proj (TangentSpace ((𝓡 n).prod 𝓘(Real, Real))) v, ?_⟩
  exact cylinderTangentFraming_contMDiff v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderTangentFraming_hom_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderTangentFraming_hom_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderTangentFraming_hom_contMDiff ``Submission.DifferentialGeometry.Geometry.cylinderTangentFraming_hom_contMDiff


def cylinderDifferentialForm {k : Nat} (α : A [⋀^Fin k]→L[Real] Real) :
    DifferentialForm ((𝓡 n).prod 𝓘(Real, Real)) (Metric.sphere (0 : A) 1 × Real) k := by
  refine ⟨fun x => α.compContinuousLinearMap (cylinderTangentFraming x).toContinuousLinearMap, ?_⟩
  have hα : ContMDiff ((𝓡 n).prod 𝓘(Real, Real))
      (((𝓡 n).prod 𝓘(Real, Real)).prod 𝓘(Real, A [⋀^Fin k]→L[Real] Real)) ∞
      (fun x : Metric.sphere (0 : A) 1 × Real =>
        (⟨x, α⟩ : _root_.Bundle.TotalSpace (A [⋀^Fin k]→L[Real] Real)
          (Bundle.continuousAlternatingMap Real (Fin k) A
            (Bundle.Trivial (Metric.sphere (0 : A) 1 × Real) A) Real
              (Bundle.Trivial (Metric.sphere (0 : A) 1 × Real) Real)))) := by
    intro x
    rw [_root_.Bundle.contMDiffAt_totalSpace]
    refine ⟨contMDiffAt_id, ?_⟩
    have heq : (fun y : Metric.sphere (0 : A) 1 × Real =>
        (_root_.FiberBundle.trivializationAt (A [⋀^Fin k]→L[Real] Real)
          (Bundle.continuousAlternatingMap Real (Fin k) A
            (Bundle.Trivial (Metric.sphere (0 : A) 1 × Real) A) Real
              (Bundle.Trivial (Metric.sphere (0 : A) 1 × Real) Real)) x ⟨y, α⟩).2) =
        fun _ => α := by
      funext y
      rw [FiberBundle.trivializationAt_continuousAlternatingMap_apply]
      ext v
      simp [ContinuousAlternatingMap.inCoordinates]
    rw [heq]
    exact contMDiffAt_const
  exact hα.alternating_bundle_comp cylinderTangentFraming_hom_contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDifferentialForm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDifferentialForm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDifferentialForm ``Submission.DifferentialGeometry.Geometry.cylinderDifferentialForm

@[simp] theorem cylinderDifferentialForm_apply {k : Nat}
    (α : A [⋀^Fin k]→L[Real] Real) (x : Metric.sphere (0 : A) 1 × Real)
    (v : Fin k → TangentSpace ((𝓡 n).prod 𝓘(Real, Real)) x) :
    cylinderDifferentialForm α x v = α (fun i => cylinderTangentFraming x (v i)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDifferentialForm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDifferentialForm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDifferentialForm_apply ``Submission.DifferentialGeometry.Geometry.cylinderDifferentialForm_apply

theorem cylinderDifferentialForm_ne_zero {k : Nat}
    (α : A [⋀^Fin k]→L[Real] Real) (hα : α ≠ 0)
    (x : Metric.sphere (0 : A) 1 × Real) : cylinderDifferentialForm (n := n) α x ≠ 0 := by
  intro h
  apply hα
  ext v
  have hv := congrArg (fun β : TangentSpace ((𝓡 n).prod 𝓘(Real, Real)) x [⋀^Fin k]→L[Real] Real =>
    β (fun i => (cylinderTangentFraming x).symm (v i))) h
  simpa [cylinderDifferentialForm_apply] using hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDifferentialForm_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDifferentialForm_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDifferentialForm_ne_zero ``Submission.DifferentialGeometry.Geometry.cylinderDifferentialForm_ne_zero

end DifferentialGeometry.Geometry
