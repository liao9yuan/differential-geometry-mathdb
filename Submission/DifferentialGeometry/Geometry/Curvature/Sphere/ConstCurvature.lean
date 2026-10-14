import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Isometry.OrthogonalAction
import Submission.DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Basic
import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Round.Shape
import Submission.DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Sections
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Sectional
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.ConstantRicci

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Metric _root_.Module _root_.Submission.Module
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.RealInnerProductSpace

open _root_.Submission.DifferentialGeometry.Geometry.Curvature.CovariantDerivative

namespace DifferentialGeometry
namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 1)] [NeZero n]

omit [NeZero n] in
theorem metricRm04_round_invariant
    (e : E ≃ₗᵢ[ℝ] E) (x : _root_.Metric.sphere (0 : E) 1)
    (X Y Z W : TangentSpace (𝓡 n) x) :
    metricRm04StandardAt (roundMetric (E := E) (n := n)) x X Y Z W
      = metricRm04StandardAt (roundMetric (E := E) (n := n)) (sphereDiffeo (n := n) e x)
          (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) x X)
          (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) x Y)
          (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) x Z)
          (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) x W) := by
  by_cases hn : n = 0
  · subst n
    let : Subsingleton (TangentSpace (𝓡 0) x) := by
      change Subsingleton (EuclideanSpace ℝ (Fin 0))
      infer_instance
    let : Subsingleton (TangentSpace (𝓡 0) (sphereDiffeo (n := 0) e x)) := by
      change Subsingleton (EuclideanSpace ℝ (Fin 0))
      infer_instance
    have hX : X = 0 := Subsingleton.elim _ _
    have hY : Y = 0 := Subsingleton.elim _ _
    have hZ : Z = 0 := Subsingleton.elim _ _
    have hW : W = 0 := Subsingleton.elim _ _
    subst X
    subst Y
    subst Z
    subst W
    have hvx : vec4 (I := 𝓡 0) (0 : TangentSpace (𝓡 0) x) 0 0 0 = 0 := by
      funext i
      exact Subsingleton.elim _ _
    have hvy : vec4 (I := 𝓡 0)
        (0 : TangentSpace (𝓡 0) (sphereDiffeo (n := 0) e x)) 0 0 0 = 0 := by
      funext i
      exact Subsingleton.elim _ _
    have hmf : mfderiv (𝓡 0) (𝓡 0) (sphereDiffeo (n := 0) e) x
        (0 : TangentSpace (𝓡 0) x) = 0 :=
      (mfderiv (𝓡 0) (𝓡 0) (sphereDiffeo (n := 0) e) x).map_zero
    unfold metricRm04StandardAt tensor04StandardAt
    rw [hmf, hvx, hvy]
    exact ((metricRm04At (I := 𝓡 0) (M := _root_.Metric.sphere (0 : E) 1)
      (roundMetric (E := E) (n := 0)) x).map_coord_zero 0 rfl).trans
        ((metricRm04At (I := 𝓡 0) (M := _root_.Metric.sphere (0 : E) 1)
          (roundMetric (E := E) (n := 0)) (sphereDiffeo (n := 0) e x)).map_coord_zero 0 rfl).symm
  · let : NeZero n := ⟨hn⟩
    have : NeZero (_root_.Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
      rw [finrank_euclideanSpace_fin]
      infer_instance
    have : IsManifold (𝓡 n) 1 (_root_.Metric.sphere (0 : E) 1) :=
      EuclideanSpace.instIsManifoldSphere.of_le le_top
    have : IsManifold (𝓡 n) ((∞ : WithTop ℕ∞) + 1) (_root_.Metric.sphere (0 : E) 1) :=
      EuclideanSpace.instIsManifoldSphere.of_le le_top
    have h := metricRm04Standard_pullback (roundMetric (E := E) (n := n))
      (sphereDiffeo (n := n) e) x X Y Z W
    rwa [pullbackMetric_round_eq] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.metricRm04_round_invariant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.metricRm04_round_invariant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.metricRm04_round_invariant ``Submission.DifferentialGeometry.Geometry.metricRm04_round_invariant

omit [NeZero n] in
omit [FiniteDimensional ℝ E] in
theorem roundMetric_sec_value (x : _root_.Metric.sphere (0 : E) 1) (X Y : TangentSpace (𝓡 n) x) :
    metricRm04StandardAt (roundMetric (E := E) (n := n)) x X Y Y X
      = (roundMetric (E := E) (n := n)).inner x X X * (roundMetric (E := E) (n := n)).inner x Y Y
        - (roundMetric (E := E) (n := n)).inner x X Y * (roundMetric (E := E) (n := n)).inner x X
          Y := by
  have : IsManifold (𝓡 n) ∞ (_root_.Metric.sphere (0 : E) 1) :=
    EuclideanSpace.instIsManifoldSphere.of_le le_top
  obtain ⟨Xc, hXc, hXcx⟩ :=
    exists_contMDiffSection_eventuallyEq_tangentConstAt (I := 𝓡 n) x X
  obtain ⟨Yc, hYc, hYcx⟩ :=
    exists_contMDiffSection_eventuallyEq_tangentConstAt (I := 𝓡 n) x Y
  rw [metricRm04StandardAt_apply,
    show metricRm04At (roundMetric (E := E) (n := n)) x
        = riemannCurvature04At (roundMetric (E := E) (n := n))
            (metricCov (roundMetric (E := E) (n := n)))
            (metricCov_smooth (roundMetric (E := E) (n := n))) x from rfl,
    riemannCurvature04At_apply_const,
    show DifferentialGeometry.Geometry.Curvature.connectionRiemannCurvatureField (metricCov (roundMetric (E := E) (n := n)))
          (CovariantDerivative.tangentConstAt x X) (CovariantDerivative.tangentConstAt x Y)
          (CovariantDerivative.tangentConstAt x Y) x
        = DifferentialGeometry.Geometry.Curvature.connectionRiemannCurvatureField (metricCov (roundMetric (E := E) (n := n)))
            (⇑Xc) (⇑Yc) (⇑Yc) x from by
        exact connectionRiemannCurvatureField_eq_smooth_of_eventuallyEq_tangentConst
          (metricCov (roundMetric (E := E) (n := n)))
          (metricCov_smooth (roundMetric (E := E) (n := n))) X Y Y Xc Yc Yc hXc hYc hYc,
    roundMetric_inner, real_inner_comm,
    dIncl_curv_inner Yc Xc Yc x X
      (ambDeriv_section_mdiffAt Yc Yc x) (ambDeriv_section_mdiffAt Yc Xc x),
    hXcx, hYcx]
  simp only [roundInner_apply, roundMetric_inner,
    real_inner_comm (dIncl (n := n) x Y) (dIncl (n := n) x X)]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundMetric_sec_value then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundMetric_sec_value"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundMetric_sec_value ``Submission.DifferentialGeometry.Geometry.roundMetric_sec_value

omit [NeZero n]
  [FiniteDimensional ℝ E] in
theorem roundMetric_constPosSec :
    ∃ c : ℝ, 0 < c ∧ ∀ (x : _root_.Metric.sphere (0 : E) 1) (X Y : TangentSpace (𝓡 n) x),
      metricRm04StandardAt (roundMetric (E := E) (n := n)) x X Y Y X
        = c * ((roundMetric (E := E) (n := n)).inner x X X * (roundMetric (E := E) (n := n)).inner x
          Y Y
            - (roundMetric (E := E) (n := n)).inner x X Y * (roundMetric (E := E) (n := n)).inner x
              X Y) :=
  ⟨1, one_pos, fun x X Y => by rw [one_mul]; exact roundMetric_sec_value x X Y⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundMetric_constPosSec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundMetric_constPosSec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundMetric_constPosSec ``Submission.DifferentialGeometry.Geometry.roundMetric_constPosSec

private instance sphereModel_neZero :
    NeZero (_root_.Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
  rw [finrank_euclideanSpace_fin]
  infer_instance

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.sphereModel_neZero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.sphereModel_neZero target :: scope.openDecls } }

omit [NeZero n] [FiniteDimensional ℝ E] in
theorem round_riemann_one (x : _root_.Metric.sphere (0 : E) 1)
    (X Y Z : TangentSpace (𝓡 n) x) :
    riemannOp (LeviCivita (I := 𝓡 n) (roundMetric (E := E) (n := n))) x X Y Z =
      (roundMetric (E := E) (n := n)).inner x Y Z • X -
        (roundMetric (E := E) (n := n)).inner x X Z • Y := by
  by_cases hn : n = 0
  · subst n
    let : Subsingleton (TangentSpace (𝓡 0) x) := by
      change Subsingleton (EuclideanSpace ℝ (Fin 0))
      infer_instance
    have hX : X = 0 := Subsingleton.elim _ _
    have hY : Y = 0 := Subsingleton.elim _ _
    have hZ : Z = 0 := Subsingleton.elim _ _
    subst X
    subst Y
    subst Z
    simp
  · let : NeZero n := ⟨hn⟩
    have : IsManifold (𝓡 n) 1 (_root_.Metric.sphere (0 : E) 1) :=
      EuclideanSpace.instIsManifoldSphere.of_le le_top
    have : IsManifold (𝓡 n) 2 (_root_.Metric.sphere (0 : E) 1) :=
      EuclideanSpace.instIsManifoldSphere.of_le le_top
    have : IsManifold (𝓡 n) 3 (_root_.Metric.sphere (0 : E) 1) :=
      EuclideanSpace.instIsManifoldSphere.of_le le_top
    have : IsManifold (𝓡 n) ((∞ : WithTop ℕ∞) + 1) (_root_.Metric.sphere (0 : E) 1) :=
      EuclideanSpace.instIsManifoldSphere.of_le le_top
    have hRm :
        ∀ A B C D : TangentSpace (𝓡 n) x,
          metricRm04StandardAt (roundMetric (E := E) (n := n)) x A B C D =
            1 * ((roundMetric (E := E) (n := n)).inner x B C *
                (roundMetric (E := E) (n := n)).inner x A D -
              (roundMetric (E := E) (n := n)).inner x A C *
                (roundMetric (E := E) (n := n)).inner x B D) := by
      exact metricRm_of_sec (I := 𝓡 n)
        (M := _root_.Metric.sphere (0 : E) 1) (roundMetric (E := E) (n := n)) x 1
          (fun A B => by
            simpa only [one_mul] using roundMetric_sec_value (E := E) (n := n) x A B)
    simpa only [one_smul] using
      riemannOp_of_rm (I := 𝓡 n)
        (M := _root_.Metric.sphere (0 : E) 1) (roundMetric (E := E) (n := n)) x 1 hRm X Y Z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.round_riemann_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.round_riemann_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.round_riemann_one ``Submission.DifferentialGeometry.Geometry.round_riemann_one

omit [FiniteDimensional ℝ E] in
theorem roundMetric_ricciTensor
    (x : _root_.Metric.sphere (0 : E) 1) (v w : TangentSpace (𝓡 n) x) :
    ricciTensor (I := 𝓡 n) (roundMetric (E := E) (n := n)) x v w =
      ((n : ℝ) - 1) * (roundMetric (E := E) (n := n)).inner x v w := by
  have h := Curvature.ricci_of_op (I := 𝓡 n)
    (roundMetric (E := E) (n := n)) x 1
    (fun X Y Z => by
      simpa using round_riemann_one (E := E) (n := n) x X Y Z)
    v w
  simpa [finrank_euclideanSpace_fin] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundMetric_ricciTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundMetric_ricciTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundMetric_ricciTensor ``Submission.DifferentialGeometry.Geometry.roundMetric_ricciTensor

end Geometry
end DifferentialGeometry
