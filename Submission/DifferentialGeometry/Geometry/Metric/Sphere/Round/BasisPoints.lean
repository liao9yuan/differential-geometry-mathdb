import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.NormDiamond
import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Metric
open scoped _root_.ENNReal _root_.Manifold

namespace DifferentialGeometry
namespace Geometry

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
variable {n : ℕ} [Fact (Module.finrank ℝ A = n + 1)]

@[reducible] noncomputable def roundBundle :
    _root_.Bundle.RiemannianBundle
      (fun x : _root_.Metric.sphere (0 : A) 1 => TangentSpace (𝓡 n) x) :=
  ⟨(roundMetric (E := A) (n := n)).toRiemannianMetric⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundBundle ``Submission.DifferentialGeometry.Geometry.roundBundle

private instance sphereModel_neZero [NeZero n] :
    NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
  rw [finrank_euclideanSpace_fin]
  infer_instance

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.sphereModel_neZero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.sphereModel_neZero target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem round_enorm :
    letI : _root_.Bundle.RiemannianBundle
        (fun x : _root_.Metric.sphere (0 : A) 1 => TangentSpace (𝓡 n) x) :=
      roundBundle (A := A) (n := n)
    ∀ (x : _root_.Metric.sphere (0 : A) 1) (w : TangentSpace (𝓡 n) x),
      ‖w‖ₑ = ENNReal.ofReal
        (Real.sqrt ((roundMetric (E := A) (n := n)).inner x w w)) := by
  let : _root_.Bundle.RiemannianBundle
      (fun x : _root_.Metric.sphere (0 : A) 1 => TangentSpace (𝓡 n) x) :=
    roundBundle (A := A) (n := n)
  intro x w
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.round_enorm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.round_enorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.round_enorm ``Submission.DifferentialGeometry.Geometry.round_enorm

def sphereBasisPt {m : ℕ} (i : Fin m) :
    sphere (0 : EuclideanSpace ℝ (Fin m)) 1 :=
  ⟨EuclideanSpace.single i 1, by
    rw [mem_sphere_zero_iff_norm, PiLp.norm_single]
    norm_num⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.sphereBasisPt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.sphereBasisPt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.sphereBasisPt ``Submission.DifferentialGeometry.Geometry.sphereBasisPt

theorem sphereBasisPt_ne {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    sphereBasisPt i ≠ sphereBasisPt j := by
  intro h
  have h' := congrArg
    (fun z : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      (z : EuclideanSpace ℝ (Fin m)) i) h
  simp [sphereBasisPt, hij] at h'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.sphereBasisPt_ne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.sphereBasisPt_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.sphereBasisPt_ne ``Submission.DifferentialGeometry.Geometry.sphereBasisPt_ne

theorem sphereBasisPt_ne_neg {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    sphereBasisPt j ≠ -sphereBasisPt i := by
  intro h
  have h' := congrArg
    (fun z : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      (z : EuclideanSpace ℝ (Fin m)) j) h
  simp [sphereBasisPt, hij] at h'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.sphereBasisPt_ne_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.sphereBasisPt_ne_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.sphereBasisPt_ne_neg ``Submission.DifferentialGeometry.Geometry.sphereBasisPt_ne_neg

theorem sphere3_basis :
    ∃ p q : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
      p ≠ q ∧ q ≠ -p := by
  refine ⟨sphereBasisPt 0, sphereBasisPt 1, ?_, ?_⟩
  · exact sphereBasisPt_ne (by decide)
  · exact sphereBasisPt_ne_neg (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.sphere3_basis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.sphere3_basis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.sphere3_basis ``Submission.DifferentialGeometry.Geometry.sphere3_basis

end Geometry
end DifferentialGeometry
