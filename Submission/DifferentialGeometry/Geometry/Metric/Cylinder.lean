import Submission.DifferentialGeometry.Geometry.Metric.Product
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.Basic
import Mathlib.Geometry.Manifold.Riemannian.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private def lineMetric : SmoothRiemannianMetric 𝓘(ℝ) ℝ where
  inner := (riemannianMetricVectorSpace ℝ).inner
  symm := (riemannianMetricVectorSpace ℝ).symm
  pos := (riemannianMetricVectorSpace ℝ).pos
  isVonNBounded := (riemannianMetricVectorSpace ℝ).isVonNBounded
  contMDiff := (riemannianMetricVectorSpace ℝ).contMDiff.of_le le_top

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Metric.lineMetric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Metric.lineMetric target :: scope.openDecls } }

def cylinderMetric (g : SmoothRiemannianMetric I M) :
    SmoothRiemannianMetric (I.prod 𝓘(ℝ)) (M × ℝ) := g.prod lineMetric

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.cylinderMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.cylinderMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.cylinderMetric ``Submission.DifferentialGeometry.Geometry.Metric.cylinderMetric

@[simp] theorem cylinderMetric_inner (g : SmoothRiemannianMetric I M) (x : M × ℝ)
    (v w : TangentSpace (I.prod 𝓘(ℝ)) x) :
    (cylinderMetric g).inner x v w = g.inner x.1 v.1 w.1 + v.2 * w.2 := by
  rw [cylinderMetric, SmoothRiemannianMetric.prod_inner]
  change _ + w.2 * v.2 = _
  rw [mul_comm w.2 v.2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.cylinderMetric_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.cylinderMetric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.cylinderMetric_inner ``Submission.DifferentialGeometry.Geometry.Metric.cylinderMetric_inner

def cylinderAxis (x : M × ℝ) : TangentSpace (I.prod 𝓘(ℝ)) x := (0, 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.cylinderAxis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.cylinderAxis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.cylinderAxis ``Submission.DifferentialGeometry.Geometry.Metric.cylinderAxis

omit [FiniteDimensional ℝ E] [T2Space M] in
theorem contMDiff_cylinderAxis :
    ContMDiff (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)).tangent ∞
      (fun x : M × ℝ ↦ (⟨x, cylinderAxis x⟩ : TangentBundle (I.prod 𝓘(ℝ)) (M × ℝ))) := by
  have h0 : ContMDiff I I.tangent ∞
      (fun x : M ↦ (⟨x, 0⟩ : TangentBundle I M)) := _root_.Bundle.contMDiff_zeroSection ℝ (TangentSpace I)
  have h1 : ContMDiff 𝓘(ℝ) 𝓘(ℝ).tangent ∞
      (fun t : ℝ ↦ (⟨t, 1⟩ : TangentBundle 𝓘(ℝ) ℝ)) := by
    intro t
    rw [_root_.Bundle.contMDiffAt_section]
    convert (contMDiffAt_const (I := 𝓘(ℝ)) (I' := 𝓘(ℝ)) (c := (1 : ℝ)) (x := t)) using 1
    funext s
    simp only [TangentBundle.trivializationAt_apply, mfld_simps]
    change (fderivWithin ℝ id Set.univ s) (1 : ℝ) = 1
    rw [fderivWithin_id uniqueDiffWithinAt_univ]
    rfl
  exact (contMDiff_equivTangentBundleProd_symm (I := I) (I' := 𝓘(ℝ))
    (M := M) (M' := ℝ)).comp (h0.prodMap h1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.contMDiff_cylinderAxis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.contMDiff_cylinderAxis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.contMDiff_cylinderAxis ``Submission.DifferentialGeometry.Geometry.Metric.contMDiff_cylinderAxis

theorem cylinderMetric_axis_inner (g : SmoothRiemannianMetric I M) (x : M × ℝ)
    (v : TangentSpace (I.prod 𝓘(ℝ)) x) :
    (cylinderMetric g).inner x (cylinderAxis x) v =
      mvfderiv (I.prod 𝓘(ℝ)) Prod.snd x v := by
  rw [cylinderMetric_inner]
  have hz : g.inner x.1 (0 : TangentSpace I x.1) v.1 = 0 := by
    rw [map_zero (g.inner x.1)]
    rfl
  change g.inner x.1 (0 : TangentSpace I x.1) v.1 + (1 : ℝ) * v.2 = _
  calc
    _ = v.2 := by rw [hz]; ring
    _ = mvfderiv (I.prod 𝓘(ℝ)) Prod.snd x v := by
      change v.2 = (show ℝ from mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ) Prod.snd x v)
      rw [mfderiv_snd]
      rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.cylinderMetric_axis_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.cylinderMetric_axis_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.cylinderMetric_axis_inner ``Submission.DifferentialGeometry.Geometry.Metric.cylinderMetric_axis_inner

theorem cylinderMetric_axis_unit (g : SmoothRiemannianMetric I M) (x : M × ℝ) :
    (cylinderMetric g).inner x (cylinderAxis x) (cylinderAxis x) = 1 := by
  rw [cylinderMetric_inner]
  change g.inner x.1 (0 : TangentSpace I x.1) 0 + (1 : ℝ) * 1 = 1
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.cylinderMetric_axis_unit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.cylinderMetric_axis_unit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.cylinderMetric_axis_unit ``Submission.DifferentialGeometry.Geometry.Metric.cylinderMetric_axis_unit

theorem gradFun_height_eq_cylinderAxis (g : SmoothRiemannianMetric I M) (x : M × ℝ) :
    gradFun (cylinderMetric g) Prod.snd x = cylinderAxis x := by
  let m := cylinderMetric g
  let z := gradFun m Prod.snd x - cylinderAxis x
  have htest (v : TangentSpace (I.prod 𝓘(ℝ)) x) :
      m.inner x (gradFun m Prod.snd x) v - m.inner x (cylinderAxis x) v = 0 := by
    rw [inner_gradFun, cylinderMetric_axis_inner]
    change mvfderiv (I.prod 𝓘(ℝ)) Prod.snd x v - mvfderiv (I.prod 𝓘(ℝ)) Prod.snd x v = 0
    exact sub_self _
  have hz : m.inner x z z = 0 := by
    change m.inner x (gradFun m Prod.snd x - cylinderAxis x) z = 0
    rw [map_sub (m.inner x), sub_apply]
    exact htest z
  have he : z = 0 := by
    by_contra hn
    exact (ne_of_gt (m.pos x z hn)) hz
  exact sub_eq_zero.mp he

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.gradFun_height_eq_cylinderAxis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.gradFun_height_eq_cylinderAxis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.gradFun_height_eq_cylinderAxis ``Submission.DifferentialGeometry.Geometry.Metric.gradFun_height_eq_cylinderAxis

end DifferentialGeometry.Geometry.Metric
