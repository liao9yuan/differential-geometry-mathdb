import Mathlib.Geometry.Manifold.Instances.Real
import Submission.DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature
import Submission.DifferentialGeometry.Geometry.Curvature.OperatorNaturality

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Manifold _root_.TopologicalSpace _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Geometry.Riemannian _root_.Submission.DifferentialGeometry.Topology.Manifold
open scoped _root_.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology
namespace DifferentialGeometry.Geometry.Curvature
private abbrev SectionE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.SectionE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.SectionE3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instNeZeroNatFinrankRealSectionE3 : NeZero (Module.finrank ℝ SectionE3) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instNeZeroNatFinrankRealSectionE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instNeZeroNatFinrankRealSectionE3 target :: scope.openDecls } }
variable {S T : Type*} [TopologicalSpace S] [ChartedSpace SectionE3 S] [IsManifold (𝓡 3) ∞ S] [T2Space S]
  [TopologicalSpace T] [ChartedSpace SectionE3 T] [IsManifold (𝓡 3) ∞ T] [T2Space T]
  [SigmaCompactSpace S]

theorem riemann_of_injective_local_isometry
    (g : SmoothRiemannianMetric (𝓡 3) S) (h : SmoothRiemannianMetric (𝓡 3) T)
    (f : S → T) (hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ f) (hinj : _root_.Function.Injective f)
    (hmetric : ∀ (x : S) (v w : TangentSpace (𝓡 3) x),
      g.inner x v w = h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w))
    (x : S) (v w z u : TangentSpace (𝓡 3) x) :
    metricRm04StandardAt g x v w z u = metricRm04StandardAt h (f x)
      (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w)
      (mfderiv (𝓡 3) (𝓡 3) f x z) (mfderiv (𝓡 3) (𝓡 3) f x u) := by
  let D := diffeomorphOntoImage f hf hinj
  have hrange : _root_.Set.range D = univ := D.surjective.range_eq
  let : SigmaCompactSpace hf.image := isSigmaCompact_univ_iff.mp
    (hrange ▸ isSigmaCompact_range D.continuous)
  have hpoint : (Subtype.val : hf.image → T) ∘ D = f := funext (diffeomorphOntoImage_apply f hf hinj)
  have hd : mfderiv (𝓡 3) (𝓡 3) D x = mfderiv (𝓡 3) (𝓡 3) f x := by
    have hc := mfderiv_comp x
      ((contMDiff_subtype_val (I := 𝓡 3) (U := hf.image) (n := ∞)).mdifferentiable (by simp) (D x))
      (D.contMDiff.mdifferentiable (by simp) x)
    rw [mfderiv_subtype_val] at hc
    exact hc.symm.trans (mfderiv_congr hpoint)
  have hg : g = pullbackMetricOfInjectiveLocalDiffeomorph h f hf hinj := by
    apply SmoothRiemannianMetric.ext_inner
    intro y a b
    rw [pullbackMetricOfInjectiveLocalDiffeomorph_inner]
    exact hmetric y a b
  have he := metricRm04Standard_pullbackCross (h.restrictOpen hf.image) D x v w z u
  have hr := metricRm04StandardAt_restrictOpen h hf.image (D x)
    (mfderiv (𝓡 3) (𝓡 3) D x v) (mfderiv (𝓡 3) (𝓡 3) D x w)
    (mfderiv (𝓡 3) (𝓡 3) D x z) (mfderiv (𝓡 3) (𝓡 3) D x u)
  rw [hg]
  change metricRm04StandardAt (Diffeomorph.pullbackMetricCross (h.restrictOpen hf.image) D) x v w z u = _
  simp only [mfderiv_subtype_val_apply] at hr
  have ht := he.trans hr
  have hDx : (D x : T) = f x := diffeomorphOntoImage_apply f hf hinj x
  dsimp only [TangentSpace] at hd
  erw [hd, hDx] at ht
  exact ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.riemann_of_injective_local_isometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.riemann_of_injective_local_isometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.riemann_of_injective_local_isometry ``Submission.DifferentialGeometry.Geometry.Curvature.riemann_of_injective_local_isometry

theorem sectional_of_injective_local_isometry
    (g : SmoothRiemannianMetric (𝓡 3) S) (h : SmoothRiemannianMetric (𝓡 3) T)
    (f : S → T) (hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ f) (hinj : _root_.Function.Injective f)
    (hmetric : ∀ (x : S) (v w : TangentSpace (𝓡 3) x),
      g.inner x v w = h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w))
    (x : S) (v w : TangentSpace (𝓡 3) x) :
    sectionalCurvature g x v w = sectionalCurvature h (f x)
      (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) := by
  rw [sectionalCurvature_eq_metricRm04StandardAt_div, sectionalCurvature_eq_metricRm04StandardAt_div,
    riemann_of_injective_local_isometry g h f hf hinj hmetric x v w w v,
    hmetric x v v, hmetric x w w, hmetric x v w]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.sectional_of_injective_local_isometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.sectional_of_injective_local_isometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.sectional_of_injective_local_isometry ``Submission.DifferentialGeometry.Geometry.Curvature.sectional_of_injective_local_isometry
end DifferentialGeometry.Geometry.Curvature
