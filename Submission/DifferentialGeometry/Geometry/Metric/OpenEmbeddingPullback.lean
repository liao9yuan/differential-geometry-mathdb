import Submission.DifferentialGeometry.Geometry.Metric.Construction.Immersion
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Submission.DifferentialGeometry.Topology.Manifold.OpenEmbedding
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Cross
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.OpenSubtype
import Submission.DifferentialGeometry.Geometry.Metric.Scaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Function _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Topology.Manifold
open scoped _root_.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry.Metric

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]

def pullbackMetricOfInjectiveLocalDiffeomorph
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hinj : _root_.Function.Injective f) :
    SmoothRiemannianMetric I M :=
  Diffeomorph.pullbackMetricCross (g.restrictOpen hf.image)
    (diffeomorphOntoImage f hf hinj)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.pullbackMetricOfInjectiveLocalDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.pullbackMetricOfInjectiveLocalDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.pullbackMetricOfInjectiveLocalDiffeomorph ``Submission.DifferentialGeometry.Geometry.Metric.pullbackMetricOfInjectiveLocalDiffeomorph

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M]
  [T2Space M] [IsManifold J ∞ N] [T2Space N] in
private theorem mfderiv_chart_eq_of_ambient_eq
    (V : TopologicalSpace.Opens N) (Φ : M ≃ₘ⟮I, J⟯ V) (f : M → N)
    (he : ∀ x, (Φ x : N) = f x) (x : M) :
    mfderiv I J Φ x = mfderiv I J f x := by
  have hcomp : (Subtype.val : V → N) ∘ Φ = f := funext he
  rw [← hcomp, mfderiv_comp x
    (contMDiff_subtype_val.mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0))
    (Φ.contMDiff.mdifferentiableAt (by decide)), mfderiv_subtype_val]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Metric.mfderiv_chart_eq_of_ambient_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Metric.mfderiv_chart_eq_of_ambient_eq target :: scope.openDecls } }

theorem pullbackMetricOfInjectiveLocalDiffeomorph_inner
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hinj : _root_.Function.Injective f)
    (x : M) (v w : TangentSpace I x) :
    (pullbackMetricOfInjectiveLocalDiffeomorph g f hf hinj).inner x v w =
      g.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) := by
  unfold pullbackMetricOfInjectiveLocalDiffeomorph
  rw [Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.restrictOpen_inner,
    mfderiv_chart_eq_of_ambient_eq hf.image (diffeomorphOntoImage f hf hinj) f
      (diffeomorphOntoImage_apply f hf hinj) x]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.pullbackMetricOfInjectiveLocalDiffeomorph_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.pullbackMetricOfInjectiveLocalDiffeomorph_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.pullbackMetricOfInjectiveLocalDiffeomorph_inner ``Submission.DifferentialGeometry.Geometry.Metric.pullbackMetricOfInjectiveLocalDiffeomorph_inner

theorem pullbackMetricOfInjectiveLocalDiffeomorph_eq_chart
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hinj : _root_.Function.Injective f)
    (V : TopologicalSpace.Opens N) (Φ : M ≃ₘ⟮I, J⟯ V)
    (he : ∀ x, (Φ x : N) = f x) :
    pullbackMetricOfInjectiveLocalDiffeomorph g f hf hinj =
      Diffeomorph.pullbackMetricCross (g.restrictOpen V) Φ := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [pullbackMetricOfInjectiveLocalDiffeomorph_inner,
    Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.restrictOpen_inner,
    mfderiv_chart_eq_of_ambient_eq V Φ f he x, he x]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.pullbackMetricOfInjectiveLocalDiffeomorph_eq_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.pullbackMetricOfInjectiveLocalDiffeomorph_eq_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.pullbackMetricOfInjectiveLocalDiffeomorph_eq_chart ``Submission.DifferentialGeometry.Geometry.Metric.pullbackMetricOfInjectiveLocalDiffeomorph_eq_chart

theorem pullbackMetricOfInjectiveLocalDiffeomorph_scale_eq_chart
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hinj : _root_.Function.Injective f)
    (c : ℝ) (hc : 0 < c)
    (V : TopologicalSpace.Opens N) (Φ : M ≃ₘ⟮I, J⟯ V)
    (he : ∀ x, (Φ x : N) = f x) :
    pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric c hc g) f hf hinj =
      Diffeomorph.pullbackMetricCross (scaleMetric c hc (g.restrictOpen V)) Φ := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [pullbackMetricOfInjectiveLocalDiffeomorph_inner,
    Diffeomorph.pullbackMetricCross_inner, scaleMetric_inner, scaleMetric_inner,
    SmoothRiemannianMetric.restrictOpen_inner,
    mfderiv_chart_eq_of_ambient_eq V Φ f he x, he x]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.pullbackMetricOfInjectiveLocalDiffeomorph_scale_eq_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.pullbackMetricOfInjectiveLocalDiffeomorph_scale_eq_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.pullbackMetricOfInjectiveLocalDiffeomorph_scale_eq_chart ``Submission.DifferentialGeometry.Geometry.Metric.pullbackMetricOfInjectiveLocalDiffeomorph_scale_eq_chart

end DifferentialGeometry.Geometry.Metric

open _root_.Manifold _root_.Submission.DifferentialGeometry.Manifold

namespace DifferentialGeometry.Geometry.Metric

open _root_.Submission.DifferentialGeometry.Topology.Manifold
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]

theorem pullbackMetricCross_eq_immersionInducedMetric_of_coe_eq
    (g : SmoothRiemannianMetric J N) {f : M → N} (hf : _root_.Manifold.IsImmersion I J ∞ f)
    (V : TopologicalSpace.Opens N) (Φ : M ≃ₘ⟮I, J⟯ V)
    (he : ∀ x, (Φ x : N) = f x) :
    Diffeomorph.pullbackMetricCross (g.restrictOpen V) Φ = immersionInducedMetric g hf := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have hcomp : (fun y => (Φ y : N)) = f := funext he
  have hd : mfderiv I J Φ x = mfderiv I J f x := by
    rw [← hcomp]
    exact (DifferentialGeometry.mfderiv_subtypeVal_comp Φ x).symm
  rw [Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.restrictOpen_inner,
    immersionInducedMetric_inner, hd, he x]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.pullbackMetricCross_eq_immersionInducedMetric_of_coe_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.pullbackMetricCross_eq_immersionInducedMetric_of_coe_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.pullbackMetricCross_eq_immersionInducedMetric_of_coe_eq ``Submission.DifferentialGeometry.Geometry.Metric.pullbackMetricCross_eq_immersionInducedMetric_of_coe_eq

theorem pullbackMetricCross_diffeomorphOntoImage_eq_immersionInducedMetric
    (g : SmoothRiemannianMetric J N) {f : M → N} (hf : _root_.Manifold.IsImmersion I J ∞ f)
    (hlocal : IsLocalDiffeomorph I J ∞ f) (hinj : Function.Injective f) :
    Diffeomorph.pullbackMetricCross (g.restrictOpen hlocal.image)
      (diffeomorphOntoImage f hlocal hinj) = immersionInducedMetric g hf :=
  pullbackMetricCross_eq_immersionInducedMetric_of_coe_eq g hf hlocal.image
    (diffeomorphOntoImage f hlocal hinj) (diffeomorphOntoImage_apply f hlocal hinj)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.pullbackMetricCross_diffeomorphOntoImage_eq_immersionInducedMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.pullbackMetricCross_diffeomorphOntoImage_eq_immersionInducedMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.pullbackMetricCross_diffeomorphOntoImage_eq_immersionInducedMetric ``Submission.DifferentialGeometry.Geometry.Metric.pullbackMetricCross_diffeomorphOntoImage_eq_immersionInducedMetric

theorem exists_diffeomorph_onto_range_pullback_eq_immersionInducedMetric
    [J.Boundaryless] (g : SmoothRiemannianMetric J N)
    {f : M → N} (hf : _root_.Manifold.IsImmersion I J ∞ f) (hinj : Function.Injective f)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    ∃ (V : TopologicalSpace.Opens N) (Φ : M ≃ₘ⟮I, J⟯ V),
      (V : Set N) = Set.range f ∧ (∀ x, (Φ x : N) = f x) ∧
        (∀ y : V, f (Φ.symm y) = (y : N)) ∧
        Diffeomorph.pullbackMetricCross (g.restrictOpen V) Φ =
          immersionInducedMetric g hf := by
  obtain ⟨V, Φ, hV, he, hi⟩ := exists_diffeomorph_onto_range_of_injective_immersion f
    hf.contMDiff hinj
    (fun x => immersionAt_mfderiv_injective (hf.isImmersionAt x)) hdim
  exact ⟨V, Φ, hV, he, hi, pullbackMetricCross_eq_immersionInducedMetric_of_coe_eq g
    hf V Φ he⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.exists_diffeomorph_onto_range_pullback_eq_immersionInducedMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.exists_diffeomorph_onto_range_pullback_eq_immersionInducedMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.exists_diffeomorph_onto_range_pullback_eq_immersionInducedMetric ``Submission.DifferentialGeometry.Geometry.Metric.exists_diffeomorph_onto_range_pullback_eq_immersionInducedMetric

end DifferentialGeometry.Geometry.Metric
