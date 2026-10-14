import Submission.DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.MetricFamilySmoothOn
import Submission.DifferentialGeometry.Geometry.Geodesic.Chart.OpenSubtype
import Submission.DifferentialGeometry.Topology.Manifold.OpenEuclideanChart

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem chartChristoffelContraction_contDiffOn
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g)
    (α : M) {s : Set X} {t : X → ℝ} {x v w : X → E}
    (ht : ContDiffOn ℝ ∞ t s) (hx : ContDiffOn ℝ ∞ x s)
    (hv : ContDiffOn ℝ ∞ v s) (hw : ContDiffOn ℝ ∞ w s)
    (htD : _root_.Set.MapsTo t s D.regular)
    (hxα : _root_.Set.MapsTo x s (interior (extChartAt I α).target)) :
    ContDiffOn ℝ ∞
      (fun p => chartChristoffelContraction (g (t p)) α (v p) (w p) (x p)) s := by
  classical
  unfold chartChristoffelContraction
  refine ContDiffOn.sum fun k _ => ContDiffOn.smul ?_ contDiffOn_const
  refine ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => ?_
  have hΓ := (chartChristoffelOnE_contDiffOn hg Subset.rfl D.regular_isOpen.uniqueDiffOn α i j k).comp
    (ht.prodMk hx) (fun p hp => ⟨htD hp, hxα hp⟩)
  have hvi : ContDiffOn ℝ ∞ (fun p => chartCoord (E := E) i (v p)) s :=
    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord i).toContinuousLinearMap.contDiff.comp_contDiffOn hv
  have hwj : ContDiffOn ℝ ∞ (fun p => chartCoord (E := E) j (w p)) s :=
    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord j).toContinuousLinearMap.contDiff.comp_contDiffOn hw
  exact (hΓ.mul hvi).mul hwj

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartChristoffelContraction_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartChristoffelContraction_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartChristoffelContraction_contDiffOn ``Submission.DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartChristoffelContraction_contDiffOn

theorem chartChristoffelContraction_euclidean_contDiffOn
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) E}
    (hg : MetricFamilySmoothOn D g)
    {s : Set X} {t : X → ℝ} {x v w : X → E}
    (ht : ContDiffOn ℝ ∞ t s) (hx : ContDiffOn ℝ ∞ x s)
    (hv : ContDiffOn ℝ ∞ v s) (hw : ContDiffOn ℝ ∞ w s)
    (htD : _root_.Set.MapsTo t s D.regular) :
    ContDiffOn ℝ ∞
      (fun p => chartChristoffelContraction (g (t p)) (x p) (v p) (w p) (x p)) s := by
  exact chartChristoffelContraction_contDiffOn hg (0 : E) ht hx hv hw htD
    (by intro p hp; simp [chartAt_self_eq])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartChristoffelContraction_euclidean_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartChristoffelContraction_euclidean_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartChristoffelContraction_euclidean_contDiffOn ``Submission.DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartChristoffelContraction_euclidean_contDiffOn

theorem chartChristoffelContraction_euclidean_joint_contDiffOn
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) E}
    (hg : MetricFamilySmoothOn D g)
    {J : Set ℝ} (hJ : J ⊆ D.regular) (V : Set E) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × E × E => chartChristoffelContraction (g p.1) p.2.1 p.2.2 p.2.2 p.2.1)
      (J ×ˢ V ×ˢ (Set.univ : Set E)) := by
  apply chartChristoffelContraction_euclidean_contDiffOn hg
  · fun_prop
  · fun_prop
  · fun_prop
  · fun_prop
  · intro p hp
    exact hJ hp.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartChristoffelContraction_euclidean_joint_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartChristoffelContraction_euclidean_joint_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartChristoffelContraction_euclidean_joint_contDiffOn ``Submission.DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartChristoffelContraction_euclidean_joint_contDiffOn

theorem chartChristoffelContraction_opens_contDiffOn
    {U : TopologicalSpace.Opens E} {D : RealTimeInterval}
    {g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) U}
    (hg : MetricFamilySmoothOn D g) (α : U)
    {s : Set X} {t : X → ℝ} {x v w : X → E}
    (ht : ContDiffOn ℝ ∞ t s) (hx : ContDiffOn ℝ ∞ x s)
    (hv : ContDiffOn ℝ ∞ v s) (hw : ContDiffOn ℝ ∞ w s)
    (htD : _root_.Set.MapsTo t s D.regular) (hxU : _root_.Set.MapsTo x s U) :
    ContDiffOn ℝ ∞
      (fun p => chartChristoffelContraction (g (t p)) α (v p) (w p) (x p)) s := by
  apply chartChristoffelContraction_contDiffOn hg α ht hx hv hw htD
  rwa [interior_extChartAt_opens_target]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartChristoffelContraction_opens_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartChristoffelContraction_opens_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartChristoffelContraction_opens_contDiffOn ``Submission.DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartChristoffelContraction_opens_contDiffOn

theorem chartChristoffelContraction_opens_joint_contDiffOn
    {U : TopologicalSpace.Opens E} {D : RealTimeInterval}
    {g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) U}
    (hg : MetricFamilySmoothOn D g) (α : U)
    {J : Set ℝ} (hJ : J ⊆ D.regular) {V : Set E} (hV : V ⊆ U) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × E × E => chartChristoffelContraction (g p.1) α p.2.2 p.2.2 p.2.1)
      (J ×ˢ V ×ˢ (Set.univ : Set E)) := by
  apply chartChristoffelContraction_opens_contDiffOn hg α
  · fun_prop
  · fun_prop
  · fun_prop
  · fun_prop
  · intro p hp
    exact hJ hp.1
  · intro p hp
    exact hV hp.2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartChristoffelContraction_opens_joint_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartChristoffelContraction_opens_joint_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartChristoffelContraction_opens_joint_contDiffOn ``Submission.DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartChristoffelContraction_opens_joint_contDiffOn

end DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn
