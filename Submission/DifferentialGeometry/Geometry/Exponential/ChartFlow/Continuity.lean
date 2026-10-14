import Submission.DifferentialGeometry.Geometry.Geodesic.Maximal.Uniqueness
import Submission.DifferentialGeometry.Geometry.Exponential.Defs
import Submission.DifferentialGeometry.Geometry.Exponential.Smoothness.AtZero.ZeroSectionConstancy
import Submission.DifferentialGeometry.Geometry.Exponential.LocalDiffeomorphism
import Submission.DifferentialGeometry.Geometry.Exponential.ChartFlow.Orbit.PreconnectedPropagation
import Submission.DifferentialGeometry.Geometry.Geodesic.Equation.Basic
import Submission.DifferentialGeometry.Geometry.Geodesic.Maximal.Interval
import Submission.DifferentialGeometry.Geometry.Geodesic.Flow.ChartPhase
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import Submission.DifferentialGeometry.Analysis.ODE.Flow.C1Regularity.ContDiffOnOne
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Compactness.Compact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section

open _root_.Set _root_.Filter _root_.Topology _root_.Metric
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space (TangentBundle I M)]

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic
open _root_.Submission.DifferentialGeometry.Integral.Measure

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalGeodesic_continuousAt_zero
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    ContinuousAt (maximalGeodesic (I := I) g p v) 0 := by
  classical
  obtain ⟨g_v, hg0, hg_int⟩ :=
    exists_isMIntegralCurveAt_geodesicVectorFieldChart (I := I) (g := g)
      (p := p) (v := v)
  have hlift_cont : ContinuousAt g_v 0 := hg_int.continuousAt
  have hπ_cont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hproj_cont : ContinuousAt (fun t => (g_v t).proj) 0 :=
    hπ_cont.continuousAt.comp hlift_cont
  obtain ⟨ε, hε, h_eq⟩ :=
    picardLift_proj_eq_maximalGeodesic_on_ball (I := I) (g := g) (p := p)
      (v := v) hg0 hg_int
  have h_eventually :
      maximalGeodesic (I := I) g p v =ᶠ[𝓝 (0 : ℝ)] fun t => (g_v t).proj := by
    have h_ball : Metric.ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) :=
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε)
    filter_upwards [h_ball] with t ht using h_eq t ht
  exact hproj_cont.congr h_eventually.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.maximalGeodesic_continuousAt_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.maximalGeodesic_continuousAt_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.maximalGeodesic_continuousAt_zero ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.maximalGeodesic_continuousAt_zero
omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless]
    [T2Space (TangentBundle I M)] in
lemma IsGeodesicOnWithInitial.continuousOn_base
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {J : Set ℝ}
    {p : M} {v : TangentSpace I p}
    (hγ : IsGeodesicOnWithInitial (I := I) g γ J p v) :
    ContinuousOn γ J := by
  obtain ⟨f, hproj, _hf0, hf⟩ := hγ
  have hf_cont : ContinuousOn f J := hf.continuousOn
  have hπ : Continuous (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hcomp : ContinuousOn (fun t => (f t).proj) J :=
    hπ.comp_continuousOn hf_cont
  exact hcomp.congr (fun t _ht => (hproj t).symm)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.IsGeodesicOnWithInitial
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.IsGeodesicOnWithInitial.continuousOn_base then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.IsGeodesicOnWithInitial.continuousOn_base"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.IsGeodesicOnWithInitial.continuousOn_base ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.IsGeodesicOnWithInitial.continuousOn_base

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
lemma maximalGeodesic_eqOn_lift_of_footInSource
    {g : SmoothRiemannianMetric I M} {p : M} {v : E}
    {f : ℝ → TangentBundle I M} {J : Set ℝ}
    (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J) (h0J : (0 : ℝ) ∈ J)
    (hf0 : f 0 = (⟨p, v⟩ : TangentBundle I M))
    (hf_on : IsMIntegralCurveOn f (geodesicVectorFieldChart (I := I) g p) J)
    (hsrc : ∀ s ∈ J, (f s).proj ∈ (chartAt H p).source) :
    Set.EqOn (maximalGeodesic (I := I) g p v) (fun t => (f t).proj) J := by
  exact maximalGeodesic_eqOn g hJ_open hJ_conn h0J
    ⟨f, fun _ => rfl, hf0,
      (isMIntegralCurveOn_geodesicVectorFieldChart_iff g p hsrc).mp hf_on⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.maximalGeodesic_eqOn_lift_of_footInSource then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.maximalGeodesic_eqOn_lift_of_footInSource"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.maximalGeodesic_eqOn_lift_of_footInSource ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.maximalGeodesic_eqOn_lift_of_footInSource

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
lemma maximalGeodesic_continuousOn_of_footInSource
    {g : SmoothRiemannianMetric I M} {p : M} {v : E}
    {f : ℝ → TangentBundle I M} {J : Set ℝ}
    (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J) (h0J : (0 : ℝ) ∈ J)
    (hf0 : f 0 = (⟨p, v⟩ : TangentBundle I M))
    (hf_on : IsMIntegralCurveOn f (geodesicVectorFieldChart (I := I) g p) J)
    (hsrc : ∀ s ∈ J, (f s).proj ∈ (chartAt H p).source) :
    ContinuousOn (maximalGeodesic (I := I) g p v) J := by
  have heq := maximalGeodesic_eqOn_lift_of_footInSource (I := I)
    hJ_open hJ_conn h0J hf0 hf_on hsrc
  have hf_cont : ContinuousOn f J := hf_on.continuousOn
  have hπ : Continuous (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hcomp : ContinuousOn (fun t => (f t).proj) J :=
    hπ.comp_continuousOn hf_cont
  exact hcomp.congr heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.maximalGeodesic_continuousOn_of_footInSource then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.maximalGeodesic_continuousOn_of_footInSource"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.maximalGeodesic_continuousOn_of_footInSource ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.maximalGeodesic_continuousOn_of_footInSource


end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
