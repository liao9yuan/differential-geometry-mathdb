import Submission.DifferentialGeometry.Geometry.Geodesic.Local
import Submission.DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem isGeodesicAt_zero_of_equation
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {U : Set ℝ}
    (hU : U ∈ 𝓝 (0 : ℝ)) (hgeo : IsGeodesicOn (I := I) g γ U)
    (hcont : ContinuousOn γ U) : IsGeodesicAt (I := I) g γ 0 := by
  obtain ⟨η, f, hfzero, hηf, hηzero, hf, hη⟩ :=
    exists_geodesic_with_initial_velocity_at g (γ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 1)
  have hvel : (mfderiv 𝓘(ℝ, ℝ) I η 0 1 : E) = mfderiv 𝓘(ℝ, ℝ) I γ 0 1 := by
    have hh := hf.mfderiv_proj_one (by rw [hfzero]; exact mem_chart_source H (γ 0))
    rw [hηf]
    exact hh.trans (congrArg (fun z : TangentBundle I M ↦ (z.snd : E)) hfzero)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (_root_.Filter.inter_mem hU (eventually_isGeodesicAt hη))
  have heq := geo_eqOn_of_initial g Metric.isOpen_ball (convex_ball (0 : ℝ) ε).isPreconnected
    (Metric.mem_ball_self hε)
    (fun s hs ↦ (hball hs).2.hasGeodesicEquationAt)
    (fun s hs ↦ hgeo s (hball hs).1)
    (fun s hs ↦ (hball hs).2.continuousAt.continuousWithinAt)
    (hcont.mono fun _ hs ↦ (hball hs).1) hηzero hvel
  exact isGeodesicAt_congr hη
    (_root_.Filter.eventually_of_mem (Metric.ball_mem_nhds 0 hε) fun s hs ↦ (heq hs).symm)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.isGeodesicAt_zero_of_equation
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.isGeodesicAt_zero_of_equation target :: scope.openDecls } }

theorem isGeodesicAt_of_isGeodesicOn
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {U : Set ℝ} {t : ℝ}
    (hU : U ∈ 𝓝 t) (hgeo : IsGeodesicOn (I := I) g γ U)
    (hcont : ContinuousOn γ U) : IsGeodesicAt (I := I) g γ t := by
  let V : Set ℝ := {s | s + t ∈ U}
  have hV : V ∈ 𝓝 (0 : ℝ) := by
    have hc : _root_.Filter.Tendsto (fun s : ℝ ↦ s + t) (𝓝 0) (𝓝 t) := by
      simpa only [zero_add] using (continuous_add_const t).tendsto 0
    exact hc hU
  have hshift : IsGeodesicOn (I := I) g (fun s ↦ γ (s + t)) V := by
    simpa only [one_mul] using isGeodesicOn_comp_affine (c := 1) (d := t) hgeo
  have hshiftcont : ContinuousOn (fun s ↦ γ (s + t)) V :=
    hcont.comp (continuous_add_const t).continuousOn (fun _ hs ↦ hs)
  have hh := isGeodesicAt_zero_of_equation g hV hshift hshiftcont
  simpa only [zero_sub, neg_neg, neg_add_cancel_right] using isGeodesicAt_comp_add hh (-t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.isGeodesicAt_of_isGeodesicOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.isGeodesicAt_of_isGeodesicOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.isGeodesicAt_of_isGeodesicOn ``Submission.DifferentialGeometry.Geometry.isGeodesicAt_of_isGeodesicOn

end DifferentialGeometry.Geometry
