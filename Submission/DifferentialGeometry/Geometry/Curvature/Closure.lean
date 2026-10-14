import Submission.DifferentialGeometry.Geometry.Curvature.Naturality.OpenRestriction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.Continuity
import Submission.DifferentialGeometry.Bundle.Section

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.TopologicalSpace _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Geometry.Curvature
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

theorem metricRm04StdAt_eq_of_eqOn_closure
    (g h : SmoothRiemannianMetric I M) (U : _root_.TopologicalSpace.Opens M) [SigmaCompactSpace U]
    (heq : ∀ y : M, y ∈ U → ∀ v w : TangentSpace I y, g.inner y v w = h.inner y v w)
    (x : M) (hx : x ∈ closure (U : Set M)) (u v w z : TangentSpace I x) :
    metricRm04StandardAt g x u v w z = metricRm04StandardAt h x u v w z := by
  classical
  have hres : g.restrictOpen U = h.restrictOpen U := restrictOpen_eq_of_eqOn g h U heq
  have hlocal (y : U) (a b c d : TangentSpace I y) :
      metricRm04StandardAt g y.val a b c d = metricRm04StandardAt h y.val a b c d := by
    have hg := metricRm04StandardAt_restrictOpen g U y a b c d
    have hh := metricRm04StandardAt_restrictOpen h U y a b c d
    simp only [mfderiv_subtype_val] at hg hh
    exact hg.symm.trans ((congrArg (fun k : SmoothRiemannianMetric I U =>
      metricRm04StandardAt k y a b c d) hres).trans hh)
  let slots : Fin 4 → TangentSpace I x := vec4 u v w z
  let V : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    fun i => (ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x (slots i)).choose
  have hV : ∀ i, V i x = slots i := fun i =>
    (ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x (slots i)).choose_spec
  have hc (k : SmoothRiemannianMetric I M) :
      Continuous (fun y : M => metricRm04 k y (fun i => V i y)) := by
    have hd : ContMDiff I 𝓘(ℝ) ∞ (fun y : M => metricRm04 k y (fun i => V i y)) :=
      fun y => tensor0SField_eval_smooth_slots_contMDiffAt (metricRm04 k) V y
    exact hd.continuous
  have hvals : _root_.Set.EqOn (fun y : M => metricRm04 g y (fun i => V i y))
      (fun y : M => metricRm04 h y (fun i => V i y)) U := by
    intro y hy
    have hs : (fun i : Fin 4 => V i y) = vec4 (V 0 y) (V 1 y) (V 2 y) (V 3 y) := by
      funext i
      fin_cases i <;> rfl
    change metricRm04 g y (fun i => V i y) = metricRm04 h y (fun i => V i y)
    rw [hs, metricRm04_apply, metricRm04_apply]
    exact hlocal ⟨y, hy⟩ (V 0 y) (V 1 y) (V 2 y) (V 3 y)
  have hat := hvals.closure (hc g) (hc h) hx
  simpa only [metricRm04_apply, hV, slots, metricRm04StandardAt_apply] using hat

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricRm04StdAt_eq_of_eqOn_closure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricRm04StdAt_eq_of_eqOn_closure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricRm04StdAt_eq_of_eqOn_closure ``Submission.DifferentialGeometry.Geometry.Curvature.metricRm04StdAt_eq_of_eqOn_closure

theorem metricScalarAt_eq_of_eqOn_closure [I.Boundaryless]
    (g h : SmoothRiemannianMetric I M) (U : _root_.TopologicalSpace.Opens M) [SigmaCompactSpace U]
    (heq : ∀ y : M, y ∈ U → ∀ v w : TangentSpace I y, g.inner y v w = h.inner y v w)
    (x : M) (hx : x ∈ closure (U : Set M)) :
    metricScalarAt g x = metricScalarAt h x := by
  have hres : g.restrictOpen U = h.restrictOpen U := restrictOpen_eq_of_eqOn g h U heq
  have hvals : _root_.Set.EqOn (metricScalarAt g) (metricScalarAt h) U := by
    intro y hy
    rw [← metricScalarAt_restrictOpen g U ⟨y, hy⟩,
      ← metricScalarAt_restrictOpen h U ⟨y, hy⟩, hres]
  exact hvals.closure (metricScalar_smooth g).continuous (metricScalar_smooth h).continuous hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricScalarAt_eq_of_eqOn_closure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricScalarAt_eq_of_eqOn_closure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricScalarAt_eq_of_eqOn_closure ``Submission.DifferentialGeometry.Geometry.Curvature.metricScalarAt_eq_of_eqOn_closure

end DifferentialGeometry.Geometry.Curvature
