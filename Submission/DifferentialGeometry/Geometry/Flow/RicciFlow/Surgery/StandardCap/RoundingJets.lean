import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.ConformalFactor
import Submission.DifferentialGeometry.Geometry.Metric.Conformal.Basic
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.Continuity
import Mathlib.Geometry.Manifold.Instances.Sphere
import Submission.DifferentialGeometry.Topology.SigmaCompactOpen
import Submission.DifferentialGeometry.Geometry.Metric.Conformal.OfContDiff
import Submission.DifferentialGeometry.Bundle.Section

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Metric
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2 + 1)]
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.IC target :: scope.openDecls } }
private abbrev Cyl := Metric.sphere (0 : E) 1 × ℝ

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.Cyl
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.Cyl target :: scope.openDecls } }

omit [InnerProductSpace ℝ E] [Fact (Module.finrank ℝ E = 2 + 1)] in
private theorem positive_height_closure (U : TopologicalSpace.Opens (Cyl (E := E)))
    (x : U) (hx : (x : Cyl (E := E)).2 = 0) :
    x ∈ closure {y : U | 0 < (y : Cyl (E := E)).2} := by
  have hopen : IsOpenMap (fun y : U => (y : Cyl (E := E)).2) :=
    isOpenMap_snd.comp U.isOpen.isOpenEmbedding_subtypeVal.isOpenMap
  apply hopen.preimage_closure_subset_closure_preimage
  change (x : Cyl (E := E)).2 ∈ closure (_root_.Set.Ioi (0 : ℝ))
  rw [closure_Ioi, hx]
  exact (show (0 : ℝ) ≤ 0 from le_rfl)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.positive_height_closure
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.positive_height_closure target :: scope.openDecls } }

theorem metricCovDeriv_conformalFactor_eq_at_height_zero
    (U : TopologicalSpace.Opens (Cyl (E := E)))
    (h gRef : SmoothRiemannianMetric IC U) (x : U)
    (hx : (x : Cyl (E := E)).2 = 0) (m : ℕ) :
    metricCovDeriv
        (conformalMetricOfContDiff h (fun y : U => conformalFactor (y : Cyl (E := E)).2)
          (contDiff_conformalFactor.contMDiff.comp
            (contMDiff_snd.comp (contMDiff_subtype_val (I := IC) (U := U)))))
        gRef m x = metricCovDeriv h gRef m x := by
  classical
  let : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos (by
    rw [show Module.finrank ℝ E = 2 + 1 from Fact.out]
    norm_num)
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen IC U.isOpen)
  let V : TopologicalSpace.Opens U :=
    ⟨{y : U | 0 < (y : Cyl (E := E)).2},
      isOpen_lt continuous_const (continuous_snd.comp continuous_subtype_val)⟩
  let : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen IC V.isOpen)
  let h' := conformalMetricOfContDiff h (fun y : U => conformalFactor (y : Cyl (E := E)).2)
    (contDiff_conformalFactor.contMDiff.comp
      (contMDiff_snd.comp (contMDiff_subtype_val (I := IC) (U := U))))
  change metricCovDeriv h' gRef m x = metricCovDeriv h gRef m x
  have heq : ∀ y : U, y ∈ V → ∀ v w : TangentSpace IC y,
      h'.inner y v w = h.inner y v w := by
    intro y hy v w
    rw [conformalMetricOfContDiff_inner, conformalFactor_eq_zero_of_nonneg (le_of_lt hy)]
    simp only [_root_.MulZeroClass.mul_zero, Real.exp_zero, one_mul]
  ext slots
  let W : Fin (m + 2) → ContMDiffSection IC (EuclideanSpace ℝ (Fin 2) × ℝ) (∞ : WithTop ℕ∞)
      (TangentSpace IC : U → Type _) := fun i =>
    (ContMDiffSection.exists_eq_at (I := IC) (F := EuclideanSpace ℝ (Fin 2) × ℝ) (V := TangentSpace IC)
      (n := (⊤ : ℕ∞)) x (slots i)).choose
  have hW : ∀ i, W i x = slots i := fun i =>
    (ContMDiffSection.exists_eq_at (I := IC) (F := EuclideanSpace ℝ (Fin 2) × ℝ) (V := TangentSpace IC)
      (n := (⊤ : ℕ∞)) x (slots i)).choose_spec
  have hcont (k : SmoothRiemannianMetric IC U) :
      Continuous (fun y : U => metricCovDeriv k gRef m y (fun i => W i y)) := by
    have hd : ContMDiff IC 𝓘(ℝ) ∞
        (fun y : U => metricCovDeriv k gRef m y (fun i => W i y)) := fun y =>
      Tensor0SBundle.tensor0SField_eval_smooth_slots_contMDiffAt
        (metricCovDeriv k gRef m) W y
    exact hd.continuous
  have hvals : _root_.Set.EqOn
      (fun y : U => metricCovDeriv h' gRef m y (fun i => W i y))
      (fun y : U => metricCovDeriv h gRef m y (fun i => W i y)) V := by
    intro y hy
    exact metricCovDeriv_eq_of_eqOn h' h gRef V heq m ⟨y, hy⟩ _
  have hat := hvals.closure (hcont h') (hcont h) (positive_height_closure U x hx)
  simpa only [hW] using hat

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.metricCovDeriv_conformalFactor_eq_at_height_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.metricCovDeriv_conformalFactor_eq_at_height_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.metricCovDeriv_conformalFactor_eq_at_height_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.metricCovDeriv_conformalFactor_eq_at_height_zero

end DifferentialGeometry.PDE.RicciFlow.StandardCap
