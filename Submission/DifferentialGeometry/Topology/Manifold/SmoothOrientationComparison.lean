import Submission.DifferentialGeometry.Topology.Manifold.SmoothOrientationLocal

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Manifold _root_.TopologicalSpace
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.Manifold
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def negSmoothOrientation (o : SmoothOrientation I M) : SmoothOrientation I M := by
  refine ⟨fun x => -o.val x, ?_⟩
  intro p
  have h := (o.property p).comp (fun a => -a)
  simpa only [Orientation.map_neg, Function.comp_def] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.negSmoothOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.negSmoothOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.negSmoothOrientation ``Submission.DifferentialGeometry.Topology.Manifold.negSmoothOrientation

theorem negSmoothOrientation_apply (o : SmoothOrientation I M) (x : M) :
    (negSmoothOrientation I o).val x = -o.val x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.negSmoothOrientation_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.negSmoothOrientation_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.negSmoothOrientation_apply ``Submission.DifferentialGeometry.Topology.Manifold.negSmoothOrientation_apply

theorem smoothOrientation_agreement_locallyConstant (o₁ o₂ : SmoothOrientation I M) :
    IsLocallyConstant (fun x : M => o₁.val x = o₂.val x) := by
  apply isLocallyConstant_of_open_neighborhoods
  intro p
  let U : _root_.TopologicalSpace.Opens M := ⟨(chartAt H p).source, (chartAt H p).open_source⟩
  have h := (o₁.property p).comp₂ (o₂.property p) (fun a b => a = b)
  refine ⟨U, mem_chart_source H p, ?_⟩
  have he : (fun x : U =>
      Orientation.map _ (preferredChartTangentEquiv I p x.val x.property).toLinearEquiv (o₁.val x.val) =
        Orientation.map _ (preferredChartTangentEquiv I p x.val x.property).toLinearEquiv (o₂.val x.val)) =
      (fun x : U => o₁.val x.val = o₂.val x.val) := by
    funext x
    exact propext (Orientation.map _
      (preferredChartTangentEquiv I p x.val x.property).toLinearEquiv).injective.eq_iff
  have h' : IsLocallyConstant (fun x : U =>
      Orientation.map _ (preferredChartTangentEquiv I p x.val x.property).toLinearEquiv (o₁.val x.val) =
        Orientation.map _ (preferredChartTangentEquiv I p x.val x.property).toLinearEquiv (o₂.val x.val)) := h
  rw [he] at h'
  exact h'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.smoothOrientation_agreement_locallyConstant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.smoothOrientation_agreement_locallyConstant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.smoothOrientation_agreement_locallyConstant ``Submission.DifferentialGeometry.Topology.Manifold.smoothOrientation_agreement_locallyConstant

theorem smoothOrientation_eq_of_eq_at [PreconnectedSpace M]
    (o₁ o₂ : SmoothOrientation I M) (p : M) (hp : o₁.val p = o₂.val p) :
    ∀ x : M, o₁.val x = o₂.val x := by
  intro x
  have h := (smoothOrientation_agreement_locallyConstant I o₁ o₂).apply_eq_of_preconnectedSpace x p
  exact h.symm ▸ hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.smoothOrientation_eq_of_eq_at then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.smoothOrientation_eq_of_eq_at"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.smoothOrientation_eq_of_eq_at ``Submission.DifferentialGeometry.Topology.Manifold.smoothOrientation_eq_of_eq_at

theorem smoothOrientation_eq_or_eq_neg [PreconnectedSpace M]
    (o₁ o₂ : SmoothOrientation I M) (p : M) :
    (∀ x : M, o₁.val x = o₂.val x) ∨ (∀ x : M, o₁.val x = -o₂.val x) := by
  rcases Orientation.eq_or_eq_neg (o₁.val p) (o₂.val p) (by simp) with hp | hp
  · exact Or.inl (smoothOrientation_eq_of_eq_at I o₁ o₂ p hp)
  · exact Or.inr (smoothOrientation_eq_of_eq_at I o₁ (negSmoothOrientation I o₂) p hp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.smoothOrientation_eq_or_eq_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.smoothOrientation_eq_or_eq_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.smoothOrientation_eq_or_eq_neg ``Submission.DifferentialGeometry.Topology.Manifold.smoothOrientation_eq_or_eq_neg
end DifferentialGeometry.Topology.Manifold
