import Submission.DifferentialGeometry.Geometry.Neck.InsertionInput

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.TopologicalSpace _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff
namespace DifferentialGeometry.Geometry.Neck.datumIsometry
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.datumIsometry.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.datumIsometry.IC target :: scope.openDecls } }
variable {E E' H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Fact (Module.finrank ℝ E = 3)]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [Fact (Module.finrank ℝ E' = 3)]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'} [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
  {g : SmoothRiemannianMetric I M} {g' : SmoothRiemannianMetric J N}
  {x₀ : M} {x₀' : N} {δ : ℝ} {k : ℕ}
  {d : normalizedDatum g x₀ δ k} {d' : normalizedDatum g' x₀' δ k}

private def sourceMap (F : datumIsometry d d') : bufferedCylinder δ → F.source :=
  fun q => ⟨d.map q, F.image_source q⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.datumIsometry.sourceMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.datumIsometry.sourceMap target :: scope.openDecls } }
private theorem sourceMap_smooth (F : datumIsometry d d') : ContMDiff IC I ∞ (sourceMap F) :=
  (ContMDiff.subtypeVal_comp_iff F.source (sourceMap F)).mp d.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.datumIsometry.sourceMap_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.datumIsometry.sourceMap_smooth target :: scope.openDecls } }
private theorem sourceMap_deriv (F : datumIsometry d d') (q : bufferedCylinder δ) :
    mfderiv IC I (sourceMap F) q = mfderiv IC I d.map q := by
  have he : (Subtype.val : F.source → M) ∘ sourceMap F = d.map := rfl
  rw [← he, mfderiv_comp q
    (contMDiff_subtype_val.mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0))
    ((sourceMap_smooth F).mdifferentiableAt (by decide)), mfderiv_subtype_val]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.datumIsometry.sourceMap_deriv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.datumIsometry.sourceMap_deriv target :: scope.openDecls } }

private theorem targetMap_deriv (F : datumIsometry d d') (q : bufferedCylinder δ) :
    mfderiv IC J d'.map q =
      (mfderiv I J F.equiv (sourceMap F q)).comp (mfderiv IC I d.map q) := by
  have he : (Subtype.val : F.target → N) ∘ F.equiv ∘ sourceMap F = d'.map :=
    funext F.chart_eq
  rw [← he, mfderiv_comp q
    (contMDiff_subtype_val.mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0))
    ((F.equiv.contMDiff.comp (sourceMap_smooth F)).mdifferentiableAt (by decide)),
    mfderiv_subtype_val]
  change mfderiv IC J (F.equiv ∘ sourceMap F) q = _
  rw [mfderiv_comp q (F.equiv.contMDiff.mdifferentiableAt (by decide))
    ((sourceMap_smooth F).mdifferentiableAt (by decide)), sourceMap_deriv]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.datumIsometry.targetMap_deriv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.datumIsometry.targetMap_deriv target :: scope.openDecls } }

theorem normalizedMetric_eq (F : datumIsometry d d') : d'.normalizedMetric = d.normalizedMetric := by
  apply SmoothRiemannianMetric.ext_inner
  intro q u v
  rw [normalizedDatum.normalizedMetric_inner, normalizedDatum.normalizedMetric_inner, F.scalar_eq]
  congr 1
  have hh := congrArg (fun G : SmoothRiemannianMetric I F.source =>
    G.inner (sourceMap F q) (mfderiv IC I d.map q u) (mfderiv IC I d.map q v)) F.metric_eq
  erw [Diffeomorph.pullbackMetricCross_inner] at hh
  change g'.inner (F.equiv (sourceMap F q)).val
      (mfderiv I J F.equiv (sourceMap F q) (mfderiv IC I d.map q u))
      (mfderiv I J F.equiv (sourceMap F q) (mfderiv IC I d.map q v)) =
    g.inner (d.map q) (mfderiv IC I d.map q u) (mfderiv IC I d.map q v) at hh
  have hp : (F.equiv (sourceMap F q)).val = d'.map q := F.chart_eq q
  rw [hp] at hh
  rw [targetMap_deriv F q]
  exact hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.datumIsometry.normalizedMetric_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.datumIsometry.normalizedMetric_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.datumIsometry.normalizedMetric_eq ``Submission.DifferentialGeometry.Geometry.Neck.datumIsometry.normalizedMetric_eq

theorem controlledMetric_eq (F : datumIsometry d d') : d'.controlledMetric = d.controlledMetric := by
  change d'.normalizedMetric.restrictOpenOfSubset _ = d.normalizedMetric.restrictOpenOfSubset _
  rw [F.normalizedMetric_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.datumIsometry.controlledMetric_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.datumIsometry.controlledMetric_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.datumIsometry.controlledMetric_eq ``Submission.DifferentialGeometry.Geometry.Neck.datumIsometry.controlledMetric_eq
end DifferentialGeometry.Geometry.Neck.datumIsometry
