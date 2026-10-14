import Submission.DifferentialGeometry.Topology.Manifold.Sigma
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OrientationComposition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology

universe u v
variable {ι : Type v} {H : Type*} [TopologicalSpace H] [Nonempty H]
  {M : ι → Type u} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {I : ModelWithCorners ℝ E H}

private theorem writtenInExtChartAt_sigmaMk_eventuallyEq_id (i : ι) (q : M i) :
    writtenInExtChartAt I I q (Sigma.mk i : M i → Σ j, M j) =ᶠ[𝓝[_root_.Set.range I] (extChartAt I q q)] id := by
  have hmem : I.symm ⁻¹' (chartAt H q).target ∩ _root_.Set.range I ∈ 𝓝[_root_.Set.range I] (extChartAt I q q) := by
    rw [← I.image_eq (chartAt H q).target]
    exact (chartAt H q).extend_image_target_mem_nhds (mem_chart_source H q)
  filter_upwards [hmem] with y hy
  rcases hy with ⟨hyT, ⟨z, rfl⟩⟩
  simp [writtenInExtChartAt, extChartAt, sigmaChartedSpace_chartAt,
    sigma_mk_injective.extend_apply (chartAt H q),
    (chartAt H q).right_inv (by simpa [Set.mem_preimage, I.left_inv] using hyT)]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.writtenInExtChartAt_sigmaMk_eventuallyEq_id
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.writtenInExtChartAt_sigmaMk_eventuallyEq_id target :: scope.openDecls } }

theorem hasMFDerivAt_sigmaMk (i : ι) (q : M i) :
    HasMFDerivAt I I (Sigma.mk i : M i → Σ j, M j) q (ContinuousLinearMap.id ℝ E) := by
  refine ⟨continuous_sigmaMk.continuousAt, ?_⟩
  exact (hasFDerivWithinAt_id _ (_root_.Set.range I)).congr_of_eventuallyEq
    (writtenInExtChartAt_sigmaMk_eventuallyEq_id i q)
    (by simp [writtenInExtChartAt, extChartAt, sigmaChartedSpace_chartAt, sigma_mk_injective.extend_apply (chartAt H q)])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hasMFDerivAt_sigmaMk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hasMFDerivAt_sigmaMk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hasMFDerivAt_sigmaMk ``Submission.DifferentialGeometry.Topology.hasMFDerivAt_sigmaMk

theorem mfderiv_sigmaMk (i : ι) (q : M i) :
    mfderiv I I (Sigma.mk i : M i → Σ j, M j) q = ContinuousLinearMap.id ℝ E :=
  (hasMFDerivAt_sigmaMk i q).mfderiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.mfderiv_sigmaMk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.mfderiv_sigmaMk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.mfderiv_sigmaMk ``Submission.DifferentialGeometry.Topology.mfderiv_sigmaMk

variable [FiniteDimensional ℝ E] [∀ i, IsManifold I ∞ (M i)] {n : ℕ}

theorem sigmaMk_preserves_orientation (hdim : Module.finrank ℝ E = n)
    (o : ∀ i, ManifoldOrientation I (M i) n) (i : ι) (q : M i) :
    Orientation.map (Fin n) ((isLocalDiffeomorph_sigmaMk (I := I) (n := ∞) i q).mfderivToContinuousLinearEquiv
      (by simp)).toLinearEquiv ((o i).orientation q) =
        (manifoldOrientationUnion hdim o).orientation (⟨i, q⟩ : Σ j, M j) := by
  have he : ((isLocalDiffeomorph_sigmaMk (I := I) (n := ∞) i q).mfderivToContinuousLinearEquiv
      (by simp)).toLinearEquiv = LinearEquiv.refl ℝ E := by
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun L : E →L[ℝ] E => L v) (mfderiv_sigmaMk i q)
  rw [he]
  change (Orientation.map (Fin n) (LinearEquiv.refl ℝ E)) ((o i).orientation q) = (o i).orientation q
  simp only [Orientation.map_refl]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sigmaMk_preserves_orientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sigmaMk_preserves_orientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sigmaMk_preserves_orientation ``Submission.DifferentialGeometry.Topology.sigmaMk_preserves_orientation

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

universe u v
variable {ι : Type v} {H : Type*} [TopologicalSpace H] [Nonempty H]
  {M : ι → Type u} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {I : ModelWithCorners ℝ E H}
  {F K N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  [TopologicalSpace N] [ChartedSpace K N]

theorem mfderiv_comp_sigmaMk (f : (Σ i, M i) → N) (i : ι) (x : M i)
    (hf : MDifferentiableAt I J f ⟨i, x⟩) :
    mfderiv I J (f ∘ Sigma.mk i) x = mfderiv I J f ⟨i, x⟩ := by
  rw [mfderiv_comp x hf (hasMFDerivAt_sigmaMk i x).mdifferentiableAt, mfderiv_sigmaMk]
  exact ContinuousLinearMap.comp_id _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.mfderiv_comp_sigmaMk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.mfderiv_comp_sigmaMk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.mfderiv_comp_sigmaMk ``Submission.DifferentialGeometry.Topology.mfderiv_comp_sigmaMk

theorem mfderiv_sigmaMk_comp (i : ι) (f : N → M i) (x : N)
    (hf : MDifferentiableAt J I f x) :
    mfderiv J I (Sigma.mk i ∘ f) x = mfderiv J I f x := by
  rw [mfderiv_comp x (hasMFDerivAt_sigmaMk i (f x)).mdifferentiableAt hf, mfderiv_sigmaMk]
  exact ContinuousLinearMap.id_comp _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.mfderiv_sigmaMk_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.mfderiv_sigmaMk_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.mfderiv_sigmaMk_comp ``Submission.DifferentialGeometry.Topology.mfderiv_sigmaMk_comp

end DifferentialGeometry.Topology
