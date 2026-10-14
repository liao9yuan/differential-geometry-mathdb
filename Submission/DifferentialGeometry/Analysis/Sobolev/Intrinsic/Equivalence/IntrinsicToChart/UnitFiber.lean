import Submission.DifferentialGeometry.Analysis.Sobolev.Intrinsic.Equivalence.NormEquivalence
import Submission.DifferentialGeometry.Analysis.Sobolev.Manifold.Measure.UniformChartComparison

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Function
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace EquivalenceReverse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart

local notation "EuclN_E" =>
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

noncomputable def chartTargetUnitFiber (α : M)
    (i : Fin (Module.finrank ℝ E)) (x : M) : TangentSpace I x :=
  (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symm x
    ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E).symm
      (EuclideanSpace.single i (1 : ℝ)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.chartTargetUnitFiber then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.chartTargetUnitFiber"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.chartTargetUnitFiber ``Submission.DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.chartTargetUnitFiber

private lemma chartTargetUnit_smoothOn (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (chartTargetUnitFiber (I := I) α i x))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  set v_E : E := (toEuclidean (E := E) : E ≃L[ℝ] EuclN_E).symm
    (EuclideanSpace.single i (1 : ℝ)) with hv_E_def
  have hiff :=
    ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α)).contMDiffOn_section_baseSet_iff
      (IB := I) (n := ∞)
      (s := fun x : M => (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symm x v_E)
  refine hiff.mpr ?_
  have hconst : ContMDiffOn I 𝓘(ℝ, E) ∞ (fun _ : M => v_E)
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := contMDiffOn_const
  refine hconst.congr ?_
  intro x hx
  exact congrArg Prod.snd
    ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).apply_mk_symm hx v_E)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.chartTargetUnit_smoothOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.chartTargetUnit_smoothOn target :: scope.openDecls } }

private lemma g_inner_chartTargetUnit_continuousOn
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (α : M) (i : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun x : M => g.inner x
        (chartTargetUnitFiber (I := I) α i x)
        (chartTargetUnitFiber (I := I) α i x))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  have hg : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        b (g.inner b))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    g.contMDiff.contMDiffOn
  have hv := chartTargetUnit_smoothOn (I := I) α i
  have happ :
      ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun m : M => (⟨m,
            g.inner m
              (chartTargetUnitFiber (I := I) α i m)
              (chartTargetUnitFiber (I := I) α i m)⟩ :
              _root_.Bundle.TotalSpace ℝ (Bundle.Trivial M ℝ)))
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (b := id) hg hv hv
  intro x hx
  have hpx := happ x hx
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpx
  exact (hpx.2.continuousWithinAt)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.g_inner_chartTargetUnit_continuousOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.g_inner_chartTargetUnit_continuousOn target :: scope.openDecls } }

noncomputable def chartTargetUnitSqSumSupOnPouTsupport
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (α : M) : ℝ := by
  classical
  set Kα : Set M := tsupport
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKα_def
  by_cases hKα_ne : Kα.Nonempty
  · have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
    have hKα_sub : Kα ⊆ (chartAt H α).source :=
      DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
    have hKα_base : Kα ⊆ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
      intro x hx
      rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source]
      exact hKα_sub hx
    have h_cont : ContinuousOn
        (fun x : M => ∑ i : Fin (Module.finrank ℝ E),
          g.inner x
            (chartTargetUnitFiber (I := I) α i x)
            (chartTargetUnitFiber (I := I) α i x)) Kα := by
      apply continuousOn_finsetSum
      intro i _
      exact (g_inner_chartTargetUnit_continuousOn (I := I) g α i).mono hKα_base
    exact (hKα_compact.image_of_continuousOn h_cont).bddAbove.choose
  · exact 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.chartTargetUnitSqSumSupOnPouTsupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.chartTargetUnitSqSumSupOnPouTsupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.chartTargetUnitSqSumSupOnPouTsupport ``Submission.DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.chartTargetUnitSqSumSupOnPouTsupport

lemma chartTargetUnitSqSumSupOnPouTsupport_nonneg
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (α : M) :
    0 ≤ chartTargetUnitSqSumSupOnPouTsupport (I := I) (M := M) g α := by
  classical
  unfold chartTargetUnitSqSumSupOnPouTsupport
  set Kα : Set M := tsupport
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKα_def
  by_cases hKα_ne : Kα.Nonempty
  · rw [dif_pos hKα_ne]
    have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
    have hKα_sub : Kα ⊆ (chartAt H α).source :=
      DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
    have hKα_base : Kα ⊆ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
      intro x hx
      rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source]
      exact hKα_sub hx
    have h_cont : ContinuousOn
        (fun x : M => ∑ i : Fin (Module.finrank ℝ E),
          g.inner x
            (chartTargetUnitFiber (I := I) α i x)
            (chartTargetUnitFiber (I := I) α i x)) Kα := by
      apply continuousOn_finsetSum
      intro i _
      exact (g_inner_chartTargetUnit_continuousOn (I := I) g α i).mono hKα_base
    set hImage :=
      (hKα_compact.image_of_continuousOn h_cont).bddAbove
    obtain ⟨x₀, hx₀⟩ := hKα_ne
    have h_val_nn : (0 : ℝ) ≤
        ∑ i : Fin (Module.finrank ℝ E),
          g.inner x₀
            (chartTargetUnitFiber (I := I) α i x₀)
            (chartTargetUnitFiber (I := I) α i x₀) := by
      apply Finset.sum_nonneg
      intro i _
      by_cases hzero : chartTargetUnitFiber (I := I) α i x₀ = 0
      · rw [hzero]
        change ((g.inner x₀) (0 : TangentSpace I x₀)) (0 : TangentSpace I x₀) ≥ 0
        rw [(g.inner x₀).map_zero]
        change (0 : TangentSpace I x₀ →L[ℝ] ℝ) (0 : TangentSpace I x₀) ≥ 0
        simp
      · exact (g.pos x₀ _ hzero).le
    have hx₀_val :
        (∑ i : Fin (Module.finrank ℝ E),
          g.inner x₀
            (chartTargetUnitFiber (I := I) α i x₀)
            (chartTargetUnitFiber (I := I) α i x₀)) ∈
        (fun x : M => ∑ i : Fin (Module.finrank ℝ E),
          g.inner x
            (chartTargetUnitFiber (I := I) α i x)
            (chartTargetUnitFiber (I := I) α i x)) '' Kα :=
      ⟨x₀, hx₀, rfl⟩
    have h_le := hImage.choose_spec hx₀_val
    exact le_trans h_val_nn h_le
  · rw [dif_neg hKα_ne]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.chartTargetUnitSqSumSupOnPouTsupport_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.chartTargetUnitSqSumSupOnPouTsupport_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.chartTargetUnitSqSumSupOnPouTsupport_nonneg ``Submission.DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.chartTargetUnitSqSumSupOnPouTsupport_nonneg

lemma chartTargetUnitSqSum_le_sup
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (α : M) {x : M}
    (hx : x ∈ tsupport
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :
    ∑ i : Fin (Module.finrank ℝ E),
        g.inner x
          (chartTargetUnitFiber (I := I) α i x)
          (chartTargetUnitFiber (I := I) α i x) ≤
      chartTargetUnitSqSumSupOnPouTsupport (I := I) (M := M) g α := by
  classical
  unfold chartTargetUnitSqSumSupOnPouTsupport
  set Kα : Set M := tsupport
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKα_def
  have hKα_ne : Kα.Nonempty := ⟨x, hx⟩
  rw [dif_pos hKα_ne]
  have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
  have hKα_sub : Kα ⊆ (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
  have hKα_base : Kα ⊆ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
    intro y hy
    rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source]
    exact hKα_sub hy
  have h_cont : ContinuousOn
      (fun y : M => ∑ i : Fin (Module.finrank ℝ E),
        g.inner y
          (chartTargetUnitFiber (I := I) α i y)
          (chartTargetUnitFiber (I := I) α i y)) Kα := by
    apply continuousOn_finsetSum
    intro i _
    exact (g_inner_chartTargetUnit_continuousOn (I := I) g α i).mono hKα_base
  set hImage :=
    (hKα_compact.image_of_continuousOn h_cont).bddAbove
  exact hImage.choose_spec ⟨x, hx, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.chartTargetUnitSqSum_le_sup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.chartTargetUnitSqSum_le_sup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.chartTargetUnitSqSum_le_sup ``Submission.DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.chartTargetUnitSqSum_le_sup

end EquivalenceReverse
end Sobolev
end Analysis
end DifferentialGeometry
