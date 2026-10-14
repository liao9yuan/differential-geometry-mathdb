import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.WeakSolution.WeakSolutionHeadline
import Submission.DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.SmoothWeakSolutionH2

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.MeasureTheory _root_.Topology
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.Matrix _root_.InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBounds

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [NeZero (Module.finrank ℝ E)] in
omit [FiniteDimensional ℝ E] in
private lemma memLp_two_contDiff_hasCompactSupport_restrict
    {f : EuclN → ℝ} (hf_cd : ContDiff ℝ ∞ f) (hf_cs : HasCompactSupport f)
    (Ω' : Set EuclN) :
    MemLp f 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω') :=
  (hf_cd.continuous.memLp_of_hasCompactSupport (μ := _root_.MeasureTheory.MeasureSpace.volume) (p := 2)
    hf_cs).restrict _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.memLp_two_contDiff_hasCompactSupport_restrict
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.memLp_two_contDiff_hasCompactSupport_restrict target :: scope.openDecls } }

theorem tensor_h2_local_chartComp
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T F : SmoothCcTensor g r s) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (P₀ : CompIdx E r s)
    (hT_support : tsupport T.toFun ⊆ (chartAt H α).source)
    (hF_support : tsupport F.toFun ⊆ (chartAt H α).source)
    (hT_K : tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) ⊆ K)
    (hweak : ∀ v : SmoothCcTensor g r s,
      ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        tensorL2Inner (I := I) (M := M) g r s F.toFun v.toFun)
    {Ω'' : Set EuclN} (hΩ'' : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω'')) :
    ∀ i k : Fin (Module.finrank ℝ E), ∃ g_ik : EuclN → ℝ,
      _root_.MeasureTheory.MemLp g_ik 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g_ik
        (fun y : EuclN =>
          (fderiv ℝ (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) y)
            (EuclideanSpace.single i 1)) Ω'' ∧
      ∃ Ω' : Set EuclN, IsOpen Ω' ∧ closure Ω'' ⊆ Ω' ∧
        closure Ω' ⊆ (Set.univ : Set EuclN) ∧
        IsCompact (closure Ω') ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ∫ x in Ω'', g_ik x ^ 2 ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) ≤
            C * (∫ x in Ω',
                  ∑ j : Fin (Module.finrank ℝ E),
                    ((fderiv ℝ
                      (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) x)
                        (EuclideanSpace.single j 1)) ^ 2
                ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) +
              ∫ x in Ω',
                  (tensorComponentEuclid (I := I) (M := M) g r s T α P₀ x) ^ 2
                ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) +
              ∫ x in Ω',
                  (tensorComponentWeakRHS (I := I) (M := M)
                    g r s T F α P₀ x) ^ 2
                ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) := by
  classical
  have h_weak :
      (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).IsSmoothWeakSolution
        (tensorComponentEuclid (I := I) (M := M) g r s T α P₀)
        (tensorComponentWeakRHS (I := I) (M := M) g r s T F α P₀) :=
    tensorComponent_isSmoothWeakSolution (I := I) (M := M)
      g r s T F α hK hK_target P₀ hT_support hF_support hT_K hweak
  have hRHS_cd : ContDiff ℝ ∞
      (tensorComponentWeakRHS (I := I) (M := M) g r s T F α P₀) :=
    tensorComponentWeakRHS_contDiff (I := I) (M := M)
      g r s T F α P₀ hT_support hF_support
  have hRHS_cs : HasCompactSupport
      (tensorComponentWeakRHS (I := I) (M := M) g r s T F α P₀) :=
    tensorComponentWeakRHS_hasCompactSupport (I := I) (M := M)
      g r s T F α hK hK_target P₀ hT_support hF_support hT_K hweak
  have hf_l2_local : ∀ {Ω' : Set EuclN}, IsCompact (closure Ω') →
      MemLp (tensorComponentWeakRHS (I := I) (M := M) g r s T F α P₀)
        2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω') := by
    intro Ω' _
    exact memLp_two_contDiff_hasCompactSupport_restrict (E := E)
      hRHS_cd hRHS_cs Ω'
  have h_room :
      Metric.cthickening 2 (closure Ω'') ⊆ (Set.univ : Set EuclN) :=
    fun y _ => Set.mem_univ y
  obtain ⟨C, hC_nn, h_eng⟩ := local_smooth_solution
    (d := Module.finrank ℝ E)
    (tensorPrincipalForm (I := I) (M := M) g α hK hK_target)
    hΩ'' hΩ''_compact_closure h_room
  intro i k
  obtain ⟨g_ik, hg_memLp, hg_weak, Ω', hΩ'_open, hΩ''_in_Ω', hΩ'_in,
    hΩ'_compact, hbound⟩ := h_eng h_weak hf_l2_local i k
  exact ⟨g_ik, hg_memLp, hg_weak, Ω', hΩ'_open, hΩ''_in_Ω', hΩ'_in,
    hΩ'_compact, C, hC_nn, hbound⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensor_h2_local_chartComp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensor_h2_local_chartComp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensor_h2_local_chartComp ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensor_h2_local_chartComp

theorem tensor_h2_local_chartComp_all
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T F : SmoothCcTensor g r s) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hT_support : tsupport T.toFun ⊆ (chartAt H α).source)
    (hF_support : tsupport F.toFun ⊆ (chartAt H α).source)
    (hT_K : ∀ P₀ : CompIdx E r s,
      tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) ⊆ K)
    (hweak : ∀ v : SmoothCcTensor g r s,
      ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        tensorL2Inner (I := I) (M := M) g r s F.toFun v.toFun)
    {Ω'' : Set EuclN} (hΩ'' : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω'')) :
    ∀ (P₀ : CompIdx E r s) (i k : Fin (Module.finrank ℝ E)),
      ∃ g_ik : EuclN → ℝ,
      _root_.MeasureTheory.MemLp g_ik 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g_ik
        (fun y : EuclN =>
          (fderiv ℝ (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) y)
            (EuclideanSpace.single i 1)) Ω'' ∧
      ∃ Ω' : Set EuclN, IsOpen Ω' ∧ closure Ω'' ⊆ Ω' ∧
        closure Ω' ⊆ (Set.univ : Set EuclN) ∧
        IsCompact (closure Ω') ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ∫ x in Ω'', g_ik x ^ 2 ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) ≤
            C * (∫ x in Ω',
                  ∑ j : Fin (Module.finrank ℝ E),
                    ((fderiv ℝ
                      (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) x)
                        (EuclideanSpace.single j 1)) ^ 2
                ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) +
              ∫ x in Ω',
                  (tensorComponentEuclid (I := I) (M := M) g r s T α P₀ x) ^ 2
                ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) +
              ∫ x in Ω',
                  (tensorComponentWeakRHS (I := I) (M := M)
                    g r s T F α P₀ x) ^ 2
                ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) :=
  fun P₀ => tensor_h2_local_chartComp (I := I) (M := M)
    g r s T F α hK hK_target P₀ hT_support hF_support (hT_K P₀) hweak hΩ'' hΩ''_compact_closure

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensor_h2_local_chartComp_all then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensor_h2_local_chartComp_all"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensor_h2_local_chartComp_all ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensor_h2_local_chartComp_all

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry
