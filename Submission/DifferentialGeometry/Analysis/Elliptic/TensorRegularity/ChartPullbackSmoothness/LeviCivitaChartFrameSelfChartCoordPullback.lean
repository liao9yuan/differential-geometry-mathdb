import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.ChartPullbackSmoothness.ChartFrameCoordMatrixPullback
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.LocalizedFrame.CovariantDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function _root_.NormedSpace
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

private noncomputable def chartModelBasisProj (m : Fin (Module.finrank ℝ E)) :
    E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (((LinearMap.proj m).comp ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun.toLinearMap)) :
      E →ₗ[ℝ] ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartModelBasisProj
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartModelBasisProj target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma chartModelBasisProj_apply (m : Fin (Module.finrank ℝ E))
    (v : E) :
    chartModelBasisProj (E := E) m v =
      ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr v) m := by
  classical
  unfold chartModelBasisProj
  change ((LinearMap.proj m).comp ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun.toLinearMap)) v = _
  rw [LinearMap.comp_apply]
  simp [Module.Basis.equivFun]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartModelBasisProj_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartModelBasisProj_apply target :: scope.openDecls } }

private lemma leviCivita_chartFrame_hom_contMDiff
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M =>
        (⟨x, (LeviCivita (I := I) g).toFun
            (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun x⟩ :
          _root_.Bundle.TotalSpace (E →L[ℝ] E) (fun x : M =>
            TangentSpace I x →L[ℝ] TangentSpace I x))) := by
  classical
  have hB :=
    (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).contMDiff
  have hB' : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1)
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x
        ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun x))
      Set.univ := by
    have h_eq : (∞ : WithTop ℕ∞) + 1 = ∞ := by
      rw [ENat.coe_top_add_one]
    rw [h_eq]
    exact hB.contMDiffOn
  have h_hom_on :=
    LeviCivita_section_contMDiffOn_univ (I := I) g (σ := fun x : M =>
      (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun x) hB'
  exact contMDiffOn_univ.mp h_hom_on

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.leviCivita_chartFrame_hom_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.leviCivita_chartFrame_hom_contMDiff target :: scope.openDecls } }

private lemma leviCivita_chartFrame_self_section_contMDiff
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M =>
        (⟨x, (LeviCivita (I := I) g).toFun
            (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun x
            ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun x)⟩ :
          TotalSpace E (TangentSpace I : M → Type _))) := by
  classical
  have h_hom := leviCivita_chartFrame_hom_contMDiff (I := I) (M := M) g α i
  have hB :=
    (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).contMDiff
  exact h_hom.clm_bundle_apply (v := fun x : M =>
    (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun x) hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.leviCivita_chartFrame_self_section_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.leviCivita_chartFrame_self_section_contMDiff target :: scope.openDecls } }

private lemma leviCivita_chartFrame_self_trivialized_contMDiffOn
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun b : M => (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
        ((LeviCivita (I := I) g).toFun
          (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have h_section :=
    leviCivita_chartFrame_self_section_contMDiff (I := I) (M := M) g α i
  have h_triv :
      ContMDiffOn I 𝓘(ℝ, E) ∞
        (fun b : M =>
          ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α)
            ⟨b, (LeviCivita (I := I) g).toFun
              (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
              ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)⟩).2)
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
    have hiff := (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).contMDiffOn_section_baseSet_iff
      (IB := I) (n := ∞)
      (s := fun b : M => (LeviCivita (I := I) g).toFun
        (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
        ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))
    exact hiff.mp h_section.contMDiffOn
  have h_eq_baseSet :
      Set.EqOn (fun b : M =>
          ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α)
            ⟨b, (LeviCivita (I := I) g).toFun
              (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
              ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)⟩).2)
        (fun b : M => (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
          ((LeviCivita (I := I) g).toFun
            (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
            ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)))
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
    intro b hb
    change ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α)
        ⟨b, (LeviCivita (I := I) g).toFun
          (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)⟩).2 =
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
        ((LeviCivita (I := I) g).toFun
          (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))
    have h₁ : ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α)
        ⟨b, (LeviCivita (I := I) g).toFun
          (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)⟩).2 =
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).continuousLinearEquivAt ℝ b hb)
          ((LeviCivita (I := I) g).toFun
            (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
            ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)) := by
      have hp := Trivialization.apply_eq_prod_continuousLinearEquivAt
        (R := ℝ) (e := _root_.FiberBundle.trivializationAt E (TangentSpace I) α) (b := b) hb
        ((LeviCivita (I := I) g).toFun
          (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))
      have hsnd := congrArg Prod.snd hp
      simp only at hsnd
      exact hsnd
    rw [h₁]
    have hclm := Trivialization.coe_continuousLinearEquivAt_eq (R := ℝ)
      (e := _root_.FiberBundle.trivializationAt E (TangentSpace I) α) (b := b) hb
    exact congrArg (fun (f : TangentSpace I b → E) => f
      ((LeviCivita (I := I) g).toFun
        (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
        ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))) hclm
  refine h_triv.congr ?_
  intro b hb
  exact (h_eq_baseSet hb).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.leviCivita_chartFrame_self_trivialized_contMDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.leviCivita_chartFrame_self_trivialized_contMDiffOn target :: scope.openDecls } }

private lemma leviCivita_chartFrame_self_coordProj_contMDiffOn
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i m : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun b : M => chartModelBasisProj (E := E) m
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
          ((LeviCivita (I := I) g).toFun
            (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
            ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have h_triv :=
    leviCivita_chartFrame_self_trivialized_contMDiffOn (I := I) (M := M) g α i
  have h_proj : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      (chartModelBasisProj (E := E) m : E → ℝ) :=
    (chartModelBasisProj (E := E) m).contMDiff
  exact h_proj.contMDiffOn.comp (t := Set.univ) h_triv (Set.subset_preimage_univ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.leviCivita_chartFrame_self_coordProj_contMDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.leviCivita_chartFrame_self_coordProj_contMDiffOn target :: scope.openDecls } }

theorem leviCivita_chartFrame_self_chartCoord_pullback_contDiffOn_chartTarget
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i m : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        chartModelBasisProj (E := E) m
          ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            ((LeviCivita (I := I) g).toFun
              (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
              ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))))))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_chart :
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) I ∞
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (chartTargetEuclid (I := I) (M := M) α) :=
    contMDiffOn_chart_symm (I := I) (M := M) α
  have h_coord :=
    leviCivita_chartFrame_self_coordProj_contMDiffOn (I := I) (M := M) g α i m
  have h_maps :
      _root_.Set.MapsTo (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (chartTargetEuclid (I := I) (M := M) α)
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
    intro y hy
    have h_source : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
        (chartAt H α).source :=
      DifferentialGeometry.Analysis.Sobolev.Chart.symm_toEuclidean_symm_mem_chartAtSource
        (I := I) (M := M) α hy
    change (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
      (chartAt H α).source
    exact h_source
  have h_comp :
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 𝓘(ℝ, ℝ) ∞
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          chartModelBasisProj (E := E) m
            ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
              ((LeviCivita (I := I) g).toFun
                (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
                ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))))))
        (chartTargetEuclid (I := I) (M := M) α) :=
    h_coord.comp h_chart h_maps
  exact (contMDiffOn_iff_contDiffOn).mp h_comp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.leviCivita_chartFrame_self_chartCoord_pullback_contDiffOn_chartTarget then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.leviCivita_chartFrame_self_chartCoord_pullback_contDiffOn_chartTarget"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.leviCivita_chartFrame_self_chartCoord_pullback_contDiffOn_chartTarget ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.leviCivita_chartFrame_self_chartCoord_pullback_contDiffOn_chartTarget

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry

end
