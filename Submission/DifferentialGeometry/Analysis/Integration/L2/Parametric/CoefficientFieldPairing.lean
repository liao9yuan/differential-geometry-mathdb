import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Parametric.PathIntegralFibreNorm
import Submission.DifferentialGeometry.Analysis.Integration.L2.SmoothSections.ParametricSmoothness
import Submission.DifferentialGeometry.Tensor.RSTensor.Smoothness.Parametric
import Submission.DifferentialGeometry.Bundle.ContinuousLinearMapSection.ParametricSmoothness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.intervalIntegral
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.RealInnerProductSpace

namespace DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Integral.L2.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Integral.L2.instNormedAddCommGroupTensorRSModelReal (r s : ℕ) :
    NormedAddCommGroup (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModelNormedAddCommGroup r s

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.instNormedAddCommGroupTensorRSModelReal
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.instNormedAddCommGroupTensorRSModelReal target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Integral.L2.instNormedSpaceRealTensorRSModel (r s : ℕ) :
    NormedSpace ℝ (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModelNormedSpace r s

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.instNormedSpaceRealTensorRSModel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.instNormedSpaceRealTensorRSModel target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Integral.L2.instTopologicalSpaceTotalSpaceTensorRSModelRealTensorRSSpace (r s : ℕ) :
    TopologicalSpace
      (_root_.Bundle.TotalSpace (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x)) :=
  Tensor0SBundle.tensorRSBundleTopology r s

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.instTopologicalSpaceTotalSpaceTensorRSModelRealTensorRSSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.instTopologicalSpaceTotalSpaceTensorRSModelRealTensorRSSpace target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Integral.L2.instFiberBundleTensorRSModelRealTensorRSSpace (r s : ℕ) :
    FiberBundle (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) :=
  Tensor0SBundle.tensorRSBundleFiber r s

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.instFiberBundleTensorRSModelRealTensorRSSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.instFiberBundleTensorRSModelRealTensorRSSpace target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem operatorFieldApplication_fixed_jointContMDiffOn
    (g : SmoothRiemannianMetric I M) {b c : ℕ}
    (A : ℝ → SmoothCcTensor g b c) (W : SmoothCcTensor g 0 b)
    (S : Set ℝ)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun x : M => TensorRSSpace b c I x) p.1
        ((A p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 0 c ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 0 c ℝ E)
        (E := fun x : M => TensorRSSpace 0 c I x) p.1
        ((ccOperatorFieldComp (I := I) (M := M) g 0 b c (A p.2) W).toSection p.1))
      ((Set.univ : Set M) ×ˢ S) := by
  have hW : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 0 b ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 0 b ℝ E)
        (E := fun x : M => TensorRSSpace 0 b I x) p.1 (W.toSection p.1))
      ((Set.univ : Set M) ×ˢ S) :=
    (W.toSection.contMDiff.comp_contMDiffOn contMDiffOn_fst).mono
      (Set.subset_univ _)
  apply contMDiffOn_clm_section_of_apply (I := I) (M := M)
    (F₁ := Tensor0SModel 0 ℝ E) (V₁ := fun x : M => Tensor0SSpace 0 I x)
    (F₂ := Tensor0SModel c ℝ E) (V₂ := fun x : M => Tensor0SSpace c I x)
    (S := S)
  intro Y
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
        (E := fun x : M => Tensor0SSpace 0 I x) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ S) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hWY := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hW hY
  have hAWY := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hA hWY
  refine hAWY.congr (fun p _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel c ℝ E)
    (E := fun x : M => Tensor0SSpace c I x) p.1 z) ?_
  rw [operatorFieldComposition_toSection]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.operatorFieldApplication_fixed_jointContMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.operatorFieldApplication_fixed_jointContMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.operatorFieldApplication_fixed_jointContMDiffOn ``Submission.DifferentialGeometry.Integral.L2.operatorFieldApplication_fixed_jointContMDiffOn

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
theorem operatorFieldApplication_pathIntegralCoeffField
    (g : SmoothRiemannianMetric I M) {b c : ℕ}
    (A : ℝ → SmoothCcTensor g b c) (W : SmoothCcTensor g 0 b)
    (S : Set ℝ) (hS : IsOpen S) (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun x : M => TensorRSSpace b c I x) p.1
        ((A p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    operatorFieldApply (I := I) (M := M) g b c
        (pathIntegralCoeffField (I := I) (M := M) g b c
          A S hS hSI hA) W =
      pathIntegralCoeffField (I := I) (M := M) g 0 c
        (fun t => ccOperatorFieldComp (I := I) (M := M) g 0 b c (A t) W)
        S hS hSI (operatorFieldApplication_fixed_jointContMDiffOn
          (I := I) (M := M) g A W S hA) := by
  classical
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  have hcontA : ∀ y : M, ContinuousOn
      (fun t : ℝ => TensorRSSpace.toModel ((A t).toSection y)) S :=
    fun y => jointContMDiff_toModel_continuous_slice
      (I := I) g b c A S hA y
  rw [pathIntegralCoeffField_operatorFieldApplication_eq
    (I := I) (M := M) g b c A W S hS hSI hA hcontA x v]
  let Ψ : ℝ → SmoothCcTensor g 0 c :=
    fun t => ccOperatorFieldComp (I := I) (M := M) g 0 b c (A t) W
  let u : Tensor0SModel 0 ℝ E :=
    Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x)
  have hΨ := operatorFieldApplication_fixed_jointContMDiffOn
    (I := I) (M := M) g A W S hA
  have hcontΨ : ContinuousOn
      (fun t : ℝ => TensorRSSpace.toModel ((Ψ t).toSection x)) S :=
    jointContMDiff_toModel_continuous_slice (I := I) g 0 c Ψ S hΨ x
  have hΨInt : IntervalIntegrable
      (fun t : ℝ => TensorRSSpace.toModel ((Ψ t).toSection x))
      volume 0 1 := (hcontΨ.mono hSI).intervalIntegrable
  have hcontApp : ContinuousOn
      (fun t : ℝ => (TensorRSSpace.toModel ((Ψ t).toSection x)) u) S :=
    (ContinuousLinearMap.apply ℝ (Tensor0SModel c ℝ E) u).continuous.comp_continuousOn
      hcontΨ
  have hΨAppInt : IntervalIntegrable
      (fun t : ℝ => (TensorRSSpace.toModel ((Ψ t).toSection x)) u)
      volume 0 1 := (hcontApp.mono hSI).intervalIntegrable
  let L : Tensor0SModel c ℝ E →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin c => E) ℝ v
  rw [unitModel, toModel_tensorRS_apply (I := I) 0 c x]
  change _ = L (TensorRSSpace.toModel
    ((pathIntegralCoeffField (I := I) (M := M) g 0 c Ψ
      S hS hSI hΨ).toSection x) u)
  rw [pathIntegralCoeffField_toModel]
  rw [ContinuousLinearMap.intervalIntegral_apply hΨInt u]
  change _ = L (∫ t in (0 : ℝ)..1,
    (TensorRSSpace.toModel ((Ψ t).toSection x)) u)
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm L hΨAppInt]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  change unitModel (I := I) (M := M) g c
      (operatorFieldApply (I := I) (M := M) g b c (A t) W) x v =
    unitModel (I := I) (M := M) g c (Ψ t) x v
  simp only [Ψ, operatorFieldComposition_zero_eq_operatorFieldApply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.operatorFieldApplication_pathIntegralCoeffField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.operatorFieldApplication_pathIntegralCoeffField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.operatorFieldApplication_pathIntegralCoeffField ``Submission.DifferentialGeometry.Integral.L2.operatorFieldApplication_pathIntegralCoeffField

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
theorem pathIntegralCoeffField_add_const
    (g : SmoothRiemannianMetric I M) {b c : ℕ}
    (A : ℝ → SmoothCcTensor g b c) (C : SmoothCcTensor g b c)
    (S : Set ℝ) (hS : IsOpen S) (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun x : M => TensorRSSpace b c I x) p.1
        ((A p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    (hAC : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun x : M => TensorRSSpace b c I x) p.1
        (((A p.2) + C).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    pathIntegralCoeffField (I := I) (M := M) g b c A S hS hSI hA + C =
      pathIntegralCoeffField (I := I) (M := M) g b c
        (fun t => A t + C) S hS hSI hAC := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply TensorRSSpace.toModel_injective
  have hcontA := jointContMDiff_toModel_continuous_slice
    (I := I) g b c A S hA x
  have hAInt : IntervalIntegrable
      (fun t : ℝ => TensorRSSpace.toModel ((A t).toSection x)) _root_.MeasureTheory.MeasureSpace.volume 0 1 :=
    (hcontA.mono hSI).intervalIntegrable
  simp only [pathIntegralCoeffField_toModel, SmoothCcTensor.toSection_add,
    ContMDiffSection.coe_add, Pi.add_apply, TensorRSSpace.toModel_add]
  rw [intervalIntegral.integral_add hAInt intervalIntegrable_const,
    intervalIntegral.integral_const]
  norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.pathIntegralCoeffField_add_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.pathIntegralCoeffField_add_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.pathIntegralCoeffField_add_const ``Submission.DifferentialGeometry.Integral.L2.pathIntegralCoeffField_add_const

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem inner_pathIntegralCoeffField_data
    (g : SmoothRiemannianMetric I M)
    (V : SmoothCcTensor g 0 2) (Φ : ℝ → SmoothCcTensor g 0 2)
    (S : Set ℝ) (hS : IsOpen S) (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun z : M => TensorRSSpace 0 2 I z) q.1
        ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S)) :
    (Inner.inner ℝ V
          (pathIntegralCoeffField (I := I) (M := M) g 0 2 Φ S hS hSI hjoint) =
        ∫ t in (0 : ℝ)..1, Inner.inner ℝ V (Φ t)) ∧
      IntervalIntegrable (fun t : ℝ => Inner.inner ℝ V (Φ t))
        volume 0 1 := by
  classical
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  let : MeasurableSpace ℝ := borel ℝ
  let : BorelSpace ℝ := ⟨rfl⟩
  let μ : _root_.MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g
  let : _root_.MeasureTheory.IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  let Ξ := pathIntegralCoeffField (I := I) (M := M) g 0 2 Φ S hS hSI hjoint
  let F : ℝ → M → ℝ := fun t x =>
    tensorInnerPointwise (I := I) (M := M) g 0 2 x
      (V.toFun x) ((Φ t).toFun x)
  have hIcc : Set.Icc (0 : ℝ) 1 ⊆ S := by
    rw [← Set.uIcc_of_le (zero_le_one (α := ℝ))]
    exact hSI
  have hswapCont : Continuous (fun p : ℝ × M => (p.2, p.1)) := by
    fun_prop
  have hdom : (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) ⊆
      (fun p : ℝ × M => (p.2, p.1)) ⁻¹' ((Set.univ : Set M) ×ˢ S) := by
    rintro ⟨t, x⟩ ⟨ht, -⟩
    exact ⟨Set.mem_univ _, hIcc ht⟩
  have hΦ : ContinuousOn
      (fun p : ℝ × M => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun z : M => TensorRSSpace 0 2 I z) p.2
        ((Φ p.1).toSection p.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) := by
    refine (hjoint.continuousOn.comp hswapCont.continuousOn hdom).congr ?_
    rintro ⟨t, x⟩ -
    rfl
  have hV : ContinuousOn
      (fun p : ℝ × M => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun z : M => TensorRSSpace 0 2 I z) p.2
        (V.toSection p.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) := by
    exact (V.toSection.contMDiff.continuous.comp continuous_snd).continuousOn
  have hinnerMap : ContinuousOn
      (fun p : ℝ × M => TotalSpace.mk'
        (TensorRSModel 0 2 ℝ E →L[ℝ] TensorRSModel 0 2 ℝ E →L[ℝ] ℝ)
        (E := fun x : M =>
          TensorRSSpace 0 2 I x →L[ℝ] TensorRSSpace 0 2 I x →L[ℝ] ℝ)
        p.2
        (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g 0 2 p.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) :=
    ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorRSRiemannianInnerCLM_continuous
      (I := I) (M := M) g 0 2).comp continuous_snd).continuousOn
  have happ : ContinuousOn
      (fun p : ℝ × M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) p.2
        (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g 0 2 p.2
          (V.toSection p.2) ((Φ p.1).toSection p.2)))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) :=
    ContinuousOn.clm_bundle_apply₂
      (F₁ := TensorRSModel 0 2 ℝ E) (F₂ := TensorRSModel 0 2 ℝ E)
      (F₃ := ℝ) (b := fun p : ℝ × M => p.2) hinnerMap hV hΦ
  have hFcont : ContinuousOn (Function.uncurry F)
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) := by
    have hscalar : ContinuousOn
        (fun p : ℝ × M =>
          DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
            (I := I) (M := M) g 0 2 p.2
            (V.toSection p.2) ((Φ p.1).toSection p.2))
        (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) := by
      intro p hp
      have hp2 := ((FiberBundle.continuousWithinAt_totalSpace ℝ
        (fun p : ℝ × M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) p.2
          (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
            (I := I) (M := M) g 0 2 p.2
            (V.toSection p.2) ((Φ p.1).toSection p.2)))).mp (happ p hp)).2
      exact hp2
    refine hscalar.congr ?_
    rintro ⟨t, x⟩ -
    simp only [F, Function.uncurry_apply_pair, SmoothCcTensor.toFun_apply]
    rw [DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_apply]
  have hcompact : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨Cb, hCb⟩ := (hcompact.image_of_continuousOn hFcont.norm).bddAbove
  have huIoc : Set.uIoc (0 : ℝ) 1 = Set.Ioc (0 : ℝ) 1 :=
    Set.uIoc_of_le (by norm_num)
  have : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    constructor
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      huIoc, Real.volume_Ioc]
    simp
  have hprodEq :
      (volume.restrict (Set.uIoc (0 : ℝ) 1)).prod μ =
        (volume.prod μ).restrict
          (Set.uIoc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) := by
    conv_lhs => rw [← Measure.restrict_univ (μ := μ)]
    rw [Measure.prod_restrict]
  have hmeas : _root_.MeasureTheory.AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod μ) := by
    rw [hprodEq]
    refine ContinuousOn.aestronglyMeasurable ?_
      (measurableSet_uIoc.prod MeasurableSet.univ)
    exact hFcont.mono
      (Set.prod_mono (huIoc ▸ Set.Ioc_subset_Icc_self) (subset_refl _))
  have hint : _root_.MeasureTheory.Integrable (Function.uncurry F)
      ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod μ) := by
    refine Integrable.of_mem_Icc (-Cb) Cb hmeas.aemeasurable ?_
    rw [hprodEq]
    have hae : ∀ᵐ p ∂((volume.prod μ).restrict
        (Set.uIoc (0 : ℝ) 1 ×ˢ (Set.univ : Set M))),
        p ∈ Set.uIoc (0 : ℝ) 1 ×ˢ (Set.univ : Set M) :=
      _root_.MeasureTheory.ae_restrict_mem (measurableSet_uIoc.prod MeasurableSet.univ)
    filter_upwards [hae] with p hp
    have hmem : p ∈ Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M) :=
      ⟨(huIoc ▸ Set.Ioc_subset_Icc_self) hp.1, hp.2⟩
    have hb := hCb (Set.mem_image_of_mem _ hmem)
    rw [Real.norm_eq_abs] at hb
    exact ⟨neg_le_of_abs_le hb, le_trans (le_abs_self _) hb⟩
  have hperx : ∀ x : M,
      tensorInnerPointwise (I := I) (M := M) g 0 2 x
          (V.toFun x) (Ξ.toFun x) =
        ∫ t in (0 : ℝ)..1, F t x := by
    intro x
    have hcontΦ := jointContMDiff_toModel_continuous_slice
      (I := I) g 0 2 Φ S hjoint x
    have hΦInt : IntervalIntegrable
        (fun t : ℝ => TensorRSSpace.toModel ((Φ t).toSection x)) _root_.MeasureTheory.MeasureSpace.volume 0 1 :=
      (hcontΦ.mono hSI).intervalIntegrable
    let LV : TensorRSModel 0 2 ℝ E →L[ℝ] ℝ :=
      DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS
        (I := I) (M := M) g 0 2 x (V.toFun x)
    change LV (TensorRSSpace.toModel (Ξ.toSection x)) = _
    rw [show Ξ = pathIntegralCoeffField (I := I) (M := M) g 0 2 Φ S hS hSI hjoint from rfl]
    rw [pathIntegralCoeffField_toModel]
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm LV hΦInt]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    simp only [F]
    rw [DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_apply]
    rfl
  have hleft : Inner.inner ℝ V Ξ =
      ∫ x, (∫ t in (0 : ℝ)..1, F t x) ∂μ := by
    rw [SmoothCcTensor.inner_def]
    unfold tensorL2Inner
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall hperx)
  have hswap :
      (∫ x, (∫ t in (0 : ℝ)..1, F t x) ∂μ) =
        ∫ t in (0 : ℝ)..1, ∫ x, F t x ∂μ :=
    (MeasureTheory.intervalIntegral_integral_swap (μ := μ) (f := F) hint).symm
  have hright : ∀ t : ℝ, Inner.inner ℝ V (Φ t) = ∫ x, F t x ∂μ := by
    intro t
    rw [SmoothCcTensor.inner_def]
    rfl
  have heq : Inner.inner ℝ V
        (pathIntegralCoeffField (I := I) (M := M) g 0 2 Φ S hS hSI hjoint) =
      ∫ t in (0 : ℝ)..1, Inner.inner ℝ V (Φ t) := by
    rw [show pathIntegralCoeffField (I := I) (M := M) g 0 2 Φ S hS hSI hjoint = Ξ from rfl]
    rw [hleft, hswap]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    exact (hright t).symm
  have hpr := hint.integral_prod_left
  change _root_.MeasureTheory.Integrable (fun t : ℝ => ∫ x, F t x ∂μ)
    (volume.restrict (Set.uIoc (0 : ℝ) 1)) at hpr
  have hfun : (fun t : ℝ => ∫ x, F t x ∂μ) =
      fun t : ℝ => Inner.inner ℝ V (Φ t) := by
    funext t
    exact (hright t).symm
  rw [hfun] at hpr
  have hintInner : IntervalIntegrable
      (fun t : ℝ => Inner.inner ℝ V (Φ t)) _root_.MeasureTheory.MeasureSpace.volume 0 1 := by
    rw [intervalIntegrable_iff]
    exact hpr
  exact ⟨heq, hintInner⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.inner_pathIntegralCoeffField_data
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.inner_pathIntegralCoeffField_data target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem inner_pathIntegralCoeffField_eq_intervalIntegral
    (g : SmoothRiemannianMetric I M)
    (V : SmoothCcTensor g 0 2) (Φ : ℝ → SmoothCcTensor g 0 2)
    (S : Set ℝ) (hS : IsOpen S) (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun z : M => TensorRSSpace 0 2 I z) q.1
        ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S)) :
    Inner.inner ℝ V
        (pathIntegralCoeffField (I := I) (M := M) g 0 2 Φ S hS hSI hjoint) =
      ∫ t in (0 : ℝ)..1, Inner.inner ℝ V (Φ t) :=
  (inner_pathIntegralCoeffField_data (I := I) (M := M)
    g V Φ S hS hSI hjoint).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.inner_pathIntegralCoeffField_eq_intervalIntegral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.inner_pathIntegralCoeffField_eq_intervalIntegral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.inner_pathIntegralCoeffField_eq_intervalIntegral ``Submission.DifferentialGeometry.Integral.L2.inner_pathIntegralCoeffField_eq_intervalIntegral

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem intervalIntegrable_inner_of_jointContMDiffOn
    (g : SmoothRiemannianMetric I M)
    (V : SmoothCcTensor g 0 2) (Φ : ℝ → SmoothCcTensor g 0 2)
    (S : Set ℝ) (hS : IsOpen S) (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun z : M => TensorRSSpace 0 2 I z) q.1
        ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S)) :
    IntervalIntegrable (fun t : ℝ => Inner.inner ℝ V (Φ t))
      volume 0 1 :=
  (inner_pathIntegralCoeffField_data (I := I) (M := M)
    g V Φ S hS hSI hjoint).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.intervalIntegrable_inner_of_jointContMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.intervalIntegrable_inner_of_jointContMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.intervalIntegrable_inner_of_jointContMDiffOn ``Submission.DifferentialGeometry.Integral.L2.intervalIntegrable_inner_of_jointContMDiffOn

end DifferentialGeometry.Integral.L2

end
