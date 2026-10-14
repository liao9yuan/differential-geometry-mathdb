import Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.ChartParallelTransportOpNorm.ChristoffelCorrectionModelNormBound
import Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.FiberNorm.FiberNormRiemannianBridge
import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovariantDerivativeBounds.SlotCorrection.Kernel

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace HebeyBlock

open _root_.Submission.DifferentialGeometry.Integral.Measure

open _root_.Submission.DifferentialGeometry.Tensor
open _root_.Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [manifold : IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

private local instance tensorRSRiemannianNormedAddCommGroup
    (r s : ℕ)
    [h : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b)] (b : M) :
    NormedAddCommGroup (TensorRSSpace r s I b) :=
  (h.g.toCore b).toNormedAddCommGroupOfTopology
    (h.g.continuousAt b) (h.g.isVonNBounded b)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.tensorRSRiemannianNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.tensorRSRiemannianNormedAddCommGroup target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma tensorRSTriv_baseSet_eq_chartSource (r s : ℕ) (α : M) :
    (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).baseSet =
      (chartAt H α).source := by
  classical
  change (_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).baseSet ∩
      (_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).baseSet = _
  have h_r : (_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).baseSet =
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := rfl
  have h_s : (_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) α).baseSet =
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := rfl
  rw [h_r, h_s, Set.inter_self,
    DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.tensorRSTriv_baseSet_eq_chartSource
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.tensorRSTriv_baseSet_eq_chartSource target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
include manifold in
private lemma slotConjFactor_self_apply
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) (w : E) :
    (chartTrivializationLinearMap (I := I) (M := M) α b).comp
        ((tangentLinearMapToModel (I := I)
            (chartLeviCivitaParallelCLM (I := I) g α b X)).comp
          (chartTrivializationLinearMapSymm (I := I) (M := M) α b)) w =
      christoffelCorrection (I := I) g α b
        (trivToE (I := I) α b (X b))
        (trivFromE (I := I) α b w) := by
  classical
  have hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := hb
  rw [ContinuousLinearMap.comp_apply]
  change chartTrivializationLinearMap (I := I) (M := M) α b
      (tangentLinearMapToModel (I := I)
        (chartLeviCivitaParallelCLM (I := I) g α b X)
        (chartTrivializationLinearMapSymm (I := I) (M := M) α b w)) = _
  rw [tangentLinearMapToModel_apply]
  rw [chartLeviCivitaParallelCLM_apply (I := I) g α b X
    ((tangentSpaceModelContinuousLinearEquiv (I := I) b).symm
      (chartTrivializationLinearMapSymm (I := I) (M := M) α b w))]
  change trivToE (I := I) α b
      (trivFromE (I := I) α b
        (christoffelCorrection (I := I) g α b
          (trivToE (I := I) α b (X b))
          (trivFromE (I := I) α b w))) = _
  rw [trivToE_trivFromE (I := I) α hb_base]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.slotConjFactor_self_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.slotConjFactor_self_apply target :: scope.openDecls } }

include manifold in
private lemma slotConjFactor_basis_norm_le_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ (k : Fin (Module.finrank ℝ E)),
          ‖(chartTrivializationLinearMap (I := I) (M := M) α b).comp
              ((tangentLinearMapToModel (I := I)
                  (chartLeviCivitaParallelCLM (I := I) g α b
                    (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k))).comp
                (chartTrivializationLinearMapSymm (I := I) (M := M) α b))‖ ≤ C := by
  classical
  obtain ⟨Cχ, hCχ_nn, hCχ_bound⟩ :=
    christoffelCorrection_norm_le_on_pouTsupport (I := I) (M := M) g α
  set Cvec : ℝ :=
    (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sup'
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩)
      (fun k => ‖(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k‖) with hCvec_def
  have hCvec_nn : 0 ≤ Cvec := by
    rw [hCvec_def]
    obtain ⟨k₀, hk₀⟩ :=
      (Finset.univ_nonempty_iff.mpr
        ⟨(⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩ : Fin (Module.finrank ℝ E))⟩)
    exact le_trans (norm_nonneg _)
      (Finset.le_sup' (f := fun k => ‖(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k‖) hk₀)
  refine ⟨Cχ * Cvec, mul_nonneg hCχ_nn hCvec_nn, ?_⟩
  intro b hb k
  have hb_source : b ∈ (chartAt H α).source := by
    have := chartAtlasPOU_isSubordinate (I := I) (M := M) α hb
    exact this
  have hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := hb_source
  have hX_triv :
      trivToE (I := I) α b (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b) =
        (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k := by
    change trivToE (I := I) α b
        (trivFromE (I := I) α b ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)) = _
    exact trivToE_trivFromE (I := I) α hb_base ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)
  have h_basis_le : ‖(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k‖ ≤ Cvec := by
    rw [hCvec_def]
    exact Finset.le_sup' (f := fun k => ‖(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k‖) (Finset.mem_univ k)
  have hpt : ∀ w : E,
      ‖(chartTrivializationLinearMap (I := I) (M := M) α b).comp
          ((tangentLinearMapToModel (I := I)
              (chartLeviCivitaParallelCLM (I := I) g α b
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k))).comp
            (chartTrivializationLinearMapSymm (I := I) (M := M) α b)) w‖ ≤ Cχ * Cvec * ‖w‖ := by
    intro w
    rw [slotConjFactor_self_apply (I := I) (M := M) g α
      (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) hb_source w, hX_triv]
    have hround :
        trivToE (I := I) α b (trivFromE (I := I) α b w) = w :=
      trivToE_trivFromE (I := I) α hb_base w
    have hbound := hCχ_bound (b := b) hb ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)
      (trivFromE (I := I) α b w)
    rw [hround] at hbound
    calc ‖christoffelCorrection (I := I) g α b ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)
            (trivFromE (I := I) α b w)‖
        ≤ Cχ * ‖(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k‖ * ‖w‖ := hbound
      _ ≤ Cχ * Cvec * ‖w‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h_basis_le hCχ_nn) (norm_nonneg _)
  exact ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg hCχ_nn hCvec_nn) hpt

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.slotConjFactor_basis_norm_le_on_pouTsupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.slotConjFactor_basis_norm_le_on_pouTsupport target :: scope.openDecls } }

private lemma slotInputConjCLM_prod_norm_le_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ (k : Fin (Module.finrank ℝ E)) (i : Fin r),
          (∏ j : Fin r,
            ‖slotInputConjCLM (I := I) g r α
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) i b j‖) ≤ C := by
  classical
  obtain ⟨C₀, hC₀_nn, hC₀_bound⟩ :=
    slotConjFactor_basis_norm_le_on_pouTsupport (I := I) (M := M) g α
  refine ⟨(_root_.Max.max C₀ 1) ^ r,
    pow_nonneg (le_trans zero_le_one (le_max_right _ _)) r, ?_⟩
  intro b hb k i
  have h_factor_le : ∀ j : Fin r,
      ‖slotInputConjCLM (I := I) g r α
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) i b j‖ ≤ _root_.Max.max C₀ 1 := by
    intro j
    by_cases hji : j = i
    · subst hji
      rw [slotInputConjCLM_self]
      exact le_trans (hC₀_bound hb k) (le_max_left _ _)
    · rw [slotInputConjCLM_other (I := I) g r α
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) i b hji]
      exact le_trans ContinuousLinearMap.norm_id_le (le_max_right _ _)
  calc (∏ j : Fin r,
        ‖slotInputConjCLM (I := I) g r α
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) i b j‖)
      ≤ ∏ _j : Fin r, _root_.Max.max C₀ 1 :=
        Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => h_factor_le j)
    _ = (_root_.Max.max C₀ 1) ^ r := by rw [Finset.prod_const]; simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.slotInputConjCLM_prod_norm_le_on_pouTsupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.slotInputConjCLM_prod_norm_le_on_pouTsupport target :: scope.openDecls } }

private lemma slotOutputConjCLM_prod_norm_le_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ (k : Fin (Module.finrank ℝ E)) (l : Fin s),
          (∏ j : Fin s,
            ‖slotOutputConjCLM (I := I) g s α
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) l b j‖) ≤ C := by
  classical
  obtain ⟨C₀, hC₀_nn, hC₀_bound⟩ :=
    slotConjFactor_basis_norm_le_on_pouTsupport (I := I) (M := M) g α
  refine ⟨(_root_.Max.max C₀ 1) ^ s,
    pow_nonneg (le_trans zero_le_one (le_max_right _ _)) s, ?_⟩
  intro b hb k l
  have h_factor_le : ∀ j : Fin s,
      ‖slotOutputConjCLM (I := I) g s α
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) l b j‖ ≤ _root_.Max.max C₀ 1 := by
    intro j
    by_cases hjl : j = l
    · subst hjl
      rw [slotOutputConjCLM_self]
      exact le_trans (hC₀_bound hb k) (le_max_left _ _)
    · rw [slotOutputConjCLM_other (I := I) g s α
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) l b hjl]
      exact le_trans ContinuousLinearMap.norm_id_le (le_max_right _ _)
  calc (∏ j : Fin s,
        ‖slotOutputConjCLM (I := I) g s α
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) l b j‖)
      ≤ ∏ _j : Fin s, _root_.Max.max C₀ 1 :=
        Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => h_factor_le j)
    _ = (_root_.Max.max C₀ 1) ^ s := by rw [Finset.prod_const]; simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.slotOutputConjCLM_prod_norm_le_on_pouTsupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.slotOutputConjCLM_prod_norm_le_on_pouTsupport target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma inputSlotChartKernel_apply_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (X : Π b' : M, TangentSpace I b') (i : Fin r) (b : M)
    (S : TensorRSModel r s ℝ E) :
    ‖inputSlotChartKernel (I := I) g r s α X i b S‖ ≤
      (∏ j : Fin r, ‖slotInputConjCLM (I := I) g r α X i b j‖) * ‖S‖ := by
  classical
  rw [inputSlotChartKernel_apply]
  calc ‖S.comp (inputSlotPrecompCLM (I := I) g r α X i b)‖
      ≤ ‖S‖ * ‖inputSlotPrecompCLM (I := I) g r α X i b‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖S‖ * (∏ j : Fin r, ‖slotInputConjCLM (I := I) g r α X i b j‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        unfold inputSlotPrecompCLM
        exact ContinuousMultilinearMap.norm_compContinuousLinearMapL_le
          (𝕜 := ℝ) (E := fun _ : Fin r => E) ℝ
          (slotInputConjCLM (I := I) g r α X i b)
    _ = (∏ j : Fin r, ‖slotInputConjCLM (I := I) g r α X i b j‖) * ‖S‖ := by
        ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.inputSlotChartKernel_apply_norm_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.inputSlotChartKernel_apply_norm_le target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma outputSlotChartKernel_apply_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (X : Π b' : M, TangentSpace I b') (l : Fin s) (b : M)
    (S : TensorRSModel r s ℝ E) :
    ‖outputSlotChartKernel (I := I) g r s α X l b S‖ ≤
      (∏ j : Fin s, ‖slotOutputConjCLM (I := I) g s α X l b j‖) * ‖S‖ := by
  classical
  rw [outputSlotChartKernel_apply]
  calc ‖(outputSlotPostcompCLM (I := I) g s α X l b).comp S‖
      ≤ ‖outputSlotPostcompCLM (I := I) g s α X l b‖ * ‖S‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (∏ j : Fin s, ‖slotOutputConjCLM (I := I) g s α X l b j‖) * ‖S‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        unfold outputSlotPostcompCLM
        exact ContinuousMultilinearMap.norm_compContinuousLinearMapL_le
          (𝕜 := ℝ) (E := fun _ : Fin s => E) ℝ
          (slotOutputConjCLM (I := I) g s α X l b)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.outputSlotChartKernel_apply_norm_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.outputSlotChartKernel_apply_norm_le target :: scope.openDecls } }

attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
theorem chartTensorRSInputSlotCorrection_riemannian_norm_le_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
    ∃ M_F : ℝ, 0 ≤ M_F ∧
      ∀ (T : Π b' : M, TensorRSSpace r s I b') {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ (k : Fin (Module.finrank ℝ E)) (i : Fin r),
          ‖chartTensorRSInputSlotCorrection (I := I) r s g α T
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b i‖ ≤
            M_F * ‖T b‖ := by
  classical
  let _ : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
  have hK_compact : IsCompact (tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
    pouTsupport_isCompact (I := I) (M := M) α
  have hK_sub : tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆ (chartAt H α).source := by
    intro x hx; exact chartAtlasPOU_isSubordinate (I := I) (M := M) α hx
  obtain ⟨Cto, hCto_pos, hCto_bound⟩ :=
    tensorRSChartFiberToModel_opNorm_isBounded_on_compact
      (I := I) (M := M) g r s α hK_compact hK_sub
  obtain ⟨Cfrom, hCfrom_pos, hCfrom_bound⟩ :=
    tensorRSChartFiberFromModel_opNorm_isBounded_on_compact
      (I := I) (M := M) g r s α hK_compact hK_sub
  obtain ⟨Cprod, hCprod_nn, hCprod_bound⟩ :=
    slotInputConjCLM_prod_norm_le_on_pouTsupport (I := I) (M := M) g r α
  refine ⟨Cfrom * Cprod * Cto,
    mul_nonneg (mul_nonneg (le_of_lt hCfrom_pos) hCprod_nn) (le_of_lt hCto_pos), ?_⟩
  intro T b hb k i
  set Y : TensorRSSpace r s I b :=
    chartTensorRSInputSlotCorrection (I := I) r s g α T
      (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b i with hY_def
  have hb_base : b ∈ (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    rw [tensorRSTriv_baseSet_eq_chartSource (I := I) (M := M) r s α]
    exact hK_sub hb
  have h_roundtrip :
      (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).symmL ℝ b
        ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y) = Y :=
    Trivialization.symmL_continuousLinearMapAt _ hb_base Y
  have h_from :
      ‖Y‖ ≤ Cfrom * ‖(_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y‖ := by
    have := hCfrom_bound b hb
      ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y)
    rwa [h_roundtrip] at this
  have h_fact :
      (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y =
        (inputSlotChartKernel (I := I) g r s α
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) i b)
          ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (T b)) :=
    chartTensorRSInputSlotCorrection_chart_kernel_factorization
      (I := I) (M := M) g r s α T (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k)
      (hK_sub hb) i
  have h_kernel :
      ‖(_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y‖ ≤
        Cprod * ‖(_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b (T b)‖ := by
    rw [h_fact]
    refine le_trans (inputSlotChartKernel_apply_norm_le (I := I) (M := M)
      g r s α (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) i b _) ?_
    exact mul_le_mul_of_nonneg_right (hCprod_bound hb k i) (norm_nonneg _)
  have h_to :
      ‖(_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b (T b)‖ ≤
        Cto * ‖T b‖ :=
    hCto_bound b hb (T b)
  have hCto_nn : 0 ≤ Cto := le_of_lt hCto_pos
  have hCfrom_nn : 0 ≤ Cfrom := le_of_lt hCfrom_pos
  calc ‖Y‖
      ≤ Cfrom * ‖(_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y‖ := h_from
    _ ≤ Cfrom * (Cprod * ‖(_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b (T b)‖) :=
        mul_le_mul_of_nonneg_left h_kernel hCfrom_nn
    _ ≤ Cfrom * (Cprod * (Cto * ‖T b‖)) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h_to hCprod_nn) hCfrom_nn
    _ = Cfrom * Cprod * Cto * ‖T b‖ := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.chartTensorRSInputSlotCorrection_riemannian_norm_le_on_pouTsupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.HebeyBlock.chartTensorRSInputSlotCorrection_riemannian_norm_le_on_pouTsupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.chartTensorRSInputSlotCorrection_riemannian_norm_le_on_pouTsupport ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.chartTensorRSInputSlotCorrection_riemannian_norm_le_on_pouTsupport

attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
theorem chartTensorRSOutputSlotCorrection_riemannian_norm_le_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
    ∃ M_F : ℝ, 0 ≤ M_F ∧
      ∀ (T : Π b' : M, TensorRSSpace r s I b') {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ (k : Fin (Module.finrank ℝ E)) (l : Fin s),
          ‖chartTensorRSOutputSlotCorrection (I := I) r s g α T
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b l‖ ≤
            M_F * ‖T b‖ := by
  classical
  let _ : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
  have hK_compact : IsCompact (tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
    pouTsupport_isCompact (I := I) (M := M) α
  have hK_sub : tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆ (chartAt H α).source := by
    intro x hx; exact chartAtlasPOU_isSubordinate (I := I) (M := M) α hx
  obtain ⟨Cto, hCto_pos, hCto_bound⟩ :=
    tensorRSChartFiberToModel_opNorm_isBounded_on_compact
      (I := I) (M := M) g r s α hK_compact hK_sub
  obtain ⟨Cfrom, hCfrom_pos, hCfrom_bound⟩ :=
    tensorRSChartFiberFromModel_opNorm_isBounded_on_compact
      (I := I) (M := M) g r s α hK_compact hK_sub
  obtain ⟨Cprod, hCprod_nn, hCprod_bound⟩ :=
    slotOutputConjCLM_prod_norm_le_on_pouTsupport (I := I) (M := M) g s α
  refine ⟨Cfrom * Cprod * Cto,
    mul_nonneg (mul_nonneg (le_of_lt hCfrom_pos) hCprod_nn) (le_of_lt hCto_pos), ?_⟩
  intro T b hb k l
  set Y : TensorRSSpace r s I b :=
    chartTensorRSOutputSlotCorrection (I := I) r s g α T
      (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b l with hY_def
  have hb_base : b ∈ (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    rw [tensorRSTriv_baseSet_eq_chartSource (I := I) (M := M) r s α]
    exact hK_sub hb
  have h_roundtrip :
      (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).symmL ℝ b
        ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y) = Y :=
    Trivialization.symmL_continuousLinearMapAt _ hb_base Y
  have h_from :
      ‖Y‖ ≤ Cfrom * ‖(_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y‖ := by
    have := hCfrom_bound b hb
      ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y)
    rwa [h_roundtrip] at this
  have h_fact :
      (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y =
        (outputSlotChartKernel (I := I) g r s α
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) l b)
          ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (T b)) :=
    chartTensorRSOutputSlotCorrection_chart_kernel_factorization
      (I := I) (M := M) g r s α T (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k)
      (hK_sub hb) l
  have h_kernel :
      ‖(_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y‖ ≤
        Cprod * ‖(_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b (T b)‖ := by
    rw [h_fact]
    refine le_trans (outputSlotChartKernel_apply_norm_le (I := I) (M := M)
      g r s α (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) l b _) ?_
    exact mul_le_mul_of_nonneg_right (hCprod_bound hb k l) (norm_nonneg _)
  have h_to :
      ‖(_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b (T b)‖ ≤
        Cto * ‖T b‖ :=
    hCto_bound b hb (T b)
  have hCto_nn : 0 ≤ Cto := le_of_lt hCto_pos
  have hCfrom_nn : 0 ≤ Cfrom := le_of_lt hCfrom_pos
  calc ‖Y‖
      ≤ Cfrom * ‖(_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y‖ := h_from
    _ ≤ Cfrom * (Cprod * ‖(_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b (T b)‖) :=
        mul_le_mul_of_nonneg_left h_kernel hCfrom_nn
    _ ≤ Cfrom * (Cprod * (Cto * ‖T b‖)) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h_to hCprod_nn) hCfrom_nn
    _ = Cfrom * Cprod * Cto * ‖T b‖ := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.chartTensorRSOutputSlotCorrection_riemannian_norm_le_on_pouTsupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.HebeyBlock.chartTensorRSOutputSlotCorrection_riemannian_norm_le_on_pouTsupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.chartTensorRSOutputSlotCorrection_riemannian_norm_le_on_pouTsupport ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.chartTensorRSOutputSlotCorrection_riemannian_norm_le_on_pouTsupport

end HebeyBlock
end Sobolev
end Analysis
end DifferentialGeometry

end
