import Submission.DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Agreement.ChartTensor0SCovariantDerivativeAgreement
import Submission.DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.ChartLeviCivitaParallelExtend
import Submission.DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.ChartTensor0SSlotShift
import Submission.DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.Tensor0SIntrinsicChartCurryFactor
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff
open _root_.Submission.DifferentialGeometry.Tensor0SBundle


namespace DifferentialGeometry
namespace Geometry
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Tensor0SNabla
open _root_.Submission.DifferentialGeometry.Tensor0SPartialEval

def TensorSectionMDiffAt (n : ℕ)
    (T : Π b : M, Tensor0SSpace n I b) (b : M) : Prop :=
  letI _h_top : TopologicalSpace (_root_.Bundle.TotalSpace (Tensor0SModel n ℝ E)
      (fun x : M => Tensor0SSpace n I x)) :=
    tensor0SBundleTopology n
  MDifferentiableAt I (I.prod 𝓘(ℝ, Tensor0SModel n ℝ E))
    (fun b' : M => TotalSpace.mk' (Tensor0SModel n ℝ E)
      (E := fun x : M => Tensor0SSpace n I x) b' (T b')) b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.TensorSectionMDiffAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.TensorSectionMDiffAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.TensorSectionMDiffAt ``Submission.DifferentialGeometry.Geometry.Connection.TensorSectionMDiffAt

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
theorem differentiableAt_tensor0SChartE_pullback_of_mdifferentiableAt
    (n : ℕ) (α : M) (T : Π b : M, Tensor0SSpace n I b)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (hT_at : TensorSectionMDiffAt (I := I) n T b) :
    DifferentiableAt ℝ
      (tensor0SChartESectionRepr (I := I) n α T ∘ (extChartAt I α).symm)
      (extChartAt I α b) := by
  classical
  let _h_top : TopologicalSpace (_root_.Bundle.TotalSpace (Tensor0SModel n ℝ E)
      (fun x : M => Tensor0SSpace n I x)) :=
    tensor0SBundleTopology n
  let _h_fib : FiberBundle (Tensor0SModel n ℝ E)
      (fun x : M => Tensor0SSpace n I x) :=
    tensor0SBundleFiber n
  have hb_base_α : b ∈ (_root_.FiberBundle.trivializationAt (Tensor0SModel n ℝ E)
      (fun y : M => Tensor0SSpace n I y) α).baseSet := by
    change b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet
    exact chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  have hα_repr_diff : MDifferentiableAt I 𝓘(ℝ, Tensor0SModel n ℝ E)
      (fun b' : M =>
        ((_root_.FiberBundle.trivializationAt (Tensor0SModel n ℝ E)
            (fun y : M => Tensor0SSpace n I y) α) ⟨b', T b'⟩).2) b :=
    (Trivialization.mdifferentiableAt_section_iff (IB := I)
      (e := _root_.FiberBundle.trivializationAt (Tensor0SModel n ℝ E)
        (fun y : M => Tensor0SSpace n I y) α) T hb_base_α).mp hT_at
  have hα_repr_eq : ∀ {b' : M}, b' ∈ (_root_.FiberBundle.trivializationAt (Tensor0SModel n ℝ E)
      (fun y : M => Tensor0SSpace n I y) α).baseSet →
      ((_root_.FiberBundle.trivializationAt (Tensor0SModel n ℝ E)
          (fun y : M => Tensor0SSpace n I y) α) ⟨b', T b'⟩).2 =
        tensor0SChartESectionRepr (I := I) n α T b' := by
    intro b' hb'
    unfold tensor0SChartESectionRepr
    have hcoe := (_root_.FiberBundle.trivializationAt (Tensor0SModel n ℝ E)
      (fun y : M => Tensor0SSpace n I y) α).coe_linearMapAt_of_mem (R := ℝ) hb'
    have happ := congrFun hcoe (T b')
    exact happ.symm
  have hbase_α_open : IsOpen ((_root_.FiberBundle.trivializationAt (Tensor0SModel n ℝ E)
      (fun y : M => Tensor0SSpace n I y) α).baseSet) :=
    (_root_.FiberBundle.trivializationAt (Tensor0SModel n ℝ E)
      (fun y : M => Tensor0SSpace n I y) α).open_baseSet
  have hbase_α_nhds : (_root_.FiberBundle.trivializationAt (Tensor0SModel n ℝ E)
      (fun y : M => Tensor0SSpace n I y) α).baseSet ∈ 𝓝 b :=
    hbase_α_open.mem_nhds hb_base_α
  have h_funeq :
      tensor0SChartESectionRepr (I := I) n α T =ᶠ[𝓝 b]
      (fun b' : M =>
        ((_root_.FiberBundle.trivializationAt (Tensor0SModel n ℝ E)
            (fun y : M => Tensor0SSpace n I y) α) ⟨b', T b'⟩).2) := by
    filter_upwards [hbase_α_nhds] with b' hb' using (hα_repr_eq hb').symm
  have hrepr_α_diff : MDifferentiableAt I 𝓘(ℝ, Tensor0SModel n ℝ E)
      (tensor0SChartESectionRepr (I := I) n α T) b :=
    hα_repr_diff.congr_of_eventuallyEq h_funeq
  have hb_source : b ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb
  have hb_int : extChartAt I α b ∈ interior ((extChartAt I α).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hb
  have hpb := mdifferentiableAt_iff_source_of_mem_source (I := I)
    (E' := Tensor0SModel n ℝ E) (I' := 𝓘(ℝ, Tensor0SModel n ℝ E)) (x := α)
    (f := tensor0SChartESectionRepr (I := I) n α T) hb_source
  have hwithin : MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, Tensor0SModel n ℝ E)
      (tensor0SChartESectionRepr (I := I) n α T ∘ (extChartAt I α).symm)
      (_root_.Set.range I) (extChartAt I α b) := hpb.mp hrepr_α_diff
  have htgt_subset : (extChartAt I α).target ⊆ _root_.Set.range I :=
    extChartAt_target_subset_range α
  have hint_open : IsOpen (interior ((extChartAt I α).target : Set E)) :=
    isOpen_interior
  have hrange_nhds : _root_.Set.range I ∈ 𝓝 (extChartAt I α b) :=
    Filter.mem_of_superset (hint_open.mem_nhds hb_int)
      (interior_subset.trans htgt_subset)
  rw [mdifferentiableWithinAt_iff_differentiableWithinAt] at hwithin
  exact hwithin.differentiableAt hrange_nhds

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.differentiableAt_tensor0SChartE_pullback_of_mdifferentiableAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.differentiableAt_tensor0SChartE_pullback_of_mdifferentiableAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.differentiableAt_tensor0SChartE_pullback_of_mdifferentiableAt ``Submission.DifferentialGeometry.Geometry.Connection.differentiableAt_tensor0SChartE_pullback_of_mdifferentiableAt

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
theorem mdifferentiableAt_curriedSection_of_section
    (s : ℕ) (T : Π b : M, Tensor0SSpace (s + 1) I b) {b : M}
    (hT_at : TensorSectionMDiffAt (I := I) (s + 1) T b) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E))
      (fun b' : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace s I y)
        b' (curriedSection I M T b')) b :=
  (mdifferentiableAt_curriedSection_iff_section (I := I) (M := M) T).mp hT_at

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.mdifferentiableAt_curriedSection_of_section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.mdifferentiableAt_curriedSection_of_section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.mdifferentiableAt_curriedSection_of_section ``Submission.DifferentialGeometry.Geometry.Connection.mdifferentiableAt_curriedSection_of_section

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
theorem TensorSectionMDiffAt_partialEval
    (s : ℕ) (α : M)
    (T : Π b : M, Tensor0SSpace (s + 1) I b)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (hT_at : TensorSectionMDiffAt (I := I) (s + 1) T b)
    (v : TangentSpace I b) :
    TensorSectionMDiffAt (I := I) s
      (tensor0SPartialEval I M T (chartParallelExtend (I := I) α b v)) b := by
  classical
  unfold TensorSectionMDiffAt
  let _h_top : TopologicalSpace (_root_.Bundle.TotalSpace (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x)) :=
    tensor0SBundleTopology s
  have hY_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b' : M => TotalSpace.mk' E
        (E := fun x : M => TangentSpace I x) b'
        (chartParallelExtend (I := I) α b v b')) b :=
    chartParallelExtend_mdifferentiableAt (I := I) α hb v
  have hCurried_at := mdifferentiableAt_curriedSection_of_section
    (I := I) (M := M) s T hT_at
  exact MDifferentiableAt.clm_bundle_apply (𝕜 := ℝ)
    (F₁ := E) (F₂ := Tensor0SModel s ℝ E)
    (E₁ := fun x : M => TangentSpace I x)
    (E₂ := fun x : M => Tensor0SSpace s I x)
    (IM := I) (IB := I)
    (b := id) (ϕ := fun b' : M => curriedSection I M T b')
    (v := fun b' : M => chartParallelExtend (I := I) α b v b')
    hCurried_at hY_at

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.TensorSectionMDiffAt_partialEval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.TensorSectionMDiffAt_partialEval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.TensorSectionMDiffAt_partialEval ``Submission.DifferentialGeometry.Geometry.Connection.TensorSectionMDiffAt_partialEval

end Connection
end Geometry
end DifferentialGeometry
