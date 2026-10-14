import Submission.DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.ChartTensor0SCovariantDerivative
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Chart.Torsion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

omit [NeZero (Module.finrank ℝ E)] in
omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartParallelExtend_repr_eventuallyEq_const
    (α : M) {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (v : TangentSpace I b) :
    (chartESectionRepr (I := I) α
        (chartParallelExtend (I := I) α b v)) ∘ (extChartAt I α).symm
      =ᶠ[𝓝 (extChartAt I α b)]
      (fun _ : E => trivToE (I := I) α b v) := by
  classical
  set U : Set M := (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet with hU_def
  have hU_open : IsOpen U :=
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).open_baseSet
  have hb_U : b ∈ U :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  have hb_source : b ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb
  have hb_int : extChartAt I α b ∈ interior ((extChartAt I α).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hb
  have hint_open : IsOpen (interior ((extChartAt I α).target : Set E)) :=
    isOpen_interior
  have hsymm_cont : ContinuousAt (extChartAt I α).symm (extChartAt I α b) :=
    continuousAt_extChartAt_symm' hb_source
  have hU_preim_nhds :
      (extChartAt I α).symm ⁻¹' U ∈ 𝓝 (extChartAt I α b) := by
    apply hsymm_cont.preimage_mem_nhds
    have hxφ_inv : (extChartAt I α).symm (extChartAt I α b) = b :=
      (extChartAt I α).left_inv hb_source
    rw [hxφ_inv]
    exact hU_open.mem_nhds hb_U
  have hint_nhds : interior ((extChartAt I α).target : Set E) ∈ 𝓝 (extChartAt I α b) :=
    hint_open.mem_nhds hb_int
  filter_upwards [hU_preim_nhds, hint_nhds] with y hy_U hy_int
  change chartESectionRepr (I := I) α (chartParallelExtend (I := I) α b v)
      ((extChartAt I α).symm y) = trivToE (I := I) α b v
  exact chartE_section_repr_chartParallelExtend (I := I) α b v hy_U

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartParallelExtend_repr_eventuallyEq_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartParallelExtend_repr_eventuallyEq_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartParallelExtend_repr_eventuallyEq_const ``Submission.DifferentialGeometry.Geometry.Connection.chartParallelExtend_repr_eventuallyEq_const

omit [NeZero (Module.finrank ℝ E)] in
omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartParallelExtend_repr_pullback_fderiv_eq_zero
    (α : M) {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (v : TangentSpace I b) :
    fderiv ℝ (chartESectionRepr (I := I) α
        (chartParallelExtend (I := I) α b v) ∘ (extChartAt I α).symm)
      (extChartAt I α b) = 0 := by
  classical
  have hev :=
    chartParallelExtend_repr_eventuallyEq_const (I := I) α hb v
  rw [Filter.EventuallyEq.fderiv_eq hev]
  exact fderiv_const_apply _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartParallelExtend_repr_pullback_fderiv_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartParallelExtend_repr_pullback_fderiv_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartParallelExtend_repr_pullback_fderiv_eq_zero ``Submission.DifferentialGeometry.Geometry.Connection.chartParallelExtend_repr_pullback_fderiv_eq_zero

omit [NeZero (Module.finrank ℝ E)] in
omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartParallelExtend_repr_pullback_fderiv_apply_eq_zero
    (α : M) {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (v : TangentSpace I b) (w : E) :
    fderiv ℝ (chartESectionRepr (I := I) α
        (chartParallelExtend (I := I) α b v) ∘ (extChartAt I α).symm)
      (extChartAt I α b) w = 0 := by
  rw [chartParallelExtend_repr_pullback_fderiv_eq_zero (I := I) α hb v]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartParallelExtend_repr_pullback_fderiv_apply_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartParallelExtend_repr_pullback_fderiv_apply_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartParallelExtend_repr_pullback_fderiv_apply_eq_zero ``Submission.DifferentialGeometry.Geometry.Connection.chartParallelExtend_repr_pullback_fderiv_apply_eq_zero

omit [NeZero (Module.finrank ℝ E)] in
omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem chartLeviCivita_chartParallelExtend
    (g : SmoothRiemannianMetric I M) (α : M)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (v : TangentSpace I b)
    (X : Π b' : M, TangentSpace I b') :
    chartLeviCivita (I := I) g α (chartParallelExtend (I := I) α b v) b (X b) =
      trivFromE (I := I) α b
        (christoffelCorrection (I := I) g α b
          (trivToE (I := I) α b v) (X b)) := by
  classical
  rw [chartLeviCivita_apply (I := I) g α
        (chartParallelExtend (I := I) α b v) hb (X b)]
  have hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  have hrepr :
      chartESectionRepr (I := I) α (chartParallelExtend (I := I) α b v) b =
        trivToE (I := I) α b v :=
    chartE_section_repr_chartParallelExtend (I := I) α b v hb_base
  have hfderiv :
      fderiv ℝ (chartESectionRepr (I := I) α
          (chartParallelExtend (I := I) α b v) ∘ (extChartAt I α).symm)
        (extChartAt I α b) (trivToE (I := I) α b (X b)) = 0 :=
    chartParallelExtend_repr_pullback_fderiv_apply_eq_zero
      (I := I) α hb v (trivToE (I := I) α b (X b))
  rw [hfderiv, hrepr]
  rw [zero_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartLeviCivita_chartParallelExtend then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartLeviCivita_chartParallelExtend"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartLeviCivita_chartParallelExtend ``Submission.DifferentialGeometry.Geometry.Connection.chartLeviCivita_chartParallelExtend

omit [NeZero (Module.finrank ℝ E)] in
omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem chartLeviCivita_chartParallelExtend_symm
    (g : SmoothRiemannianMetric I M) (α : M)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (v : TangentSpace I b)
    (X : Π b' : M, TangentSpace I b') :
    chartLeviCivita (I := I) g α (chartParallelExtend (I := I) α b v) b (X b) =
      trivFromE (I := I) α b
        (christoffelCorrection (I := I) g α b
          (trivToE (I := I) α b (X b)) v) := by
  classical
  rw [chartLeviCivita_chartParallelExtend (I := I) g α hb v X]
  congr 1
  exact (christoffelCorrection_symm_cancel (I := I) g α b v (X b)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartLeviCivita_chartParallelExtend_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartLeviCivita_chartParallelExtend_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartLeviCivita_chartParallelExtend_symm ``Submission.DifferentialGeometry.Geometry.Connection.chartLeviCivita_chartParallelExtend_symm

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
    [T2Space M] in
lemma chartParallelExtend_mdifferentiableAt
    (α : M) {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (v : TangentSpace I b) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b' : M => TotalSpace.mk' E
        (E := fun x : M => TangentSpace I x) b'
        (chartParallelExtend (I := I) α b v b')) b := by
  classical
  set e := _root_.FiberBundle.trivializationAt E (TangentSpace I) α with he_def
  have hb_base : b ∈ e.baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  have hbase_open : IsOpen e.baseSet := e.open_baseSet
  have hbase_nhds : e.baseSet ∈ 𝓝 b := hbase_open.mem_nhds hb_base
  have hconst :
      (fun b' : M => (e ⟨b', chartParallelExtend (I := I) α b v b'⟩).2) =ᶠ[𝓝 b]
        (fun _ : M => trivToE (I := I) α b v) := by
    filter_upwards [hbase_nhds] with b' hb'
    have hcoe := e.coe_linearMapAt_of_mem (R := ℝ) (b := b') hb'
    have happ := congrFun hcoe (chartParallelExtend (I := I) α b v b')
    change (e ⟨b', chartParallelExtend (I := I) α b v b'⟩).2 = trivToE (I := I) α b v
    rw [← happ]
    change (trivToE (I := I) α b') (chartParallelExtend (I := I) α b v b') = trivToE (I := I) α b v
    change (trivToE (I := I) α b') (trivFromE (I := I) α b' (trivToE (I := I) α b v)) =
      trivToE (I := I) α b v
    exact trivToE_trivFromE (I := I) α hb' _
  have hrep_diff :
      MDifferentiableAt I 𝓘(ℝ, E)
        (fun b' : M => (e ⟨b', chartParallelExtend (I := I) α b v b'⟩).2) b :=
    (mdifferentiableAt_const (c := trivToE (I := I) α b v)).congr_of_eventuallyEq hconst
  exact (Trivialization.mdifferentiableAt_section_iff (IB := I) e
    (fun b' : M => chartParallelExtend (I := I) α b v b') hb_base).mpr hrep_diff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartParallelExtend_mdifferentiableAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartParallelExtend_mdifferentiableAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartParallelExtend_mdifferentiableAt ``Submission.DifferentialGeometry.Geometry.Connection.chartParallelExtend_mdifferentiableAt

end Connection
end Geometry
end DifferentialGeometry
