import Submission.DifferentialGeometry.Bundle.SmoothScalarGerm
import Submission.DifferentialGeometry.Geometry.Comparison.Variation.Coordinates.FixedChartIdentities
import Submission.DifferentialGeometry.Geometry.Connection.ChartBridge.Curvature.BasisBracket
import Submission.DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeAlong

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

set_option autoImplicit false

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Function _root_.Manifold _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CovariantDerivativeAlong

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.AlongCurve
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem contMDiff_sum_along
    {ι : Type*} (s : Finset ι) (gamma : Real -> M)
    (V : ι -> forall t, TangentSpace I (gamma t))
    (hgamma : ContMDiff 𝓘(Real, Real) I ∞ gamma)
    (hV : forall i, i ∈ s -> ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun t : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (gamma t) (V i t) : TangentBundle I M))) :
    ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun t : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (gamma t) (∑ i ∈ s, V i t) : TangentBundle I M)) := by
  intro t0
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨hgamma t0, ?_⟩
  have hsum : ContMDiffAt 𝓘(Real, Real) 𝓘(Real, E) ∞
      (fun t : Real =>
        ∑ i ∈ s,
          ((_root_.FiberBundle.trivializationAt E (TangentSpace I) (gamma t0))
            (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
              (gamma t) (V i t))).2) t0 := by
    apply ContMDiffAt.sum
    intro i hi
    exact ((Bundle.contMDiffAt_totalSpace (f := fun t : Real =>
      (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
        (gamma t) (V i t) : TangentBundle I M))).1 (hV i hi t0)).2
  refine hsum.congr_of_eventuallyEq ?_
  have hbase :
      ∀ᶠ t in 𝓝 t0,
        gamma t ∈
          (_root_.FiberBundle.trivializationAt E (TangentSpace I) (gamma t0)).baseSet := by
    have hmem :
        gamma t0 ∈
          (_root_.FiberBundle.trivializationAt E (TangentSpace I) (gamma t0)).baseSet :=
      FiberBundle.mem_baseSet_trivializationAt' (gamma t0)
    exact (hgamma t0).continuousAt.preimage_mem_nhds
      ((_root_.FiberBundle.trivializationAt E (TangentSpace I) (gamma t0)).open_baseSet.mem_nhds
        hmem)
  filter_upwards [hbase] with t ht
  simp only [TotalSpace.mk']
  rw [(_root_.FiberBundle.trivializationAt E (TangentSpace I) (gamma t0)).apply_eq_prod_continuousLinearEquivAt
    Real (gamma t) ht]
  simp_rw [(_root_.FiberBundle.trivializationAt E (TangentSpace I) (gamma t0)).apply_eq_prod_continuousLinearEquivAt
    Real (gamma t) ht]
  rw [map_sum]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.contMDiff_sum_along then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.contMDiff_sum_along"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.contMDiff_sum_along ``Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.contMDiff_sum_along

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem exists_frame_exp
    (gamma : Real -> M) (V : forall s, TangentSpace I (gamma s)) (t : Real)
    (hgamma : ContMDiff 𝓘(Real, Real) I ∞ gamma)
    (hV : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (gamma s) (V s) : TangentBundle I M)))
    (B : Fin (Module.finrank Real E) -> forall x : M, TangentSpace I x)
    (hBnear : ∀ᶠ x in 𝓝 (gamma t), forall i,
      B i x = DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) (gamma t) i x) :
    exists c : Fin (Module.finrank Real E) -> Real -> Real,
      (forall i, ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ∞ (c i)) /\
      (forall i, c i t =
        chartSectionCoord (E := E) (chartRepAt (I := I) gamma V t) i t) /\
      V =ᶠ[𝓝 t] fun s => ∑ i, c i s • B i (gamma s) := by
  classical
  let e := _root_.FiberBundle.trivializationAt E (TangentSpace I) (gamma t)
  let S : Real -> TangentBundle I M := fun s =>
    TotalSpace.mk' E (E := (TangentSpace I : M -> Type _)) (gamma s) (V s)
  let U : Set Real := gamma ⁻¹' e.baseSet
  let cLocal : Fin (Module.finrank Real E) -> Real -> Real :=
    fun i => chartSectionCoord (E := E) (chartRepAt (I := I) gamma V t) i
  have hUopen : IsOpen U :=
    hgamma.continuous.isOpen_preimage _ e.open_baseSet
  have htU : t ∈ U :=
    _root_.FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (gamma t)
  have hSMaps : _root_.Set.MapsTo S U e.source := by
    intro s hs
    exact e.mem_source.mpr hs
  have hcoord :
      ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) ∞
        (fun s => (e (S s)).2) U :=
    (e.contMDiffOn_iff hSMaps).mp hV.contMDiffOn |>.2
  have hcLocalOn : forall i,
      ContMDiffOn 𝓘(Real, Real) 𝓘(Real, Real) ∞ (cLocal i) U := by
    intro i
    refine ((chartCoordCLM (E := E) i).contMDiff.comp_contMDiffOn hcoord).congr ?_
    intro s hs
    change chartCoordCLM (E := E) i
          (e.continuousLinearMapAt Real (gamma s) (V s)) =
        chartCoordCLM (E := E) i ((e (S s)).2)
    congr 1
    rw [e.continuousLinearMapAt_apply (R := Real)]
    rw [e.coe_linearMapAt_of_mem hs]
  have hc : forall i, exists f : Real -> Real,
      ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ∞ f /\
        f =ᶠ[𝓝 t] cLocal i :=
    fun i => exists_smooth_germ (I := 𝓘(Real, Real))
      hUopen htU (hcLocalOn i)
  choose c hcsm hceq using hc
  have hgammaCont : ContinuousAt gamma t := hgamma.continuous.continuousAt
  have hBcurve :
      ∀ᶠ s in 𝓝 t, forall i, B i (gamma s) =
        DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) (gamma t) i (gamma s) :=
    hgammaCont hBnear
  have hbase :
      ∀ᶠ s in 𝓝 t,
        gamma s ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) (gamma t)).baseSet := by
    exact hgammaCont
      ((_root_.FiberBundle.trivializationAt E (TangentSpace I) (gamma t)).open_baseSet.mem_nhds
        (_root_.FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (gamma t)))
  refine ⟨c, hcsm, fun i => (hceq i).self_of_nhds, ?_⟩
  filter_upwards [hBcurve, hbase, Filter.eventually_all.mpr hceq] with
    s hBs hs hcs
  have hcancel :
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) (gamma t)).symmL Real (gamma s)
          ((_root_.FiberBundle.trivializationAt E (TangentSpace I) (gamma t)).continuousLinearMapAt
            Real (gamma s) (V s)) =
        V s :=
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) (gamma t)).symmL_continuousLinearMapAt
      (R := Real) hs (V s)
  rw [← hcancel, symmL_eq_sum_chartBasisVecFiber (I := I)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hcs i, hBs i]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.exists_frame_exp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.exists_frame_exp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.exists_frame_exp ``Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.exists_frame_exp

end CovariantDerivativeAlong
end Riemannian
end Geometry
end DifferentialGeometry
