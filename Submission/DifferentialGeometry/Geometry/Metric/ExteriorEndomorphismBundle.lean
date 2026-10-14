import Submission.DifferentialGeometry.Geometry.Metric.ExteriorEndomorphism
import Submission.DifferentialGeometry.Geometry.Metric.ExteriorPowerRiemannian
import Submission.DifferentialGeometry.Geometry.Metric.ExteriorPowerDualityBundle
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Basis
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.ContDiff _root_.Topology _root_.RealInnerProductSpace

namespace Bundle.ExteriorPower
open _root_.Bundle

variable {B : Type*} [TopologicalSpace B]
  (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  (V : B → Type*) [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  [ChartedSpace HB B]

theorem contMDiffAt_ιMulti (k : ℕ) (n : ℕ∞ω) (Y : Fin k → ∀ x, V x) {x : B}
    (hY : ∀ i, ContMDiffAt IB (IB.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, Y i y⟩ : _root_.Bundle.TotalSpace F V)) x) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := totalSpaceTopology F V k
    letI := fiberBundle F V k
    letI := vector_bundle F V k
    ContMDiffAt IB (IB.prod 𝓘(ℝ, ⋀[ℝ]^k F)) n
      (fun y => (⟨y, exteriorPower.ιMulti ℝ k (fun i => Y i y)⟩ :
        TotalSpace (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x)))) x := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := totalSpaceTopology F V k
  let := fiberBundle F V k
  let := vector_bundle F V k
  rw [_root_.Bundle.contMDiffAt_section]
  have hYc := fun i => (_root_.Bundle.contMDiffAt_section _).mp (hY i)
  have hpi : ContMDiffAt IB 𝓘(ℝ, Fin k → F) n
      (fun y i => (_root_.FiberBundle.trivializationAt F V x ⟨y, Y i y⟩).2) x :=
    contMDiffAt_pi_space.mpr hYc
  have h := ((exteriorPower.contDiff_ιMulti (E := F) k n).contMDiff.contMDiffAt).comp x hpi
  apply h.congr_of_eventuallyEq
  let e := _root_.FiberBundle.trivializationAt F V x
  filter_upwards [e.open_baseSet.mem_nhds (_root_.FiberBundle.mem_baseSet_trivializationAt F V x)] with y hy
  rw [trivializationAt_eq F V k x, trivialization_apply,
    exteriorPower.map_apply_ιMulti]
  change exteriorPower.ιMulti ℝ k
      (fun i => e.continuousLinearMapAt ℝ y (Y i y)) =
    exteriorPower.ιMulti ℝ k (fun i => (e ⟨y, Y i y⟩).2)
  apply congrArg (exteriorPower.ιMulti ℝ k)
  funext i
  exact Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hy (Y i y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.ExteriorPower.contMDiffAt_ιMulti then
    throwError "Refusing to shadow existing declaration Bundle.ExteriorPower.contMDiffAt_ιMulti"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.ExteriorPower.contMDiffAt_ιMulti ``Submission.Bundle.ExteriorPower.contMDiffAt_ιMulti

variable {n : ℕ∞ω} [ContMDiffVectorBundle n F V IB]
  [IsContMDiffRiemannianBundle IB n F V]

theorem contMDiff_endomorphismTensor (k : ℕ) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := totalSpaceTopology F V k
    letI := fiberBundle F V k
    letI := vector_bundle F V k
    ∀ (R : ∀ x, (⋀[ℝ]^k (V x)) →L[ℝ] ⋀[ℝ]^k (V x)),
    ContMDiff IB (IB.prod 𝓘(ℝ, (⋀[ℝ]^k F) →L[ℝ] ⋀[ℝ]^k F)) n
      (fun x => TotalSpace.mk' ((⋀[ℝ]^k F) →L[ℝ] ⋀[ℝ]^k F) x (R x)) →
    ContMDiff IB
      (IB.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin (k + k) => F) ℝ)) n
      (fun x => TotalSpace.mk'
        (ContinuousMultilinearMap ℝ (fun _ : Fin (k + k) => F) ℝ)
        (E := Bundle.continuousMultilinearMap ℝ (k + k) F V) x
        (exteriorPower.endomorphismTensor k (R x))) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := totalSpaceTopology F V k
  let := fiberBundle F V k
  let := vector_bundle F V k
  let := contMDiffVectorBundle (IB := IB) (n := n) F V k
  let := isContMDiffRiemannianBundle (IB := IB) (n := n) F V k
  intro R hR
  let b := Module.finBasis ℝ F
  rw [DifferentialGeometry.Tensor.Multilinear.contMDiff_multilinearSection_iff_coord V n b]
  intro σ x
  let e := _root_.FiberBundle.trivializationAt F V x
  let Y (i : Fin (k + k)) := e.localFrame b (σ i)
  have hY (i) : ContMDiffAt IB (IB.prod 𝓘(ℝ, F)) n (T% (Y i)) x :=
    contMDiffAt_localFrame_of_mem (I := IB) n e b (σ i) (_root_.FiberBundle.mem_baseSet_trivializationAt F V x)
  have hleft := contMDiffAt_ιMulti F V k n (fun i => Y (Fin.castAdd k i))
    (fun i => hY (Fin.castAdd k i))
  have hright := contMDiffAt_ιMulti F V k n (fun i => Y (Fin.natAdd k i))
    (fun i => hY (Fin.natAdd k i))
  have h := ((hR x).clm_bundle_apply hleft).inner_bundle hright
  apply h.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds (_root_.FiberBundle.mem_baseSet_trivializationAt F V x)] with y hy
  rw [DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMap_basis_repr]
  change exteriorPower.endomorphismTensor k (R y)
      (fun i => e.symmL ℝ y (b (σ i))) = _
  rw [exteriorPower.endomorphismTensor_apply]
  simp only [Y, Trivialization.localFrame_apply_of_mem_baseSet e b hy,
    Trivialization.basisAt, Module.Basis.map_apply,
    Trivialization.symmL_apply _ hy]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.ExteriorPower.contMDiff_endomorphismTensor then
    throwError "Refusing to shadow existing declaration Bundle.ExteriorPower.contMDiff_endomorphismTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.ExteriorPower.contMDiff_endomorphismTensor ``Submission.Bundle.ExteriorPower.contMDiff_endomorphismTensor

end Bundle.ExteriorPower
