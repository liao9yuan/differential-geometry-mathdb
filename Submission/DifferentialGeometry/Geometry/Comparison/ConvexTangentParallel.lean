import Submission.DifferentialGeometry.Geometry.Comparison.ConvexTangentSpace
import Submission.DifferentialGeometry.Geometry.Comparison.Nonnegative.RauchParallel

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.HopfRinow
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Variation

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]



omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
private theorem mfderiv_shift {f : ℝ → M} {s : ℝ}
    (hf : MDifferentiableAt 𝓘(ℝ, ℝ) I f s) :
    (mfderiv 𝓘(ℝ, ℝ) I (fun σ : ℝ => f (s + σ)) 0 1 : E)
      = (mfderiv 𝓘(ℝ, ℝ) I f s 1 : E) := by
  have hline : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun σ : ℝ => s + σ) 0
      (ContinuousLinearMap.id ℝ ℝ) :=
    ((hasFDerivAt_id (0 : ℝ)).const_add s).hasMFDerivAt
  have hf0 : MDifferentiableAt 𝓘(ℝ, ℝ) I f ((fun σ : ℝ => s + σ) 0) := by
    simpa only [add_zero] using hf
  have hcomp : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun σ : ℝ => f (s + σ)) 0
      ((mfderiv 𝓘(ℝ, ℝ) I f ((fun σ : ℝ => s + σ) 0)).comp
        (ContinuousLinearMap.id ℝ ℝ)) :=
    HasMFDerivAt.comp (0 : ℝ) hf0.hasMFDerivAt hline
  rw [hcomp.mfderiv]
  exact congrArg (fun t : ℝ => (mfderiv 𝓘(ℝ, ℝ) I f t 1 : E)) (add_zero s)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Topology.mfderiv_shift
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Topology.mfderiv_shift target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
theorem curveVelocity_mem_sliceTangent {S : Set M} {c : ℝ → M} {t : ℝ}
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) I c t)
    (hev : ∀ᶠ σ in 𝓝[>] (0 : ℝ), c (t + σ) ∈ S) :
    (mfderiv 𝓘(ℝ, ℝ) I c t 1 : TangentSpace I (c t)) ∈ sliceTangent I S (c t) := by
  have hline : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun σ : ℝ => t + σ) 0 :=
    (((hasFDerivAt_id (0 : ℝ)).const_add t).hasMFDerivAt).mdifferentiableAt
  have hf0 : MDifferentiableAt 𝓘(ℝ, ℝ) I c ((fun σ : ℝ => t + σ) 0) := by
    simpa only [add_zero] using hc
  have hshift : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun σ : ℝ => c (t + σ)) 0 :=
    MDifferentiableAt.comp (0 : ℝ) hf0 hline
  have h := mem_sliceTangent_of_curve (I := I) (S := S) (f := fun σ : ℝ => c (t + σ))
    (x := c t) (by simp) hev hshift
  have heq : (mfderiv 𝓘(ℝ, ℝ) I c t 1 : TangentSpace I (c t))
      = (mfderiv 𝓘(ℝ, ℝ) I (fun σ : ℝ => c (t + σ)) 0 1 : TangentSpace I (c t)) :=
    (mfderiv_shift hc).symm
  rw [heq]
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.curveVelocity_mem_sliceTangent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.curveVelocity_mem_sliceTangent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.curveVelocity_mem_sliceTangent ``Submission.DifferentialGeometry.Geometry.Topology.curveVelocity_mem_sliceTangent

omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
theorem curveVelocity_intrinsicGeodesic_mem_sliceTangent
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} {y : M} {u : TangentSpace I y} {L : ℝ}
    (hτ : ∀ s ∈ _root_.Set.Icc (0 : ℝ) L,
      intrinsicGeodesic (I := I) g hEnorm y u s ∈ maxSliceLocus I C)
    {t : ℝ} (ht : t ∈ _root_.Set.Ico (0 : ℝ) L) :
    curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm y u) t
      ∈ sliceTangent I (maxSliceLocus I C) (intrinsicGeodesic (I := I) g hEnorm y u t) := by
  have hsmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ (intrinsicGeodesic (I := I) g hEnorm y u) :=
    intrinsicGeodesic_contMDiff (I := I) g hEnorm y u
  have hc : MDifferentiableAt 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm y u) t :=
    hsmooth.contMDiffAt.mdifferentiableAt (by simp)
  have hev : ∀ᶠ σ in 𝓝[>] (0 : ℝ),
      intrinsicGeodesic (I := I) g hEnorm y u (t + σ) ∈ maxSliceLocus I C := by
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 ht.2)] with σ hσ
    exact hτ (t + σ) ⟨by linarith [hσ.1, ht.1], by linarith [hσ.2]⟩
  exact curveVelocity_mem_sliceTangent hc hev

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.curveVelocity_intrinsicGeodesic_mem_sliceTangent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.curveVelocity_intrinsicGeodesic_mem_sliceTangent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.curveVelocity_intrinsicGeodesic_mem_sliceTangent ``Submission.DifferentialGeometry.Geometry.Topology.curveVelocity_intrinsicGeodesic_mem_sliceTangent



theorem parallelShift_mem_maxSliceLocus
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C)
    {y : M} {u : TangentSpace I y}
    {ξ : ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t)} {t : ℝ}
    (hτt : intrinsicGeodesic (I := I) g hEnorm y u t ∈ maxSliceLocus I C)
    (hunit : g.inner (intrinsicGeodesic (I := I) g hEnorm y u t) (ξ t) (ξ t) = 1)
    (hξt : ξ t ∈
      sliceTangent I (maxSliceLocus I C) (intrinsicGeodesic (I := I) g hEnorm y u t))
    {h : ℝ} (hh : |h| < Metric.infDist (intrinsicGeodesic (I := I) g hEnorm y u t)
      (relBoundary I C)) :
    parallelShift (I := I) g hEnorm y u ξ h t ∈ maxSliceLocus I C := by
  have hmem : h • ξ t ∈
      sliceTangent I (maxSliceLocus I C) (intrinsicGeodesic (I := I) g hEnorm y u t) :=
    (sliceTangent I (maxSliceLocus I C)
      (intrinsicGeodesic (I := I) g hEnorm y u t)).smul_mem h hξt
  have hlen : Real.sqrt (g.inner (intrinsicGeodesic (I := I) g hEnorm y u t)
      (h • ξ t) (h • ξ t)) = |h| := by
    rw [gInner_smul_self (I := I) g (intrinsicGeodesic (I := I) g hEnorm y u t) h (ξ t),
      hunit, mul_one, Real.sqrt_sq_eq_abs]
  have hexp := expMapIntrinsic_mem_maxSliceLocus hEnorm hC hCclosed hτt hmem
    (by rw [hlen]; exact hh)
  rw [parallelShift]
  exact hexp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.parallelShift_mem_maxSliceLocus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.parallelShift_mem_maxSliceLocus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.parallelShift_mem_maxSliceLocus ``Submission.DifferentialGeometry.Geometry.Topology.parallelShift_mem_maxSliceLocus

omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
theorem mem_sliceTangent_of_parallelShift_mem
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm (I := I) g}
    {C : Set M} {y : M} {u : TangentSpace I y}
    {ξ : ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t)} {t : ℝ}
    (hmem : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      parallelShift (I := I) g hEnorm y u ξ h t ∈ maxSliceLocus I C) :
    ξ t ∈ sliceTangent I (maxSliceLocus I C)
      (intrinsicGeodesic (I := I) g hEnorm y u t) := by
  refine mem_sliceTangent_of_isInnerDirection (g := g) (hEnorm := hEnorm) (C := C) ?_
  exact hmem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.mem_sliceTangent_of_parallelShift_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.mem_sliceTangent_of_parallelShift_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.mem_sliceTangent_of_parallelShift_mem ``Submission.DifferentialGeometry.Geometry.Topology.mem_sliceTangent_of_parallelShift_mem



def HasSliceParallelTransport (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) (C : Set M) : Prop :=
  ∀ (y : M) (u : TangentSpace I y)
    (ξ : ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t)) (L : ℝ),
    IsParallelPerpUnitField (I := I) g hEnorm y u ξ L →
      (∀ t ∈ _root_.Set.Icc (0 : ℝ) L,
        intrinsicGeodesic (I := I) g hEnorm y u t ∈ maxSliceLocus I C) →
        ξ 0 ∈ sliceTangent I (maxSliceLocus I C)
            (intrinsicGeodesic (I := I) g hEnorm y u 0) →
          ∀ t ∈ _root_.Set.Icc (0 : ℝ) L, ξ t ∈ sliceTangent I (maxSliceLocus I C)
            (intrinsicGeodesic (I := I) g hEnorm y u t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.HasSliceParallelTransport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.HasSliceParallelTransport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.HasSliceParallelTransport ``Submission.DifferentialGeometry.Geometry.Topology.HasSliceParallelTransport

theorem parallelShift_mem_maxSliceLocus_of_sliceParallelTransport
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C)
    (hpar : HasSliceParallelTransport (I := I) g hEnorm C)
    {y : M} {u : TangentSpace I y}
    {ξ : ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t)} {L : ℝ}
    (hξ : IsParallelPerpUnitField (I := I) g hEnorm y u ξ L)
    (hτ : ∀ t ∈ _root_.Set.Icc (0 : ℝ) L,
      intrinsicGeodesic (I := I) g hEnorm y u t ∈ maxSliceLocus I C)
    (hξ0 : ξ 0 ∈ sliceTangent I (maxSliceLocus I C)
      (intrinsicGeodesic (I := I) g hEnorm y u 0))
    {t : ℝ} (ht : t ∈ _root_.Set.Icc (0 : ℝ) L)
    {h : ℝ} (hh : |h| < Metric.infDist (intrinsicGeodesic (I := I) g hEnorm y u t)
      (relBoundary I C)) :
    parallelShift (I := I) g hEnorm y u ξ h t ∈ maxSliceLocus I C :=
  parallelShift_mem_maxSliceLocus hEnorm hC hCclosed (hτ t ht) (hξ.2.2.1 t ht)
    (hpar y u ξ L hξ hτ hξ0 t ht) hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.parallelShift_mem_maxSliceLocus_of_sliceParallelTransport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.parallelShift_mem_maxSliceLocus_of_sliceParallelTransport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.parallelShift_mem_maxSliceLocus_of_sliceParallelTransport ``Submission.DifferentialGeometry.Geometry.Topology.parallelShift_mem_maxSliceLocus_of_sliceParallelTransport

end DifferentialGeometry.Geometry.Topology
