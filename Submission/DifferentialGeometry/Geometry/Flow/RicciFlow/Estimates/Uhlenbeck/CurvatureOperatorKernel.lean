import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.Isometry
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.BundleEquivalence
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.KernelNaturality
import Submission.DifferentialGeometry.Geometry.Connection.Pullback
import Submission.DifferentialGeometry.Geometry.Connection.ParallelTransport.Pullback

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Variation
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]

noncomputable def uhlenbeckEndomorphismLinearEquivAt
    {T : Real} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basisAt : ∀ x : M, Module.Basis Idx Real (TangentSpace I x))
    (iota : MatrixComp M Idx)
    (hiota0 : ∀ x : M, ∀ a k : Idx, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : Real, t ∈ _root_.Set.Icc 0 T → ∀ x : M, ∀ a b : Idx,
      movingFrameGramInFrame
          (metricCompInFrame (I := I) S (fun a x => basisAt x a))
          iota t x a b =
        movingFrameGramInFrame
          (metricCompInFrame (I := I) S (fun a x => basisAt x a))
          iota 0 x a b)
    {t : Real} (ht : t ∈ _root_.Set.Icc 0 T) (x : M) :
    TangentSpace I x ≃ₗ[Real] TangentSpace I x :=
  LinearEquiv.ofBijective
    (uhlenbeckEndomorphismAt (basisAt x) iota t).toLinearMap
    (uhlenbeckEndomorphism_invertible hT S basisAt iota hiota0 hgram ht x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uhlenbeckEndomorphismLinearEquivAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uhlenbeckEndomorphismLinearEquivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uhlenbeckEndomorphismLinearEquivAt ``Submission.DifferentialGeometry.PDE.RicciFlow.uhlenbeckEndomorphismLinearEquivAt

omit [T2Space M] in
@[simp] theorem uhlenbeckEndomorphismLinearEquivAt_apply
    {T : Real} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basisAt : ∀ x : M, Module.Basis Idx Real (TangentSpace I x))
    (iota : MatrixComp M Idx)
    (hiota0 : ∀ x : M, ∀ a k : Idx, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : Real, t ∈ _root_.Set.Icc 0 T → ∀ x : M, ∀ a b : Idx,
      movingFrameGramInFrame
          (metricCompInFrame (I := I) S (fun a x => basisAt x a))
          iota t x a b =
        movingFrameGramInFrame
          (metricCompInFrame (I := I) S (fun a x => basisAt x a))
          iota 0 x a b)
    {t : Real} (ht : t ∈ _root_.Set.Icc 0 T) (x : M) (v : TangentSpace I x) :
    uhlenbeckEndomorphismLinearEquivAt hT S basisAt iota hiota0 hgram ht x v =
      uhlenbeckEndomorphismAt (basisAt x) iota t v :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uhlenbeckEndomorphismLinearEquivAt_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uhlenbeckEndomorphismLinearEquivAt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uhlenbeckEndomorphismLinearEquivAt_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.uhlenbeckEndomorphismLinearEquivAt_apply

theorem uhlenbeckPulledRm04At_eq_pullback
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    {T : Real} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basisAt : ∀ x : M, Module.Basis Idx Real (TangentSpace I x))
    (iota : MatrixComp M Idx)
    (hiota0 : ∀ x : M, ∀ a k : Idx, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : Real, t ∈ _root_.Set.Icc 0 T → ∀ x : M, ∀ a b : Idx,
      movingFrameGramInFrame
          (metricCompInFrame (I := I) S (fun a x => basisAt x a))
          iota t x a b =
        movingFrameGramInFrame
          (metricCompInFrame (I := I) S (fun a x => basisAt x a))
          iota 0 x a b)
    {t : Real} (ht : t ∈ _root_.Set.Icc 0 T) (x : M) :
    (⟨uhlenbeckPulledRm04At S basisAt iota t x,
        uhlenbeckPulledRm04At_mem_algebraicCurvatureTensorSubmodule
          S basisAt iota t x⟩ :
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x) =
      algebraicCurvatureTensorPullbackCLE
        (uhlenbeckEndomorphismLinearEquivAt
          hT S basisAt iota hiota0 hgram ht x)
        ⟨S.base.rm04 t x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (S.base.metric t) x⟩ := by
  apply Subtype.ext
  apply tensor0SSpace_ext 4 x
  intro v
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uhlenbeckPulledRm04At_eq_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uhlenbeckPulledRm04At_eq_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uhlenbeckPulledRm04At_eq_pullback ``Submission.DifferentialGeometry.PDE.RicciFlow.uhlenbeckPulledRm04At_eq_pullback

theorem curvatureOperatorKernelAt_map_uhlenbeckEndomorphism
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    {T : Real} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basisAt : ∀ x : M, Module.Basis Idx Real (TangentSpace I x))
    (iota : MatrixComp M Idx)
    (hiota0 : ∀ x : M, ∀ a k : Idx, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : Real, t ∈ _root_.Set.Icc 0 T → ∀ x : M, ∀ a b : Idx,
      movingFrameGramInFrame
          (metricCompInFrame (I := I) S (fun a x => basisAt x a))
          iota t x a b =
        movingFrameGramInFrame
          (metricCompInFrame (I := I) S (fun a x => basisAt x a))
          iota 0 x a b)
    {t : Real} (ht : t ∈ _root_.Set.Icc 0 T) (x : M) :
    let e := uhlenbeckEndomorphismLinearEquivAt
      hT S basisAt iota hiota0 hgram ht x
    Submodule.map
        (e.toContinuousLinearEquiv.continuousAlternatingMapCongrLeft
          (ι := Fin 2)).toLinearMap
        (curvatureOperatorKernelAt (I := I) (S.family.metric 0) x
          ⟨uhlenbeckPulledRm04At S basisAt iota t x,
            uhlenbeckPulledRm04At_mem_algebraicCurvatureTensorSubmodule
              S basisAt iota t x⟩) =
      curvatureOperatorKernelAt (I := I) (S.family.metric t) x
        ⟨S.base.rm04 t x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (S.base.metric t) x⟩ := by
  dsimp only
  rw [uhlenbeckPulledRm04At_eq_pullback
    hT S basisAt iota hiota0 hgram ht x]
  apply curvatureOperatorKernelAt_map_congrLeft
  intro v w
  exact uhlenbeckEndomorphism_isometry
    hT S basisAt iota hiota0 hgram ht x v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.curvatureOperatorKernelAt_map_uhlenbeckEndomorphism then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.curvatureOperatorKernelAt_map_uhlenbeckEndomorphism"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.curvatureOperatorKernelAt_map_uhlenbeckEndomorphism ``Submission.DifferentialGeometry.PDE.RicciFlow.curvatureOperatorKernelAt_map_uhlenbeckEndomorphism

omit [T2Space M] in
theorem uhlenbeckEndomorphism_parallelTransport_intertwining
    [I.Boundaryless]
    {T : Real} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basisAt : ∀ x : M, Module.Basis Idx Real (TangentSpace I x))
    (iota : MatrixComp M Idx)
    (hiota0 : ∀ x : M, ∀ a k : Idx, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : Real, t ∈ _root_.Set.Icc 0 T → ∀ x : M, ∀ a b : Idx,
      movingFrameGramInFrame
          (metricCompInFrame (I := I) S (fun a x => basisAt x a))
          iota t x a b =
        movingFrameGramInFrame
          (metricCompInFrame (I := I) S (fun a x => basisAt x a))
          iota 0 x a b)
    {t : Real} (ht : t ∈ _root_.Set.Icc 0 T)
    (gamma : Real → M)
    (hgamma : ContMDiff 𝓘(Real, Real) I (2 : ℕ∞) gamma)
    {a b : Real} (hab : a < b) :
    let phi := fun x => uhlenbeckEndomorphismLinearEquivAt
      hT S basisAt iota hiota0 hgram ht x
    let PSource :=
      (_root_.Submission.CovariantDerivative.pullbackParallelTransportLinearEquivBetween
        phi (S.family.metric t) gamma hgamma hab).toContinuousLinearEquiv
    let PTarget :=
      (parallelTransportLinearEquivBetween
        (I := I) (S.family.metric t) gamma hgamma hab).toContinuousLinearEquiv
    let FSource := (phi (gamma a)).toContinuousLinearEquiv
      |>.continuousAlternatingMapCongrLeft (ι := Fin 2) (F := Real)
    let FTarget := (phi (gamma b)).toContinuousLinearEquiv
      |>.continuousAlternatingMapCongrLeft (ι := Fin 2) (F := Real)
    FTarget.toLinearMap.comp
        (PSource.continuousAlternatingMapCongrLeft
          (ι := Fin 2) (F := Real)).toLinearMap =
      (PTarget.continuousAlternatingMapCongrLeft
        (ι := Fin 2) (F := Real)).toLinearMap.comp FSource.toLinearMap := by
  dsimp only
  exact _root_.Submission.CovariantDerivative.pullbackParallelTransportContinuousAlternatingMap_intertwining
      (fun x => uhlenbeckEndomorphismLinearEquivAt
        hT S basisAt iota hiota0 hgram ht x)
      (S.family.metric t) gamma hgamma hab

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uhlenbeckEndomorphism_parallelTransport_intertwining then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uhlenbeckEndomorphism_parallelTransport_intertwining"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uhlenbeckEndomorphism_parallelTransport_intertwining ``Submission.DifferentialGeometry.PDE.RicciFlow.uhlenbeckEndomorphism_parallelTransport_intertwining

theorem exists_uhlenbeck_curvatureOperatorKernel_intertwining
    [I.Boundaryless]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    {T : Real} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    {s t : Real} (hs : 0 < s) (hst : s < t) (htT : t < T) :
    ∃ (phi : ∀ x : M, TangentSpace I x ≃ₗ[Real] TangentSpace I x)
      (hphi : ContMDiff (I.prod 𝓘(Real, E)) (I.prod 𝓘(Real, E)) ∞
        (fun p : TangentBundle I M =>
          (⟨p.1, phi p.1 p.2⟩ : TangentBundle I M))),
      ContMDiff (I.prod 𝓘(Real, E)) (I.prod 𝓘(Real, E)) ∞
        (fun p : TangentBundle I M =>
          (⟨p.1, (phi p.1).symm p.2⟩ : TangentBundle I M)) ∧
      (∀ x : M, ∀ v w : TangentSpace I x,
        (S.family.metric t).inner x (phi x v) (phi x w) =
          (S.family.metric s).inner x v w) ∧
      (let cov := leviCivitaConnectionOfMetric (I := I) (S.family.metric t)
       let D := _root_.Submission.CovariantDerivative.pullbackFiberwiseLinearEquiv
         phi (hphi.of_le (by norm_num)) cov
       ∀ (sigma : ∀ x : M, TangentSpace I x) (x : M) (X : TangentSpace I x),
         phi x (D sigma x X) = cov (fun y => phi y (sigma y)) x X) ∧
      (∀ x : M,
        let A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
          ⟨S.base.rm04 t x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (S.base.metric t) x⟩
        let e := (phi x).toContinuousLinearEquiv
          |>.continuousAlternatingMapCongrLeft (ι := Fin 2) (F := Real)
        Submodule.map e.toLinearMap
            (curvatureOperatorKernelAt (I := I) (S.family.metric s) x
              (algebraicCurvatureTensorPullbackCLE (I := I) (M := M)
                (phi x) A)) =
          curvatureOperatorKernelAt (I := I) (S.family.metric t) x A) ∧
      ∀ (gamma : Real → M)
        (hgamma : ContMDiff 𝓘(Real, Real) I (2 : ℕ∞) gamma)
        {a b : Real} (hab : a < b),
        let PSource :=
          (_root_.Submission.CovariantDerivative.pullbackParallelTransportLinearEquivBetween
            phi (S.family.metric t) gamma hgamma hab).toContinuousLinearEquiv
        let PTarget :=
          (parallelTransportLinearEquivBetween
            (I := I) (S.family.metric t) gamma hgamma hab).toContinuousLinearEquiv
        let FSource := (phi (gamma a)).toContinuousLinearEquiv
          |>.continuousAlternatingMapCongrLeft (ι := Fin 2) (F := Real)
        let FTarget := (phi (gamma b)).toContinuousLinearEquiv
          |>.continuousAlternatingMapCongrLeft (ι := Fin 2) (F := Real)
        FTarget.toLinearMap.comp
            (PSource.continuousAlternatingMapCongrLeft
              (ι := Fin 2) (F := Real)).toLinearMap =
          (PTarget.continuousAlternatingMapCongrLeft
            (ι := Fin 2) (F := Real)).toLinearMap.comp FSource.toLinearMap := by
  obtain ⟨phi, hphi, hphiInv, hiso⟩ :=
    exists_uhlenbeck_tangent_bundle_isometry
      (I := I) (M := M) hT S hS hs hst htT
  refine ⟨phi, hphi, hphiInv, hiso, ?_, ?_, ?_⟩
  · dsimp only
    intro sigma x X
    exact _root_.Submission.CovariantDerivative.map_pullbackFiberwiseLinearEquiv_apply
      phi (hphi.of_le (by norm_num)) _ sigma x X
  · intro x
    dsimp only
    apply curvatureOperatorKernelAt_map_congrLeft
    exact hiso x
  · intro gamma hgamma a b hab
    dsimp only
    exact _root_.Submission.CovariantDerivative.pullbackParallelTransportContinuousAlternatingMap_intertwining
      phi (S.family.metric t) gamma hgamma hab

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_uhlenbeck_curvatureOperatorKernel_intertwining then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_uhlenbeck_curvatureOperatorKernel_intertwining"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_uhlenbeck_curvatureOperatorKernel_intertwining ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_uhlenbeck_curvatureOperatorKernel_intertwining

end DifferentialGeometry.PDE.RicciFlow
