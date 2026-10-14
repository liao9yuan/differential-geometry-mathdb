import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.InverseSmooth

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle

open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]
variable [SigmaCompactSpace M] [T2Space M]

section Components

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {n : WithTop ℕ∞} {u : Set M}

noncomputable def localFrameInv
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u) :
    Real → DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx :=
  by
    classical
    exact fun t x i j =>
      if hx : x ∈ u then
        basisInvMetric (I := I) (M := M) (S.family.metric t) x
          (hframe.toBasisAt hx) i j
      else 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.localFrameInv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.localFrameInv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.localFrameInv ``Submission.DifferentialGeometry.PDE.RicciFlow.localFrameInv

omit [Fintype Idx] [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem localFrameInv_of_mem
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    {x : M} (hx : x ∈ u) (t : Real) (i j : Idx) :
    localFrameInv (I := I) S frame hframe t x i j =
      basisInvMetric (I := I) (M := M) (S.family.metric t) x
        (hframe.toBasisAt hx) i j := by
  simp [localFrameInv, hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.localFrameInv_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.localFrameInv_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.localFrameInv_of_mem ``Submission.DifferentialGeometry.PDE.RicciFlow.localFrameInv_of_mem

omit [SigmaCompactSpace M] [T2Space M] in
theorem localFrameInv_real
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u) :
    InvMetricLocal (I := I) S (localFrameInv (I := I) S frame hframe) frame u := by
  intro t x hx i j
  have hreal :=
    basisInvMetric_isInverse (I := I) (M := M) (g := S.family.metric t) (x := x)
      (basis := hframe.toBasisAt hx)
  simpa [metricCompInFrame, localFrameInv_of_mem (I := I) S frame hframe hx,
    hframe.toBasisAt_coe] using hreal i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.localFrameInv_real then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.localFrameInv_real"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.localFrameInv_real ``Submission.DifferentialGeometry.PDE.RicciFlow.localFrameInv_real

omit [SigmaCompactSpace M] [T2Space M] in
private theorem frameGram_time
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx → (x : M) → TangentSpace I x)
    {K : Set Real} (x : M)
    (hmetric : ∀ i j : Idx, ContDiffOn Real ∞
      (fun t : Real => metricCompInFrame (I := I) S frame t x i j) K) :
    ContDiffOn Real ∞
      (fun t : Real => frameGramCLM (I := I) S frame (t, x)) K := by
  classical
  unfold frameGramCLM
  apply ContDiffOn.sum
  intro i _hi
  apply ContDiffOn.sum
  intro j _hj
  exact (hmetric i j).smul contDiffOn_const

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.frameGram_time
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.frameGram_time target :: scope.openDecls } }

omit [Fintype Idx] [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem localFrameInv_time
    [Finite Idx]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    {K : Set Real}
    (hmetric : ∀ x : M, x ∈ u → ∀ i j : Idx, ContDiffOn Real ∞
      (fun t : Real => metricCompInFrame (I := I) S frame t x i j) K)
    (x : M) (i j : Idx) :
    ContDiffOn Real ∞
      (fun t : Real => localFrameInv (I := I) S frame hframe t x i j) K := by
  classical
  let := Fintype.ofFinite Idx
  by_cases hx : x ∈ u
  · have hgram := frameGram_time (I := I) S frame x (hmetric x hx)
    have hinvSmooth : ContDiffOn Real ∞
        (fun t : Real => ContinuousLinearMap.inverse
          (frameGramCLM (I := I) S frame (t, x))) K := by
      intro t ht
      have hinv :=
        frameGramCLM_isInvertible_at (I := I) S
          (localFrameInv (I := I) S frame hframe) frame (t, x)
          (fun a b => (localFrameInv_real (I := I) S frame hframe t x hx a b).1)
          (fun a b => (localFrameInv_real (I := I) S frame hframe t x hx a b).2)
      have hinvAt : ContDiffAt Real ∞ ContinuousLinearMap.inverse
          (frameGramCLM (I := I) S frame (t, x)) :=
        hinv.contDiffAt_map_inverse
      simpa [Function.comp_def] using
        hinvAt.comp_contDiffWithinAt t (hgram t ht)
    have happ : ContDiffOn Real ∞
        (fun t : Real => ContinuousLinearMap.inverse
          (frameGramCLM (I := I) S frame (t, x)) (Pi.single j 1)) K :=
      hinvSmooth.clm_apply contDiffOn_const
    have hcoord : ContDiffOn Real ∞
        (fun t : Real => ContinuousLinearMap.inverse
          (frameGramCLM (I := I) S frame (t, x)) (Pi.single j 1) i) K :=
      (contDiffOn_const (c := LinearMap.toContinuousLinearMap
        (LinearMap.proj (R := Real) (φ := fun _ : Idx => Real) i))).clm_apply happ
    refine hcoord.congr ?_
    intro t _ht
    rw [frameGInvCLM_eq_inverse_at (I := I) S
      (localFrameInv (I := I) S frame hframe) frame (t, x)
      (fun a b => (localFrameInv_real (I := I) S frame hframe t x hx a b).1)
      (fun a b => (localFrameInv_real (I := I) S frame hframe t x hx a b).2)]
    simpa using
      (sum_mul_pi_single (Idx := Idx)
        (fun k => localFrameInv (I := I) S frame hframe t x i k) j).symm
  · simpa [localFrameInv, hx] using
      (contDiffOn_const (c := (0 : Real)) :
        ContDiffOn Real ∞ (fun _ : Real => (0 : Real)) K)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.localFrameInv_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.localFrameInv_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.localFrameInv_time ``Submission.DifferentialGeometry.PDE.RicciFlow.localFrameInv_time

noncomputable def localFrameInvDt
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u) :
    Real → M → Idx → Idx → Real :=
  fun t x i j => derivWithin
    (fun s : Real => localFrameInv (I := I) S frame hframe s x i j)
    D.carrier t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.localFrameInvDt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.localFrameInvDt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.localFrameInvDt ``Submission.DifferentialGeometry.PDE.RicciFlow.localFrameInvDt

omit [SigmaCompactSpace M] [T2Space M] in
theorem localFrameTimeRegularity
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    (hmetric : ∀ x : M, x ∈ u → ∀ i j : Idx, ContDiffOn Real ∞
      (fun t : Real => metricCompInFrame (I := I) S frame t x i j) D.carrier)
    (hunique : ∀ t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D,
      UniqueDiffWithinAt Real D.carrier (t : Real)) :
    MetricFrameTimeRegularityInFrameOnLocal
      (I := I) S (localFrameInv (I := I) S frame hframe)
      (localFrameInvDt (I := I) S frame hframe) frame u where
  metricSmooth := hmetric
  nondegenerateGram := localFrameInv_real (I := I) S frame hframe
  inverseMetricDerivative := by
    intro t x _hx i j
    have hdiff :=
      (localFrameInv_time (I := I) S frame hframe hmetric x i j).differentiableOn
        (by simp) (t : Real) (D.regular_subset t.2)
    simpa [localFrameInvDt] using hdiff.hasDerivWithinAt
  uniqueTimeDerivatives := hunique

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.localFrameTimeRegularity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.localFrameTimeRegularity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.localFrameTimeRegularity ``Submission.DifferentialGeometry.PDE.RicciFlow.localFrameTimeRegularity

end Components

end DifferentialGeometry.PDE.RicciFlow
