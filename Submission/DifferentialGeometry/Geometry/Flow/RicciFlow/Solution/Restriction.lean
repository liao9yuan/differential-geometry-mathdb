import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.LocalFrameInverse

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

namespace SolutionOn

def timeRestrict
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (D' : DifferentialGeometry.Geometry.Curvature.RealTimeInterval) :
    SolutionOn (I := I) (M := M) D' where
  base := S.base

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.SolutionOn.timeRestrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.SolutionOn.timeRestrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.SolutionOn.timeRestrict ``Submission.DifferentialGeometry.PDE.RicciFlow.SolutionOn.timeRestrict

omit [FiniteDimensional Real E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem timeRestrict_base
    {D D' : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    (S.timeRestrict D').base = S.base := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.SolutionOn.timeRestrict_base then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.SolutionOn.timeRestrict_base"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.SolutionOn.timeRestrict_base ``Submission.DifferentialGeometry.PDE.RicciFlow.SolutionOn.timeRestrict_base

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem timeRestrict_metric
    {D D' : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    (S.timeRestrict D').family.metric t = S.family.metric t := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.SolutionOn.timeRestrict_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.SolutionOn.timeRestrict_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.SolutionOn.timeRestrict_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.SolutionOn.timeRestrict_metric

end SolutionOn

omit [SigmaCompactSpace M] in
theorem isSolutionOn_timeRestrict
    {D D' : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S)
    (hcar : D'.carrier ⊆ D.carrier)
    (hreg : D'.regular ⊆ D.regular) :
    IsSolutionOn (I := I) (S.timeRestrict D') where
  smoothMetric := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x X Y
      simpa [SolutionOn.timeRestrict, SolutionOn.family] using
        (hS.smoothMetric.coeff x X Y).mono hreg
    · intro x X Y
      simpa [SolutionOn.timeRestrict, SolutionOn.family] using
        (hS.smoothMetric.coeff_cont x X Y).mono hcar
    · simpa [SolutionOn.timeRestrict, SolutionOn.family] using
        DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.mono
          (I := I) (M := M) hS.smoothMetric.metricTensor_cont hcar
    · intro Idx _ frame u hframe i j
      simpa [SolutionOn.timeRestrict, SolutionOn.family] using
        (hS.smoothMetric.frameCompSmooth frame hframe i j).mono
          (Set.prod_mono hreg Set.Subset.rfl)
  smoothConnection := by
    intro t
    let t' : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D :=
      ⟨(t : Real), hcar t.2⟩
    simpa [t', SolutionOn.timeRestrict, SolutionOn.family,
      DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.connectionAt] using
      hS.smoothConnection t'
  equation := by
    intro t x X Y
    let t' : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D :=
      ⟨(t : Real), hreg t.2⟩
    simpa [t', MetricVariationEquationOn, SolutionOn.timeRestrict, SolutionOn.family,
      SolutionOn.ricciAt, RicciAtFamily.toTensorField] using
      (hS.equation t' x X Y).mono hcar
  scalarCont := by
    simpa [SolutionOn.timeRestrict, SolutionOn.scalar] using
      hS.scalarCont.mono (Set.prod_mono hcar Set.Subset.rfl)
  scalarTime := by
    intro K t ht hK x
    simpa [SolutionOn.timeRestrict, SolutionOn.scalar] using
      hS.scalarTime ht (fun s hs => hcar (hK hs)) x
  ricciCont := by
    simpa [SolutionOn.timeRestrict, SolutionOn.ricci] using
      DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.mono
        (I := I) (M := M) hS.ricciCont hcar
  rm04Cont := by
    simpa [SolutionOn.timeRestrict] using
      DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.mono
        (I := I) (M := M) hS.rm04Cont hcar
  ricciNormSpace := by
    intro t ht x
    change MDiffAt (ricciNorm (I := I) S t) x
    exact hS.ricciNormSpace t (hcar ht) x
  ricciNormGrad := by
    intro t ht x
    have h := hS.ricciNormGrad t (hcar ht) x
    exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.isSolutionOn_timeRestrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.isSolutionOn_timeRestrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.isSolutionOn_timeRestrict ``Submission.DifferentialGeometry.PDE.RicciFlow.isSolutionOn_timeRestrict

omit [SigmaCompactSpace M] in
theorem isSolutionOn_tailRestrict
    {alpha t₀ omega : Real} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega hαω)}
    (hS : IsSolutionOn (I := I) S)
    (hαt₀ : alpha < t₀) (ht₀ω : t₀ < omega) :
    IsSolutionOn (I := I)
      (S.timeRestrict
        (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen t₀ omega ht₀ω)) := by
  apply isSolutionOn_timeRestrict (I := I) hS
  · intro t ht
    exact ⟨le_of_lt (lt_of_lt_of_le hαt₀ ht.1), ht.2⟩
  · intro t ht
    exact ⟨lt_trans hαt₀ ht.1, ht.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.isSolutionOn_tailRestrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.isSolutionOn_tailRestrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.isSolutionOn_tailRestrict ``Submission.DifferentialGeometry.PDE.RicciFlow.isSolutionOn_tailRestrict

omit [SigmaCompactSpace M] in
theorem tailFrameTimeRegularity
    [IsManifold I 1 M] {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {n : WithTop ℕ∞} {u : Set M}
    {alpha t₀ omega : Real} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega hαω)}
    (hS : IsSolutionOn (I := I) S)
    (hαt₀ : alpha < t₀) (ht₀ω : t₀ < omega)
    (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u) :
    MetricFrameTimeRegularityInFrameOnLocal
      (I := I)
      (S.timeRestrict
        (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen t₀ omega ht₀ω))
      (localFrameInv (I := I)
        (S.timeRestrict
          (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen t₀ omega ht₀ω))
        frame hframe)
      (localFrameInvDt (I := I)
        (S.timeRestrict
          (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen t₀ omega ht₀ω))
        frame hframe)
      frame u := by
  apply localFrameTimeRegularity (I := I)
  · intro x _hx i j
    have hsmooth := hS.smoothMetric.coeff x (frame i x) (frame j x)
    have hsub :
        (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen t₀ omega ht₀ω).carrier
          ⊆
          (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega
            hαω).regular := by
      intro t ht
      exact ⟨lt_of_lt_of_le hαt₀ ht.1, ht.2⟩
    simpa [metricCompInFrame, SolutionOn.timeRestrict, SolutionOn.family] using
      hsmooth.mono hsub
  · intro t
    exact (uniqueDiffOn_Ico t₀ omega).uniqueDiffWithinAt
      ((DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen t₀ omega
        ht₀ω).regular_subset t.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.tailFrameTimeRegularity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.tailFrameTimeRegularity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.tailFrameTimeRegularity ``Submission.DifferentialGeometry.PDE.RicciFlow.tailFrameTimeRegularity

end DifferentialGeometry.PDE.RicciFlow
