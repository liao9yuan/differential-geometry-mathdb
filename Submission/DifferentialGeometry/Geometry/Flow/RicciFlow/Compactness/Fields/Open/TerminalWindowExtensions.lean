import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.WindowRestriction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalBackwardExtension
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Restriction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.PointedPullbackExtensions
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.TimeLipschitz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Set _root_.Submission.Set _root_.Filter
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

def StaticTerminalLimit.windowSequence {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) (hdepth : 0 ≤ depthBound) :
    PointedFlowSeq.{u, 0, 0} I3 :=
  X.timeRestrict (RealTimeInterval.closed (-depthBound) 0 (neg_nonpos.mpr hdepth))
    L.carrier_window L.regular_window

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StaticTerminalLimit.windowSequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StaticTerminalLimit.windowSequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StaticTerminalLimit.windowSequence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StaticTerminalLimit.windowSequence

@[simp] theorem StaticTerminalLimit.windowSequence_atTime
    {X : FlowSequence.{u}} {depthBound : ℝ} (L : StaticTerminalLimit X depthBound)
    (hdepth : 0 ≤ depthBound) (t : ℝ) :
    (L.windowSequence hdepth).atTime t = X.atTime t := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StaticTerminalLimit.windowSequence_atTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StaticTerminalLimit.windowSequence_atTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StaticTerminalLimit.windowSequence_atTime ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StaticTerminalLimit.windowSequence_atTime

theorem StaticTerminalLimit.exists_metric_extensions_on_window
    {X : FlowSequence.{u}} {depthBound : ℝ} (L : StaticTerminalLimit X depthBound)
    {width : ℝ} (hw : 0 < width) (hwd : width < depthBound) :
    let Y := L.windowSequence (hw.le.trans hwd.le)
    let Phi := pointedCGHMapsOfManifold Y L.space L.subseq L.maps
    ∃ (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi)
      (htgt : TargetIsSigmaCompact Phi),
      let G := gSeqExt Phi L.space.metric bf hsrc htgt
      (∀ K : Set L.space.M, IsCompact K → ∀ᶠ i in _root_.Filter.atTop,
        ∃ U : Set L.space.M, IsOpen U ∧ K ⊆ U ∧
          U ⊆ (L.maps.partialDiffeomorph i).source ∧
          ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I3 x,
            (G i t).inner x v w = ((X.term (L.subseq i)).S.base.metric t).inner
              (L.maps.partialDiffeomorph i x)
              (mfderiv I3 I3 (L.maps.partialDiffeomorph i) x v)
              (mfderiv I3 I3 (L.maps.partialDiffeomorph i) x w)) ∧
      ∀ i : ℕ, ∀ K : Set L.space.M, IsCompact K → ∀ p : ℕ,
        ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ _root_.Set.Icc (-width) 0, ∀ t ∈ _root_.Set.Icc (-width) 0,
          ∀ q ≤ p, ∀ x ∈ K,
            metricDerivNorm q (G i s) (G i t) L.space.metric x ≤ C * |s - t| := by
  classical
  let Y := L.windowSequence (hw.le.trans hwd.le)
  let Phi := pointedCGHMapsOfManifold Y L.space L.subseq L.maps
  have hsrc : SourceIsSigmaCompact Phi := fun i =>
    DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 (Phi.source_open i)
  have htgt : TargetIsSigmaCompact Phi := fun i =>
    DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 (Phi.target_open i)
  obtain ⟨bf⟩ := nonempty_bumpFamily Phi
  refine ⟨bf, hsrc, htgt, ?_, ?_⟩
  · intro K hK
    obtain ⟨N, hN⟩ := bf.grow_cover K hK
    filter_upwards [_root_.Filter.eventually_ge_atTop N] with i hi
    obtain ⟨W, hW, hgrow, hchi⟩ := bf.chi_one i
    refine ⟨W ∩ Phi.source i, hW.inter (Phi.source_open i),
      fun x hx => ⟨hgrow (hN i hi hx), bf.grow_subset i (hN i hi hx)⟩,
      _root_.Set.inter_subset_right, ?_⟩
    intro t x hx v w
    have heq := gSeqExt_inner_of_mem Phi L.space.metric bf hsrc htgt i t x hx.2 v w
    rw [hchi x hx.1, one_smul, sub_self, zero_smul, add_zero] at heq
    exact heq.trans
      (KappaSolutions.pointed_srcMetric_inner_eq_pullback Phi hsrc htgt i t x hx.2 v w)
  · intro i K hK p
    let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
    exact exists_metric_extension_time_lipschitz_constant_on_closed_interval
      Phi L.space.metric bf hsrc htgt (a := -width) (b := 0)
      (by linarith)
      (fun t ht => ⟨by linarith [ht.1], ht.2⟩)
      (fun t ht => ⟨by linarith [ht.1], ht.2⟩) i K hK p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StaticTerminalLimit.exists_metric_extensions_on_window then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StaticTerminalLimit.exists_metric_extensions_on_window"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StaticTerminalLimit.exists_metric_extensions_on_window ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StaticTerminalLimit.exists_metric_extensions_on_window

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
