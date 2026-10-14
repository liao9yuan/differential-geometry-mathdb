import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.PointedPullbackExtensions
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BumpMetricTimeJets
import Submission.DifferentialGeometry.Geometry.Metric.Construction.BumpTimeJets
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ClosedWindowMetricFields

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance pointedJetTopology
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : TopologicalSpace P.M := P.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedJetTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedJetTopology target :: scope.openDecls } }
private local instance pointedJetCharted
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : ChartedSpace H P.M := P.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedJetCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedJetCharted target :: scope.openDecls } }
private local instance pointedJetSmooth
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : IsManifold I ∞ P.M := P.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedJetSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedJetSmooth target :: scope.openDecls } }
private local instance pointedJetC1
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : IsManifold I 1 P.M :=
  IsManifold.of_le (I := I) (M := P.M) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedJetC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedJetC1 target :: scope.openDecls } }
private local instance pointedJetT2
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : T2Space P.M := P.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedJetT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedJetT2 target :: scope.openDecls } }
private local instance pointedJetSigma
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : SigmaCompactSpace P.M := P.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedJetSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedJetSigma target :: scope.openDecls } }

private local instance pointedJetFlowTopology {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedJetFlowTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedJetFlowTopology target :: scope.openDecls } }
private local instance pointedJetFlowCharted {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedJetFlowCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedJetFlowCharted target :: scope.openDecls } }
private local instance pointedJetFlowSmooth {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedJetFlowSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedJetFlowSmooth target :: scope.openDecls } }
private local instance pointedJetFlowSigma {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedJetFlowSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedJetFlowSigma target :: scope.openDecls } }


theorem exists_pointed_extension_time_jets
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (I := I) X P phi)
    {b : ℝ} (hcarrier : X.D.carrier = _root_.Set.Iic b) (hregular : X.D.regular = _root_.Set.Iio b) :
    ∃ G : ℕ → ℝ → SmoothRiemannianMetric I P.M,
    ∃ B : ℕ → ℕ → ℝ → Tensor0SField (I := I) (M := P.M) (n := ∞) 2,
      (∀ i t, B i 0 t = metricTensorField (G i t)) ∧
      (∀ i q t, t ≤ b → ∀ x : P.M,
        HasDerivWithinAt (fun s => B i q s x) (B i (q + 1) t x) (_root_.Set.Iic b) t) ∧
      ∀ K : Set P.M, IsCompact K → ∀ᶠ i in _root_.Filter.atTop,
        ∃ U : Set P.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ Phi.source i ∧
          ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
            (G i t).inner x v w =
              ((X.term (phi i)).S.base.metric t).inner (Phi.map i x)
                (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x w) := by
  classical
  have hsrc : SourceIsSigmaCompact Phi := fun i =>
    DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I (Phi.source_open i)
  have htgt : TargetIsSigmaCompact Phi := fun i =>
    DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I (Phi.target_open i)
  obtain ⟨bf⟩ := nonempty_bumpFamily Phi
  let G : ℕ → ℝ → SmoothRiemannianMetric I P.M := gSeqExt Phi P.metric bf hsrc htgt
  have hBi (i : ℕ) :
      ∃ B : ℕ → ℝ → Tensor0SField (I := I) (M := P.M) (n := ∞) 2,
        (∀ t, B 0 t = metricTensorField (G i t)) ∧
        ∀ q t, t ≤ b → ∀ x : P.M,
          HasDerivWithinAt (fun s => B q s x) (B (q + 1) t x) (_root_.Set.Iic b) t := by
    let : TopologicalSpace (SourceDomain Phi i) := sourceDomTop Phi i
    let : ChartedSpace H (SourceDomain Phi i) := sourceDomCharted Phi i
    let : IsManifold I ∞ (SourceDomain Phi i) := sourceDomSmooth Phi i
    let : T2Space (SourceDomain Phi i) := sourceDomT2 Phi i
    let : SigmaCompactSpace (SourceDomain Phi i) := sourceDomSigmaOf Phi i (hsrc i)
    exact exists_bump_metric_time_jets P.metric (sourceOpen Phi i)
      (sourceFlow Phi i (hsrc i) (htgt i))
      (isSolutionOn_sourceFlow Phi i (hsrc i) (htgt i)) hcarrier hregular
      (bf.chi i) (bf.chi_smooth i) (bf.chi01 i) (bf.chi_support i)
  choose B hBzero hBderiv using hBi
  refine ⟨G, B, hBzero, hBderiv, ?_⟩
  intro K hK
  obtain ⟨N, hN⟩ := bf.grow_cover K hK
  filter_upwards [Filter.eventually_ge_atTop N] with i hi
  obtain ⟨W, hW, hgrow, hchi⟩ := bf.chi_one i
  refine ⟨W ∩ Phi.source i, hW.inter (Phi.source_open i),
    fun x hx => ⟨hgrow (hN i hi hx), bf.grow_subset i (hN i hi hx)⟩,
    _root_.Set.inter_subset_right, ?_⟩
  intro t x hx v w
  have heq := gSeqExt_inner_of_mem Phi P.metric bf hsrc htgt i t x hx.2 v w
  rw [hchi x hx.1, one_smul, sub_self, zero_smul, add_zero] at heq
  exact heq.trans (pointed_srcMetric_inner_eq_pullback Phi hsrc htgt i t x hx.2 v w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_extension_time_jets then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_extension_time_jets"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_extension_time_jets ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_extension_time_jets

theorem exists_pointed_extension_time_jets_on_closed_window
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (I := I) X P phi)
    (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : _root_.Set.Icc a b ⊆ X.D.carrier) (hreg : _root_.Set.Ioo a b ⊆ X.D.regular) :
    ∃ B : ℕ → ℕ → ℝ → Tensor0SField (I := I) (M := P.M) (n := ∞) 2,
      (∀ i t, B i 0 t = metricTensorField (gSeqExt Phi R bf hsrc htgt i t)) ∧
      ∀ i q t, t ∈ _root_.Set.Icc c b → ∀ x : P.M,
        HasDerivWithinAt (fun s => B i q s x) (B i (q + 1) t x) (_root_.Set.Icc c b) t := by
  classical
  have hBi (i : ℕ) :
      ∃ B : ℕ → ℝ → Tensor0SField (I := I) (M := P.M) (n := ∞) 2,
        (∀ t, B 0 t = metricTensorField (gSeqExt Phi R bf hsrc htgt i t)) ∧
        ∀ q t, t ∈ _root_.Set.Icc c b → ∀ x : P.M,
          HasDerivWithinAt (fun s => B q s x) (B (q + 1) t x) (_root_.Set.Icc c b) t := by
    let : TopologicalSpace (SourceDomain Phi i) := sourceDomTop Phi i
    let : ChartedSpace H (SourceDomain Phi i) := sourceDomCharted Phi i
    let : IsManifold I ∞ (SourceDomain Phi i) := sourceDomSmooth Phi i
    let : T2Space (SourceDomain Phi i) := sourceDomT2 Phi i
    let : SigmaCompactSpace (SourceDomain Phi i) := sourceDomSigmaOf Phi i (hsrc i)
    obtain ⟨A, hA0, hA⟩ :=
      CanonicalNeighborhood.FiniteHorn.exists_closedWindow_metric_time_fields
        (sourceFlow Phi i (hsrc i) (htgt i)) (isSolutionOn_sourceFlow Phi i (hsrc i) (htgt i))
        hac hcb hslab hreg
    exact exists_bump_metric_time_jets_of_tower R (sourceOpen Phi i)
      (sourceMetric Phi hsrc htgt i) A hA0 (_root_.Set.Icc c b) (fun q t ht x => (hA q t ht x).2)
      (bf.chi i) (bf.chi_smooth i) (bf.chi01 i) (bf.chi_support i)
  choose B hB0 hB using hBi
  exact ⟨B, hB0, hB⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_extension_time_jets_on_closed_window then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_extension_time_jets_on_closed_window"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_extension_time_jets_on_closed_window ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_extension_time_jets_on_closed_window

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
