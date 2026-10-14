import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.MetricExtension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

private local instance pullbackExtensionTopology
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : TopologicalSpace P.M := P.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullbackExtensionTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullbackExtensionTopology target :: scope.openDecls } }
private local instance pullbackExtensionCharted
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : ChartedSpace H P.M := P.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullbackExtensionCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullbackExtensionCharted target :: scope.openDecls } }
private local instance pullbackExtensionSmooth
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : IsManifold I ∞ P.M := P.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullbackExtensionSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullbackExtensionSmooth target :: scope.openDecls } }
private local instance pullbackExtensionT2
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : T2Space P.M := P.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullbackExtensionT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullbackExtensionT2 target :: scope.openDecls } }
private local instance pullbackExtensionSigma
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : SigmaCompactSpace P.M := P.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullbackExtensionSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullbackExtensionSigma target :: scope.openDecls } }

private local instance pullbackExtensionFlowTopology {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullbackExtensionFlowTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullbackExtensionFlowTopology target :: scope.openDecls } }
private local instance pullbackExtensionFlowCharted {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullbackExtensionFlowCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullbackExtensionFlowCharted target :: scope.openDecls } }
private local instance pullbackExtensionFlowSmooth {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullbackExtensionFlowSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullbackExtensionFlowSmooth target :: scope.openDecls } }
private local instance pullbackExtensionFlowSigma {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullbackExtensionFlowSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullbackExtensionFlowSigma target :: scope.openDecls } }


theorem pointed_srcMetric_inner_eq_pullback
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (I := I) X P phi)
    (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (i : ℕ) (t : ℝ) (x : P.M) (hx : x ∈ Phi.source i)
    (v w : TangentSpace I x) :
    (sourceMetric Phi hsrc htgt i t).inner ⟨x, hx⟩ v w =
      ((X.term (phi i)).S.base.metric t).inner (Phi.map i x)
        (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x w) := by
  let : TopologicalSpace (SourceDomain Phi i) := sourceDomTop Phi i
  let : ChartedSpace H (SourceDomain Phi i) := sourceDomCharted Phi i
  let : IsManifold I ∞ (SourceDomain Phi i) := sourceDomSmooth Phi i
  let : T2Space (SourceDomain Phi i) := sourceDomT2 Phi i
  let : SigmaCompactSpace (SourceDomain Phi i) := sourceDomSigmaOf Phi i (hsrc i)
  let d := SourceDomainMetricData.ofRestrictPullback (I := I) (Φ := Phi) (k := i)
    (hsrc i) (fun _ => sourceMetricRestriction Phi P.metric i) (fun _ => P.metric)
  have hmetric : sourceMetric Phi hsrc htgt i t = d.pullbackMetric t :=
    sourceFlow_metric_eq Phi i (hsrc i) (htgt i)
      (fun _ => sourceMetricRestriction Phi P.metric i) (fun _ => P.metric) t
  have hval : MDifferentiableAt I I
      (fun y : SourceDomain Phi i => (y : P.M)) ⟨x, hx⟩ :=
    ((contMDiff_subtype_val (I := I) (U := sourceOpen Phi i)
      (n := ∞)).contMDiffAt).mdifferentiableAt (by simp)
  have hPhi : MDifferentiableAt I I (Phi.map i) x :=
    (Phi.partialDiffeomorph i).mdifferentiableAt (by simp) hx
  have hderiv (z : TangentSpace I x) :
      mfderiv I I (fun y : SourceDomain Phi i => Phi.map i (y : P.M)) ⟨x, hx⟩ z =
        mfderiv I I (Phi.map i) x z := by
    have hcomp := mfderiv_comp_apply (⟨x, hx⟩ : SourceDomain Phi i) hPhi hval z
    have hincl :
        mfderiv I I (fun y : SourceDomain Phi i => (y : P.M)) ⟨x, hx⟩ z = z :=
      mfderiv_subtype_val_apply (I := I) (sourceOpen Phi i) ⟨x, hx⟩ z
    exact hcomp.trans (congrArg (mfderiv I I (Phi.map i) x) hincl)
  rw [hmetric]
  exact (d.pullback_inner t ⟨x, hx⟩ v w).trans
    (congrArg₂ (fun v' w' => ((X.term (phi i)).S.base.metric t).inner
      (Phi.map i x) v' w') (hderiv v) (hderiv w))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointed_srcMetric_inner_eq_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointed_srcMetric_inner_eq_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointed_srcMetric_inner_eq_pullback ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointed_srcMetric_inner_eq_pullback


theorem exists_pointed_pullback_metric_extensions
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (I := I) X P phi) :
    ∃ G : ℕ → ℝ → SmoothRiemannianMetric I P.M,
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
  refine ⟨gSeqExt Phi P.metric bf hsrc htgt, ?_⟩
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
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_pullback_metric_extensions then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_pullback_metric_extensions"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_pullback_metric_extensions ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_pullback_metric_extensions

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedFlowData.topology PointedFlowData.charted PointedFlowData.smooth
  PointedFlowData.sigmaCompact

theorem eventually_gSeqExt_eq_pullback
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (I := I) X P phi)
    (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi) :
    ∀ K : Set P.M, IsCompact K → ∀ᶠ i in _root_.Filter.atTop,
      ∃ U : Set P.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ Phi.source i ∧
        ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
          (gSeqExt Phi R bf hsrc htgt i t).inner x v w =
            ((X.term (phi i)).S.base.metric t).inner (Phi.map i x)
              (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x w) := by
  intro K hK
  obtain ⟨N, hN⟩ := bf.grow_cover K hK
  filter_upwards [Filter.eventually_ge_atTop N] with i hi
  obtain ⟨W, hW, hgrow, hchi⟩ := bf.chi_one i
  refine ⟨W ∩ Phi.source i, hW.inter (Phi.source_open i),
    fun x hx => ⟨hgrow (hN i hi hx), bf.grow_subset i (hN i hi hx)⟩,
    _root_.Set.inter_subset_right, ?_⟩
  intro t x hx v w
  have heq := gSeqExt_inner_of_mem Phi R bf hsrc htgt i t x hx.2 v w
  rw [hchi x hx.1, one_smul, sub_self, zero_smul, add_zero] at heq
  exact heq.trans (pointed_srcMetric_inner_eq_pullback Phi hsrc htgt i t x hx.2 v w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eventually_gSeqExt_eq_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eventually_gSeqExt_eq_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eventually_gSeqExt_eq_pullback ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eventually_gSeqExt_eq_pullback

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
