import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedExtensionTimeJets

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.Submission.Set _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

private local instance errorJetFlowC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.errorJetFlowC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.errorJetFlowC1 target :: scope.openDecls } }


theorem exists_pointed_metric_error_time_jets
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi)
    {c : ℝ} (hcarrier : X.D.carrier = _root_.Set.Iic c) (hregular : X.D.regular = _root_.Set.Iio c) :
    ∃ G : ℕ → ℝ → SmoothRiemannianMetric I L.M,
    ∃ J : ℕ → ℕ → ℝ → Tensor0SField (I := I) (M := L.M) (n := ∞) 2,
      (∀ i t, J i 0 t = metricTensorField (G i t) - metricTensorField (L.S.base.metric t)) ∧
      (∀ i q t, t ≤ c → ∀ x : L.M,
        HasDerivWithinAt (fun s => J i q s x) (J i (q + 1) t x) (_root_.Set.Iic c) t) ∧
      ∀ K : Set L.M, IsCompact K → ∀ᶠ i in _root_.Filter.atTop,
        ∃ U : Set L.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ Phi.source i ∧
          ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
            (G i t).inner x v w =
              ((X.term (phi i)).S.base.metric t).inner (Phi.map i x)
                (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x w) := by
  obtain ⟨G, B, hBzero, hBderiv, hG⟩ := exists_pointed_extension_time_jets Phi hcarrier hregular
  obtain ⟨C, hCzero, hCderiv⟩ := exists_ancient_ordinary_metric_time_jets
    L.S L.isSolution hcarrier hregular
  let B' : ℕ → ℕ → ℝ → Tensor0SField (I := I) (M := L.M) (n := ∞) 2 := B
  let C' : ℕ → ℝ → Tensor0SField (I := I) (M := L.M) (n := ∞) 2 := C
  let J : ℕ → ℕ → ℝ → Tensor0SField (I := I) (M := L.M) (n := ∞) 2 :=
    fun i q t => B' i q t - C' q t
  refine ⟨G, J, ?_, ?_, hG⟩
  · intro i t
    change B' i 0 t - C' 0 t = _
    exact congrArg₂ (fun A C : Tensor0SField (I := I) (M := L.M) (n := ∞) 2 => A - C)
      (hBzero i t) (hCzero t)
  · intro i q t ht x
    change HasDerivWithinAt (fun s => B' i q s x - C' q s x)
      (B' i (q + 1) t x - C' (q + 1) t x) (_root_.Set.Iic c) t
    exact (hBderiv i q t ht x).sub (hCderiv q t ht x).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_metric_error_time_jets then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_metric_error_time_jets"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_metric_error_time_jets ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_metric_error_time_jets

section ClosedWindow

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance errorJetC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.errorJetC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.errorJetC1 target :: scope.openDecls } }

omit [CompleteSpace E] [I.Boundaryless] in
theorem tensor_time_tower_derivWithin_Icc {r : ℕ}
    (B : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) r)
    {c : ℝ} (hB : ∀ q t, t ≤ c → ∀ x : M,
      HasDerivWithinAt (fun s => B q s x) (B (q + 1) t x) (_root_.Set.Iic c) t)
    {a b : ℝ} (hab : a < b) (hbc : b ≤ c)
    (q : ℕ) (t : ℝ) (ht : t ∈ _root_.Set.Icc a b) (x : M) (v : Fin r → TangentSpace I x) :
    B (q + 1) t x v = derivWithin (fun s => B q s x v) (_root_.Set.Icc a b) t := by
  have hd := (hB q t (ht.2.trans hbc) x).mono
    (fun s hs => hs.2.trans hbc : _root_.Set.Icc a b ⊆ _root_.Set.Iic c)
  have hv : HasDerivWithinAt (fun s => B q s x v) (B (q + 1) t x v) (_root_.Set.Icc a b) t :=
    (tensor0SEvalCLM (I := I) (x := x) v).hasFDerivAt.comp_hasDerivWithinAt t hd
  exact (hv.derivWithin (uniqueDiffOn_Icc hab t ht)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensor_time_tower_derivWithin_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensor_time_tower_derivWithin_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensor_time_tower_derivWithin_Icc ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensor_time_tower_derivWithin_Icc

end ClosedWindow

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
