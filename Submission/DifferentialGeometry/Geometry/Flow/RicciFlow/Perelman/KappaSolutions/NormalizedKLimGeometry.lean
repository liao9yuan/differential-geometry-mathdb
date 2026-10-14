import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SeedVolume

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

private local instance normalizedKLimTopology {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedKLimTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedKLimTopology target :: scope.openDecls } }
private local instance normalizedKLimCharted {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedKLimCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedKLimCharted target :: scope.openDecls } }
private local instance normalizedKLimSmooth {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedKLimSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedKLimSmooth target :: scope.openDecls } }
private local instance normalizedKLimC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedKLimC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedKLimC1 target :: scope.openDecls } }
private local instance normalizedKLimT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedKLimT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedKLimT2 target :: scope.openDecls } }
private local instance normalizedKLimSigma {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedKLimSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedKLimSigma target :: scope.openDecls } }
private local instance normalizedKLimTangentT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space (TangentBundle I F.M) :=
  F.t2TangentBundle

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedKLimTangentT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedKLimTangentT2 target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem normalizedKLim_edist_triangle {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D)
    (g : SmoothRiemannianMetric I F.M) (x y z : F.M) :
    riemannianEDistOf (I := I) g x z ≤
      riemannianEDistOf (I := I) g x y + riemannianEDistOf (I := I) g y z := by
  let _ : _root_.Bundle.RiemannianBundle (fun q : F.M => TangentSpace I q) := ⟨g.toRiemannianMetric⟩
  change Manifold.riemannianEDist I x z ≤
    Manifold.riemannianEDist I x y + Manifold.riemannianEDist I y z
  exact Manifold.riemannianEDist_triangle (I := I) (x := x) (y := y) (z := z)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedKLim_edist_triangle
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedKLim_edist_triangle target :: scope.openDecls } }

theorem klim_buffered_ball_subset {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) {kappa : ℝ}
    (hK : KLim kappa F) {s A rho : ℝ} (hs : s ≤ 0)
    (hA : 0 ≤ A) (hrho : 0 ≤ rho) (x y z : F.M)
    (hy : riemannianEDistOf (I := I) (F.S.base.metric 0) x y ≤ ENNReal.ofReal A)
    (hz : riemannianEDistOf (I := I) (F.S.base.metric s) y z ≤ ENNReal.ofReal rho) :
    riemannianEDistOf (I := I) (F.S.base.metric 0) x z ≤
      ENNReal.ofReal (A + rho) := by
  calc
    _ ≤ riemannianEDistOf (I := I) (F.S.base.metric 0) x y +
        riemannianEDistOf (I := I) (F.S.base.metric 0) y z :=
      normalizedKLim_edist_triangle F _ x y z
    _ ≤ ENNReal.ofReal A + ENNReal.ofReal rho :=
      add_le_add hy ((hK.edist_le hs le_rfl y z).trans hz)
    _ = ENNReal.ofReal (A + rho) := (ENNReal.ofReal_add hA hrho).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.klim_buffered_ball_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.klim_buffered_ball_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.klim_buffered_ball_subset ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.klim_buffered_ball_subset

variable [I.Boundaryless]

theorem exists_normalized_klim_local_curvature_constants
    (hdim : Module.finrank ℝ E = 3) (kappa : ℝ) :
    ∃ C : ℝ → ℝ, (∀ A, 0 < C A) ∧
      ∀ (D : RealTimeInterval) (F : PointedFlowData.{u, uE, uH} (I := I) D),
        KLim kappa F → F.S.scalar 0 F.basepoint = 1 →
        ∀ A : ℝ, ∀ y : F.M,
          riemannianEDistOf (I := I) (F.S.base.metric 0) F.basepoint y ≤
            ENNReal.ofReal A → ∀ t : ℝ, t ≤ 0 →
          (0 ≤ F.S.scalar t y ∧ F.S.scalar t y ≤ C A) ∧
            F.rmNormSq (I := I) t y ≤ 3 * (C A) ^ 2 := by
  classical
  choose C hC hbound using fun A : ℝ =>
    exists_normalized_bounded_distance_scalar_constant (I := I) hdim kappa A
  refine ⟨C, hC, ?_⟩
  intro D F hK hbase A y hy t ht
  have hterminal := hbound A D F hK F.basepoint hbase y hy
  exact ⟨⟨hK.scalar_nonneg ht y, (hK.scalar_le_terminal ht y).trans hterminal⟩,
    hK.rmNormSq_le_of_terminal_scalar_le F hdim ht y hterminal⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_normalized_klim_local_curvature_constants then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_normalized_klim_local_curvature_constants"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_normalized_klim_local_curvature_constants ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_normalized_klim_local_curvature_constants

theorem exists_normalized_klim_buffered_curvature_constants
    (hdim : Module.finrank ℝ E = 3) (kappa : ℝ) :
    ∃ C : ℝ → ℝ, (∀ A, 0 < C A) ∧
      ∀ (D : RealTimeInterval) (F : PointedFlowData.{u, uE, uH} (I := I) D),
        KLim kappa F → F.S.scalar 0 F.basepoint = 1 →
        ∀ A : ℝ, 0 ≤ A → ∀ t : ℝ, t ≤ 0 → ∀ y z : F.M,
          riemannianEDistOf (I := I) (F.S.base.metric 0) F.basepoint y ≤
            ENNReal.ofReal A →
          riemannianEDistOf (I := I) (F.S.base.metric t) y z ≤ ENNReal.ofReal 1 →
          (0 ≤ F.S.scalar t z ∧ F.S.scalar t z ≤ C A) ∧
            F.rmNormSq (I := I) t z ≤ 3 * (C A) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_normalized_klim_local_curvature_constants (I := I) hdim kappa
  refine ⟨fun A => C (A + 2), fun A => hC (A + 2), ?_⟩
  intro D F hK hbase A hA t ht y z hy hz
  apply hbound D F hK hbase (A + 2) z _ t ht
  exact (klim_buffered_ball_subset F hK ht hA zero_le_one
    F.basepoint y z hy hz).trans (ENNReal.ofReal_le_ofReal (by linarith))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_normalized_klim_buffered_curvature_constants then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_normalized_klim_buffered_curvature_constants"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_normalized_klim_buffered_curvature_constants ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_normalized_klim_buffered_curvature_constants

theorem exists_normalized_klim_base_injectivity [NeZero (Module.finrank ℝ E)]
    (hdim : Module.finrank ℝ E = 3) (kappa : ℝ) (hkappa : 0 < kappa) :
    ∃ iota : ℝ, 0 < iota ∧
      ∀ (D : RealTimeInterval) (F : PointedFlowData.{u, uE, uH} (I := I) D),
        KLim kappa F → F.S.scalar 0 F.basepoint = 1 →
          HasInjRadiusAt (I := I) (F.atTime (I := I) 0) F.basepoint iota := by
  classical
  obtain ⟨C, hC, hbound⟩ :=
    exists_normalized_bounded_distance_scalar_constant (I := I) hdim kappa 1
  let rho : ℝ := 1 / (4 * (C + 1))
  have hrho : 0 < rho := by dsimp only [rho]; positivity
  let hscale := exists_uniform_local_jacobi_scale (Module.finrank ℝ E)
    (R := rho) (K := 2 * C + 1) hrho (by linarith)
  let rJ : ℝ := hscale.choose
  let R : ℝ := _root_.Min.min rJ (Real.pi / Real.sqrt (2 * C + 1))
  have hR : 0 < R := lt_min hscale.choose_spec.1
    (div_pos Real.pi_pos (by positivity))
  refine ⟨selectedCGTInjRadius E kappa R,
    selectedCGTInjRadius_pos (E := E) hkappa hR, ?_⟩
  intro D F hK hbase
  let X : PointedFlowSeq.{u, uE, uH} (I := I) := { D := D, term := fun _ => F }
  have hunit : ∀ i,
      let _ : TopologicalSpace (X.term i).M := (X.term i).topology
      let _ : ChartedSpace H (X.term i).M := (X.term i).charted
      let _ : IsManifold I ∞ (X.term i).M := (X.term i).smooth
      ∀ z : (X.term i).M,
        riemannianEDistOf (I := I) ((X.term i).S.base.metric 0)
          (X.term i).basepoint z < ENNReal.ofReal 1 → (X.term i).S.scalar 0 z ≤ C := by
    intro i
    dsimp only [X]
    intro z hz
    exact hbound D F hK F.basepoint hbase z hz.le
  let B := klim_three_baseInjBound_of_unit_scalar_bound X (fun _ => hK) hdim C hC hunit
  exact B.bound 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_normalized_klim_base_injectivity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_normalized_klim_base_injectivity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_normalized_klim_base_injectivity ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_normalized_klim_base_injectivity

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
