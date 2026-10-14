import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessSpatialBuffer
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.OpenTensorJets
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricContinuity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance closedBallJetsC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.closedBallJetsC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.closedBallJetsC1 target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] in
theorem closure_riemannianBallOf [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete g)
    (p : M) {R : ℝ} (hR : 0 < R) :
    closure (riemannianBallOf g p R) = riemannianClosedBallOf g p R := by
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : CompleteSpace M := hg.complete
  have hEnorm : IsMetricNorm (I := I) (M := M) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  have hnorm (v : TangentSpace I p) : ‖v‖ = Real.sqrt (g.inner p v v) := by
    have hv := hEnorm p v
    rw [← ofReal_norm] at hv
    exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg v) (Real.sqrt_nonneg _)).mp hv
  have himage : (expMapIntrinsic (I := I) g hEnorm p) ''
      Metric.ball (0 : TangentSpace I p) R ⊆ riemannianBallOf g p R := by
    rintro _ ⟨v, hv, rfl⟩
    have hvR : Real.sqrt (g.inner p v v) < R := by
      simpa only [Metric.mem_ball, dist_zero_right, hnorm] using hv
    have hd := intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm p v
      (show (0 : ℝ) ≤ 1 by norm_num)
    rw [intrinsicGeodesic_zero, ← expMapIntrinsic_def, sub_zero, mul_one] at hd
    exact hd.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hvR)
  apply Subset.antisymm
  · have hsub : riemannianBallOf g p R ⊆ riemannianClosedBallOf g p R := by
      intro x hx
      change riemannianEDistOf (I := I) g p x < ENNReal.ofReal R at hx
      change riemannianEDistOf (I := I) g p x ≤ ENNReal.ofReal R
      exact hx.le
    exact closure_minimal hsub
      (isClosed_le (continuous_riemannianEDist g p) continuous_const)
  · intro x hx
    have hfinite : _root_.Manifold.riemannianEDist I p x ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hx
    obtain ⟨v, hv, hlen⟩ :=
      hopf_rinow_expMapIntrinsic_surjective_minimizing_of_ne_top g hEnorm p x hfinite
    have hvclosed : v ∈ Metric.closedBall (0 : TangentSpace I p) R := by
      rw [Metric.mem_closedBall, dist_zero_right, hnorm, hlen]
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hx).trans_eq
        (ENNReal.toReal_ofReal hR.le)
    have hvclosure : v ∈ closure (Metric.ball (0 : TangentSpace I p) R) := by
      rwa [closure_ball _ hR.ne']
    have hexp := image_closure_subset_closure_image
      (expMapIntrinsic_continuous (I := I) g hEnorm p) ⟨v, hvclosure, hv⟩
    exact closure_mono himage hexp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.closure_riemannianBallOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.closure_riemannianBallOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.closure_riemannianBallOf ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.closure_riemannianBallOf

omit [SigmaCompactSpace M] in
theorem tensor02CovDerivNormWith_eq_on_closure
    (gcov gnorm : SmoothRiemannianMetric I M)
    (A B : Tensor0SField (I := I) (M := M) (n := ∞) 2)
    {U : Set M} (hU : IsOpen U) (hAB : ∀ x ∈ U, A x = B x) (a : ℕ) :
    _root_.Set.EqOn (tensor02CovDerivNormWith a A gcov gnorm)
      (tensor02CovDerivNormWith a B gcov gnorm) (closure U) := by
  let V : TopologicalSpace.Opens M := ⟨U, hU⟩
  have hrestrict : restrictOpen0S (I := I) 2 (V := V) A =
      restrictOpen0S (I := I) 2 (V := V) B := by
    ext x v
    change A (x : M) v = B (x : M) v
    exact congrArg (fun T => T v) (hAB x x.property)
  have heq : _root_.Set.EqOn (tensor02CovDerivNormWith a A gcov gnorm)
      (tensor02CovDerivNormWith a B gcov gnorm) U := by
    intro x hx
    calc
      _ = tensor02CovDerivNormWith a (restrictOpen0S (I := I) 2 (V := V) A)
          (gcov.restrictOpen V) (gnorm.restrictOpen V) (⟨x, hx⟩ : V) :=
        (tensor02CovDerivNormWith_restrictOpen0S V gcov gnorm A a ⟨x, hx⟩).symm
      _ = tensor02CovDerivNormWith a (restrictOpen0S (I := I) 2 (V := V) B)
          (gcov.restrictOpen V) (gnorm.restrictOpen V) (⟨x, hx⟩ : V) := by rw [hrestrict]
      _ = _ := tensor02CovDerivNormWith_restrictOpen0S V gcov gnorm B a ⟨x, hx⟩
  exact heq.closure
    (Real.continuous_sqrt.comp (normSq0S_cont gnorm (tensor02CovDeriv A gcov a)))
    (Real.continuous_sqrt.comp (normSq0S_cont gnorm (tensor02CovDeriv B gcov a)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tensor02CovDerivNormWith_eq_on_closure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tensor02CovDerivNormWith_eq_on_closure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tensor02CovDerivNormWith_eq_on_closure ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tensor02CovDerivNormWith_eq_on_closure


theorem tensor02CovDerivNormWith_eq_on_riemannianClosedBall
    [I.Boundaryless] [NeZero (Module.finrank ℝ E)] [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete g)
    (p : M) {R : ℝ} (hR : 0 < R)
    (gcov gnorm : SmoothRiemannianMetric I M)
    (A B : Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (hAB : ∀ x ∈ riemannianClosedBallOf g p R, A x = B x) (a : ℕ) :
    _root_.Set.EqOn (tensor02CovDerivNormWith a A gcov gnorm)
      (tensor02CovDerivNormWith a B gcov gnorm) (riemannianClosedBallOf g p R) := by
  rw [← closure_riemannianBallOf g hg p hR]
  exact tensor02CovDerivNormWith_eq_on_closure gcov gnorm A B
    (isOpen_lt (continuous_riemannianEDist g p) continuous_const)
    (fun x hx => hAB x (by
      change riemannianEDistOf (I := I) g p x ≤ ENNReal.ofReal R
      exact hx.le)) a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tensor02CovDerivNormWith_eq_on_riemannianClosedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tensor02CovDerivNormWith_eq_on_riemannianClosedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tensor02CovDerivNormWith_eq_on_riemannianClosedBall ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tensor02CovDerivNormWith_eq_on_riemannianClosedBall

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
