import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.ClosedMinimizingSlice
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Rigidity.GaussianJacobian

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] {D : RealTimeInterval}

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry target :: scope.openDecls } }

theorem lMinDomain_slice_eq_univ_of_redVolume_eq_one
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ y : M,
        normSq0S (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K)
    {tau : ℝ} (htau : 0 < tau) (hslab : _root_.Set.Icc (T - tau) T ⊆ D.regular)
    (hvol : redVolume S T x tau = 1) :
    {Z : E | (Z, tau) ∈ lMinDomain S T x} = univ := by
  have hclosed := lMinSlice_closed_of_rm S hS T hg x hRm htau hslab
  apply (hclosed.ae_eq_univ_iff_eq (μ := modelHaar)).mp
  filter_upwards [ae_mem_lInjDomain_of_redVolume_eq_one S hS T hg x hRm htau hslab hvol]
    with Z hZ
  have hmin : (Z, tau) ∈ lMinDomain S T x := by
    obtain ⟨sigma, hsigma, hmin⟩ := hZ
    have hdom := ((mem_lMinDomain S T x Z sigma).mp hmin).1
    have hreg : _root_.Set.Icc (T - sigma) T ⊆ D.regular := by
      intro t ht
      have ht0 : 0 ≤ T - t := sub_nonneg.mpr ht.2
      have htS : T - t ≤ sigma := by linarith only [ht.1]
      have hsqrt : Real.sqrt (T - t) ∈ _root_.Set.Icc (0 : ℝ) (Real.sqrt sigma) :=
        ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt htS⟩
      have h := lExpPosDom_regularity S T x Z hdom hsqrt
      have heq : T - (Real.sqrt (T - t)) ^ 2 = t := by
        rw [Real.sq_sqrt ht0]
        ring
      simpa only [heq] using h
    obtain ⟨K, hK⟩ := hRm sigma (htau.trans hsigma) hreg
    exact lMinDomain_down_of_rm S hS K T x Z hmin htau hsigma.le hK
  exact propext (iff_of_true hmin (_root_.Set.mem_univ Z))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lMinDomain_slice_eq_univ_of_redVolume_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lMinDomain_slice_eq_univ_of_redVolume_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lMinDomain_slice_eq_univ_of_redVolume_eq_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lMinDomain_slice_eq_univ_of_redVolume_eq_one

theorem lInjDomain_eq_univ_of_redVolume_eq_one
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ y : M,
        normSq0S (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K)
    {tau s : ℝ} (htau : 0 < tau) (hstau : s < tau)
    (hslab : _root_.Set.Icc (T - tau) T ⊆ D.regular)
    (hvol : redVolume S T x tau = 1) :
    lInjDomain S T x s = univ := by
  have hmin := lMinDomain_slice_eq_univ_of_redVolume_eq_one S hS T hg x hRm
    htau hslab hvol
  apply Set.eq_univ_of_forall
  intro Z
  refine ⟨tau, hstau, ?_⟩
  have hZ : Z ∈ {W : E | (W, tau) ∈ lMinDomain S T x} := by
    rw [hmin]
    exact _root_.Set.mem_univ Z
  exact hZ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lInjDomain_eq_univ_of_redVolume_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lInjDomain_eq_univ_of_redVolume_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lInjDomain_eq_univ_of_redVolume_eq_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lInjDomain_eq_univ_of_redVolume_eq_one

end DifferentialGeometry.PDE.RicciFlow.Perelman
