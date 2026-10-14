import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.CanonicalIdentification
import Submission.DifferentialGeometry.Bundle.FiberBundleHausdorff
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Rigidity.RicciSoliton
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.UpperBound

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

section InnerProductModel

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] {D : RealTimeInterval}

private theorem scalar_eq_zero_of_redVolume_eq_one_of_innerProductSpace
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ y : M,
        normSq0S (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K)
    {tau s : ℝ} (hs : 0 < s) (hstau : s < tau)
    (hslab : _root_.Set.Icc (T - tau) T ⊆ D.regular)
    (hvol : redVolume S T x tau = 1) (y : M) :
    S.scalar (T - s) y = 0 := by
  obtain ⟨hf, hsol, _hnormal⟩ :=
    gradientRicciSoliton_and_hamiltonNormalized_of_redVolume_eq_one
      S hS T hg x hRm hs hstau hslab hvol
  obtain ⟨K, hK⟩ := hRm tau (hs.trans hstau) hslab
  exact Soliton.metricScalarAt_eq_zero_of_gradientRicciSoliton_slice
    S hS hs hstau (hslab.trans D.regular_subset)
    (Ioo_subset_Icc_self.trans hslab) hK hg
    ⟨fun z => redLength S T x z s, hf⟩ (by simpa only [one_div] using hsol) y

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.scalar_eq_zero_of_redVolume_eq_one_of_innerProductSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.scalar_eq_zero_of_redVolume_eq_one_of_innerProductSpace target :: scope.openDecls } }

end InnerProductModel

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  {D : RealTimeInterval}

theorem scalar_eq_zero_of_redVolume_eq_one
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ y : M,
        normSq0S (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K)
    {tau s : ℝ} (hs : 0 < s) (hstau : s < tau)
    (hslab : _root_.Set.Icc (T - tau) T ⊆ D.regular)
    (hvol : redVolume S T x tau = 1) (y : M) :
    S.scalar (T - s) y = 0 := by
  by_cases hdim : Module.finrank ℝ E = 0
  · exact metricScalarAt_eq_zero_of_finrank_eq_zero (S.base.metric (T - s)) hdim y
  let _ : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : PseudoMetricSpace M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric M
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv.trans
      (EuclideanSpace.equiv (Fin (Module.finrank ℝ E)) ℝ).symm
  let J := I.transContinuousLinearEquiv e
  let Phi := ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M e
  let U : SolutionOn (I := J) (M := M) D := S.pullback Phi.symm
  let _ : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) :=
    ⟨by simpa using (NeZero.ne (Module.finrank ℝ E))⟩
  have hU : IsSolutionOn U := hS.pullback S Phi.symm
  have hcomplete : RiemannianMetricComplete (I := J) (U.base.metric T) :=
    RiemannianMetricComplete.pullbackCross (S.base.metric T) Phi.symm hg
  have hRmU : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ z : M,
        normSq0S (I := J) (U.base.metric t) z 4 (U.base.rm04 t z) ≤ K := by
    intro sigma hsigma hreg
    obtain ⟨K, hK⟩ := hRm sigma hsigma hreg
    refine ⟨K, fun t ht z => ?_⟩
    change normSq0S (Diffeomorph.pullbackMetricCross (S.base.metric t) Phi.symm) z 4
      (metricRm04At (Diffeomorph.pullbackMetricCross (S.base.metric t) Phi.symm) z) ≤ K
    rw [riemannNormSq_cross]
    exact hK t ht z
  have hvolU : redVolume U T x tau = 1 := by
    rw [redVolume_transContinuousLinearEquiv S e T x tau]
    exact hvol
  have h := scalar_eq_zero_of_redVolume_eq_one_of_innerProductSpace
    U hU T hcomplete x hRmU hs hstau hslab hvolU y
  change (S.pullback Phi.symm).scalar (T - s) y = 0 at h
  rw [SolutionOn.pullback_scalar] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.scalar_eq_zero_of_redVolume_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.scalar_eq_zero_of_redVolume_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.scalar_eq_zero_of_redVolume_eq_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.scalar_eq_zero_of_redVolume_eq_one

theorem redVolume_lt_one_of_scalar_ne_zero
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ y : M,
        normSq0S (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K)
    {tau s : ℝ} (hs : 0 < s) (hstau : s < tau)
    (hslab : _root_.Set.Icc (T - tau) T ⊆ D.regular)
    (y : M) (hscalar : S.scalar (T - s) y ≠ 0) :
    redVolume S T x tau < 1 := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨fun hdim => hscalar
    (metricScalarAt_eq_zero_of_finrank_eq_zero (S.base.metric (T - s)) hdim y)⟩
  refine lt_of_le_of_ne (redVolume_le_one_of_rm S hS T hg x hRm
    (hs.trans hstau) hslab) ?_
  intro hvol
  exact hscalar (scalar_eq_zero_of_redVolume_eq_one
    S hS T hg x hRm hs hstau hslab hvol y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_lt_one_of_scalar_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_lt_one_of_scalar_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_lt_one_of_scalar_ne_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_lt_one_of_scalar_ne_zero

end DifferentialGeometry.PDE.RicciFlow.Perelman
