import Submission.DifferentialGeometry.Geometry.Operator.Gradient.PullbackAt
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.PointedPullbackExtensions

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Operator
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : PointedFlowSeq.{u, uE, uH} (I := I)}
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem normGradSqFun_gSeqExt_of_chi_eq_one
    (Phi : PointedCGHMaps X P phi) (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (k : ℕ) (t : ℝ) (x : P.M) (hx : x ∈ Phi.source k) (hchi : bf.chi k x = 1)
    {f : (X.term (phi k)).M → ℝ}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f (Phi.map k x)) :
    normGradSqFun (gSeqExt Phi R bf hsrc htgt k t) (f ∘ Phi.map k) x =
      normGradSqFun ((X.term (phi k)).S.base.metric t) f (Phi.map k x) := by
  have hPhi := (Phi.partialDiffeomorph k).isLocalDiffeomorphAt I I ∞ hx
  apply normGradSqFun_comp_of_pullback_inner
    (gSeqExt Phi R bf hsrc htgt k t) ((X.term (phi k)).S.base.metric t)
    (hPhi.mdifferentiableAt (by simp)) _
    (hPhi.mfderivToContinuousLinearEquiv (by simp)).surjective hf
  intro v w
  have heq := gSeqExt_inner_of_mem Phi R bf hsrc htgt k t x hx v w
  rw [hchi, one_smul, sub_self, zero_smul, add_zero] at heq
  exact heq.trans
    (PDE.RicciFlow.Perelman.KappaSolutions.pointed_srcMetric_inner_eq_pullback
      Phi hsrc htgt k t x hx v w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.normGradSqFun_gSeqExt_of_chi_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.normGradSqFun_gSeqExt_of_chi_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.normGradSqFun_gSeqExt_of_chi_eq_one ``Submission.DifferentialGeometry.CheegerGromovCompactness.normGradSqFun_gSeqExt_of_chi_eq_one

theorem eventually_normGradSqFun_gSeqExt_eq_on_compact
    (Phi : PointedCGHMaps X P phi) (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    {K : Set P.M} (hK : IsCompact K) :
    ∀ᶠ k in _root_.Filter.atTop, ∀ t : ℝ, ∀ x ∈ K, ∀ f : (X.term (phi k)).M → ℝ,
      MDifferentiableAt I 𝓘(ℝ, ℝ) f (Phi.map k x) →
      normGradSqFun (gSeqExt Phi R bf hsrc htgt k t) (f ∘ Phi.map k) x =
        normGradSqFun ((X.term (phi k)).S.base.metric t) f (Phi.map k x) := by
  obtain ⟨N, hN⟩ := bf.grow_cover K hK
  filter_upwards [_root_.Filter.eventually_ge_atTop N] with k hk
  intro t x hx f hf
  obtain ⟨W, _hW, hgrow, hchi⟩ := bf.chi_one k
  exact normGradSqFun_gSeqExt_of_chi_eq_one Phi R bf hsrc htgt k t x
    (bf.grow_subset k (hN k hk hx)) (hchi x (hgrow (hN k hk hx))) hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.eventually_normGradSqFun_gSeqExt_eq_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.eventually_normGradSqFun_gSeqExt_eq_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.eventually_normGradSqFun_gSeqExt_eq_on_compact ``Submission.DifferentialGeometry.CheegerGromovCompactness.eventually_normGradSqFun_gSeqExt_eq_on_compact

end DifferentialGeometry.CheegerGromovCompactness
