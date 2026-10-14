import Submission.DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CrossVolumeNaturality

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem crossModelBall_edist_le_of_pullback_inner
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → N) (hf : ContMDiff I J ∞ f)
    (hmetric : ∀ (x : M) (v w : TangentSpace I x),
      h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) =
        g.inner x v w) (x y : M) :
    riemannianEDistOf (I := J) h (f x) (f y) ≤
      riemannianEDistOf (I := I) g x y := by
  rw [edistOf_iInf, edistOf_iInf]
  refine le_iInf fun gamma => le_iInf fun hgamma => ?_
  have hmap : ContMDiff (𝓡∂ 1) J 1 (gamma.map hf.continuous) := by
    change ContMDiff (𝓡∂ 1) J 1 (f ∘ gamma)
    exact (hf.of_le (by simp)).comp hgamma
  refine iInf_le_of_le (gamma.map hf.continuous) (iInf_le_of_le hmap ?_)
  apply le_of_eq
  apply _root_.MeasureTheory.lintegral_congr
  intro t
  have hderiv : mfderiv (𝓡∂ 1) J (gamma.map hf.continuous) t 1 =
      mfderiv I J f (gamma t) (mfderiv (𝓡∂ 1) I gamma t 1) := by
    change mfderiv (𝓡∂ 1) J (f ∘ gamma) t 1 = _
    exact mfderiv_comp_apply t (hf.mdifferentiable (by simp) (gamma t))
      (hgamma.mdifferentiable one_ne_zero t) 1
  change ENNReal.ofReal (Real.sqrt (h.inner (f (gamma t))
    (mfderiv (𝓡∂ 1) J (gamma.map hf.continuous) t 1)
    (mfderiv (𝓡∂ 1) J (gamma.map hf.continuous) t 1))) = _
  rw [hderiv, hmetric]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossModelBall_edist_le_of_pullback_inner
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossModelBall_edist_le_of_pullback_inner target :: scope.openDecls } }

variable [FiniteDimensional ℝ E] [T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDistOf_pullbackMetricCross
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N) (x y : M) :
    riemannianEDistOf (I := I) (Diffeomorph.pullbackMetricCross g Phi) x y =
      riemannianEDistOf (I := J) g (Phi x) (Phi y) := by
  have hsymm : ∀ (z : N) (v w : TangentSpace J z),
      (Diffeomorph.pullbackMetricCross g Phi).inner (Phi.symm z)
        (mfderiv J I (Phi.symm : N → M) z v)
        (mfderiv J I (Phi.symm : N → M) z w) = g.inner z v w := by
    intro z v w
    have hd :=
      (Phi.toOpenPartialHomeomorph_mdifferentiable (by simp)).comp_symm_deriv
        (x := z) (by trivial)
    have hdv := congrArg (fun L => L v) hd
    have hdw := congrArg (fun L => L w) hd
    change mfderiv I J (Phi : M → N) (Phi.symm z)
      (mfderiv J I (Phi.symm : N → M) z v) = v at hdv
    change mfderiv I J (Phi : M → N) (Phi.symm z)
      (mfderiv J I (Phi.symm : N → M) z w) = w at hdw
    rw [Diffeomorph.pullbackMetricCross_inner, hdv, hdw]
    exact congrArg (fun q => (g.inner q : F →L[ℝ] F →L[ℝ] ℝ) v w)
      (Phi.apply_symm_apply z)
  apply le_antisymm
  · simpa only [Phi.symm_apply_apply] using
      crossModelBall_edist_le_of_pullback_inner g
        (Diffeomorph.pullbackMetricCross g Phi) Phi.symm Phi.symm.contMDiff
        hsymm (Phi x) (Phi y)
  · apply crossModelBall_edist_le_of_pullback_inner
      (Diffeomorph.pullbackMetricCross g Phi) g Phi Phi.contMDiff _ x y
    intro z v w
    exact (Diffeomorph.pullbackMetricCross_inner g Phi z v w).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.riemannianEDistOf_pullbackMetricCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.riemannianEDistOf_pullbackMetricCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.riemannianEDistOf_pullbackMetricCross ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.riemannianEDistOf_pullbackMetricCross

theorem preimage_riemannianBallOf_pullbackMetricCross
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    (x : M) (r : ℝ) :
    (Phi : M → N) ⁻¹' riemannianBallOf (I := J) g (Phi x) r =
      riemannianBallOf (I := I) (Diffeomorph.pullbackMetricCross g Phi) x r := by
  ext y
  change (riemannianEDistOf (I := J) g (Phi x) (Phi y) < ENNReal.ofReal r) ↔
    (riemannianEDistOf (I := I) (Diffeomorph.pullbackMetricCross g Phi) x y <
      ENNReal.ofReal r)
  rw [riemannianEDistOf_pullbackMetricCross]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.preimage_riemannianBallOf_pullbackMetricCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.preimage_riemannianBallOf_pullbackMetricCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.preimage_riemannianBallOf_pullbackMetricCross ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.preimage_riemannianBallOf_pullbackMetricCross

theorem image_riemannianBallOf_pullbackMetricCross
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    (x : M) (r : ℝ) :
    (Phi : M → N) ''
        riemannianBallOf (I := I) (Diffeomorph.pullbackMetricCross g Phi) x r =
      riemannianBallOf (I := J) g (Phi x) r := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    change riemannianEDistOf (I := J) g (Phi x) (Phi z) < ENNReal.ofReal r
    rw [← riemannianEDistOf_pullbackMetricCross]
    exact hz
  · intro hy
    refine ⟨Phi.symm y, ?_, Phi.apply_symm_apply y⟩
    change riemannianEDistOf (I := I) (Diffeomorph.pullbackMetricCross g Phi)
      x (Phi.symm y) < ENNReal.ofReal r
    rw [riemannianEDistOf_pullbackMetricCross, Phi.apply_symm_apply]
    exact hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.image_riemannianBallOf_pullbackMetricCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.image_riemannianBallOf_pullbackMetricCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.image_riemannianBallOf_pullbackMetricCross ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.image_riemannianBallOf_pullbackMetricCross

section Volume

variable [I.Boundaryless] [FiniteDimensional ℝ F] [CompleteSpace E] [CompleteSpace F]
  [SigmaCompactSpace M] [T2Space N] [SigmaCompactSpace N]

private local instance crossModelBallMeasurableM : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossModelBallMeasurableM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossModelBallMeasurableM target :: scope.openDecls } }
private local instance crossModelBallBorelM : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossModelBallBorelM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossModelBallBorelM target :: scope.openDecls } }
private local instance crossModelBallMeasurableN : MeasurableSpace N := borel N

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossModelBallMeasurableN
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossModelBallMeasurableN target :: scope.openDecls } }
private local instance crossModelBallBorelN : BorelSpace N := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossModelBallBorelN
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossModelBallBorelN target :: scope.openDecls } }

omit [CompleteSpace E] [CompleteSpace F] in
theorem riemannianBallOf_volume_pullbackMetricCross
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    (x : M) (r : ℝ) :
    riemannianVolumeMeasure (I := I) (M := M)
        (Diffeomorph.pullbackMetricCross g Phi)
        (riemannianBallOf (I := I) (Diffeomorph.pullbackMetricCross g Phi) x r) =
      riemannianVolumeMeasure (I := J) (M := N) g
        (riemannianBallOf (I := J) g (Phi x) r) := by
  have hPhi : MeasurableEmbedding (Phi : M → N) :=
    Phi.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have hvolume :=
    (volumeMeasurePreserving_pullbackMetricCross g Phi).measure_preimage_emb hPhi
      (riemannianBallOf (I := J) g (Phi x) r)
  rw [preimage_riemannianBallOf_pullbackMetricCross] at hvolume
  exact hvolume

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.riemannianBallOf_volume_pullbackMetricCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.riemannianBallOf_volume_pullbackMetricCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.riemannianBallOf_volume_pullbackMetricCross ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.riemannianBallOf_volume_pullbackMetricCross

end Volume

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
