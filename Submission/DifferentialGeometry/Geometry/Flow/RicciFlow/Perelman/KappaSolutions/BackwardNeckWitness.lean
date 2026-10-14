import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardForwardJetControl

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set _root_.Filter
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

private local instance backwardWitnessC1
    (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval) : IsManifold I3 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardWitnessC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardWitnessC1 target :: scope.openDecls } }

private theorem backwardNeck_normalizedMetric_inner
    (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)
    (tau : ℝ) (htau : 0 < tau) (q : F.M) (hQ : 0 < F.S.scalar (-tau) q)
    {epsilon : ℝ} {f : C(spatialNeckBuffer epsilon, F.M)}
    (hf : _root_.Manifold.IsSmoothEmbedding SpatialNeckCylinderModel I3 ∞ f)
    (s : ℝ) (x : spatialNeckBuffer epsilon)
    (v w : TangentSpace SpatialNeckCylinderModel x) :
    (strongNeckNormalizedMetric F.S q (-tau) hQ hf s).inner x v w =
      (scaleMetric (tau * F.S.scalar (-tau) q) (mul_pos htau hQ)
        (immersionInducedMetric (backwardScaledMetric F.S tau htau
          (1 - s / (tau * F.S.scalar (-tau) q))) hf.isImmersion)).inner x v w := by
  rw [strongNeckNormalizedMetric_inner, scaleMetric_inner, immersionInducedMetric_inner]
  have hmetric := congrArg (fun g : SmoothRiemannianMetric I3 F.M =>
      g.inner (f x) (mfderiv SpatialNeckCylinderModel I3 f x v)
        (mfderiv SpatialNeckCylinderModel I3 f x w))
    (backwardForwardNeck_metric_eq F.S tau (F.S.scalar (-tau) q) htau hQ s)
  simpa only [rescaledMetric, scaleMetric_inner, parabolicTime, div_eq_mul_inv, mul_comm] using hmetric

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardNeck_normalizedMetric_inner
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardNeck_normalizedMetric_inner target :: scope.openDecls } }


theorem backwardComparison_strongNeckWitness
    (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon_one : epsilon < 1)
    (tau : ℝ) (htau : 0 < tau) (q : F.M) (yStar : SpatialNeckSphere)
    (f : C(spatialNeckBuffer epsilon, F.M))
    (hf : _root_.Manifold.IsSmoothEmbedding SpatialNeckCylinderModel I3 ∞ f)
    (hmarked : f (spatialNeckCentralPoint epsilon hepsilon yStar) = q)
    (hfactor : (1 : ℝ) / 2 ≤ tau * F.S.scalar (-tau) q)
    (J : ℕ → ℝ → Tensor0SField (I := SpatialNeckCylinderModel)
      (M := spatialNeckBuffer epsilon) (n := ∞) 2)
    (hzero : ∀ theta ∈ _root_.Set.Icc (1 : ℝ) 3, ∀ x v,
      J 0 theta x v = (backwardScaledMetric F.S tau htau theta).inner (f x)
        (mfderiv SpatialNeckCylinderModel I3 f x (v 0))
        (mfderiv SpatialNeckCylinderModel I3 f x (v 1)) -
          (strongNeckBackgroundMetric epsilon (1 - theta)).inner x (v 0) (v 1))
    (hderiv : ∀ b theta, theta ∈ _root_.Set.Icc (1 : ℝ) 3 → ∀ (x : spatialNeckBuffer epsilon)
      (v : Fin 2 → TangentSpace SpatialNeckCylinderModel x),
      HasDerivWithinAt (fun r => J b r x v) (J (b + 1) theta x v) (_root_.Set.Icc (1 : ℝ) 3) theta)
    (hclose : StrongNeckJetControl epsilon
      (backwardForwardErrorJet epsilon (tau * F.S.scalar (-tau) q) J)) :
    ∃ W : StrongNeckWitness F.S yStar q (-tau) epsilon, W.embedding = f := by
  have hQ : 0 < F.S.scalar (-tau) q := by
    by_contra hnonpos
    have hn := mul_nonpos_of_nonneg_of_nonpos htau.le (le_of_not_gt hnonpos)
    linarith
  let G (theta : ℝ) := immersionInducedMetric (backwardScaledMetric F.S tau htau theta)
    hf.isImmersion
  have hG : ∀ theta ∈ _root_.Set.Icc (1 : ℝ) 3, ∀ x v,
      J 0 theta x v = (G theta).inner x (v 0) (v 1) -
        (strongNeckBackgroundMetric epsilon (1 - theta)).inner x (v 0) (v 1) := by
    intro theta htheta x v
    rw [immersionInducedMetric_inner]
    exact hzero theta htheta x v
  let W : StrongNeckWitness F.S yStar q (-tau) epsilon := {
    dimension_three := by simp [ThreeSpace]
    isSolution := F.isSolution
    epsilon_pos := hepsilon
    epsilon_lt_one := hepsilon_one
    scalar_pos := hQ
    time_window := by
      intro t ht
      change t ≤ 0
      exact ht.2.trans (neg_nonpos.mpr htau.le)
    embedding := f
    smooth_embedding := hf
    marked := hmarked
    jet := backwardForwardErrorJet epsilon (tau * F.S.scalar (-tau) q) J
    jet_zero := by
      intro s hs x v
      have hjet := backwardForwardErrorJet_zero epsilon (tau * F.S.scalar (-tau) q)
        hfactor G J hG s hs x v
      have hmetric := backwardNeck_normalizedMetric_inner F tau htau q hQ hf s x (v 0) (v 1)
      exact hjet.trans (congrArg (fun r : ℝ =>
        r - (strongNeckBackgroundMetric epsilon s).inner x (v 0) (v 1)) hmetric.symm)
    jet_succ := backwardForwardErrorJet_hasDerivWithinAt epsilon
      (tau * F.S.scalar (-tau) q) hfactor J hderiv
    closeness := hclose }
  exact ⟨W, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardComparison_strongNeckWitness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardComparison_strongNeckWitness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardComparison_strongNeckWitness ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardComparison_strongNeckWitness


theorem backwardComparison_eventually_strongNeckWitness
    (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon_one : epsilon < 1)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M) (yStar : SpatialNeckSphere)
    (f : ℕ → C(spatialNeckBuffer epsilon, F.M))
    (J : ℕ → ℕ → ℝ → Tensor0SField (I := SpatialNeckCylinderModel)
      (M := spatialNeckBuffer epsilon) (n := ∞) 2)
    (hfactor : _root_.Filter.Tendsto (fun i => tau i * F.S.scalar (-tau i) (q i)) _root_.Filter.atTop (𝓝 (1 : ℝ)))
    (hdata : ∀ᶠ i in _root_.Filter.atTop,
      _root_.Manifold.IsSmoothEmbedding SpatialNeckCylinderModel I3 ∞ (f i) ∧
      f i (spatialNeckCentralPoint epsilon hepsilon yStar) = q i ∧
      (∀ theta ∈ _root_.Set.Icc (1 : ℝ) 3, ∀ x v,
        J i 0 theta x v = (backwardScaledMetric F.S (tau i) (htau i) theta).inner (f i x)
          (mfderiv SpatialNeckCylinderModel I3 (f i) x (v 0))
          (mfderiv SpatialNeckCylinderModel I3 (f i) x (v 1)) -
            (strongNeckBackgroundMetric epsilon (1 - theta)).inner x (v 0) (v 1)) ∧
      (∀ b theta, theta ∈ _root_.Set.Icc (1 : ℝ) 3 → ∀ (x : spatialNeckBuffer epsilon)
        (v : Fin 2 → TangentSpace SpatialNeckCylinderModel x),
        HasDerivWithinAt (fun r => J i b r x v) (J i (b + 1) theta x v)
          (_root_.Set.Icc (1 : ℝ) 3) theta))
    (hconv : ∀ eta : ℝ, 0 < eta → ∀ᶠ i in _root_.Filter.atTop,
      ∀ a b : ℕ, a + 2 * b ≤ Nat.ceil epsilon⁻¹ →
      ∀ theta ∈ _root_.Set.Icc (1 : ℝ) 3, ∀ x ∈ spatialNeckClosedCore epsilon,
        tensor02CovDerivNormWith a (J i b theta)
          (strongNeckBackgroundMetric epsilon (1 - theta))
          (strongNeckBackgroundMetric epsilon (1 - theta)) x ≤ eta) :
    ∀ᶠ i in _root_.Filter.atTop, ∃ W : StrongNeckWitness F.S yStar (q i) (-tau i) epsilon,
      W.embedding = f i := by
  have hhalf : ∀ᶠ i in _root_.Filter.atTop, (1 : ℝ) / 2 ≤ tau i * F.S.scalar (-tau i) (q i) :=
    ((tendsto_order.1 hfactor).1 (1 / 2) (by norm_num)).mono fun _ hi => hi.le
  have hcontrol := backwardForwardErrorJet_eventually_control epsilon hepsilon J hfactor hconv
  filter_upwards [hdata, hhalf, hcontrol] with i hi hhalf_i hcontrol_i
  exact backwardComparison_strongNeckWitness F epsilon hepsilon hepsilon_one (tau i) (htau i)
    (q i) yStar (f i) hi.1 hi.2.1 hhalf_i (J i) hi.2.2.1 hi.2.2.2 hcontrol_i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardComparison_eventually_strongNeckWitness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardComparison_eventually_strongNeckWitness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardComparison_eventually_strongNeckWitness ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardComparison_eventually_strongNeckWitness

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
