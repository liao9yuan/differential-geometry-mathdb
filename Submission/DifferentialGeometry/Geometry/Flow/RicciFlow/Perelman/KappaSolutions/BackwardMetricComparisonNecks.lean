import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardNeckWitness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardComparisonTimeJets
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedDomainEmbedding

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set _root_.Filter
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

private local instance backwardComparisonNeckC1
    (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval) : IsManifold I3 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardComparisonNeckC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardComparisonNeckC1 target :: scope.openDecls } }

private local instance backwardComparisonNeckLimitC1
    (L : PointedRiemannianManifold.{u, 0, 0} (I := I3)) : IsManifold I3 1 L.M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardComparisonNeckLimitC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardComparisonNeckLimitC1 target :: scope.openDecls } }

private local instance backwardComparisonNeckBufferSigma (epsilon : ℝ) :
    SigmaCompactSpace (spatialNeckBuffer epsilon) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen SpatialNeckCylinderModel (spatialNeckBuffer epsilon).isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardComparisonNeckBufferSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardComparisonNeckBufferSigma target :: scope.openDecls } }


theorem backwardMetricComparisons_eventually_strongNeckWitness
    (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon_one : epsilon < 1)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M) (yStar : SpatialNeckSphere)
    (f : ℕ → C(spatialNeckBuffer epsilon, F.M))
    (hfactor : _root_.Filter.Tendsto (fun i => tau i * F.S.scalar (-tau i) (q i)) _root_.Filter.atTop (𝓝 (1 : ℝ)))
    (hmaps : ∀ᶠ i in _root_.Filter.atTop, _root_.Manifold.IsSmoothEmbedding SpatialNeckCylinderModel I3 ∞ (f i) ∧
      f i (spatialNeckCentralPoint epsilon hepsilon yStar) = q i)
    (hcomparison : ∀ eta : ℝ, 0 < eta → ∀ᶠ i in _root_.Filter.atTop,
      Nonempty (MetricComparisonOn
        (fun theta => strongNeckBackgroundMetric epsilon (1 - theta))
        (backwardScaledMetric F.S (tau i) (htau i)) (f i) _root_.Set.univ
        (_root_.Set.Icc (1 : ℝ) 3) (Nat.ceil epsilon⁻¹) eta)) :
    ∀ᶠ i in _root_.Filter.atTop, ∃ W : StrongNeckWitness F.S yStar (q i) (-tau i) epsilon,
      W.embedding = f i := by
  let c (i : ℕ) := tau i * F.S.scalar (-tau i) (q i)
  let order := Nat.ceil epsilon⁻¹
  let K : ℝ := _root_.Max.max 1 (Real.sqrt ((3 : ℝ) ^ (order + 2)))
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hhalf : ∀ᶠ i in _root_.Filter.atTop, (1 : ℝ) / 2 ≤ c i :=
    ((tendsto_order.1 hfactor).1 (1 / 2) (by norm_num)).mono fun _ hi => hi.le
  have hcoeff (b : ℕ) : ∀ᶠ i in _root_.Filter.atTop, |c i * (-(c i)⁻¹) ^ b| ≤ 2 := by
    have hlim : _root_.Filter.Tendsto (fun i => |c i * (-(c i)⁻¹) ^ b|) _root_.Filter.atTop (𝓝 (1 : ℝ)) := by
      simpa only [abs_pow, abs_neg, abs_one, one_pow] using
        (backwardForward_jet_coefficient_tendsto hfactor b).abs
    exact ((tendsto_order.1 hlim).2 2 (by norm_num)).mono fun _ hi => hi.le
  have hcoeffs : ∀ᶠ i in _root_.Filter.atTop,
      ∀ b ∈ Finset.range (order + 1), |c i * (-(c i)⁻¹) ^ b| ≤ 2 :=
    (_root_.Filter.eventually_all_finset (Finset.range (order + 1))).2 (fun b _hb => hcoeff b)
  have hmodelLimit : _root_.Filter.Tendsto (fun i => |c i - 1| * (3 * Real.sqrt 3)) _root_.Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, abs_zero, _root_.MulZeroClass.zero_mul] using
      ((hfactor.sub_const 1).abs.mul_const (3 * Real.sqrt 3))
  have hmodel : ∀ᶠ i in _root_.Filter.atTop, |c i - 1| * (3 * Real.sqrt 3) ≤ epsilon / 4 :=
    ((tendsto_order.1 hmodelLimit).2 (epsilon / 4) (by positivity)).mono fun _ hi => hi.le
  have heta : 0 < epsilon / (8 * K) := div_pos hepsilon (mul_pos (by norm_num) hK)
  filter_upwards [hmaps, hhalf, hcoeffs, hmodel, hcomparison (epsilon / (8 * K)) heta]
    with i hmaps_i hhalf_i hcoeff_i hmodel_i hcomparison_i
  obtain ⟨C⟩ := hcomparison_i
  have hclose : StrongNeckJetControl epsilon (backwardForwardErrorJet epsilon (c i) C.jet) := by
    apply backwardForwardErrorJet_control epsilon hepsilon (c i) hhalf_i C.jet ?_ hmodel_i ?_
    · intro b hb
      exact hcoeff_i b (Finset.mem_range.mpr (by dsimp only [order]; omega))
    · intro a b hab theta htheta x _hx
      exact C.close a b hab theta htheta x (_root_.Set.mem_univ x)
  apply backwardComparison_strongNeckWitness F epsilon hepsilon hepsilon_one
    (tau i) (htau i) (q i) yStar (f i) hmaps_i.1 hmaps_i.2 hhalf_i C.jet ?_ ?_ hclose
  · intro theta _htheta x v
    exact (C.jet_zero theta x v).trans
      (congrArg (fun r : ℝ => r - (strongNeckBackgroundMetric epsilon (1 - theta)).inner
        x (v 0) (v 1)) (C.pullback_eq theta x (_root_.Set.mem_univ x) v))
  · exact backwardMetricComparison_hasDerivWithinAt F (tau i) (htau i) epsilon C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardMetricComparisons_eventually_strongNeckWitness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardMetricComparisons_eventually_strongNeckWitness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardMetricComparisons_eventually_strongNeckWitness ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardMetricComparisons_eventually_strongNeckWitness


theorem canonicalBackwardMetricComparisons_eventually_strongNeckWitness
    (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {L : PointedRiemannianManifold.{u, 0, 0} (I := I3)} {phi : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps (I := I3) (backwardSliceSequence F tau htau q) L phi)
    (C : MetricConvergenceData (I := I3) Phi)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData Phi i)
    (hscalar : metricScalarAt L.metric L.basepoint = 1)
    (e : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, I3⟯ L.M)
    (yStar : SpatialNeckSphere) (hmarked : e (yStar, 0) = L.basepoint)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon_one : epsilon < 1)
    (hcomparison : ∀ eta : ℝ, 0 < eta → ∀ᶠ i in _root_.Filter.atTop,
      Nonempty (MetricComparisonOn
        (fun theta => strongNeckBackgroundMetric epsilon (1 - theta))
        (backwardScaledMetric F.S (tau (phi i)) (htau (phi i)))
        (fun x : spatialNeckBuffer epsilon => Phi.map i (e (x : SpatialNeckCylinder))) _root_.Set.univ
        (_root_.Set.Icc (1 : ℝ) 3) (Nat.ceil epsilon⁻¹) eta)) :
    ∀ᶠ i in _root_.Filter.atTop,
      ∃ W : StrongNeckWitness F.S yStar (q (phi i)) (-tau (phi i)) epsilon,
        ∀ x : spatialNeckBuffer epsilon, W.embedding x = Phi.map i (e (x : SpatialNeckCylinder)) := by
  classical
  let U := spatialNeckBuffer epsilon
  let Kbuffer : Set SpatialNeckCylinder :=
    (_root_.Set.univ : Set SpatialNeckSphere) ×ˢ _root_.Set.Icc (-epsilon⁻¹ - 1) (epsilon⁻¹ + 1)
  have hbuffer : IsCompact Kbuffer := isCompact_univ.prod _root_.CompactIccSpace.isCompact_Icc
  have hUbuffer : (U : Set SpatialNeckCylinder) ⊆ Kbuffer := by
    intro x hx
    exact ⟨mem_univ _, hx.1.le, hx.2.le⟩
  obtain ⟨i0, hi0⟩ := Phi.source_subset (hbuffer.image e.continuous)
  have hsource : ∀ᶠ i in _root_.Filter.atTop, e '' (U : Set SpatialNeckCylinder) ⊆ Phi.source i :=
    eventually_atTop.2 ⟨i0, fun i hi => (_root_.Set.image_mono hUbuffer).trans (hi0 i hi)⟩
  let f (i : ℕ) : C(U, F.M) :=
    if hU : e '' (U : Set SpatialNeckCylinder) ⊆ Phi.source i then
      pointedDomainEmbedding Phi e U i hU
    else ContinuousMap.const U (q (phi i))
  have hmaps : ∀ᶠ i in _root_.Filter.atTop, _root_.Manifold.IsSmoothEmbedding SpatialNeckCylinderModel I3 ∞ (f i) ∧
      ∀ x : U, f i x = Phi.map i (e (x : SpatialNeckCylinder)) := by
    filter_upwards [hsource] with i hi
    dsimp only [f]
    rw [dif_pos hi]
    exact ⟨pointedMaps_restrict_isSmoothEmbedding Phi e U i hi, fun _ => rfl⟩
  have hcomparison_f : ∀ eta : ℝ, 0 < eta → ∀ᶠ i in _root_.Filter.atTop,
      Nonempty (MetricComparisonOn
        (fun theta => strongNeckBackgroundMetric epsilon (1 - theta))
        (backwardScaledMetric F.S (tau (phi i)) (htau (phi i))) (f i) _root_.Set.univ
        (_root_.Set.Icc (1 : ℝ) 3) (Nat.ceil epsilon⁻¹) eta) := by
    intro eta heta
    filter_upwards [hcomparison eta heta, hmaps] with i hi hmaps_i
    have hfeq : (f i : U → F.M) = fun x : U => Phi.map i (e (x : SpatialNeckCylinder)) :=
      funext hmaps_i.2
    rw [hfeq]
    exact hi
  have hfactor := backwardScalarFactor_tendsto_one F tau htau q Phi C hcanonical hscalar
  have hgood : ∀ᶠ i in _root_.Filter.atTop, _root_.Manifold.IsSmoothEmbedding SpatialNeckCylinderModel I3 ∞ (f i) ∧
      f i (spatialNeckCentralPoint epsilon hepsilon yStar) = q (phi i) := by
    filter_upwards [hmaps] with i hi
    refine ⟨hi.1, ?_⟩
    rw [hi.2]
    change Phi.map i (e (yStar, 0)) = q (phi i)
    rw [hmarked]
    exact Phi.basepoint_map i
  have hwitness := backwardMetricComparisons_eventually_strongNeckWitness F epsilon
    hepsilon hepsilon_one (fun i => tau (phi i)) (fun i => htau (phi i))
    (fun i => q (phi i)) yStar f hfactor hgood hcomparison_f
  filter_upwards [hwitness, hmaps] with i hi hmaps_i
  obtain ⟨W, hW⟩ := hi
  refine ⟨W, ?_⟩
  intro x
  exact (congrArg (fun g => g x) hW).trans (hmaps_i.2 x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.canonicalBackwardMetricComparisons_eventually_strongNeckWitness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.canonicalBackwardMetricComparisons_eventually_strongNeckWitness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.canonicalBackwardMetricComparisons_eventually_strongNeckWitness ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.canonicalBackwardMetricComparisons_eventually_strongNeckWitness

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
