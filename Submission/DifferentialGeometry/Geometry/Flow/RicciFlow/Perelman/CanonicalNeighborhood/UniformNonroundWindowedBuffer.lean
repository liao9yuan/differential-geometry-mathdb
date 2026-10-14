import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedNonroundBufferedLimit
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalCapCollar
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalKappaGap
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalToleranceMonotone
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientKappaFixedCompactness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointNeckArmReduction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section
set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

theorem exists_universal_nonround_windowed_buffer_constant_with_cap_neck_charts
    {alpha : ℝ} (ha : 0 < alpha) (hasmall : alpha < 1 / 11) (H : ℝ) :
    ∃ C delta0 : ℝ, 1 ≤ C ∧ 0 < delta0 ∧ delta0 < 1 ∧
      ∀ (kappa : ℝ) (D : RealTimeInterval) (P : PointedFlowData.{u, 0, 0} I3 D)
        (delta t : ℝ) (W : WindowedModelWitness delta kappa P.S P.basepoint t),
        delta ≤ delta0 → _root_.Set.Ioo (t - (delta * P.S.scalar t P.basepoint)⁻¹) t ⊆ D.regular →
        (¬ IsShrinkingSphericalSpaceFormFlow W.model) → TangentOrientationSection W.model.M →
        ∃ B : BufferedCanonical P.S alpha C H P.basepoint t,
          B.witness.capTubeHasNeckChart alpha := by
  classical
  by_contra hnone
  have hbad (n : ℕ) : ∃ (kappa : ℝ) (D : RealTimeInterval) (P : PointedFlowData.{u, 0, 0} I3 D)
      (delta t : ℝ) (W : WindowedModelWitness delta kappa P.S P.basepoint t),
      delta ≤ 1 / ((n : ℝ) + 2) ∧ _root_.Set.Ioo (t - (delta * P.S.scalar t P.basepoint)⁻¹) t ⊆ D.regular ∧
      (¬ IsShrinkingSphericalSpaceFormFlow W.model) ∧ Nonempty (TangentOrientationSection W.model.M) ∧
      ¬ ∃ B : BufferedCanonical P.S alpha ((n : ℝ) + 1) H P.basepoint t,
        B.witness.capTubeHasNeckChart alpha := by
    by_contra hn
    push Not at hn
    apply hnone
    refine ⟨(n : ℝ) + 1, 1 / ((n : ℝ) + 2), by linarith [Nat.cast_nonneg (α := ℝ) n], by positivity, ?_, ?_⟩
    · apply (div_lt_one (by positivity : 0 < (n : ℝ) + 2)).mpr
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · intro kappa D P delta t W hd hreg hnc o
      exact hn kappa D P delta t W hd hreg hnc ⟨o⟩
  choose kappa D P delta t W hdelta hregular hnotround horient hfail using hbad
  let W0 (i : ℕ) : WindowedModelWitness (delta i) universalKappaConstant (P i).S (P i).basepoint (t i) :=
    { W i with model_ancient := ((ancientKappaThree_universal_kappa_gap (W i).model (W i).model_ancient (by simp [ThreeSpace])).resolve_left (hnotround i)) }
  have hzero : _root_.Filter.Tendsto delta _root_.Filter.atTop (𝓝 0) := by
    have hbound : _root_.Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) _root_.Filter.atTop (𝓝 0) := by
      have hnat : _root_.Filter.Tendsto (fun n : ℕ => (n : ℝ) + 2) _root_.Filter.atTop atTop := _root_.Filter.tendsto_atTop_add_const_right _root_.Filter.atTop 2 tendsto_natCast_atTop_atTop
      simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hnat
    exact squeeze_zero (fun i => (W i).eps_pos.le) hdelta hbound
  let models := fun i => (W0 i).model
  obtain ⟨L, phi, hphi, Phi, hL, hLbase, _hKL, _hconv, hcmp⟩ :=
    exists_ancientKappa_fixed_kappa_compactness models (fun i => (W0 i).model_ancient)
      (fun i => (W0 i).model_scalar_base)
  let F : PointedRiemannianConvergenceMaps ⟨fun i => (W0 i).model.atTime 0⟩ (L.atTime 0) phi :=
    Phi.atTime (X := ancientPointedFlowSeq models) (L := L) 0
  have hcmp' : ∀ K : Set L.M, IsCompact K → ∀ A : ℝ, 0 < A → ∀ order : ℕ,
      ∀ eta : ℝ, 0 < eta → ∀ᶠ i in _root_.Filter.atTop,
        Nonempty (MetricComparisonOn L.S.base.metric (W0 (phi i)).model.S.base.metric
          (F.map i) K (_root_.Set.Icc (-A) 0) order eta) :=
    fun K hK A hA order eta heta => hcmp (-A) 0 (by linarith) le_rfl K hK order eta heta
  obtain ⟨C, _hC, hbuffer⟩ := exists_eventually_buffered_with_cap_neck_charts_of_nonround_oriented_windowed_models
    (fun i => (P i).isSolution) W0 hzero hregular L hphi.tendsto_atTop F hcmp' hL hLbase hnotround
    (fun i => Classical.choice (horient i)) ha hasmall H
  have hlarge : ∀ᶠ i in _root_.Filter.atTop, C < (phi i : ℝ) + 1 :=
    ((_root_.Filter.tendsto_atTop_add_const_right _root_.Filter.atTop 1 tendsto_natCast_atTop_atTop).comp hphi.tendsto_atTop).eventually_gt_atTop C
  obtain ⟨i, hi, hCi⟩ := (hbuffer.and hlarge).exists
  obtain ⟨B, hB⟩ := hi
  apply hfail (phi i)
  refine ⟨B.enlarge_constants hCi, ?_⟩
  change (B.witness.enlarge_constants hCi.le hCi.le).capTubeHasNeckChart alpha
  exact hB.enlarge_constants hCi.le hCi.le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_universal_nonround_windowed_buffer_constant_with_cap_neck_charts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_universal_nonround_windowed_buffer_constant_with_cap_neck_charts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_universal_nonround_windowed_buffer_constant_with_cap_neck_charts ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_universal_nonround_windowed_buffer_constant_with_cap_neck_charts

theorem exists_universal_nonround_windowed_buffer_constant
    {alpha : ℝ} (ha : 0 < alpha) (hasmall : alpha < 1 / 11) (H : ℝ) :
    ∃ C delta0 : ℝ, 1 ≤ C ∧ 0 < delta0 ∧ delta0 < 1 ∧
      ∀ (kappa : ℝ) (D : RealTimeInterval) (P : PointedFlowData.{u, 0, 0} I3 D)
        (delta t : ℝ) (W : WindowedModelWitness delta kappa P.S P.basepoint t),
        delta ≤ delta0 → _root_.Set.Ioo (t - (delta * P.S.scalar t P.basepoint)⁻¹) t ⊆ D.regular →
        (¬ IsShrinkingSphericalSpaceFormFlow W.model) → TangentOrientationSection W.model.M →
        Nonempty (BufferedCanonical P.S alpha C H P.basepoint t) := by
  obtain ⟨C, delta0, hC, hd, hd1, hmain⟩ :=
    exists_universal_nonround_windowed_buffer_constant_with_cap_neck_charts.{u} ha hasmall H
  refine ⟨C, delta0, hC, hd, hd1, ?_⟩
  intro kappa D P delta t W hdelta hreg hnc orient
  obtain ⟨B, _⟩ := hmain kappa D P delta t W hdelta hreg hnc orient
  exact ⟨B⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_universal_nonround_windowed_buffer_constant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_universal_nonround_windowed_buffer_constant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_universal_nonround_windowed_buffer_constant ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_universal_nonround_windowed_buffer_constant

theorem exists_universal_nonround_windowed_bufferedCanonical_with_cap_neck_charts
    {alpha : ℝ} (ha : 0 < alpha) (hasmall : alpha < 1 / 11) (H : ℝ) :
    ∃ C delta0 : ℝ, 1 ≤ C ∧ 0 < delta0 ∧ delta0 < 1 ∧
      ∀ (kappa : ℝ) (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
        IsSolutionOn S → ∀ (delta : ℝ) (x : M) (t : ℝ)
          (W : WindowedModelWitness delta kappa S x t),
          delta ≤ delta0 → _root_.Set.Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
          (¬ IsShrinkingSphericalSpaceFormFlow W.model) → TangentOrientationSection W.model.M →
          ∃ B : BufferedCanonical S alpha C H x t, B.witness.capTubeHasNeckChart alpha := by
  obtain ⟨C, delta0, hC, hd, hd1, hmain⟩ := exists_universal_nonround_windowed_buffer_constant_with_cap_neck_charts.{u} ha hasmall H
  refine ⟨C, delta0, hC, hd, hd1, ?_⟩
  intro kappa M _ _ _ _ _ D S hS delta x t W hdelta hreg hnc orient
  let P : PointedFlowData.{u, 0, 0} I3 D := { M := M, basepoint := x, S := S, isSolution := hS }
  exact hmain kappa D P delta t W hdelta hreg hnc orient

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_universal_nonround_windowed_bufferedCanonical_with_cap_neck_charts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_universal_nonround_windowed_bufferedCanonical_with_cap_neck_charts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_universal_nonround_windowed_bufferedCanonical_with_cap_neck_charts ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_universal_nonround_windowed_bufferedCanonical_with_cap_neck_charts

theorem exists_universal_nonround_windowed_bufferedCanonical
    {alpha : ℝ} (ha : 0 < alpha) (hasmall : alpha < 1 / 11) (H : ℝ) :
    ∃ C delta0 : ℝ, 1 ≤ C ∧ 0 < delta0 ∧ delta0 < 1 ∧
      ∀ (kappa : ℝ) (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
        IsSolutionOn S → ∀ (delta : ℝ) (x : M) (t : ℝ)
          (W : WindowedModelWitness delta kappa S x t),
          delta ≤ delta0 → _root_.Set.Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
          (¬ IsShrinkingSphericalSpaceFormFlow W.model) → TangentOrientationSection W.model.M →
          Nonempty (BufferedCanonical S alpha C H x t) := by
  obtain ⟨C, delta0, hC, hd, hd1, hmain⟩ :=
    exists_universal_nonround_windowed_bufferedCanonical_with_cap_neck_charts.{u} ha hasmall H
  refine ⟨C, delta0, hC, hd, hd1, ?_⟩
  intro kappa M _ _ _ _ _ D S hS delta x t W hdelta hreg hnc orient
  obtain ⟨B, _⟩ := hmain kappa M D S hS delta x t W hdelta hreg hnc orient
  exact ⟨B⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_universal_nonround_windowed_bufferedCanonical then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_universal_nonround_windowed_bufferedCanonical"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_universal_nonround_windowed_bufferedCanonical ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_universal_nonround_windowed_bufferedCanonical

theorem exists_universal_nonround_windowed_canonicalWitness
    {eps : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11) :
    ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧ ∀ kappa : ℝ,
      ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
          (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
          IsSolutionOn S → ∀ (x : M) (t : ℝ) (W : WindowedModelWitness delta kappa S x t),
          _root_.Set.Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
          (¬ IsShrinkingSphericalSpaceFormFlow W.model) → TangentOrientationSection W.model.M →
          Nonempty (CanonicalWitness S eps C1 C2 x t) := by
  obtain ⟨C, delta, hC, hd, hd1, hmain⟩ := exists_universal_nonround_windowed_bufferedCanonical.{u} heps hsmall 1
  refine ⟨C, C, hC, hC, fun kappa => ⟨delta, hd, hd1, ?_⟩⟩
  intro M _ _ _ _ _ D S hS x t W hreg hnc orient
  obtain ⟨B⟩ := hmain kappa M D S hS delta x t W le_rfl hreg hnc orient
  exact ⟨B.canonicalWitness_mono B.tolerance_lt.le hsmall⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_universal_nonround_windowed_canonicalWitness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_universal_nonround_windowed_canonicalWitness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_universal_nonround_windowed_canonicalWitness ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_universal_nonround_windowed_canonicalWitness

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
