import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalClassificationReduction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.ENNReal _root_.Topology _root_.Submission.Topology

universe u

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

def windowedCanonicalPullback : Prop :=
  ∃ epsCan : ℝ, 0 < epsCan ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsCan →
    ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧ ∀ kappa : ℝ, 0 < kappa →
      ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
          (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
          IsSolutionOn S → ∀ (x : M) (t : ℝ),
          Set.Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
          WindowedModelWitness delta kappa S x t →
            Nonempty (CanonicalWitness S eps C1 C2 x t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.windowedCanonicalPullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.windowedCanonicalPullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.windowedCanonicalPullback ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.windowedCanonicalPullback

theorem kappaUniformCanonicalClassification_of_windowedCanonicalPullback
    (hpullback : windowedCanonicalPullback.{u}) :
    kappaUniformCanonicalClassification.{u} := by
  obtain ⟨epsCan, hepsCan, hmain⟩ := hpullback
  intro eps heps heps44
  obtain ⟨C1, C2, hC1, hC2, hfinal⟩ :=
    hmain (_root_.Min.min (eps / 2) epsCan) (lt_min (by linarith) hepsCan) (min_le_right _ _)
  refine ⟨C1, C2, hC1, hC2, fun kappa hkappa => ?_⟩
  obtain ⟨delta, hdelta, hdelta1, himp⟩ := hfinal kappa hkappa
  refine ⟨delta, hdelta, hdelta1, fun M _ _ _ _ _ D S hS o x t hreg hw => ?_⟩
  obtain ⟨W, _oN, _hO⟩ := hw
  obtain ⟨Wc⟩ := himp M D S hS x t hreg W
  exact ⟨Wc.mono_eps (min_le_left _ _) (by linarith)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.kappaUniformCanonicalClassification_of_windowedCanonicalPullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.kappaUniformCanonicalClassification_of_windowedCanonicalPullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.kappaUniformCanonicalClassification_of_windowedCanonicalPullback ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.kappaUniformCanonicalClassification_of_windowedCanonicalPullback

theorem kappaUniformCanonicalClassification_iff_scaled_tolerance {c : ℝ}
    (hc0 : 0 < c) (hc : c ≤ 1) :
    kappaUniformCanonicalClassification.{u} ↔
      (∀ eps : ℝ, 0 < eps → eps ≤ 1 / 44 →
        ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧ ∀ kappa : ℝ, 0 < kappa →
          ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
            ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
              [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
              (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
              IsSolutionOn S → ∀ (o : TangentOrientationSection M) (x : M) (t : ℝ),
              Set.Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
              OrientedWitness S o delta kappa x t →
                Nonempty (CanonicalWitness S (c * eps) C1 C2 x t)) := by
  constructor
  · intro hclass eps heps heps44
    have hpos : 0 < _root_.Min.min eps (2 * (c * eps)) := lt_min heps (by positivity)
    have hbound : _root_.Min.min eps (2 * (c * eps)) ≤ 1 / 44 := (min_le_left _ _).trans heps44
    obtain ⟨C1, C2, hC1, hC2, hmain⟩ := hclass (_root_.Min.min eps (2 * (c * eps))) hpos hbound
    refine ⟨C1, C2, hC1, hC2, fun kappa hkappa => ?_⟩
    obtain ⟨delta, hdelta, hdelta1, himp⟩ := hmain kappa hkappa
    refine ⟨delta, hdelta, hdelta1, fun M _ _ _ _ _ D S hS o x t hreg hw => ?_⟩
    obtain ⟨W⟩ := himp M D S hS o x t hreg hw
    have hle : _root_.Min.min eps (2 * (c * eps)) / 2 ≤ c * eps := by
      have h1 : _root_.Min.min eps (2 * (c * eps)) / 2 ≤ 2 * (c * eps) / 2 :=
        div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
      have h2 : 2 * (c * eps) / 2 = c * eps := by ring
      linarith [h1, h2]
    exact ⟨W.mono_eps hle (by nlinarith [heps.le, heps44, hc])⟩
  · intro hscaled eps heps heps44
    obtain ⟨C1, C2, hC1, hC2, hmain⟩ :=
      hscaled (eps / 2) (by linarith) (by linarith)
    refine ⟨C1, C2, hC1, hC2, fun kappa hkappa => ?_⟩
    obtain ⟨delta, hdelta, hdelta1, himp⟩ := hmain kappa hkappa
    refine ⟨delta, hdelta, hdelta1, fun M _ _ _ _ _ D S hS o x t hreg hw => ?_⟩
    obtain ⟨W⟩ := himp M D S hS o x t hreg hw
    have hle : c * (eps / 2) ≤ eps / 2 := by nlinarith [heps.le, hc]
    exact ⟨W.mono_eps hle (by linarith)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.kappaUniformCanonicalClassification_iff_scaled_tolerance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.kappaUniformCanonicalClassification_iff_scaled_tolerance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.kappaUniformCanonicalClassification_iff_scaled_tolerance ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.kappaUniformCanonicalClassification_iff_scaled_tolerance

theorem kappaUniformCanonicalClassification_iff_lt_two_elevenths :
    kappaUniformCanonicalClassification.{u} ↔
      (∀ eps : ℝ, 0 < eps → eps < 2 / 11 →
        ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧ ∀ kappa : ℝ, 0 < kappa →
          ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
            ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
              [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
              (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
              IsSolutionOn S → ∀ (o : TangentOrientationSection M) (x : M) (t : ℝ),
              Set.Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
              OrientedWitness S o delta kappa x t →
                Nonempty (CanonicalWitness S (eps / 2) C1 C2 x t)) := by
  constructor
  · intro hclass eps heps heps11
    have hpos : 0 < _root_.Min.min eps (1 / 44) := lt_min heps (by norm_num)
    have hbound : _root_.Min.min eps (1 / 44) ≤ 1 / 44 := min_le_right _ _
    obtain ⟨C1, C2, hC1, hC2, hmain⟩ := hclass (_root_.Min.min eps (1 / 44)) hpos hbound
    refine ⟨C1, C2, hC1, hC2, fun kappa hkappa => ?_⟩
    obtain ⟨delta, hdelta, hdelta1, himp⟩ := hmain kappa hkappa
    refine ⟨delta, hdelta, hdelta1, fun M _ _ _ _ _ D S hS o x t hreg hw => ?_⟩
    obtain ⟨W⟩ := himp M D S hS o x t hreg hw
    exact ⟨W.mono_eps (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
      (by linarith)⟩
  · intro hclass eps heps heps44
    exact hclass eps heps (by linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.kappaUniformCanonicalClassification_iff_lt_two_elevenths then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.kappaUniformCanonicalClassification_iff_lt_two_elevenths"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.kappaUniformCanonicalClassification_iff_lt_two_elevenths ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.kappaUniformCanonicalClassification_iff_lt_two_elevenths

theorem halfWindow_transfer_of_transfer {eps C1 C2 kappa : ℝ}
    (htransfer : ∀ (delta : ℝ)
      (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
      (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
      IsSolutionOn S → ∀ (x : M) (t : ℝ),
      Set.Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular → ∀ (W : WindowedModelWitness delta kappa S x t),
      Nonempty (CanonicalWitness W.model.S (eps / 2) C1 C2 W.model.basepoint 0) →
        Nonempty (CanonicalWitness S (eps / 2) C1 C2 x t)) :
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
      (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
      IsSolutionOn S → ∀ (x : M) (t : ℝ),
      Set.Ioo (t - ((1 / 2) * S.scalar t x)⁻¹) t ⊆ D.regular → ∀ (W : WindowedModelWitness (1 / 2) kappa S x t),
      Nonempty (CanonicalWitness W.model.S (eps / 2) C1 C2 W.model.basepoint 0) →
        Nonempty (CanonicalWitness S (eps / 2) C1 C2 x t) :=
  fun M _ _ _ _ _ D S hS x t hreg W hw => htransfer (1 / 2) M D S hS x t hreg W hw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.halfWindow_transfer_of_transfer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.halfWindow_transfer_of_transfer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.halfWindow_transfer_of_transfer ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.halfWindow_transfer_of_transfer

theorem kappaUniformCanonicalClassification_of_ancientModelClassification_halfWindow
    (hgap : ∀ (kappa : ℝ), 0 < kappa →
      ∀ P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval,
        IsAncientKappaSolution (I := I3) kappa P →
          IsShrinkingSphericalSpaceFormFlow (I := I3) P ∨
            IsAncientKappaSolution (I := I3) universalKappaConstant P)
    (hclass : ∀ eps : ℝ, 0 < eps → eps ≤ 1 / 44 →
      ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧
        ∀ P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval,
          (IsShrinkingSphericalSpaceFormFlow (I := I3) P ∨
            IsAncientKappaSolution (I := I3) universalKappaConstant P) →
          PointedFlowScalarAtBase (I := I3) P 1 →
            Nonempty (CanonicalWitness P.S (eps / 2) C1 C2 P.basepoint 0))
    (htransfer : ∀ (eps C1 C2 kappa : ℝ)
      (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
      (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
      IsSolutionOn S → ∀ (x : M) (t : ℝ),
      Set.Ioo (t - ((1 / 2) * S.scalar t x)⁻¹) t ⊆ D.regular → ∀ (W : WindowedModelWitness (1 / 2) kappa S x t),
      Nonempty (CanonicalWitness W.model.S (eps / 2) C1 C2 W.model.basepoint 0) →
        Nonempty (CanonicalWitness S (eps / 2) C1 C2 x t)) :
    kappaUniformCanonicalClassification.{u} := by
  intro eps heps heps44
  obtain ⟨C1, C2, hC1, hC2, hmain⟩ := hclass eps heps heps44
  refine ⟨C1, C2, hC1, hC2, fun kappa hkappa => ?_⟩
  refine ⟨1 / 2, by norm_num, by norm_num, fun M _ _ _ _ _ D S hS o x t hreg hw => ?_⟩
  obtain ⟨W, _oN, _hO⟩ := hw
  exact htransfer eps C1 C2 kappa M D S hS x t hreg W
    (hmain W.model (hgap kappa hkappa W.model W.model_ancient) W.model_scalar_base)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.kappaUniformCanonicalClassification_of_ancientModelClassification_halfWindow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.kappaUniformCanonicalClassification_of_ancientModelClassification_halfWindow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.kappaUniformCanonicalClassification_of_ancientModelClassification_halfWindow ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.kappaUniformCanonicalClassification_of_ancientModelClassification_halfWindow

theorem buffered_canonical_pullback_of_ancientModelClassification_halfWindow
    (hgap : ∀ (kappa : ℝ), 0 < kappa →
      ∀ P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval,
        IsAncientKappaSolution (I := I3) kappa P →
          IsShrinkingSphericalSpaceFormFlow (I := I3) P ∨
            IsAncientKappaSolution (I := I3) universalKappaConstant P)
    (hclass : ∀ eps : ℝ, 0 < eps → eps ≤ 1 / 44 →
      ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧
        ∀ P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval,
          (IsShrinkingSphericalSpaceFormFlow (I := I3) P ∨
            IsAncientKappaSolution (I := I3) universalKappaConstant P) →
          PointedFlowScalarAtBase (I := I3) P 1 →
            Nonempty (CanonicalWitness P.S (eps / 2) C1 C2 P.basepoint 0))
    (htransfer : ∀ (eps C1 C2 kappa : ℝ)
      (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
      (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
      IsSolutionOn S → ∀ (x : M) (t : ℝ),
      Set.Ioo (t - ((1 / 2) * S.scalar t x)⁻¹) t ⊆ D.regular → ∀ (W : WindowedModelWitness (1 / 2) kappa S x t),
      Nonempty (CanonicalWitness W.model.S (eps / 2) C1 C2 W.model.basepoint 0) →
        Nonempty (CanonicalWitness S (eps / 2) C1 C2 x t)) :
    ∃ epsCan : ℝ, 0 < epsCan ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsCan →
      ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧ ∀ kappa : ℝ, 0 < kappa →
        ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
          ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
            [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
            (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
            IsSolutionOn S → ∀ (o : TangentOrientationSection M) (x : M) (t : ℝ),
            Set.Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
            OrientedWitness S o delta kappa x t →
              Nonempty (CanonicalWitness S eps C1 C2 x t) :=
  buffered_canonical_pullback_of_classification
    (kappaUniformCanonicalClassification_of_ancientModelClassification_halfWindow
      hgap hclass htransfer)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.buffered_canonical_pullback_of_ancientModelClassification_halfWindow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.buffered_canonical_pullback_of_ancientModelClassification_halfWindow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.buffered_canonical_pullback_of_ancientModelClassification_halfWindow ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.buffered_canonical_pullback_of_ancientModelClassification_halfWindow

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
