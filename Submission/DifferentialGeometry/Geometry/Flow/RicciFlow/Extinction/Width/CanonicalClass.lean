import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.Comparison
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FreeLoopClass

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

universe u uK

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [CompactSpace M]
  [ConnectedSpace M] [SimplyConnectedSpace M]

def canonicalWidth (g : SmoothRiemannianMetric ThreeModel M)
    (o : TangentOrientationSection M) : ℝ :=
  classWidth g (positiveFreeContractibleClass o)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.canonicalWidth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.canonicalWidth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.canonicalWidth ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.canonicalWidth

theorem canonicalWidth_nonneg (g : SmoothRiemannianMetric ThreeModel M)
    (o : TangentOrientationSection M) : 0 ≤ canonicalWidth g o :=
  classWidth_nonneg g (positiveFreeContractibleClass o)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.canonicalWidth_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.canonicalWidth_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.canonicalWidth_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.canonicalWidth_nonneg


theorem canonical_regularRepresentative_nonempty (o : TangentOrientationSection M) :
    Nonempty (RegularRepresentative (I := ThreeModel) (positiveFreeContractibleClass o)) :=
  regularRepresentative_nonempty (I := ThreeModel) (positiveFreeContractibleClass o)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.canonical_regularRepresentative_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.canonical_regularRepresentative_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.canonical_regularRepresentative_nonempty ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.canonical_regularRepresentative_nonempty

theorem canonicalWidth_smooth_near_minimizer (g : SmoothRiemannianMetric ThreeModel M)
    (o : TangentOrientationSection M) {n : ℕ}
    (e : SmoothLoopEmbedding (I := ThreeModel) (Q := M) n) {η : ℝ} (hη : 0 < η) :
    ∃ Γ : RegularRepresentative (I := ThreeModel) (positiveFreeContractibleClass o),
      familyMaximum g Γ.1 < canonicalWidth g o + η ∧
        HasContinuousSmoothLoopJets e Γ.1 :=
  rfs_width_finiteness g (positiveFreeContractibleClass o) e hη

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.canonicalWidth_smooth_near_minimizer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.canonicalWidth_smooth_near_minimizer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.canonicalWidth_smooth_near_minimizer ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.canonicalWidth_smooth_near_minimizer


theorem canonical_regularRepresentative_not_null
    (o : TangentOrientationSection M)
    (Γ : RegularRepresentative (I := ThreeModel) (positiveFreeContractibleClass o)) (q : M) :
    ¬ ContinuousMap.Homotopic (contractibleRegularLoopInclusion.comp Γ.1)
      (ContinuousMap.const (Sphere 2)
        (⟨constantLoops q, isContractibleLoop_constant q⟩ : ContractibleContinuousLoop M)) := by
  intro h
  apply positiveFreeContractibleClass_nontrivial o q
  exact Γ.2.symm.trans ((FreeHomotopyClass.mk_eq_mk_iff _ _).mpr h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.canonical_regularRepresentative_not_null then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.canonical_regularRepresentative_not_null"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.canonical_regularRepresentative_not_null ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.canonical_regularRepresentative_not_null

theorem rfs_canonical_short_loop_fillings (g : SmoothRiemannianMetric ThreeModel M)
    (o : TangentOrientationSection M) :
    ∃ σ K₀ : ℝ, 0 < σ ∧ 0 ≤ K₀ ∧
      (∀ (γ : ContinuousFreeLoop M), IsLipschitzLoop g γ → loopLength g γ < σ →
        ∃ u : DiskCompetitor g γ, diskArea g u.1.map ≤ K₀ * loopLength g γ ^ 2) ∧
      (∀ (K : Type uK) [TopologicalSpace K] [CompactSpace K]
        (Γ : RegularFamily (I := ThreeModel) (Q := M) K),
        (∀ k, loopLength g (Γ k).1.toContinuousLoop < σ) →
        ∃ F : C(_root_.Set.Icc (0 : ℝ) 1 × K,
            ContractibleRegularLoop (I := ThreeModel) (Q := M)),
          (∀ k, F (⟨0, by simp⟩, k) = Γ k) ∧
          ∀ k, F (⟨1, by simp⟩, k) = constantContractibleRegularLoop ((Γ k).1 0)) ∧
      (∀ Γ : RegularRepresentative (I := ThreeModel) (positiveFreeContractibleClass o),
        ∃ k : Sphere 2, σ ≤ loopLength g (Γ.1 k).1.toContinuousLoop) := by
  classical
  obtain ⟨σ, K₀, hσ, hK₀, hfill, hcontract, hnull⟩ := rfs_short_loop_fillings.{uK} g
  refine ⟨σ, K₀, hσ, hK₀, hfill, hcontract, ?_⟩
  intro Γ
  by_contra h
  have hshort : ∀ k, loopLength g (Γ.1 k).1.toContinuousLoop < σ := by
    intro k
    exact lt_of_not_ge (fun hk => h ⟨k, hk⟩)
  obtain ⟨q, hq⟩ := hnull (fun q => (rfs_homotopy_groups q).1) Γ.1 hshort
  exact canonical_regularRepresentative_not_null o Γ q hq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_canonical_short_loop_fillings then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_canonical_short_loop_fillings"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_canonical_short_loop_fillings ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_canonical_short_loop_fillings

theorem canonicalWidth_scale (g : SmoothRiemannianMetric ThreeModel M)
    (o : TangentOrientationSection M) {c : ℝ} (hc : 0 < c) :
    canonicalWidth (scaleMetric c hc g) o = c * canonicalWidth g o :=
  classWidth_scale g hc (positiveFreeContractibleClass o)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.canonicalWidth_scale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.canonicalWidth_scale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.canonicalWidth_scale ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.canonicalWidth_scale

variable {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
  [IsManifold ThreeModel ∞ N] [T2Space N] [CompactSpace N]
  [ConnectedSpace N] [SimplyConnectedSpace N]

theorem rfs_canonical_width_lipschitz
    (g : SmoothRiemannianMetric ThreeModel M) (h : SmoothRiemannianMetric ThreeModel N)
    (oM : TangentOrientationSection M) (oN : TangentOrientationSection N)
    (f : C(M, N)) (hdegree : orientedDegree oM oN f = 1) (L : ℝ≥0)
    (hf : ∀ x y, riemannianEDistOf h (f x) (f y) ≤
      (L : ℝ≥0∞) * riemannianEDistOf g x y) :
    canonicalWidth h oN ≤ (L : ℝ) ^ 2 * canonicalWidth g oM := by
  have hw := rfs_width_lipschitz g h f L hf (positiveFreeContractibleClass oM)
  rw [positiveFreeContractibleClass_natural oM oN f hdegree] at hw
  exact hw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_canonical_width_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_canonical_width_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_canonical_width_lipschitz ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_canonical_width_lipschitz

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
