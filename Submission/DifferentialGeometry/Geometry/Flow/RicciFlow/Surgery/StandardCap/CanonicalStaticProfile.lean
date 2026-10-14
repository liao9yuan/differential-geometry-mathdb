import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Neck
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
  {d : normalizedDatum g x₀ δ k} {A D ε : ℝ} {hA : 0 < A} {m : ℕ}

theorem CanonicalStaticInsertionWitness.profileTip_neg
    (w : CanonicalStaticInsertionWitness d A hA D m ε) :
    w.data.profileTip < 0 := by
  have htip := w.properties.profileTip_location.2
  linarith [transitionEnd_pos]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.profileTip_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.profileTip_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.profileTip_neg ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.profileTip_neg

theorem CanonicalStaticInsertionWitness.profile_derivWithin_mem_Icc
    (w : CanonicalStaticInsertionWitness d A hA D m ε)
    {z : ℝ} (hz : z ∈ _root_.Set.Icc w.data.profileTip 0) :
    derivWithin w.data.profile (_root_.Set.Icc w.data.profileTip 0) z ∈ _root_.Set.Icc (0 : ℝ) 1 := by
  rw [(w.properties.profile_smooth.differentiable (by simp) z).derivWithin
    (uniqueDiffOn_Icc w.profileTip_neg z hz)]
  exact w.properties.profile_speed z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.profile_derivWithin_mem_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.profile_derivWithin_mem_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.profile_derivWithin_mem_Icc ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.profile_derivWithin_mem_Icc

theorem CanonicalStaticInsertionWitness.profile_tip_germ
    (w : CanonicalStaticInsertionWitness d A hA D m ε) :
    ∃ e : ℝ, 0 < e ∧
      ∀ z ∈ _root_.Set.Icc w.data.profileTip (_root_.Min.min 0 (w.data.profileTip + e)),
        w.data.profile z = z - w.data.profileTip := by
  obtain ⟨e, he, h⟩ := w.properties.profile_linear
  exact ⟨e, he, fun z hz => h z (hz.2.trans (min_le_right _ _))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.profile_tip_germ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.profile_tip_germ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.profile_tip_germ ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.profile_tip_germ

theorem CanonicalStaticInsertionWitness.profile_collar_eq_standardCapRadiusOfZ
    (w : CanonicalStaticInsertionWitness d A hA D m ε)
    {z : ℝ} (hz : z ∈ _root_.Set.Icc (-2 * A) 0) :
    w.data.profile z = standardCapRadiusOfZ z := by
  rw [standardCapRadiusOfZ_eq_conformalRadius]
  exact w.properties.profile_collar z hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.profile_collar_eq_standardCapRadiusOfZ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.profile_collar_eq_standardCapRadiusOfZ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.profile_collar_eq_standardCapRadiusOfZ ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.profile_collar_eq_standardCapRadiusOfZ

theorem CanonicalStaticInsertionWitness.profile_properties
    (w : CanonicalStaticInsertionWitness d A hA D m ε) :
    ContinuousOn w.data.profile (_root_.Set.Icc w.data.profileTip 0) ∧
      MonotoneOn w.data.profile (_root_.Set.Icc w.data.profileTip 0) ∧
      _root_.Set.MapsTo w.data.profile (_root_.Set.Icc w.data.profileTip 0) (_root_.Set.Icc 0 standardCapL) ∧
      ContDiffOn ℝ ∞ w.data.profile (_root_.Set.Ioc w.data.profileTip 0) ∧
      w.data.profile w.data.profileTip = 0 ∧
      w.data.profile 0 = standardCapL ∧
      (∀ z ∈ _root_.Set.Ioc w.data.profileTip 0,
        0 ≤ derivWithin w.data.profile (_root_.Set.Icc w.data.profileTip 0) z ∧
          derivWithin w.data.profile (_root_.Set.Icc w.data.profileTip 0) z ≤ 1) ∧
      (∃ e : ℝ, 0 < e ∧
        ∀ z ∈ _root_.Set.Icc w.data.profileTip (_root_.Min.min 0 (w.data.profileTip + e)),
          w.data.profile z = z - w.data.profileTip) ∧
      (∀ z ∈ _root_.Set.Icc (-2 * A) 0, w.data.profile z = standardCapRadiusOfZ z) := by
  refine ⟨w.properties.profile_smooth.continuous.continuousOn,
    w.properties.profile_monotone.monotoneOn _, w.properties.profile_mapsTo,
    w.properties.profile_smooth.contDiffOn, w.properties.profile_tip,
    w.properties.profile_zero, ?_, w.profile_tip_germ,
    fun z hz => w.profile_collar_eq_standardCapRadiusOfZ hz⟩
  intro z hz
  exact w.profile_derivWithin_mem_Icc ⟨hz.1.le, hz.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.profile_properties then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.profile_properties"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.profile_properties ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.profile_properties

end DifferentialGeometry.PDE.RicciFlow.StandardCap
