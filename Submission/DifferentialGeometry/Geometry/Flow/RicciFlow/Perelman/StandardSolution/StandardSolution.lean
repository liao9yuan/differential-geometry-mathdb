import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.LifetimeInterval
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Metric
import Submission.DifferentialGeometry.Geometry.Metric.Completeness
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }

structure PartialStandardSolution where
  lifetime : ℝ≥0∞
  lifetime_pos : 0 < lifetime
  metric : ℝ → SmoothRiemannianMetric (𝓡 3) E3
  smooth : ContDiffOn ℝ ∞ (F := E3 →L[ℝ] E3 →L[ℝ] ℝ)
    (fun p : ℝ × E3 => by exact (metric p.1).inner p.2)
    ((lifetimeInterval lifetime lifetime_pos).carrier ×ˢ (_root_.Set.univ : Set E3))
  equation : ∀ t ∈ (lifetimeInterval lifetime lifetime_pos).carrier,
    ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
      HasDerivWithinAt (fun s => (metric s).inner x v w)
        (-2 * ricciTensor (metric t) x v w) (_root_.Set.Ici 0) t
  initial : metric 0 = DifferentialGeometry.PDE.RicciFlow.StandardCap.metric
  complete : ∀ t ∈ (lifetimeInterval lifetime lifetime_pos).carrier,
    RiemannianMetricComplete (metric t)
  curvature_bound : ∀ θ : ℝ, 0 ≤ θ → ENNReal.ofReal θ < lifetime →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ _root_.Set.Icc 0 θ, ∀ x : E3,
      Real.sqrt (normSq0S (metric t) x 4 (metricRm04 (metric t) x)) ≤ K

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution

namespace PartialStandardSolution

abbrev domain (S : PartialStandardSolution) : Set ℝ :=
  (lifetimeInterval S.lifetime S.lifetime_pos).carrier

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.domain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.domain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.domain ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.domain

def IsExtendedBy (S S' : PartialStandardSolution) : Prop :=
  S.lifetime ≤ S'.lifetime ∧ ∀ t ∈ S.domain, S'.metric t = S.metric t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.IsExtendedBy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.IsExtendedBy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.IsExtendedBy ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.IsExtendedBy

theorem isExtendedBy_refl (S : PartialStandardSolution) : S.IsExtendedBy S :=
  ⟨le_rfl, fun _ _ => rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.isExtendedBy_refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.isExtendedBy_refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.isExtendedBy_refl ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.isExtendedBy_refl

theorem isExtendedBy_trans {S S' S'' : PartialStandardSolution}
    (h : S.IsExtendedBy S') (h' : S'.IsExtendedBy S'') : S.IsExtendedBy S'' := by
  refine ⟨h.1.trans h'.1, ?_⟩
  intro t ht
  exact (h'.2 t (lifetimeInterval_carrier_mono S.lifetime_pos S'.lifetime_pos h.1 ht)).trans
    (h.2 t ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.isExtendedBy_trans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.isExtendedBy_trans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.isExtendedBy_trans ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.isExtendedBy_trans

theorem lifetime_eq_and_metric_eq_of_mutual_extension {S S' : PartialStandardSolution}
    (h : S.IsExtendedBy S') (h' : S'.IsExtendedBy S) :
    S.lifetime = S'.lifetime ∧ ∀ t ∈ S.domain, S'.metric t = S.metric t :=
  ⟨le_antisymm h.1 h'.1, h.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.lifetime_eq_and_metric_eq_of_mutual_extension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.lifetime_eq_and_metric_eq_of_mutual_extension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.lifetime_eq_and_metric_eq_of_mutual_extension ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.lifetime_eq_and_metric_eq_of_mutual_extension

def IsMaximal (S : PartialStandardSolution) : Prop :=
  ∀ S' : PartialStandardSolution, S.IsExtendedBy S' → S'.IsExtendedBy S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.IsMaximal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.IsMaximal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.IsMaximal ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.IsMaximal

theorem isMaximal_iff_no_strict_extension (S : PartialStandardSolution) :
    S.IsMaximal ↔ ¬ ∃ S' : PartialStandardSolution,
      S.IsExtendedBy S' ∧ S.lifetime < S'.lifetime := by
  constructor
  · intro h ⟨S', he, hlt⟩
    exact (not_le_of_gt hlt) (h S' he).1
  · intro h S' he
    have hle : S'.lifetime ≤ S.lifetime := by
      by_contra hn
      exact h ⟨S', he, lt_of_not_ge hn⟩
    refine ⟨hle, ?_⟩
    intro t ht
    exact (he.2 t (lifetimeInterval_carrier_mono S'.lifetime_pos S.lifetime_pos hle ht)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.isMaximal_iff_no_strict_extension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.isMaximal_iff_no_strict_extension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.isMaximal_iff_no_strict_extension ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.isMaximal_iff_no_strict_extension

def restrict (S : PartialStandardSolution) (T : ℝ≥0∞) (hT : 0 < T)
    (hTS : T ≤ S.lifetime) : PartialStandardSolution where
  lifetime := T
  lifetime_pos := hT
  metric := S.metric
  smooth := S.smooth.mono (_root_.Set.prod_mono
    (lifetimeInterval_carrier_mono hT S.lifetime_pos hTS) Subset.rfl)
  equation := fun t ht => S.equation t
    (lifetimeInterval_carrier_mono hT S.lifetime_pos hTS ht)
  initial := S.initial
  complete := fun t ht => S.complete t
    (lifetimeInterval_carrier_mono hT S.lifetime_pos hTS ht)
  curvature_bound := fun θ hθ hθT => S.curvature_bound θ hθ (hθT.trans_le hTS)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.restrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.restrict ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.restrict

theorem restrict_metric (S : PartialStandardSolution) (T : ℝ≥0∞) (hT : 0 < T)
    (hTS : T ≤ S.lifetime) : (S.restrict T hT hTS).metric = S.metric := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.restrict_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.restrict_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.restrict_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.restrict_metric

theorem restrict_isExtendedBy (S : PartialStandardSolution) (T : ℝ≥0∞) (hT : 0 < T)
    (hTS : T ≤ S.lifetime) : (S.restrict T hT hTS).IsExtendedBy S :=
  ⟨hTS, fun _ _ => rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.restrict_isExtendedBy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.restrict_isExtendedBy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.restrict_isExtendedBy ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.restrict_isExtendedBy

theorem not_isMaximal_restrict (S : PartialStandardSolution) (T : ℝ≥0∞) (hT : 0 < T)
    (hTS : T < S.lifetime) : ¬ (S.restrict T hT hTS.le).IsMaximal := by
  intro hmax
  exact (not_le_of_gt hTS) (hmax S (S.restrict_isExtendedBy T hT hTS.le)).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.not_isMaximal_restrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.not_isMaximal_restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.not_isMaximal_restrict ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.not_isMaximal_restrict

theorem initial_equation (S : PartialStandardSolution) (x : E3)
    (v w : TangentSpace (𝓡 3) x) :
    HasDerivWithinAt (fun t => (S.metric t).inner x v w)
      (-2 * ricciTensor DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x v w) (_root_.Set.Ici 0) 0 := by
  have h := S.equation 0 ((mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos 0).mpr
    ⟨le_rfl, by simpa using S.lifetime_pos⟩) x v w
  simpa only [S.initial] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.initial_equation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.initial_equation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.initial_equation ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.initial_equation
end PartialStandardSolution

def StandardSolution := {S : PartialStandardSolution // S.IsMaximal}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardSolution
end DifferentialGeometry.PDE.RicciFlow
