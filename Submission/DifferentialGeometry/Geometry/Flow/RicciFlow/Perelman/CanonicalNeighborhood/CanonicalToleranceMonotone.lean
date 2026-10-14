import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonComposition
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckTransportDecoupled
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BufferedCanonical

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

def LocalNeck.mono_eps {eps eps' : ℝ} {x : M} {t : ℝ} {U : Set M}
    (L : LocalNeck S eps x t U) (heps : eps ≤ eps') (hsmall : eps' < 1 / 11) :
    LocalNeck S eps' x t U where
  strong := L.strong.mono heps hsmall
  region_eq := L.region_eq
  boundary_eq := L.boundary_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalNeck.mono_eps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalNeck.mono_eps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalNeck.mono_eps ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalNeck.mono_eps

def OrderedNeckChain.mono_eps {eps eps' t : ℝ} {V : Set M}
    (c : OrderedNeckChain S eps t V) (heps : eps ≤ eps') (hsmall : eps' < 1 / 11) :
    OrderedNeckChain S eps' t V where
  count := c.count
  count_pos := c.count_pos
  centers := c.centers
  necks := fun i => (c.necks i).mono heps hsmall
  lo := c.lo
  hi := c.hi
  lo_lt_hi := c.lo_lt_hi
  inside := c.inside
  swept_eq := c.swept_eq
  transition_increasing := c.transition_increasing

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.OrderedNeckChain.mono_eps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.OrderedNeckChain.mono_eps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.OrderedNeckChain.mono_eps ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.OrderedNeckChain.mono_eps

def LocalCap.mono_eps {eps eps' : ℝ} {x : M} {t : ℝ} {U : Set M}
    (C : LocalCap S eps x t U) (heps : eps ≤ eps') (hsmall : eps' < 1 / 11) :
    LocalCap S eps' x t U where
  core := C.core
  core_inside := C.core_inside
  center_inside := C.center_inside
  core_model := C.core_model
  tube := C.tube
  tube_map := C.tube_map
  tube_domain := C.tube_domain
  tube_eq := C.tube_eq
  union_eq := C.union_eq
  overlap_eq := C.overlap_eq
  inner_boundary := C.inner_boundary
  outer_boundary := C.outer_boundary
  boundary_eq := C.boundary_eq
  boundaries_disjoint := C.boundaries_disjoint
  chain := C.chain.mono_eps heps hsmall
  core_boundary_map := C.core_boundary_map
  core_boundary_eq := C.core_boundary_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.mono_eps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.mono_eps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.mono_eps ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.mono_eps

def RoundComponent.mono_eps {eps eps' : ℝ} {x : M} {t : ℝ} {U : Set M}
    (R : RoundComponent S eps x t U) (hpos : 0 < eps) (heps : eps ≤ eps') :
    RoundComponent S eps' x t U := by
  letI : TopologicalSpace R.Z := R.topology
  letI : ChartedSpace ThreeSpace R.Z := R.charted
  letI : IsManifold I3 ∞ R.Z := R.smooth
  letI : T2Space R.Z := R.t2
  letI : CompactSpace R.Z := R.compact
  letI : ConnectedSpace R.Z := R.connected
  exact
    { Z := R.Z
      topology := R.topology
      charted := R.charted
      smooth := R.smooth
      t2 := R.t2
      compact := R.compact
      connected := R.connected
      metric := R.metric
      p := R.p
      scalar_one := R.scalar_one
      constant_curvature := R.constant_curvature
      map := R.map
      source_eq := R.source_eq
      target_eq := R.target_eq
      center_eq := R.center_eq
      Q_pos := R.Q_pos
      comparison := R.comparison.mono (subset_refl _)
        (Nat.ceil_mono (inv_anti₀ hpos heps)) heps
      metric_bounds := R.metric_bounds }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RoundComponent.mono_eps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RoundComponent.mono_eps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RoundComponent.mono_eps ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RoundComponent.mono_eps

def CanonicalAlternative.mono_eps {eps eps' C : ℝ} {x : M} {t : ℝ} {U : Set M}
    (A : CanonicalAlternative S eps C x t U) (hpos : 0 < eps) (heps : eps ≤ eps')
    (hsmall : eps' < 1 / 11) : CanonicalAlternative S eps' C x t U := by
  cases A with
  | neck data => exact .neck (data.mono_eps heps hsmall)
  | cap data deep => exact .cap (data.mono_eps heps hsmall) deep
  | positive whole data sec => exact .positive whole data sec
  | round whole data => exact .round whole (data.mono_eps hpos heps)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalAlternative.mono_eps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalAlternative.mono_eps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalAlternative.mono_eps ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalAlternative.mono_eps

omit [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem CanonicalAlternative.mono_eps_requiresVolume {eps eps' C : ℝ} {x : M} {t : ℝ}
    {U : Set M} (A : CanonicalAlternative S eps C x t U) (hpos : 0 < eps) (heps : eps ≤ eps')
    (hsmall : eps' < 1 / 11) :
    (A.mono_eps hpos heps hsmall).requiresVolume = A.requiresVolume := by
  cases A <;> rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalAlternative.mono_eps_requiresVolume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalAlternative.mono_eps_requiresVolume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalAlternative.mono_eps_requiresVolume ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalAlternative.mono_eps_requiresVolume

def CanonicalWitness.mono_eps {eps eps' C1 C2 : ℝ} {x : M} {t : ℝ}
    (W : CanonicalWitness S eps C1 C2 x t)
    (heps : eps ≤ eps') (hsmall : eps' < 1 / 11) :
    CanonicalWitness S eps' C1 C2 x t where
  Q_pos := W.Q_pos
  time_mem := W.time_mem
  eps_pos := W.eps_pos.trans_le heps
  eps_lt_one := lt_trans hsmall (by norm_num)
  domain := W.domain
  center_inside := W.center_inside
  radius := W.radius
  radius_lower := W.radius_lower
  radius_upper := W.radius_upper
  ball_inside := W.ball_inside
  inside_ball := W.inside_ball
  scalar_bounds := W.scalar_bounds
  rm_bound := W.rm_bound
  alternative := W.alternative.mono_eps W.eps_pos heps hsmall
  volume := by
    intro hv
    exact W.volume (by
      simpa only [CanonicalAlternative.mono_eps_requiresVolume] using hv)
  gradient := W.gradient
  time_derivative := W.time_derivative

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.mono_eps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.mono_eps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.mono_eps ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.mono_eps

def BufferedCanonical.canonicalWitness_mono {alpha C H : ℝ} {x : M} {t : ℝ}
    (B : BufferedCanonical S alpha C H x t) {eps : ℝ}
    (heps : B.tolerance ≤ eps) (hsmall : eps < 1 / 11) :
    CanonicalWitness S eps C C x t :=
  B.witness.mono_eps heps hsmall

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.BufferedCanonical.canonicalWitness_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.BufferedCanonical.canonicalWitness_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.BufferedCanonical.canonicalWitness_mono ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.BufferedCanonical.canonicalWitness_mono

def kappaUniformCanonicalClassification : Prop :=
  ∀ eps : ℝ, 0 < eps → eps ≤ 1 / 44 →
    ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧ ∀ kappa : ℝ, 0 < kappa →
      ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
          (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
          IsSolutionOn S → ∀ (o : TangentOrientationSection M) (x : M) (t : ℝ),
          Set.Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
          OrientedWitness S o delta kappa x t →
            Nonempty (CanonicalWitness S (eps / 2) C1 C2 x t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.kappaUniformCanonicalClassification then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.kappaUniformCanonicalClassification"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.kappaUniformCanonicalClassification ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.kappaUniformCanonicalClassification

theorem buffered_canonical_pullback_of_classification
    (hclass : kappaUniformCanonicalClassification.{u}) :
    ∃ epsCan : ℝ, 0 < epsCan ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsCan →
      ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧ ∀ kappa : ℝ, 0 < kappa →
        ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
          ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
            [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
            (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
            IsSolutionOn S → ∀ (o : TangentOrientationSection M) (x : M) (t : ℝ),
            Set.Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
            OrientedWitness S o delta kappa x t →
              Nonempty (CanonicalWitness S eps C1 C2 x t) := by
  refine ⟨1 / 44, by norm_num, fun eps heps heps44 => ?_⟩
  obtain ⟨C1, C2, h1, h2, hmain⟩ := hclass eps heps heps44
  refine ⟨C1, C2, h1, h2, fun kappa hk => ?_⟩
  obtain ⟨delta, hd, hd1, himp⟩ := hmain kappa hk
  refine ⟨delta, hd, hd1, fun M _ _ _ _ _ D S hS o x t hreg hw => ?_⟩
  obtain ⟨W⟩ := himp M D S hS o x t hreg hw
  exact ⟨W.mono_eps (by linarith) (by linarith)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.buffered_canonical_pullback_of_classification then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.buffered_canonical_pullback_of_classification"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.buffered_canonical_pullback_of_classification ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.buffered_canonical_pullback_of_classification

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
