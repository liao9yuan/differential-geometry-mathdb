import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckArmNoReturn
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TransverseCrossingPath

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set
open scoped _root_.Topology _root_.Submission.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M]


theorem exists_transversePath_of_neg_pos [T2Space M] {J : RealTimeInterval}
    {S : SolutionOn (I := I3) (M := M) J} {eps : ℝ} {x : M} {t : ℝ}
    (neck : StrongNeck S eps x t) (a b : MinimizingArm (S.base.metric t) x) {s v : ℝ}
    (hs : s ∈ _root_.Set.Icc (0 : ℝ) a.length) (hv : v ∈ _root_.Set.Icc (0 : ℝ) b.length)
    {p q : Sphere 2} {k l : ℝ}
    (ha : a.point s = neck.map (p, k)) (hb : b.point v = neck.map (q, l))
    (hkneg : k < 0) (hlpos : 0 < l) (hk : -k < eps⁻¹) (hl : l < eps⁻¹)
    (hano : ∀ w ∈ _root_.Set.Icc s a.length, a.point w ∉ neck.map '' (_root_.Set.univ ×ˢ ({0} : Set ℝ)))
    (hbno : ∀ w ∈ _root_.Set.Icc v b.length, b.point w ∉ neck.map '' (_root_.Set.univ ×ˢ ({0} : Set ℝ))) :
    ∃ path : TransversePath (a.point a.length) (b.point b.length)
        (neck.map '' (_root_.Set.univ ×ˢ ({0} : Set ℝ))),
      path.intersection = 1 := by
  obtain ⟨path, h1, -⟩ := exists_transversePath_of_opposite_arms neck a b hs hv ha hb
    (mul_neg_of_neg_of_pos hkneg hlpos) (by rw [abs_of_neg hkneg]; exact hk)
    (by rw [abs_of_pos hlpos]; exact hl) hano hbno
  exact ⟨path, h1 hlpos⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_transversePath_of_neg_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_transversePath_of_neg_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_transversePath_of_neg_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_transversePath_of_neg_pos


theorem exists_transversePath_of_pos_neg [T2Space M] {J : RealTimeInterval}
    {S : SolutionOn (I := I3) (M := M) J} {eps : ℝ} {x : M} {t : ℝ}
    (neck : StrongNeck S eps x t) (a b : MinimizingArm (S.base.metric t) x) {s v : ℝ}
    (hs : s ∈ _root_.Set.Icc (0 : ℝ) a.length) (hv : v ∈ _root_.Set.Icc (0 : ℝ) b.length)
    {p q : Sphere 2} {k l : ℝ}
    (ha : a.point s = neck.map (p, k)) (hb : b.point v = neck.map (q, l))
    (hkpos : 0 < k) (hlneg : l < 0) (hk : k < eps⁻¹) (hl : -l < eps⁻¹)
    (hano : ∀ w ∈ _root_.Set.Icc s a.length, a.point w ∉ neck.map '' (_root_.Set.univ ×ˢ ({0} : Set ℝ)))
    (hbno : ∀ w ∈ _root_.Set.Icc v b.length, b.point w ∉ neck.map '' (_root_.Set.univ ×ˢ ({0} : Set ℝ))) :
    ∃ path : TransversePath (a.point a.length) (b.point b.length)
        (neck.map '' (_root_.Set.univ ×ˢ ({0} : Set ℝ))),
      path.intersection = -1 := by
  obtain ⟨path, -, h2⟩ := exists_transversePath_of_opposite_arms neck a b hs hv ha hb
    (mul_neg_of_pos_of_neg hkpos hlneg) (by rw [abs_of_pos hkpos]; exact hk)
    (by rw [abs_of_neg hlneg]; exact hl) hano hbno
  exact ⟨path, h2 hlneg⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_transversePath_of_pos_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_transversePath_of_pos_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_transversePath_of_pos_neg ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_transversePath_of_pos_neg


theorem exists_transversePath_of_far_arms [T2Space M] :
    ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (J : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) J)
      (eps : ℝ) (x : M) (t : ℝ) (neck : StrongNeck S eps x t)
      (a b : MinimizingArm (S.base.metric t) x) (s v : ℝ),
      s ∈ _root_.Set.Icc (0 : ℝ) a.length → v ∈ _root_.Set.Icc (0 : ℝ) b.length →
      ∀ (p q : Sphere 2) (k l : ℝ),
      a.point s = neck.map (p, k) → b.point v = neck.map (q, l) →
      k * l < 0 → H₀ ≤ |k| → |k| < eps⁻¹ → H₀ ≤ |l| → |l| < eps⁻¹ →
      ∃ path : TransversePath (a.point a.length) (b.point b.length)
          (neck.map '' (_root_.Set.univ ×ˢ ({0} : Set ℝ))),
        (path.intersection = 1 ∨ path.intersection = -1) ∧
        (∀ w ∈ _root_.Set.Icc s a.length, a.point w ∉ neck.map '' (_root_.Set.univ ×ˢ ({0} : Set ℝ))) ∧
        (∀ w ∈ _root_.Set.Icc v b.length, b.point w ∉ neck.map '' (_root_.Set.univ ×ˢ ({0} : Set ℝ))) := by
  obtain ⟨H₀, hH₀, hno⟩ := exists_fixed_neck_two_arm_no_return_depth (M := M)
  refine ⟨H₀, hH₀, ?_⟩
  intro J S eps x t neck a b s v hs hv p q k l ha hb hkl hkdeep hk hldeep hl
  obtain ⟨hano, hbno⟩ :=
    hno J S eps x t neck a b s v hs hv p q k l ha hb hkdeep hk hldeep hl
  obtain ⟨path, h1, h2⟩ :=
    exists_transversePath_of_opposite_arms neck a b hs hv ha hb hkl hk hl hano hbno
  refine ⟨path, ?_, hano, hbno⟩
  rcases lt_trichotomy l 0 with hneg | hzero | hpos
  · exact Or.inr (h2 hneg)
  · exfalso
    rw [hzero, _root_.MulZeroClass.mul_zero] at hkl
    exact absurd hkl (lt_irrefl 0)
  · exact Or.inl (h1 hpos)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_transversePath_of_far_arms then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_transversePath_of_far_arms"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_transversePath_of_far_arms ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_transversePath_of_far_arms


noncomputable def twoArmNoReturnDepth [T2Space M] : ℝ :=
  Classical.choose (exists_transversePath_of_far_arms (M := M))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.twoArmNoReturnDepth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.twoArmNoReturnDepth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.twoArmNoReturnDepth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.twoArmNoReturnDepth

theorem twoArmNoReturnDepth_pos [T2Space M] : 0 < twoArmNoReturnDepth (M := M) :=
  (Classical.choose_spec (exists_transversePath_of_far_arms (M := M))).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.twoArmNoReturnDepth_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.twoArmNoReturnDepth_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.twoArmNoReturnDepth_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.twoArmNoReturnDepth_pos

theorem twoArmNoReturnDepth_spec [T2Space M]
    {J : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) J} {eps : ℝ} {x : M} {t : ℝ}
    (neck : StrongNeck S eps x t) (a b : MinimizingArm (S.base.metric t) x) {s v : ℝ}
    (hs : s ∈ _root_.Set.Icc (0 : ℝ) a.length) (hv : v ∈ _root_.Set.Icc (0 : ℝ) b.length)
    {p q : Sphere 2} {k l : ℝ}
    (ha : a.point s = neck.map (p, k)) (hb : b.point v = neck.map (q, l))
    (hkl : k * l < 0) (hk : twoArmNoReturnDepth (M := M) ≤ |k|) (hk' : |k| < eps⁻¹)
    (hl : twoArmNoReturnDepth (M := M) ≤ |l|) (hl' : |l| < eps⁻¹) :
    ∃ path : TransversePath (a.point a.length) (b.point b.length)
        (neck.map '' (_root_.Set.univ ×ˢ ({0} : Set ℝ))),
      (path.intersection = 1 ∨ path.intersection = -1) ∧
      (∀ w ∈ _root_.Set.Icc s a.length, a.point w ∉ neck.map '' (_root_.Set.univ ×ˢ ({0} : Set ℝ))) ∧
      (∀ w ∈ _root_.Set.Icc v b.length, b.point w ∉ neck.map '' (_root_.Set.univ ×ˢ ({0} : Set ℝ))) :=
  (Classical.choose_spec (exists_transversePath_of_far_arms (M := M))).2 J S eps x t neck a b s v
    hs hv p q k l ha hb hkl hk hk' hl hl'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.twoArmNoReturnDepth_spec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.twoArmNoReturnDepth_spec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.twoArmNoReturnDepth_spec ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.twoArmNoReturnDepth_spec

theorem exists_transversePath_of_neck_heights [T2Space M] {J : RealTimeInterval}
    {S : SolutionOn (I := I3) (M := M) J} {alpha : ℝ} {x : M} {t : ℝ}
    (neck : StrongNeck S (2 * alpha) x t) (a b : MinimizingArm (S.base.metric t) x)
    {s v : ℝ} (hs : s ∈ Set.Ioc 0 a.length) (hv : v ∈ Set.Ioc 0 b.length)
    {p q : Sphere 2} {k l : ℝ}
    (ha : a.point s = neck.map (p, k)) (hb : b.point v = neck.map (q, l))
    (hkl : k * l < 0) (hk : twoArmNoReturnDepth (M := M) ≤ |k|)
    (hk' : |k| < (2 * alpha)⁻¹) (hl : twoArmNoReturnDepth (M := M) ≤ |l|)
    (hl' : |l| < (2 * alpha)⁻¹) :
    ∃ path : TransversePath (a.point a.length) (b.point b.length)
        (neck.map '' (_root_.Set.univ ×ˢ ({0} : Set ℝ))),
      (path.intersection = 1 ∨ path.intersection = -1) ∧
      (∀ w ∈ _root_.Set.Icc s a.length, a.point w ∉ neck.map '' (_root_.Set.univ ×ˢ ({0} : Set ℝ))) ∧
      (∀ w ∈ _root_.Set.Icc v b.length, b.point w ∉ neck.map '' (_root_.Set.univ ×ˢ ({0} : Set ℝ))) :=
  twoArmNoReturnDepth_spec neck a b ⟨hs.1.le, hs.2⟩ ⟨hv.1.le, hv.2⟩ ha hb hkl hk hk' hl hl'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_transversePath_of_neck_heights then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_transversePath_of_neck_heights"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_transversePath_of_neck_heights ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_transversePath_of_neck_heights


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
