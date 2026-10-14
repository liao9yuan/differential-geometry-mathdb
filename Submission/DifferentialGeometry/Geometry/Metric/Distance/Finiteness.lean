import Submission.DifferentialGeometry.Geometry.Metric.Distance.Basic
import Mathlib.Geometry.Manifold.Riemannian.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Filter _root_.Bundle _root_.Manifold
open scoped _root_.Topology _root_.Manifold _root_.ContDiff _root_.ENNReal

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (TangentSpace I : M → Type _)]

open _root_.Manifold in
theorem Manifold.riemannianEDist_lt_top
    [PreconnectedSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (p q : M) : _root_.Manifold.riemannianEDist I p q < (⊤ : ℝ≥0∞) := by
  set S : Set M := {z : M | _root_.Manifold.riemannianEDist I p z ≠ ⊤} with hS
  have hpS : p ∈ S := by
    simp only [hS, Set.mem_ofPred_eq, _root_.Manifold.riemannianEDist_self]; exact ENNReal.zero_ne_top
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro z₀ hz₀
    have hfin : _root_.Manifold.riemannianEDist I p z₀ ≠ ⊤ := hz₀
    have hloc : ∀ᶠ z in nhds z₀, _root_.Manifold.riemannianEDist I z₀ z < (1 : ℝ≥0∞) :=
      eventually_riemannianEDist_lt I z₀ one_pos
    filter_upwards [hloc] with z hz
    simp only [hS, Set.mem_ofPred_eq]
    have htri : _root_.Manifold.riemannianEDist I p z ≤
        riemannianEDist I p z₀ + _root_.Manifold.riemannianEDist I z₀ z := _root_.Manifold.riemannianEDist_triangle
    have hlt : _root_.Manifold.riemannianEDist I p z < ⊤ :=
      lt_of_le_of_lt htri
        (ENNReal.add_lt_top.mpr ⟨lt_of_le_of_ne le_top hfin,
          lt_of_lt_of_le hz (by norm_num)⟩)
    exact hlt.ne
  have hScompl_open : IsOpen Sᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro z₀ hz₀
    have hinf : _root_.Manifold.riemannianEDist I p z₀ = ⊤ := by
      simpa only [hS, Set.mem_compl_iff, Set.mem_ofPred_eq, _root_.Classical.not_not] using hz₀
    have hloc : ∀ᶠ z in nhds z₀, _root_.Manifold.riemannianEDist I z₀ z < (1 : ℝ≥0∞) :=
      eventually_riemannianEDist_lt I z₀ one_pos
    filter_upwards [hloc] with z hz
    simp only [hS, Set.mem_compl_iff, Set.mem_ofPred_eq, _root_.Classical.not_not]
    by_contra hpz
    have hpz' : _root_.Manifold.riemannianEDist I p z ≠ ⊤ := hpz
    have htri : _root_.Manifold.riemannianEDist I p z₀ ≤
        riemannianEDist I p z + _root_.Manifold.riemannianEDist I z z₀ := _root_.Manifold.riemannianEDist_triangle
    have hzz0 : _root_.Manifold.riemannianEDist I z z₀ < ⊤ := by
      rw [_root_.Manifold.riemannianEDist_comm]; exact lt_of_lt_of_le hz (by norm_num)
    have hfin' : _root_.Manifold.riemannianEDist I p z₀ < ⊤ :=
      lt_of_le_of_lt htri
        (ENNReal.add_lt_top.mpr ⟨lt_of_le_of_ne le_top hpz', hzz0⟩)
    exact hfin'.ne hinf
  have hSclopen : IsClopen S := ⟨⟨hScompl_open⟩, hSopen⟩
  have hSuniv : S = Set.univ := by
    rcases isClopen_iff.mp hSclopen with hempty | huniv
    · exact absurd (hempty ▸ hpS) (by simp)
    · exact huniv
  exact lt_top_iff_ne_top.mpr (hSuniv ▸ Set.mem_univ q : q ∈ S)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Manifold
  let env ← Lean.getEnv
  if env.contains `Manifold.riemannianEDist_lt_top then
    throwError "Refusing to shadow existing declaration Manifold.riemannianEDist_lt_top"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.riemannianEDist_lt_top ``Submission.Manifold.riemannianEDist_lt_top

end

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem riemannianEDistOf_ne_top [PreconnectedSpace M]
    (g : SmoothRiemannianMetric I M) (x y : M) :
    riemannianEDistOf (I := I) g x y ≠ (⊤ : ℝ≥0∞) := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  exact (Manifold.riemannianEDist_lt_top (I := I) x y).ne

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.riemannianEDistOf_ne_top then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.riemannianEDistOf_ne_top"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.riemannianEDistOf_ne_top ``Submission.DifferentialGeometry.riemannianEDistOf_ne_top

end DifferentialGeometry
