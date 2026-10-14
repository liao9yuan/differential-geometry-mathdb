import Submission.DifferentialGeometry.Topology.Manifold.SurvivingSlabSelection
import Submission.DifferentialGeometry.Geometry.Neck.ProperSlabEnd

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Submission.Set.Submission.Finite.exists_strictMono_enumeration_fiber then
    throwError "Refusing to shadow existing declaration Submission.Set.Submission.Finite.exists_strictMono_enumeration_fiber"
  Lean.modifyEnv fun env => Lean.addAlias env `Submission.Set.Submission.Finite.exists_strictMono_enumeration_fiber ``Submission.Set.Finite.exists_strictMono_enumeration_fiber

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem exists_proper_neck_end_of_infinite_updates
    {M ι : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    [T2Space M]
    (g : SmoothRiemannianMetric I3 M) {eps : ℝ} (heps : eps ≤ 1 / 156000)
    (hcompact : ∀ B : ℝ, IsCompact {x : M | Geometry.Curvature.metricScalarAt g x ≤ B})
    (label : ℕ → ι) (i : ι) (hinfinite : {n | label n = i}.Infinite)
    (sphere : ℕ → ι → Sphere 2 → M)
    (hunchanged : ∀ n, label n ≠ i → sphere (n + 1) i = sphere n i)
    (P : ℕ → PartialDiffeomorph IC I3 Cylinder M ∞)
    (hsource : ∀ n, _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ (P n).source)
    (μ : ℕ → Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2)
    (hlower : ∀ n z, P n (z, 0) = sphere n (label n) z)
    (hupper : ∀ n z, P n (z, 1) = sphere (n + 1) (label n) (μ n z))
    (W : ℕ → Set M) (hW : Monotone W)
    (hcontained : ∀ n, P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ⊆ W (n + 1))
    (hinter : ∀ n, P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∩ W n = _root_.Set.range (sphere n (label n)))
    (hsphere : ∀ n, _root_.Set.range (sphere n (label n)) ⊆ frontier (W n))
    (hfilled : ∀ n, _root_.Set.range (sphere n (label n)) ⊆ interior (W (n + 1)))
    (point : ℕ → M) (neck : ∀ n, SpatialNeck g eps (point n))
    (hcontrolled : ∀ n, P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ⊆
      (neck n).map '' (_root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹))
    (hband : ∀ n, (neck n).map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (1 : ℝ) 2) ⊆
      P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ (∀ n, label (s n) = i) ∧
      (∀ m, label m = i ↔ ∃ n, s n = m) ∧
      ∃ Θ : Cylinder → M,
        ContMDiffOn IC I3 ∞ Θ (_root_.Set.univ ×ˢ _root_.Set.Ici (0 : ℝ)) ∧
        _root_.Set.InjOn Θ (_root_.Set.univ ×ˢ _root_.Set.Ici (0 : ℝ)) ∧
        IsProperMap (fun z : Sphere 2 × ℝ≥0 => Θ (z.1, z.2.val)) ∧
        (let U : TopologicalSpace.Opens Cylinder :=
          ⟨univ ×ˢ _root_.Set.Ioi (0 : ℝ), isOpen_univ.prod isOpen_Ioi⟩
         _root_.Manifold.IsSmoothEmbedding IC I3 ∞ (fun z : U => Θ z)) ∧
        Θ '' (_root_.Set.univ ×ˢ _root_.Set.Ici (0 : ℝ)) = ⋃ n, P (s n) '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∧
        Θ '' (_root_.Set.univ ×ˢ _root_.Set.Ici (0 : ℝ)) ∩ W 0 = _root_.Set.range (sphere 0 i) ∩ W 0 ∧
        (∀ z t, t ∈ _root_.Set.Icc (0 : ℝ) 1 → Θ (z, t) = P (s 0) (z, t)) ∧
        (∀ z, Θ (z, 0) = sphere 0 i z) ∧
        ∀ B : ℝ, ∃ T : ℝ≥0, ∀ (z : Sphere 2) (t : ℝ≥0),
          T ≤ t → B < Geometry.Curvature.metricScalarAt g (Θ (z, t.val)) := by
  obtain ⟨s, hmono, hlabel, hcover, hbase, hs, hseam, hadj, hsep, hinitial⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_slab_sequence_of_infinite_updates
      label i hinfinite sphere hunchanged P hsource μ hlower hupper W hW
        hcontained hinter hsphere hfilled
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ThreeSpace M
  obtain ⟨Θ, hsm, hi, hp, he, hr, hb, _, hscalar⟩ :=
    exists_proper_neck_product_of_fresh_slabs_eq_on_first_slab g heps
      (fun n => point (s n)) (fun n => neck (s n))
      hcompact (fun n => P (s n)) (fun n => (μ (s n)).symm) hs hseam hadj hsep
      (fun n => hcontrolled (s n)) (fun n => hband (s n))
  refine ⟨s, hmono, hlabel, hcover, Θ, hsm, hi, hp, he, hr, ?_, hb, ?_, hscalar⟩
  · rw [hr]
    exact hinitial
  intro z
  exact (hb z 0 ⟨le_rfl, zero_le_one⟩).trans (hbase z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_proper_neck_end_of_infinite_updates then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_proper_neck_end_of_infinite_updates"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_proper_neck_end_of_infinite_updates ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_proper_neck_end_of_infinite_updates

theorem exists_proper_neck_end_of_finite_updates
    {M ι : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    [T2Space M]
    (g : SmoothRiemannianMetric I3 M) {eps : ℝ} (heps : eps ≤ 1 / 156000)
    (hcompact : ∀ B : ℝ, IsCompact {x : M | Geometry.Curvature.metricScalarAt g x ≤ B})
    (label : ℕ → ι) (hlabels : (_root_.Set.range label).Finite)
    (sphere : ℕ → ι → Sphere 2 → M)
    (hunchanged : ∀ n i, label n ≠ i → sphere (n + 1) i = sphere n i)
    (P : ℕ → PartialDiffeomorph IC I3 Cylinder M ∞)
    (hsource : ∀ n, _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ (P n).source)
    (μ : ℕ → Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2)
    (hlower : ∀ n z, P n (z, 0) = sphere n (label n) z)
    (hupper : ∀ n z, P n (z, 1) = sphere (n + 1) (label n) (μ n z))
    (W : ℕ → Set M) (hW : Monotone W)
    (hcontained : ∀ n, P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ⊆ W (n + 1))
    (hinter : ∀ n, P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∩ W n = _root_.Set.range (sphere n (label n)))
    (hsphere : ∀ n, _root_.Set.range (sphere n (label n)) ⊆ frontier (W n))
    (hfilled : ∀ n, _root_.Set.range (sphere n (label n)) ⊆ interior (W (n + 1)))
    (point : ℕ → M) (neck : ∀ n, SpatialNeck g eps (point n))
    (hcontrolled : ∀ n, P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ⊆
      (neck n).map '' (_root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹))
    (hband : ∀ n, (neck n).map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (1 : ℝ) 2) ⊆
      P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) :
    ∃ i : ι, ∃ s : ℕ → ℕ, StrictMono s ∧ (∀ n, label (s n) = i) ∧
      ∃ Θ : Cylinder → M,
        ContMDiffOn IC I3 ∞ Θ (_root_.Set.univ ×ˢ _root_.Set.Ici (0 : ℝ)) ∧
        _root_.Set.InjOn Θ (_root_.Set.univ ×ˢ _root_.Set.Ici (0 : ℝ)) ∧
        IsProperMap (fun z : Sphere 2 × ℝ≥0 => Θ (z.1, z.2.val)) ∧
        (let U : TopologicalSpace.Opens Cylinder :=
          ⟨univ ×ˢ _root_.Set.Ioi (0 : ℝ), isOpen_univ.prod isOpen_Ioi⟩
         _root_.Manifold.IsSmoothEmbedding IC I3 ∞ (fun z : U => Θ z)) ∧
        Θ '' (_root_.Set.univ ×ˢ _root_.Set.Ici (0 : ℝ)) = ⋃ n, P (s n) '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∧
        Θ '' (_root_.Set.univ ×ˢ _root_.Set.Ici (0 : ℝ)) ∩ W 0 = _root_.Set.range (sphere 0 i) ∩ W 0 ∧
        (∀ z, Θ (z, 0) = sphere 0 i z) ∧
        ∀ B : ℝ, ∃ T : ℝ≥0, ∀ (z : Sphere 2) (t : ℝ≥0),
          T ≤ t → B < Geometry.Curvature.metricScalarAt g (Θ (z, t.val)) := by
  obtain ⟨i, s, hmono, hlabel, _⟩ := hlabels.exists_strictMono_enumeration_fiber
  have hinfinite : {n | label n = i}.Infinite :=
    (Set.infinite_range_of_injective hmono.injective).mono (by
      rintro n ⟨m, rfl⟩
      exact hlabel m)
  obtain ⟨t, ht, hlabelt, _, Θ, hsm, hi, hp, he, hr, hinitial, _, hb, hscalar⟩ :=
    exists_proper_neck_end_of_infinite_updates g heps hcompact label i hinfinite sphere
      (fun n => hunchanged n i) P hsource μ hlower hupper W hW hcontained hinter hsphere hfilled
      point neck hcontrolled hband
  exact ⟨i, t, ht, hlabelt, Θ, hsm, hi, hp, he, hr, hinitial, hb, hscalar⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_proper_neck_end_of_finite_updates then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_proper_neck_end_of_finite_updates"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_proper_neck_end_of_finite_updates ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_proper_neck_end_of_finite_updates

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
