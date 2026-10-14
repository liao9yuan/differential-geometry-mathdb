/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PlanarDiskArcNeighborhood
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheoremDiskArcSide
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscut
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CircleArcs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem IsPLBall.exists_isPLBall_neighborhood_with_crosscut_traces
    {ι : Type*} [Finite ι] {D U : Set Plane} (hD : IsPLBall 2 D)
    (hU : IsOpen U) (hDU : D ⊆ U) (A : ι → Set Plane)
    (q : ι → (Fin 2 → ℝ) → Plane)
    (hq : ∀ i, IsPLHomeomorphOn (q i) (stdSimplex ℝ (Fin 2)) (A i))
    (hDA : ∀ i, IsPLBall 1 (D ∩ A i))
    (hends : ∀ i, Disjoint D (q i '' stdSimplexBoundary 1)) :
    ∃ (Q : Set Plane) (γ : ι → ℝ → Plane),
      IsPLBall 2 Q ∧ D ⊆ interior Q ∧ Q ⊆ U ∧
      ∀ i, IsPLHomeomorphOn (γ i) (_root_.Set.Icc 0 1) (A i ∩ Q) ∧
        Schoenflies.IsCrosscut (frontier Q) (A i ∩ Q) (γ i 0) (γ i 1) := by
  classical
  obtain ⟨Q, hQ, hDQ, hQU, htr⟩ :=
    hD.exists_isPLBall_neighborhood_with_arc_traces hU hDU A q hq hDA hends
  have hparam (i : ι) : ∃ γ : ℝ → Plane,
      IsPLHomeomorphOn γ (_root_.Set.Icc 0 1) (A i ∩ Q) ∧
        Schoenflies.IsCrosscut (frontier Q) (A i ∩ Q) (γ 0) (γ 1) := by
    obtain ⟨r, hr⟩ := (htr i).1
    have hbd : r '' stdSimplexBoundary 1 = (A i ∩ Q) ∩ frontier Q := by
      rw [(htr i).2 r hr]
      ext x
      exact ⟨fun hx => ⟨⟨hx.1, hQ.isPolyhedron.isClosed.frontier_subset hx.2⟩, hx.2⟩,
        fun hx => ⟨hx.1.1, hx.2⟩⟩
    obtain ⟨γ, hγ, he⟩ := exists_isPLHomeomorphOn_Icc_of_stdSimplex_one hr hbd
    refine ⟨γ, hγ, hγ.isCrosscut_of_image_Ioo_subset_interior hQ ?_ ?_ ?_⟩
    · exact (he.subset (Or.inl rfl)).2
    · exact (he.subset (Or.inr rfl)).2
    · rw [hγ.image_Ioo_eq_sdiff_endpoints (by norm_num), he]
      intro x hx
      rw [← closure_sdiff_frontier, hQ.isPolyhedron.isClosed.closure_eq]
      exact ⟨hx.1.2, fun hxf => hx.2 ⟨hx.1, hxf⟩⟩
  choose γ hγ using hparam
  exact ⟨Q, γ, hQ, hDQ, hQU, hγ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.exists_isPLBall_neighborhood_with_crosscut_traces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.exists_isPLBall_neighborhood_with_crosscut_traces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.exists_isPLBall_neighborhood_with_crosscut_traces ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.exists_isPLBall_neighborhood_with_crosscut_traces

theorem isPLHomeomorphOn_fst_openPartialHomeomorph
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (e : OpenPartialHomeomorph E (F × ℝ))
    (he : IsPiecewiseAffineOn e e.source) {T : Set E} (hT : IsPolyhedron T)
    (hTs : T ⊆ e.source) (hTz : ∀ x ∈ T, (e x).2 = 0) :
    IsPLHomeomorphOn (fun x => (e x).1) T ((fun x => (e x).1) '' T) := by
  have hp : IsPiecewiseAffineOn (Prod.fst : F × ℝ → F) univ :=
    isPiecewiseAffineOn_of_affine (LinearMap.fst ℝ F ℝ).toAffineMap isOpen_univ
  have hpa : IsPiecewiseAffineOn (fun x => (e x).1) e.source := by
    simpa only [_root_.Set.preimage_univ, _root_.Set.inter_univ, Function.comp_def] using hp.comp he
  have hinj : _root_.Set.InjOn (fun x => (e x).1) T := by
    intro x hx y hy hxy
    apply e.injOn (hTs hx) (hTs hy)
    exact Prod.ext hxy ((hTz x hx).trans (hTz y hy).symm)
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hT
    (hpa.mono_of_isPolyhedron hT hTs) hinj.bijOn_image

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_fst_openPartialHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_fst_openPartialHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_fst_openPartialHomeomorph ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_fst_openPartialHomeomorph

theorem IsPLBall.exists_isPLBall_neighborhood_with_chart_crosscuts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Finite ι] (e : OpenPartialHomeomorph E (Plane × ℝ))
    (he : IsPiecewiseAffineOn e e.source) {D : Set E} (hD : IsPLBall 2 D)
    (hDs : D ⊆ e.source) (hDz : ∀ x ∈ D, (e x).2 = 0)
    (A : ι → Set E) (q : ι → (Fin 2 → ℝ) → E)
    (hq : ∀ i, IsPLHomeomorphOn (q i) (stdSimplex ℝ (Fin 2)) (A i))
    (hAs : ∀ i, A i ⊆ e.source) (hAz : ∀ i, ∀ x ∈ A i, (e x).2 = 0)
    (hDA : ∀ i, IsPLBall 1 (D ∩ A i))
    (hends : ∀ i, Disjoint D (q i '' stdSimplexBoundary 1))
    {U : Set Plane} (hU : IsOpen U) (hDU : (fun x => (e x).1) '' D ⊆ U) :
    ∃ (Q : Set Plane) (γ : ι → ℝ → Plane),
      IsPLBall 2 Q ∧ (fun x => (e x).1) '' D ⊆ interior Q ∧ Q ⊆ U ∧
      ∀ i, IsPLHomeomorphOn (γ i) (_root_.Set.Icc 0 1) (((fun x => (e x).1) '' A i) ∩ Q) ∧
        Schoenflies.IsCrosscut (frontier Q) (((fun x => (e x).1) '' A i) ∩ Q)
          (γ i 0) (γ i 1) := by
  let f : E → Plane := fun x => (e x).1
  have hfD : IsPLHomeomorphOn f D (f '' D) :=
    isPLHomeomorphOn_fst_openPartialHomeomorph e he hD.isPolyhedron hDs hDz
  have hA (i : ι) : IsPLBall 1 (A i) := ⟨q i, hq i⟩
  have hfA (i : ι) : IsPLHomeomorphOn f (A i) (f '' A i) :=
    isPLHomeomorphOn_fst_openPartialHomeomorph e he (hA i).isPolyhedron (hAs i) (hAz i)
  have hinj (i : ι) {x y : E} (hx : x ∈ D) (hy : y ∈ A i) (hxy : f x = f y) :
      x = y :=
    e.injOn (hDs hx) (hAs i hy) (Prod.ext hxy ((hDz x hx).trans (hAz i y hy).symm))
  have hinter (i : ι) : f '' (D ∩ A i) = (f '' D) ∩ (f '' A i) :=
    _root_.Set.image_inter_on fun x hx y hy hxy => (hinj i hy hx hxy.symm).symm
  have hDA' (i : ι) : IsPLBall 1 ((f '' D) ∩ (f '' A i)) := by
    rw [← hinter i]
    exact (hDA i).of_isPLHomeomorphOn
      (isPLHomeomorphOn_fst_openPartialHomeomorph e he (hDA i).isPolyhedron
        (inter_subset_left.trans hDs) (fun x hx => hDz x hx.1))
  have he' (i : ι) : Disjoint (f '' D) ((f ∘ q i) '' stdSimplexBoundary 1) := by
    refine disjoint_left.mpr ?_
    rintro z ⟨x, hx, rfl⟩ ⟨t, ht, htx⟩
    have htA : q i t ∈ A i := (hq i).bijOn.mapsTo ht.1
    have hxt : x = q i t := hinj i hx htA htx.symm
    exact (disjoint_left.mp (hends i)) hx (hxt ▸ _root_.Set.mem_image_of_mem (q i) ht)
  exact (hD.of_isPLHomeomorphOn hfD).exists_isPLBall_neighborhood_with_crosscut_traces
    hU hDU (fun i => f '' A i) (fun i => f ∘ q i)
      (fun i => (hq i).trans (hfA i)) hDA' he'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.exists_isPLBall_neighborhood_with_chart_crosscuts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.exists_isPLBall_neighborhood_with_chart_crosscuts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.exists_isPLBall_neighborhood_with_chart_crosscuts ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.exists_isPLBall_neighborhood_with_chart_crosscuts

end DifferentialGeometry.Topology.PiecewiseLinear
