import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34BoundaryMotionExtension
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34SurfaceBigonSlide
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34RawBigonSlide

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open _root_.Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_boundary_crosscut_slide
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {N A J L : Set E}
    {n a : (Fin 3 → ℝ) → E} (hn : IsPLHomeomorphOn n (stdSimplex ℝ (Fin 3)) N)
    (hNB : N ⊆ (boundaryComplex 3 K).space) (hJB : J ⊆ (boundaryComplex 3 K).space)
    {γ : ℝ → E} (hγ : IsPLHomeomorphOn γ (_root_.Set.Icc 0 1) (J ∩ N))
    (hends : (J ∩ N) ∩ n '' stdSimplexBoundary 2 = {γ 0, γ 1})
    (ha : IsPLHomeomorphOn a (stdSimplex ℝ (Fin 3)) A) (hAN : A ⊆ N)
    (hside : A ∩ (L ∪ n '' stdSimplexBoundary 2) ⊆ a '' stdSimplexBoundary 2)
    (h₀ : γ 0 ∈ a '' stdSimplexBoundary 2) (h₁ : γ 1 ∈ a '' stdSimplexBoundary 2)
    (h₀L : γ 0 ∉ L) (h₁L : γ 1 ∉ L) :
    ∃ F : E → E, IsPLHomeomorphOn F K.space K.space ∧
      _root_.Set.EqOn F id (closure ((boundaryComplex 3 K).space \ N)) ∧ F '' N = N ∧
      F '' J ∩ L = (J \ N) ∩ L := by
  classical
  let B := boundaryComplex 3 K
  let _ : Finite B.faces := (boundaryComplex_faces_finite 3 K).to_subtype
  have hB := isCombinatorialManifold_boundaryComplex K hK
  obtain ⟨H, hH, hfix, hHN, htrace⟩ := hB.exists_crosscut_slide_of_side_disk B hn hNB hJB
    hγ hends ha hAN hside h₀ h₁ h₀L h₁L
  obtain ⟨F, hF, hFH⟩ :=
    hK.exists_boundary_extension_of_disk_support K hn hNB hH hfix hHN
  have hCB : closure (B.space \ N) ⊆ B.space :=
    closure_minimal _root_.Set.sdiff_subset (isPolyhedron_space B).isClosed
  exact ⟨F, hF, (hFH.mono hCB).trans hfix, (hFH.mono hNB).image_eq.trans hHN,
    (congrArg (· ∩ L) (hFH.mono hJB).image_eq).trans htrace⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_boundary_crosscut_slide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_boundary_crosscut_slide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_boundary_crosscut_slide ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_boundary_crosscut_slide

theorem strict_intersection_decrease_of_deleted_trace
    {X : Type*} {J L N : Set X} {F : X → X}
    (htrace : F '' J ∩ L = (J \ N) ∩ L) (hfinite : (J ∩ L).Finite)
    (hne : (J ∩ L ∩ N).Nonempty) : (F '' J ∩ L).ncard < (J ∩ L).ncard := by
  rw [htrace]
  apply _root_.Set.ncard_lt_ncard (s := (J \ N) ∩ L) (t := J ∩ L) ?_ hfinite
  refine ssubset_iff_subset_ne.mpr ⟨fun _ hx => ⟨hx.1.1, hx.2⟩, ?_⟩
  intro heq
  obtain ⟨x, hxJL, hxN⟩ := hne
  exact (heq.symm.subset hxJL).1.2 hxN

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.strict_intersection_decrease_of_deleted_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.strict_intersection_decrease_of_deleted_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.strict_intersection_decrease_of_deleted_trace ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.strict_intersection_decrease_of_deleted_trace

open _root_.Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_boundary_raw_bigon_slide
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {B Ω J L : Set E}
    (hB : IsPLBall 2 B) (hBK : B ⊆ (boundaryComplex 3 K).space)
    (hΩ : IsOpen Ω) (hBΩ : B ⊆ Ω) (hJ : IsPLSphere 1 J) (hL : IsPLSphere 1 L)
    (hJK : J ⊆ (boundaryComplex 3 K).space) (hLK : L ⊆ (boundaryComplex 3 K).space)
    (hBJ : IsPLBall 1 (B ∩ J)) (hBL : IsPLBall 1 (B ∩ L))
    (c : Fin 2 → E) (hc : Function.Injective c) (htrace : B ∩ (J ∩ L) = {c 0, c 1})
    (e : Fin 2 → OpenPartialHomeomorph (ℝ × ℝ) (boundaryComplex 3 K).space)
    (ε : Fin 2 → ℝ) (hε : ∀ i, 0 < ε i)
    (hsource : ∀ i, _root_.Set.Ioo (-ε i) (ε i) ×ˢ _root_.Set.Ioo (-ε i) (ε i) ⊆ (e i).source)
    (hcenter : ∀ i, (e i (0, 0) : E) = c i)
    (hfirst : ∀ i, ∀ p ∈ _root_.Set.Ioo (-ε i) (ε i) ×ˢ _root_.Set.Ioo (-ε i) (ε i),
      (e i p : E) ∈ J ↔ p.1 = 0)
    (hsecond : ∀ i, ∀ p ∈ _root_.Set.Ioo (-ε i) (ε i) ×ˢ _root_.Set.Ioo (-ε i) (ε i),
      (e i p : E) ∈ L ↔ p.2 = 0) :
    ∃ (N : Set E) (r : (Fin 3 → ℝ) → E) (F : E → E),
      IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) N ∧
      N ⊆ (boundaryComplex 3 K).space ∩ Ω ∧ B ⊆ r '' openSimplex (stdVertices 1) ∧
      IsPLHomeomorphOn F K.space K.space ∧
      _root_.Set.EqOn F id (closure ((boundaryComplex 3 K).space \ N)) ∧ F '' N = N ∧
      F '' J ∩ L = (J ∩ L) \ {c 0, c 1} ∧ N ∩ (J ∩ L) = {c 0, c 1} ∧
      F '' J ∩ L = (J \ N) ∩ L := by
  classical
  let S := boundaryComplex 3 K
  let _ : Finite S.faces := (boundaryComplex_faces_finite 3 K).to_subtype
  have hS := isCombinatorialManifold_boundaryComplex K hK
  obtain ⟨N, r, H, hr, hNS, hBN, hH, hfix, hHN, htrace', hNtrace, hafter⟩ :=
    hS.exists_raw_bigon_slide S hB hBK hΩ hBΩ hJ hL hJK hLK hBJ hBL c hc htrace
      e ε hε hsource hcenter hfirst hsecond
  have hNB := hNS.trans _root_.Set.inter_subset_left
  obtain ⟨F, hF, hFH⟩ :=
    hK.exists_boundary_extension_of_disk_support K hr hNB hH hfix hHN
  have hCS : closure (S.space \ N) ⊆ S.space :=
    closure_minimal _root_.Set.sdiff_subset (isPolyhedron_space S).isClosed
  exact ⟨N, r, F, hr, hNS, hBN, hF, (hFH.mono hCS).trans hfix,
    (hFH.mono hNB).image_eq.trans hHN,
    (congrArg (· ∩ L) (hFH.mono hJK).image_eq).trans htrace', hNtrace,
    (congrArg (· ∩ L) (hFH.mono hJK).image_eq).trans hafter⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_boundary_raw_bigon_slide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_boundary_raw_bigon_slide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_boundary_raw_bigon_slide ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_boundary_raw_bigon_slide

theorem intersection_count_of_deleted_pair
    {X : Type*} {J L : Set X} {F : X → X} {p q : X} (hpq : p ≠ q)
    (hp : p ∈ J ∩ L) (hq : q ∈ J ∩ L)
    (htrace : F '' J ∩ L = (J ∩ L) \ {p, q}) (hfinite : (J ∩ L).Finite) :
    (F '' J ∩ L).ncard + 2 = (J ∩ L).ncard := by
  rw [htrace, ← _root_.Set.ncard_pair hpq]
  exact _root_.Set.ncard_sdiff_add_ncard_of_subset (_root_.Set.pair_subset hp hq) hfinite

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.intersection_count_of_deleted_pair then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.intersection_count_of_deleted_pair"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.intersection_count_of_deleted_pair ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.intersection_count_of_deleted_pair

end DifferentialGeometry.Topology.PiecewiseLinear
