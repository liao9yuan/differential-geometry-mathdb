/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CompactEmbeddingApproximation
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Mesh

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

private theorem isEmbedding_domRestrict_of_subset {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} {K U : Set X}
    (hf : Topology.IsEmbedding (K.domRestrict f)) (hUK : U ⊆ K) :
    Topology.IsEmbedding (U.domRestrict f) :=
  hf.comp (Topology.IsEmbedding.inclusion hUK)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isEmbedding_domRestrict_of_subset
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.isEmbedding_domRestrict_of_subset target :: scope.openDecls } }

private theorem isPLOn_id_of_isOpen {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] {s : Set M}
    (hs : IsOpen s) : IsPLOn n n (id : M → M) s := by
  intro x hx
  have hnb : s ∈ 𝓝[(_root_.Set.univ : Set M)] x := by
    rw [nhdsWithin_univ]
    exact hs.mem_nhds hx
  have h₂ : ChartedSpace.LiftPropWithinAt (piecewiseAffineProperty n n) (id : M → M)
      (_root_.Set.univ ∩ s) x :=
    (piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_inter' hnb).mpr (isPL_id x)
  rwa [_root_.Set.univ_inter] at h₂

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLOn_id_of_isOpen
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.isPLOn_id_of_isOpen target :: scope.openDecls } }

theorem exists_isSubdivision_diam_image_closedStars_lt {E Z : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MetricSpace Z] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {g : E → Z} (hg : ContinuousOn g K.space) {φ : E → ℝ} (hφ : ContinuousOn φ K.space)
    (hpos : ∀ x ∈ K.space, 0 < φ x) :
    ∃ R : Geometry.SimplicialComplex ℝ E, IsSubdivision R K ∧ R.faces.Finite ∧
      ∀ s ∈ R.faces, ∀ x ∈ ⋃ v ∈ s, closedStar R v,
        Metric.diam (g '' ⋃ v ∈ s, closedStar R v) < φ x := by
  have hKc : IsCompact K.space :=
    DifferentialGeometry.Topology.SimplicialComplex.isCompact_geometricSpace K
  obtain ⟨c, hc, hcle⟩ := exists_pos_forall_le_of_continuousOn hKc hφ hpos
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (hKc.uniformContinuousOn_of_continuous hg) (c / 2) (by positivity)
  obtain ⟨R, hR, hRfin, hstar⟩ :=
    exists_isSubdivision_closedStars_subset_cover K
      (fun z : K.space => Metric.ball (z : E) (δ / 2))
      (fun _ => Metric.isOpen_ball.preimage continuous_subtype_val)
      (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (half_pos hδ)⟩)
  refine ⟨R, hR, hRfin, fun s hs x hx => ?_⟩
  obtain ⟨z, hz⟩ := hstar s hs
  have hsub : (⋃ v ∈ s, closedStar R v) ⊆ K.space :=
    _root_.Set.iUnion₂_subset fun v _ => (closedStar_subset_space R v).trans hR.space_eq.subset
  have hdiam : Metric.diam (g '' ⋃ v ∈ s, closedStar R v) ≤ c / 2 := by
    refine Metric.diam_le_of_forall_dist_le (by positivity) ?_
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
    refine le_of_lt (hclose y (hsub hy) y' (hsub hy') ?_)
    have h₁ : _root_.Dist.dist y (z : E) < δ / 2 := Metric.mem_ball.mp (hz hy)
    have h₂ : _root_.Dist.dist y' (z : E) < δ / 2 := Metric.mem_ball.mp (hz hy')
    calc _root_.Dist.dist y y' ≤ _root_.Dist.dist y (z : E) + _root_.Dist.dist (z : E) y' := dist_triangle _ _ _
      _ < δ := by rw [dist_comm (z : E) y']; linarith
  exact hdiam.trans_lt (lt_of_lt_of_le (by linarith) (hcle x (hsub hx)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isSubdivision_diam_image_closedStars_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isSubdivision_diam_image_closedStars_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isSubdivision_diam_image_closedStars_lt ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isSubdivision_diam_image_closedStars_lt

def Moise352InwardPush (n : ℕ) : Prop :=
  ∀ {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂]
    [HasGroupoid M₁ (plGroupoid n)] [HasGroupoid M₂ (plGroupoid n)]
    {K : Set M₁}, IsLocallyFinitePolyhedralManifoldWithBoundary (n := n) n K →
    ∀ {h : M₁ → M₂}, Topology.IsEmbedding (K.domRestrict h) →
    ∀ ψ : M₁ → ℝ, ContinuousOn ψ K → (∀ x ∈ K, 0 < ψ x) →
    ∃ p q : M₁ → M₁, ∃ W : Set M₁, IsOpen W ∧ W ⊆ interior K ∧ _root_.Set.MapsTo p K W ∧
      IsPLOn n n p K ∧ _root_.Set.InjOn p K ∧ IsPLOn n n q W ∧ _root_.Set.MapsTo q W K ∧ _root_.Set.LeftInvOn q p K ∧
      ∀ x ∈ K, _root_.Dist.dist (h (p x)) (h x) < ψ x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Moise352InwardPush then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Moise352InwardPush"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Moise352InwardPush ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Moise352InwardPush

theorem exists_isPLOn_injOn_leftInvOn_of_isOpen {n : ℕ} {M₁ M₂ : Type*} [TopologicalSpace M₁]
    [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁]
    {K : Set M₁} (hK : IsOpen K) (h : M₁ → M₂) {ψ : M₁ → ℝ}
    (hψ : ∀ x ∈ K, 0 < ψ x) :
    ∃ p q : M₁ → M₁, ∃ W : Set M₁, IsOpen W ∧ W ⊆ interior K ∧ _root_.Set.MapsTo p K W ∧
      IsPLOn n n p K ∧ _root_.Set.InjOn p K ∧ IsPLOn n n q W ∧ _root_.Set.MapsTo q W K ∧ _root_.Set.LeftInvOn q p K ∧
      ∀ x ∈ K, _root_.Dist.dist (h (p x)) (h x) < ψ x :=
  ⟨id, id, K, hK, hK.interior_eq.ge, _root_.Set.mapsTo_id K, isPLOn_id_of_isOpen hK, _root_.Set.injOn_id K,
    isPLOn_id_of_isOpen hK, _root_.Set.mapsTo_id K, fun _ _ => rfl, fun x hx => by simpa using hψ x hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLOn_injOn_leftInvOn_of_isOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLOn_injOn_leftInvOn_of_isOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLOn_injOn_leftInvOn_of_isOpen ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLOn_injOn_leftInvOn_of_isOpen

def Moise352SkeletonExtension (n : ℕ) : Prop :=
  ∀ {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂]
    [HasGroupoid M₁ (plGroupoid n)] [HasGroupoid M₂ (plGroupoid n)]
    {K : Set M₁}, IsLocallyFinitePolyhedralManifoldWithBoundary (n := n) n K →
    ∀ {h : M₁ → M₂}, Topology.IsEmbedding (K.domRestrict h) →
    ∀ φ : M₁ → ℝ, ContinuousOn φ K → (∀ x ∈ K, 0 < φ x) →
    (∀ ψ : M₁ → ℝ, ContinuousOn ψ K → (∀ x ∈ K, 0 < ψ x) →
      ∃ p q : M₁ → M₁, ∃ W : Set M₁, IsOpen W ∧ W ⊆ interior K ∧ _root_.Set.MapsTo p K W ∧
        IsPLOn n n p K ∧ _root_.Set.InjOn p K ∧ IsPLOn n n q W ∧ _root_.Set.MapsTo q W K ∧ _root_.Set.LeftInvOn q p K ∧
        ∀ x ∈ K, _root_.Dist.dist (h (p x)) (h x) < ψ x) →
    (∀ {U : Set M₁}, IsOpen U → U ⊆ K → ∀ {G : Set M₁}, G ⊆ U →
      IsClosed (((↑) : U → M₁) ⁻¹' G) → IsLocallyFinitePolyhedralGraph (n := n) G →
      ∀ ψ : M₁ → ℝ, ContinuousOn ψ U → (∀ x ∈ U, 0 < ψ x) →
        ∃ N : Set M₁, IsLocallyFiniteRegularNeighborhoodOf (n := n) N G U ∧
          ∃ f : M₁ → M₂, IsPLHomeomorphInto n f N ∧ f '' N ∈ nhdsSet (h '' G) ∧
            ∀ x ∈ N, _root_.Dist.dist (f x) (h x) < ψ x) →
    ∃ f : M₁ → M₂, IsPLHomeomorphInto n f K ∧ ∀ x ∈ K, _root_.Dist.dist (f x) (h x) < φ x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Moise352SkeletonExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Moise352SkeletonExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Moise352SkeletonExtension ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Moise352SkeletonExtension

theorem moise352_of_inwardPush_of_skeletonExtension (hpush : Moise352InwardPush.{u} 3)
    (h351 : Moise351.{u}) (hext : Moise352SkeletonExtension.{u} 3) : Moise352.{u} 3 := by
  intro M₁ M₂ _ _ _ _ _ _ _ _ _ K hK h hh φ hφ hpos
  refine hext hK hh φ hφ hpos (fun ψ hψ hψpos => hpush hK hh ψ hψ hψpos) ?_
  intro U hU hUK G hGU hGclosed hGgraph ψ hψ hψpos
  exact h351 hU hGU hGclosed hGgraph (isEmbedding_domRestrict_of_subset hh hUK) ψ hψ hψpos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.moise352_of_inwardPush_of_skeletonExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.moise352_of_inwardPush_of_skeletonExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.moise352_of_inwardPush_of_skeletonExtension ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.moise352_of_inwardPush_of_skeletonExtension

theorem exists_isPLHomeomorphInto_dist_lt_of_skeletonExtension_of_isOpen (h351 : Moise351.{u})
    (hext : Moise352SkeletonExtension.{u} 3) {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁]
    [SecondCountableTopology M₁] [Nonempty M₁] [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
    [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)] {K : Set M₁}
    (hK : IsOpen K) {h : M₁ → M₂} (hh : Topology.IsEmbedding (K.domRestrict h)) (φ : M₁ → ℝ)
    (hφ : ContinuousOn φ K) (hpos : ∀ x ∈ K, 0 < φ x) :
    ∃ f : M₁ → M₂, IsPLHomeomorphInto 3 f K ∧ ∀ x ∈ K, _root_.Dist.dist (f x) (h x) < φ x := by
  refine hext (isLocallyFinitePolyhedralManifoldWithBoundary_of_isOpen (m := 2) hK) hh φ hφ hpos
    (fun _ _ hψpos => exists_isPLOn_injOn_leftInvOn_of_isOpen hK h hψpos) ?_
  intro U hU hUK G hGU hGclosed hGgraph ψ hψ hψpos
  exact h351 hU hGU hGclosed hGgraph (isEmbedding_domRestrict_of_subset hh hUK) ψ hψ hψpos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphInto_dist_lt_of_skeletonExtension_of_isOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphInto_dist_lt_of_skeletonExtension_of_isOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphInto_dist_lt_of_skeletonExtension_of_isOpen ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphInto_dist_lt_of_skeletonExtension_of_isOpen

theorem exists_isPLHomeomorphInto_dist_lt_id_of_isOpen {n : ℕ} {M : Type*} [MetricSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] {K : Set M}
    (hK : IsOpen K) {φ : M → ℝ} (hpos : ∀ x ∈ K, 0 < φ x) :
    ∃ f : M → M, IsPLHomeomorphInto n f K ∧ ∀ x ∈ K, _root_.Dist.dist (f x) (id x) < φ x := by
  refine ⟨id, ⟨isPLOn_id_of_isOpen hK, _root_.Set.injOn_id K, ?_⟩, fun x hx => by simpa using hpos x hx⟩
  intro y hy
  rw [Set.image_id] at hy
  exact ⟨id, by rw [Set.image_id]; exact isPLOn_id_of_isOpen hK y hy, fun _ _ => rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphInto_dist_lt_id_of_isOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphInto_dist_lt_id_of_isOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphInto_dist_lt_id_of_isOpen ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphInto_dist_lt_id_of_isOpen

theorem isLocallyFinitePolyhedralManifoldWithBoundary_univ_three :
    (_root_.Set.univ : Set (EuclideanSpace ℝ (Fin 3))).Nonempty ∧
      IsLocallyFinitePolyhedralManifoldWithBoundary (n := 3) 3
        (_root_.Set.univ : Set (EuclideanSpace ℝ (Fin 3))) ∧
      ∃ f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
        IsPLHomeomorphInto 3 f _root_.Set.univ ∧
          ∀ x ∈ (_root_.Set.univ : Set (EuclideanSpace ℝ (Fin 3))), _root_.Dist.dist (f x) (id x) < 1 :=
  ⟨univ_nonempty, isLocallyFinitePolyhedralManifoldWithBoundary_of_isOpen (m := 2) isOpen_univ,
    exists_isPLHomeomorphInto_dist_lt_id_of_isOpen isOpen_univ fun _ _ => one_pos⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isLocallyFinitePolyhedralManifoldWithBoundary_univ_three then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isLocallyFinitePolyhedralManifoldWithBoundary_univ_three"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isLocallyFinitePolyhedralManifoldWithBoundary_univ_three ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isLocallyFinitePolyhedralManifoldWithBoundary_univ_three

end DifferentialGeometry.Topology.PiecewiseLinear
