import Submission.DifferentialGeometry.Topology.Diffeomorph.SphereGermExtension
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Boundary
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.CompactGluing
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Metric _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.E3 target :: scope.openDecls } }

variable {Z M : Type*} [TopologicalSpace Z] [ChartedSpace E3 Z] [T3Space Z]
  [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]

theorem exists_partialDiffeomorph_ball_replacement_eqOn_complement
    (b : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞)
    (P : PartialDiffeomorph (𝓡 3) (𝓡 3) Z M ∞)
    (G : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (hb : _root_.Metric.closedBall (0 : E3) 1 ⊆ b.source)
    (hG : _root_.Metric.closedBall (0 : E3) 1 ⊆ G.source)
    {Ω : Set Z} (hΩ : IsCompact Ω)
    (hbΩ : b '' _root_.Metric.closedBall (0 : E3) 1 ⊆ interior Ω)
    (hP : Ω \ b '' _root_.Metric.ball (0 : E3) 1 ⊆ P.source)
    (hboundary : P '' (b '' _root_.Metric.sphere (0 : E3) 1) = G '' _root_.Metric.sphere (0 : E3) 1)
    (hinter : P '' (Ω \ b '' _root_.Metric.ball (0 : E3) 1) ∩ G '' _root_.Metric.closedBall (0 : E3) 1 ⊆
      G '' _root_.Metric.sphere (0 : E3) 1) :
    ∃ (J : PartialDiffeomorph (𝓡 3) (𝓡 3) Z M ∞)
      (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞),
      Ω ⊆ J.source ∧
      J '' Ω = P '' (Ω \ b '' _root_.Metric.ball (0 : E3) 1) ∪ G '' _root_.Metric.closedBall (0 : E3) 1 ∧
      D '' _root_.Metric.closedBall (0 : E3) 1 = _root_.Metric.closedBall (0 : E3) 1 ∧
      (∀ z ∈ _root_.Metric.closedBall (0 : E3) 1, J (b z) = G (D z)) ∧
      ∃ O : Set Z, IsOpen O ∧ Ω \ b '' _root_.Metric.ball (0 : E3) 1 ⊆ O ∧
        O ⊆ P.source ∧ _root_.Set.EqOn J P O := by
  let K := Ω \ b '' _root_.Metric.ball (0 : E3) 1
  have hbB : _root_.Metric.ball (0 : E3) 1 ⊆ b.source := ball_subset_closedBall.trans hb
  have hbS : _root_.Metric.sphere (0 : E3) 1 ⊆ b.source := sphere_subset_closedBall.trans hb
  have hK : IsCompact K := hΩ.inter_right
    (b.toOpenPartialHomeomorph.isOpen_image_of_subset_source _root_.Metric.isOpen_ball hbB).isClosed_compl
  have hbsK : b '' _root_.Metric.sphere (0 : E3) 1 ⊆ K := by
    rintro y ⟨z, hz, rfl⟩
    refine ⟨interior_subset (hbΩ ⟨z, _root_.Metric.sphere_subset_closedBall hz, rfl⟩), ?_⟩
    rintro ⟨w, hw, hwz⟩
    have hwz' : w = z := b.toPartialEquiv.injOn (hbB hw) (hbS hz) hwz
    exact (mem_ball_zero_iff.mp (hwz' ▸ hw)).ne (mem_sphere_zero_iff_norm.mp hz)
  let P₀ := DifferentialGeometry.Topology.PartialDiffeomorph.restrict P (interior Ω) isOpen_interior
  let A := (b.trans P₀).trans G.symm
  have hAs : _root_.Metric.sphere (0 : E3) 1 ⊆ A.source := by
    intro z hz
    have hzK := hbsK ⟨z, hz, rfl⟩
    refine ⟨⟨hbS hz, hP hzK, hbΩ ⟨z, _root_.Metric.sphere_subset_closedBall hz, rfl⟩⟩, ?_⟩
    obtain ⟨w, hw, heq⟩ := hboundary ▸ _root_.Set.mem_image_of_mem P (_root_.Set.mem_image_of_mem b hz)
    change P (b z) ∈ G.target
    exact heq ▸ G.map_source (hG (_root_.Metric.sphere_subset_closedBall hw))
  have hAsphere : A '' _root_.Metric.sphere (0 : E3) 1 = _root_.Metric.sphere (0 : E3) 1 := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨w, hw, heq⟩ := hboundary ▸ _root_.Set.mem_image_of_mem P (_root_.Set.mem_image_of_mem b hz)
      change G.symm (P (b z)) ∈ _root_.Metric.sphere (0 : E3) 1
      rw [← heq]
      exact (G.toPartialEquiv.left_inv (hG (_root_.Metric.sphere_subset_closedBall hw))).symm ▸ hw
    · intro hy
      obtain ⟨_, ⟨z, hz, rfl⟩, heq⟩ := hboundary.symm ▸ _root_.Set.mem_image_of_mem G hy
      refine ⟨z, hz, ?_⟩
      change G.symm (P (b z)) = y
      rw [heq]
      exact G.toPartialEquiv.left_inv (hG (_root_.Metric.sphere_subset_closedBall hy))
  have hAout : _root_.Set.MapsTo A ((_root_.Metric.ball (0 : E3) 1)ᶜ ∩ A.source) (_root_.Metric.ball (0 : E3) 1)ᶜ := by
    intro z hz hAin
    have hbzK : b z ∈ K := by
      refine ⟨interior_subset hz.2.1.2.2, ?_⟩
      rintro ⟨w, hw, heq⟩
      exact hz.1 ((b.toPartialEquiv.injOn (hbB hw) hz.2.1.1 heq) ▸ hw)
    have hPbinG : P (b z) ∈ G '' _root_.Metric.closedBall (0 : E3) 1 := by
      exact ⟨A z, _root_.Metric.ball_subset_closedBall hAin, G.right_inv hz.2.2⟩
    obtain ⟨w, hw, heq⟩ := hinter ⟨mem_image_of_mem P hbzK, hPbinG⟩
    have he : A z = w := by
      change G.symm (P (b z)) = w
      rw [← heq]
      exact G.toPartialEquiv.left_inv (hG (_root_.Metric.sphere_subset_closedBall hw))
    exact (mem_ball_zero_iff.mp (he ▸ hAin)).ne (mem_sphere_zero_iff_norm.mp hw)
  obtain ⟨D, hDball, V, hV, hSV, hVA, hDA⟩ :=
    exists_diffeomorph_eqOn_neighborhood_of_sphere_preserving_partialDiffeomorph_of_compl_ball
      A hAs hAsphere hAout
  let Q := (b.symm.trans D.toPartialDiffeomorph).trans G
  have hQsource : b '' _root_.Metric.closedBall (0 : E3) 1 ⊆ Q.source := by
    rintro y ⟨z, hz, rfl⟩
    refine ⟨⟨b.map_source (hb hz), _root_.Set.mem_univ _⟩, ?_⟩
    change D (b.symm (b z)) ∈ G.source
    have hbz : b.symm.toPartialEquiv (b.toPartialEquiv z) = z :=
      b.toPartialEquiv.left_inv (hb hz)
    rw [hbz]
    exact hG (hDball ▸ _root_.Set.mem_image_of_mem D hz)
  have hQapply (z : E3) (hz : z ∈ _root_.Metric.closedBall (0 : E3) 1) : Q (b z) = G (D z) := by
    change G (D (b.symm (b z))) = G (D z)
    have hbz : b.symm.toPartialEquiv (b.toPartialEquiv z) = z :=
      b.toPartialEquiv.left_inv (hb hz)
    rw [hbz]
  have hQimage : Q '' (b '' _root_.Metric.closedBall (0 : E3) 1) = G '' _root_.Metric.closedBall (0 : E3) 1 := by
    calc
      _ = G '' (D '' _root_.Metric.closedBall (0 : E3) 1) := by
        ext y
        constructor
        · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
          exact ⟨D z, _root_.Set.mem_image_of_mem D hz, (hQapply z hz).symm⟩
        · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
          exact ⟨b z, _root_.Set.mem_image_of_mem b hz, hQapply z hz⟩
      _ = _ := by rw [hDball]
  let O := b '' V
  have hVb : V ⊆ b.source := fun z hz => (hVA hz).1.1
  have hO : IsOpen O := b.toOpenPartialHomeomorph.isOpen_image_of_subset_source hV hVb
  have hPQ : _root_.Set.EqOn P Q O := by
    rintro y ⟨z, hz, rfl⟩
    change P (b z) = G (D (b.symm (b z)))
    have hbz : b.symm.toPartialEquiv (b.toPartialEquiv z) = z :=
      b.toPartialEquiv.left_inv (hVb hz)
    rw [hbz, hDA hz]
    exact (G.right_inv (hVA hz).2).symm
  have hKball : K ∩ (b '' _root_.Metric.closedBall (0 : E3) 1) = b '' _root_.Metric.sphere (0 : E3) 1 := by
    apply subset_antisymm
    · rintro y ⟨hyK, z, hz, rfl⟩
      refine ⟨z, ?_, rfl⟩
      rw [mem_sphere_zero_iff_norm]
      exact le_antisymm (mem_closedBall_zero_iff.mp hz)
        (not_lt.mp (fun h => hyK.2 ⟨z, mem_ball_zero_iff.mpr h, rfl⟩))
    · exact fun y hy => ⟨hbsK hy, _root_.Set.image_mono _root_.Metric.sphere_subset_closedBall hy⟩
  have himage : P '' K ∩ Q '' (b '' _root_.Metric.closedBall (0 : E3) 1) ⊆
      P '' (K ∩ (b '' _root_.Metric.closedBall (0 : E3) 1)) := by
    rw [hQimage, hKball, hboundary]
    exact hinter
  have hbc : IsCompact (b '' _root_.Metric.closedBall (0 : E3) 1) :=
    (_root_.ProperSpace.isCompact_closedBall _ _).image_of_continuousOn (b.contMDiffOn_toFun.continuousOn.mono hb)
  obtain ⟨J, O₀, O₁, hO₀, _, hKO₀, hBO₁, hJO, hJP, hJQ⟩ :=
    PartialDiffeomorph.exists_eqOn_neighborhoods_of_isCompact P Q hK hbc hP hQsource
      hO (hKball ▸ _root_.Set.image_mono hSV) hPQ himage
  have hcover : K ∪ (b '' _root_.Metric.closedBall (0 : E3) 1) = Ω := by
    apply subset_antisymm
    · exact _root_.Set.union_subset _root_.Set.sdiff_subset (hbΩ.trans interior_subset)
    · intro x hx
      by_cases hb : x ∈ b '' _root_.Metric.ball (0 : E3) 1
      · exact Or.inr (_root_.Set.image_mono _root_.Metric.ball_subset_closedBall hb)
      · exact Or.inl ⟨hx, hb⟩
  have hJsource : Ω ⊆ J.source := by
    rw [← hcover]
    exact (_root_.Set.union_subset_union hKO₀ hBO₁).trans hJO
  refine ⟨J, D, hJsource, ?_, hDball, ?_, O₀ ∩ P.source, hO₀.inter P.open_source,
    _root_.Set.subset_inter hKO₀ hP, _root_.Set.inter_subset_right, fun z hz => hJP hz.1⟩
  · calc
      J '' Ω = J '' (K ∪ b '' _root_.Metric.closedBall (0 : E3) 1) := congrArg (Set.image J) hcover.symm
      _ = P '' K ∪ G '' _root_.Metric.closedBall (0 : E3) 1 := by
        rw [_root_.Set.image_union, (hJP.mono hKO₀).image_eq, (hJQ.mono hBO₁).image_eq, hQimage]
  · exact fun z hz => (hJQ (hBO₁ (_root_.Set.mem_image_of_mem b hz))).trans (hQapply z hz)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_ball_replacement_eqOn_complement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_ball_replacement_eqOn_complement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_ball_replacement_eqOn_complement ``Submission.DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_ball_replacement_eqOn_complement

end DifferentialGeometry.Topology.Manifold

section

open _root_.Set _root_.Metric _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {Z M ι : Type*} [TopologicalSpace Z] [ChartedSpace E3 Z] [T3Space Z]
  [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]

omit [T3Space Z] in
private theorem ball_chart_sphere_subset_punctured
    (b : ι → PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞)
    (s : Finset ι)
    (hb : ∀ i ∈ s, _root_.Metric.closedBall (0 : E3) 1 ⊆ (b i).source) {Ω : Set Z}
    (hΩ : ∀ i ∈ s, b i '' _root_.Metric.closedBall (0 : E3) 1 ⊆ Ω)
    (hdis : (s : Set ι).Pairwise (fun i j => Disjoint
      (b i '' _root_.Metric.closedBall (0 : E3) 1) (b j '' _root_.Metric.closedBall (0 : E3) 1)))
    (i : ι) (hi : i ∈ s) :
    b i '' _root_.Metric.sphere (0 : E3) 1 ⊆ Ω \ ⋃ j ∈ s, b j '' _root_.Metric.ball (0 : E3) 1 := by
  rintro y ⟨z,hz,rfl⟩
  refine ⟨hΩ i hi (_root_.Set.mem_image_of_mem (b i) (_root_.Metric.sphere_subset_closedBall hz)),?_⟩
  intro hy
  obtain ⟨j,hj,w,hw,heq⟩ := mem_iUnion₂.mp hy
  by_cases hij : i = j
  · subst j
    have he := (b i).injOn (hb i hi (_root_.Metric.ball_subset_closedBall hw)) (hb i hi (_root_.Metric.sphere_subset_closedBall hz)) heq
    exact (mem_ball_zero_iff.mp (he ▸ hw)).ne (mem_sphere_zero_iff_norm.mp hz)
  · exact disjoint_left.mp (hdis hi hj hij)
      (_root_.Set.mem_image_of_mem (b i) (_root_.Metric.sphere_subset_closedBall hz))
      ⟨w,_root_.Metric.ball_subset_closedBall hw,heq⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.ball_chart_sphere_subset_punctured
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.ball_chart_sphere_subset_punctured target :: scope.openDecls } }

theorem exists_partialDiffeomorph_finite_ball_replacement_eqOn_complement
    (s : Finset ι)
    (b : ι → PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞)
    (G : ι → PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (hb : ∀ i ∈ s, _root_.Metric.closedBall (0 : E3) 1 ⊆ (b i).source)
    (hG : ∀ i ∈ s, _root_.Metric.closedBall (0 : E3) 1 ⊆ (G i).source)
    {Ω : Set Z} (hΩ : IsCompact Ω)
    (hbΩ : ∀ i ∈ s, b i '' _root_.Metric.closedBall (0 : E3) 1 ⊆ interior Ω)
    (hdisb : (s : Set ι).Pairwise (fun i j => Disjoint
      (b i '' _root_.Metric.closedBall (0 : E3) 1) (b j '' _root_.Metric.closedBall (0 : E3) 1)))
    (hdisG : (s : Set ι).Pairwise (fun i j => Disjoint
      (G i '' _root_.Metric.closedBall (0 : E3) 1) (G j '' _root_.Metric.closedBall (0 : E3) 1)))
    (P : PartialDiffeomorph (𝓡 3) (𝓡 3) Z M ∞)
    (hP : Ω \ ⋃ i ∈ s, b i '' _root_.Metric.ball (0 : E3) 1 ⊆ P.source)
    (hboundary : ∀ i ∈ s, P '' (b i '' _root_.Metric.sphere (0 : E3) 1) = G i '' _root_.Metric.sphere (0 : E3) 1)
    (hinter : ∀ i ∈ s, P '' (Ω \ ⋃ j ∈ s, b j '' _root_.Metric.ball (0 : E3) 1) ∩
      G i '' _root_.Metric.closedBall (0 : E3) 1 ⊆ G i '' _root_.Metric.sphere (0 : E3) 1) :
    ∃ J : PartialDiffeomorph (𝓡 3) (𝓡 3) Z M ∞,
      Ω ⊆ J.source ∧
      J '' Ω = P '' (Ω \ ⋃ i ∈ s, b i '' _root_.Metric.ball (0 : E3) 1) ∪
        ⋃ i ∈ s, G i '' _root_.Metric.closedBall (0 : E3) 1 ∧
      (∀ i ∈ s, ∃ D : E3 ≃ₘ[ℝ] E3,
        D '' _root_.Metric.closedBall (0 : E3) 1 = _root_.Metric.closedBall (0 : E3) 1 ∧
        ∀ z ∈ _root_.Metric.closedBall (0 : E3) 1, J (b i z) = G i (D z)) ∧
      ∃ O : Set Z, IsOpen O ∧ (Ω \ ⋃ i ∈ s, b i '' _root_.Metric.ball (0 : E3) 1) ⊆ O ∧
        O ⊆ P.source ∧ _root_.Set.EqOn J P O := by
  classical
  induction s using Finset.induction_on generalizing P with
  | empty =>
    refine ⟨P,?_,?_,?_,P.source,P.open_source,?_,subset_rfl,fun _ _ => rfl⟩
    · simpa using hP
    · simp
    · simp
    · simpa using hP
  | @insert a s ha ih =>
    let A := b a '' _root_.Metric.closedBall (0 : E3) 1
    let U := ⋃ i ∈ s, b i '' _root_.Metric.ball (0 : E3) 1
    let Ω₀ := Ω \ U
    let K := Ω \ ⋃ i ∈ _root_.Insert.insert a s, b i '' _root_.Metric.ball (0 : E3) 1
    have hUopen : IsOpen U := isOpen_biUnion (fun i hi =>
      (b i).toOpenPartialHomeomorph.isOpen_image_of_subset_source _root_.Metric.isOpen_ball
        (ball_subset_closedBall.trans (hb i (Finset.mem_insert_of_mem hi))))
    have hΩ₀ : IsCompact Ω₀ := hΩ.diff hUopen
    have hAΩ : A ⊆ interior Ω₀ := by
      let V := ⋃ i ∈ s, b i '' _root_.Metric.closedBall (0 : E3) 1
      have hVclosed : IsClosed V := s.finite_toSet.isClosed_biUnion (fun i hi =>
        ((_root_.ProperSpace.isCompact_closedBall _ _).image_of_continuousOn
          ((b i).contMDiffOn_toFun.continuousOn.mono (hb i (Finset.mem_insert_of_mem hi)))).isClosed)
      have hAV : Disjoint A V := by
        rw [_root_.Set.disjoint_left]
        intro y hyA hyV
        obtain ⟨i,hi,hy⟩ := mem_iUnion₂.mp hyV
        exact disjoint_left.mp (hdisb (x := a) (y := i) (by simp) (by simp [hi]) (fun he => ha (he.symm ▸ hi))) hyA hy
      have hopen : IsOpen (interior Ω \ V) := isOpen_interior.sdiff hVclosed
      apply subset_trans _ (hopen.subset_interior_iff.mpr _)
      · intro y hy
        exact ⟨hbΩ a (by simp) hy,disjoint_left.mp hAV hy⟩
      · intro y hy
        refine ⟨interior_subset hy.1,?_⟩
        intro hu
        obtain ⟨i,hi,hw⟩ := mem_iUnion₂.mp hu
        exact hy.2 (mem_iUnion₂.mpr ⟨i,hi,_root_.Set.image_mono _root_.Metric.ball_subset_closedBall hw⟩)
    have hK : Ω₀ \ b a '' _root_.Metric.ball (0 : E3) 1 = K := by
      dsimp [Ω₀,K,U]
      rw [Finset.set_biUnion_insert]
      ext y
      simp only [_root_.Set.mem_sdiff,_root_.Set.mem_union,not_or]
      tauto
    obtain ⟨Q,D,hQ,hQi,hD,hQball,O,hO,hKO,hOP,hQP⟩ :=
      exists_partialDiffeomorph_ball_replacement_eqOn_complement (b a) P (G a) (hb a (by simp)) (hG a (by simp))
        hΩ₀ hAΩ (hK.symm ▸ hP) (hboundary a (by simp))
        (hK.symm ▸ hinter a (by simp))
    have hKO' : K ⊆ O := hK ▸ hKO
    have hQimage : Q '' Ω₀ = P '' K ∪ G a '' _root_.Metric.closedBall (0 : E3) 1 := by
      simpa only [hK] using hQi
    have hremaining_boundary (i : ι) (hi : i ∈ s) :
        Q '' (b i '' _root_.Metric.sphere (0 : E3) 1) = G i '' _root_.Metric.sphere (0 : E3) 1 := by
      have hiK := ball_chart_sphere_subset_punctured b (_root_.Insert.insert a s) hb
        (fun j hj => (hbΩ j hj).trans interior_subset) hdisb i (by simp [hi])
      rw [(hQP.mono (hiK.trans hKO')).image_eq]
      exact hboundary i (by simp [hi])
    have hremaining_inter (i : ι) (hi : i ∈ s) :
        Q '' Ω₀ ∩ G i '' _root_.Metric.closedBall (0 : E3) 1 ⊆ G i '' _root_.Metric.sphere (0 : E3) 1 := by
      rw [hQimage]
      rintro y ⟨hy,hyi⟩
      rcases hy with hy | hy
      · exact hinter i (by simp [hi]) ⟨hy,hyi⟩
      · exact False.elim (disjoint_left.mp
          (hdisG (x := a) (y := i) (by simp) (by simp [hi]) (fun he => ha (he.symm ▸ hi))) hy hyi)
    obtain ⟨J,hJ,hJi,hJballs,O',hO',hΩ₀O',hO'Q,hJQ⟩ := ih
      (fun i hi => hb i (by simp [hi]))
      (fun i hi => hG i (by simp [hi]))
      (fun i hi => hbΩ i (by simp [hi]))
      (hdisb.mono (by intro i hi; simp [hi]))
      (hdisG.mono (by intro i hi; simp [hi])) Q hQ hremaining_boundary hremaining_inter
    refine ⟨J,hJ,?_,?_,O ∩ O',hO.inter hO',?_,inter_subset_left.trans hOP,?_⟩
    · rw [hJi,hQimage]
      change (P '' K ∪ G a '' _root_.Metric.closedBall (0 : E3) 1) ∪ _ = P '' K ∪ _
      rw [Finset.set_biUnion_insert, _root_.Set.union_assoc]
    · intro i hi
      rcases Finset.mem_insert.mp hi with heq | hi
      · subst i
        refine ⟨D,hD,?_⟩
        intro z hz
        have hbz : b a z ∈ Ω₀ := interior_subset (hAΩ (_root_.Set.mem_image_of_mem (b a) hz))
        exact (hJQ (hΩ₀O' hbz)).trans (hQball z hz)
      · exact hJballs i hi
    · intro y hy
      refine ⟨hKO' hy,hΩ₀O' ⟨hy.1,?_⟩⟩
      intro hu
      apply hy.2
      rw [Finset.set_biUnion_insert]
      exact Or.inr hu
    · intro y hy
      exact (hJQ hy.2).trans (hQP hy.1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_finite_ball_replacement_eqOn_complement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_finite_ball_replacement_eqOn_complement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_finite_ball_replacement_eqOn_complement ``Submission.DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_finite_ball_replacement_eqOn_complement

end DifferentialGeometry.Topology.Manifold

end
