import Submission.DifferentialGeometry.Topology.Diffeomorph.SphereGermExtension
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Boundary
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.CompactGluing
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Globalization

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Metric
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.Manifold

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Z M : Type*} [TopologicalSpace Z] [ChartedSpace E3 Z]
  [IsManifold (𝓡 3) ∞ Z] [T2Space Z] [CompactSpace Z]
  [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M]

omit [IsManifold (𝓡 3) ∞ Z] [IsManifold (𝓡 3) ∞ M] in
theorem exists_diffeomorph_of_ball_complement_and_ball
    (b : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞)
    (P : PartialDiffeomorph (𝓡 3) (𝓡 3) Z M ∞)
    (G : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (hb1 : _root_.Metric.closedBall (0 : E3) 1 ⊆ b.source)
    (hP : (b '' _root_.Metric.ball (0 : E3) 1)ᶜ ⊆ P.source)
    (hG : _root_.Metric.closedBall (0 : E3) 1 ⊆ G.source)
    {U : Set M} (hPU : P '' (b '' _root_.Metric.ball (0 : E3) 1)ᶜ = U)
    (hGo : G '' _root_.Metric.ball (0 : E3) 1 = Uᶜ)
:
    ∃ e : Diffeomorph (𝓡 3) (𝓡 3) Z M ∞,
      _root_.Set.EqOn e P (b '' _root_.Metric.ball (0 : E3) 1)ᶜ ∧
      e '' (b '' _root_.Metric.ball (0 : E3) 1) = Uᶜ ∧
      ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        D '' _root_.Metric.closedBall (0 : E3) 1 = _root_.Metric.closedBall (0 : E3) 1 ∧
        (∀ z ∈ _root_.Metric.closedBall (0 : E3) 1, e (b z) = G (D z)) ∧
        ∃ O : Set Z, IsOpen O ∧ (b '' _root_.Metric.ball (0 : E3) 1)ᶜ ⊆ O ∧
          O ⊆ P.source ∧ _root_.Set.EqOn e P O := by
  let K := (b '' _root_.Metric.ball (0 : E3) 1)ᶜ
  have hbS : _root_.Metric.sphere (0 : E3) 1 ⊆ b.source := sphere_subset_closedBall.trans hb1
  have hbB : _root_.Metric.ball (0 : E3) 1 ⊆ b.source := ball_subset_closedBall.trans hb1
  have hKc : IsCompact K :=
    (DifferentialGeometry.image_opens_isOpen b (U := ⟨_, isOpen_ball⟩) hbB).isClosed_compl.isCompact
  have hUc : IsClosed U := by
    rw [← hPU]
    exact (hKc.image_of_continuousOn (P.contMDiffOn_toFun.continuousOn.mono hP)).isClosed
  have hGc : G '' _root_.Metric.closedBall (0 : E3) 1 = closure Uᶜ := by
    rw [← closure_image_ball_of_partialDiffeomorph G hG, hGo]
  have hGs : G '' _root_.Metric.sphere (0 : E3) 1 = frontier U := by
    rw [← frontier_image_ball_of_partialDiffeomorph G hG, hGo, frontier_compl]
  have hPs : P '' (b '' _root_.Metric.sphere (0 : E3) 1) = frontier U := by
    rw [← hPU]
    exact image_sphere_eq_frontier_of_ball_complement b P hb1 hKc hP
  have hbsK : b '' _root_.Metric.sphere (0 : E3) 1 ⊆ K := by
    rintro y ⟨z, hz, rfl⟩ ⟨w, hw, heq⟩
    have heq' : w = z := b.toPartialEquiv.injOn (hbB hw) (hbS hz) heq
    subst w
    exact (ne_of_lt hw) hz
  let A := (b.trans P).trans G.symm
  have hAsource : _root_.Metric.sphere (0 : E3) 1 ⊆ A.source := by
    intro z hz
    refine ⟨⟨hbS hz, hP (hbsK (_root_.Set.mem_image_of_mem _ hz))⟩, ?_⟩
    have hzF : P (b z) ∈ frontier U := hPs ▸ _root_.Set.mem_image_of_mem P (_root_.Set.mem_image_of_mem b hz)
    obtain ⟨w, hw, heq⟩ := hGs.symm ▸ hzF
    change P (b z) ∈ G.target
    rw [← heq]
    exact G.map_source' (hG (_root_.Metric.sphere_subset_closedBall hw))
  have hAsphere : A '' _root_.Metric.sphere (0 : E3) 1 = _root_.Metric.sphere (0 : E3) 1 := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzF : P (b z) ∈ frontier U := hPs ▸ _root_.Set.mem_image_of_mem P (_root_.Set.mem_image_of_mem b hz)
      obtain ⟨w, hw, heq⟩ := hGs.symm ▸ hzF
      change G.symm (P (b z)) ∈ _root_.Metric.sphere (0 : E3) 1
      rw [← heq]
      have hleft : G.symm (G w) = w := G.left_inv' (hG (_root_.Metric.sphere_subset_closedBall hw))
      rwa [hleft]
    · intro hy
      have hyF : G y ∈ frontier U := hGs ▸ _root_.Set.mem_image_of_mem G hy
      obtain ⟨_, ⟨z, hz, rfl⟩, heq⟩ := hPs.symm ▸ hyF
      refine ⟨z, hz, ?_⟩
      change G.symm (P (b z)) = y
      rw [heq]
      exact G.left_inv' (hG (_root_.Metric.sphere_subset_closedBall hy))
  have hAmap : _root_.Set.MapsTo A (_root_.Metric.closedBall (0 : E3) 1 ∩ A.source) (_root_.Metric.closedBall (0 : E3) 1) := by
    intro z hz
    by_cases hzS : z ∈ _root_.Metric.sphere (0 : E3) 1
    · exact _root_.Metric.sphere_subset_closedBall (hAsphere ▸ _root_.Set.mem_image_of_mem A hzS)
    · have hzB : z ∈ _root_.Metric.ball (0 : E3) 1 := lt_of_le_of_ne hz.1 hzS
      have hnotU : P (b z) ∉ U := by
        rw [← hPU]
        rintro ⟨w, hw, heq⟩
        have hwz : w = b z := P.toPartialEquiv.injOn (hP hw) hz.2.1.2 heq
        exact hw (hwz ▸ _root_.Set.mem_image_of_mem b hzB)
      obtain ⟨w, hw, heq⟩ := hGo.symm.subset hnotU
      change G.symm (P (b z)) ∈ _root_.Metric.closedBall (0 : E3) 1
      rw [← heq]
      have hleft : G.symm (G w) = w := G.left_inv' (hG (_root_.Metric.ball_subset_closedBall hw))
      rw [hleft]
      exact _root_.Metric.ball_subset_closedBall hw
  obtain ⟨D, hDball, V, hVo, hSV, hVA, hDA⟩ :=
    exists_diffeomorph_eqOn_neighborhood_of_sphere_preserving_partialDiffeomorph A hAsource hAsphere hAmap
  let Q := (b.symm.trans D.toPartialDiffeomorph).trans G
  have hQsource : b '' _root_.Metric.closedBall (0 : E3) 1 ⊆ Q.source := by
    rintro y ⟨z, hz, rfl⟩
    have hbz : b.symm (b z) = z := b.left_inv' (hb1 hz)
    refine ⟨⟨b.map_source' (hb1 hz), _root_.Set.mem_univ _⟩, ?_⟩
    change D (b.symm (b z)) ∈ G.source
    rw [hbz]
    exact hG (hDball ▸ _root_.Set.mem_image_of_mem D hz)
  have hQapply {z : E3} (hz : z ∈ _root_.Metric.closedBall (0 : E3) 1) : Q (b z) = G (D z) := by
    change G (D (b.symm (b z))) = G (D z)
    rw [show b.symm (b z) = z from b.left_inv' (hb1 hz)]
  have hQimage : Q '' (b '' _root_.Metric.closedBall (0 : E3) 1) = closure Uᶜ := by
    calc
      Q '' (b '' _root_.Metric.closedBall (0 : E3) 1) = G '' (D '' _root_.Metric.closedBall (0 : E3) 1) := by
        ext y
        constructor
        · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
          exact ⟨D z, _root_.Set.mem_image_of_mem D hz, (hQapply hz).symm⟩
        · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
          exact ⟨b z, _root_.Set.mem_image_of_mem b hz, hQapply hz⟩
      _ = closure Uᶜ := by rw [hDball, hGc]
  let O := b '' V
  have hVb : V ⊆ b.source := fun z hz => (hVA hz).1.1
  have hOo : IsOpen O := DifferentialGeometry.image_opens_isOpen b (U := ⟨V, hVo⟩) hVb
  have hPQ : _root_.Set.EqOn P Q O := by
    rintro y ⟨z, hz, rfl⟩
    have hbz : b.symm (b z) = z := b.left_inv' (hVb hz)
    change P (b z) = G (D (b.symm (b z)))
    rw [hbz, hDA hz]
    exact (G.right_inv' (hVA hz).2).symm
  have hK1c : IsCompact (b '' _root_.Metric.closedBall (0 : E3) 1) :=
    (_root_.ProperSpace.isCompact_closedBall (0 : E3) 1).image_of_continuousOn (b.contMDiffOn_toFun.continuousOn.mono hb1)
  have hinter : K ∩ (b '' _root_.Metric.closedBall (0 : E3) 1) = b '' _root_.Metric.sphere (0 : E3) 1 := by
    apply subset_antisymm
    · rintro y ⟨hyK, z, hz, rfl⟩
      refine ⟨z, ?_, rfl⟩
      exact le_antisymm hz (not_lt.mp fun h => hyK (_root_.Set.mem_image_of_mem b h))
    · rintro y ⟨z, hz, rfl⟩
      exact ⟨hbsK (_root_.Set.mem_image_of_mem b hz), _root_.Set.mem_image_of_mem b (_root_.Metric.sphere_subset_closedBall hz)⟩
  have hKO : K ∩ (b '' _root_.Metric.closedBall (0 : E3) 1) ⊆ O := by rw [hinter]; exact _root_.Set.image_mono hSV
  have himage : P '' K ∩ Q '' (b '' _root_.Metric.closedBall (0 : E3) 1) ⊆ P '' (K ∩ (b '' _root_.Metric.closedBall (0 : E3) 1)) := by
    rw [hPU, hQimage, hinter, hPs, closure_compl, hUc.frontier_eq]
    exact subset_rfl
  obtain ⟨J, O0, O1, hO0o, _hO1o, hKO0, hK1O1, hOsrc, hJP, hJQ⟩ :=
    PartialDiffeomorph.exists_eqOn_neighborhoods_of_isCompact P Q hKc hK1c hP hQsource hOo hKO hPQ himage
  have hcover : K ∪ (b '' _root_.Metric.closedBall (0 : E3) 1) = univ := by
    apply _root_.Set.eq_univ_of_forall
    intro z
    by_cases hz : z ∈ b '' _root_.Metric.ball (0 : E3) 1
    · exact Or.inr (_root_.Set.image_mono _root_.Metric.ball_subset_closedBall hz)
    · exact Or.inl hz
  have hJsrc : J.source = univ := _root_.Set.eq_univ_of_univ_subset (by
    rw [← hcover]
    exact (_root_.Set.union_subset_union hKO0 hK1O1).trans hOsrc)
  have hJtarget : J.target = univ := _root_.Set.eq_univ_of_forall fun y => by
    by_cases hy : y ∈ U
    · obtain ⟨z, hz, hzy⟩ := hPU.symm.subset hy
      have hJz : J z = P z := hJP (hKO0 hz)
      rw [← hzy, ← hJz]
      exact J.map_source' (by rw [hJsrc]; trivial)
    · obtain ⟨z, hz, hzy⟩ := hQimage.symm.subset (subset_closure hy)
      have hJz : J z = Q z := hJQ (hK1O1 hz)
      rw [← hzy, ← hJz]
      exact J.map_source' (by rw [hJsrc]; trivial)
  let e := PDE.RicciFlow.Perelman.KappaSolutions.globalDiffeomorphOfUniv J hJsrc hJtarget
  have heP : _root_.Set.EqOn e P K := fun z hz => hJP (hKO0 hz)
  refine ⟨e, heP, ?_, D, hDball, ?_, O0 ∩ P.source, hO0o.inter P.open_source,
    _root_.Set.subset_inter hKO0 hP, _root_.Set.inter_subset_right, fun z hz => hJP hz.1⟩
  · have heK : e '' K = U := (heP.image_eq).trans hPU
    have hcomp : e '' Kᶜ = Uᶜ := by
      change e.toHomeomorph '' Kᶜ = Uᶜ
      rw [e.toHomeomorph.image_compl]
      exact congrArg _root_.Compl.compl heK
    simpa only [K, compl_compl] using hcomp
  · intro z hz
    exact (hJQ (hK1O1 (_root_.Set.mem_image_of_mem b hz))).trans (hQapply hz)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_diffeomorph_of_ball_complement_and_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_diffeomorph_of_ball_complement_and_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_diffeomorph_of_ball_complement_and_ball ``Submission.DifferentialGeometry.Topology.Manifold.exists_diffeomorph_of_ball_complement_and_ball

end DifferentialGeometry.Topology.Manifold

end

end
