import Submission.DifferentialGeometry.Topology.PiecewiseLinear.OpenStar
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SimplicialMap
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Mesh
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Combinatorial
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem mem_carrierFace_of_mem_openStar {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : Geometry.SimplicialComplex ℝ F) {w y : F} (hy : y ∈ openStar L w) :
    w ∈ carrierFace L y := by
  by_contra hw
  exact hy.2 (_root_.Set.mem_biUnion (s := {t ∈ L.faces | w ∉ t})
    (t := fun t => convexHull ℝ (t : Set F)) ⟨carrierFace_mem hy.1, hw⟩
    (mem_convexHull_carrierFace hy.1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_carrierFace_of_mem_openStar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_carrierFace_of_mem_openStar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_carrierFace_of_mem_openStar ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_carrierFace_of_mem_openStar

open _root_.Classical in
theorem exists_isSubdivision_simplicialApproximation
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (L : Geometry.SimplicialComplex ℝ F) [Finite L.faces]
    {f : E → F} (hf : ContinuousOn f K.space) (hmap : _root_.Set.MapsTo f K.space L.space) :
    ∃ (K' : Geometry.SimplicialComplex ℝ E) (φ : E → F),
      IsSubdivision K' K ∧ K'.faces.Finite ∧
      (∀ s ∈ K'.faces, s.image φ ∈ L.faces) ∧
      ∀ x ∈ K.space, simplicialMap K' φ x ∈
        convexHull ℝ ((carrierFace L (f x) : Finset F) : Set F) := by
  classical
  have hKc : IsCompact K.space := (isPolyhedron_space K).isCompact
  choose V hVopen hVeq using fun w : {w : F // {w} ∈ L.faces} =>
    continuousOn_iff'.mp hf (avoidingUnion L w.1)ᶜ (isClosed_avoidingUnion L w.1).isOpen_compl
  obtain ⟨d, hd, hdsub⟩ := lebesgue_number_lemma_of_metric hKc hVopen (by
    intro x hx
    obtain ⟨w, hw, hxw⟩ := exists_vertex_mem_openStar L (hmap hx)
    refine mem_iUnion.mpr ⟨⟨w, hw⟩, ?_⟩
    have hx' : x ∈ f ⁻¹' (avoidingUnion L w)ᶜ ∩ K.space := ⟨hxw.2, hx⟩
    rw [hVeq ⟨w, hw⟩] at hx'
    exact hx'.1)
  obtain ⟨K', hK', hK'fin, -, hK'diam⟩ :=
    exists_isSubdivision_diam_lt K (N := Module.finrank ℝ E)
      (fun s hs => card_le_finrank_succ_of_mem_faces K hs) hd
  let _ : Finite K'.faces := hK'fin.to_subtype
  have hK'space : K'.space = K.space := hK'.space_eq
  have hstarball : ∀ v : E, closedStar K' v ⊆ _root_.Metric.ball v d := by
    intro v y hy
    obtain ⟨s, ⟨hs, hvs⟩, hys⟩ := mem_iUnion₂.mp hy
    have hbdd : Bornology.IsBounded (convexHull ℝ (s : Set E)) :=
      isBounded_convexHull.mpr s.finite_toSet.isBounded
    rw [_root_.Metric.mem_ball]
    exact lt_of_le_of_lt (_root_.Metric.dist_le_diam_of_mem hbdd hys hvs) (hK'diam s hs)
  have hvert : ∀ v : {v : E // {v} ∈ K'.faces}, ∃ w : F, {w} ∈ L.faces ∧
      ∀ y ∈ closedStar K' v.1 ∩ K.space, f y ∈ openStar L w := by
    rintro ⟨v, hv⟩
    have hvK : v ∈ K.space := by
      rw [← hK'space]
      exact K'.convexHull_subset_space hv (subset_convexHull ℝ _ (by simp))
    obtain ⟨w, hw⟩ := hdsub v hvK
    refine ⟨w.1, w.2, fun y hy => ?_⟩
    have hy' : y ∈ f ⁻¹' (avoidingUnion L w.1)ᶜ ∩ K.space := by
      rw [hVeq w]
      exact ⟨hw (hstarball v hy.1), hy.2⟩
    exact ⟨hmap hy.2, hy'.1⟩
  choose ψ hψmem hψstar using hvert
  set φ : E → F := fun x => if h : {x} ∈ K'.faces then ψ ⟨x, h⟩ else 0 with hφdef
  have hkey : ∀ s ∈ K'.faces, ∀ x ∈ convexHull ℝ (s : Set E), ∀ v ∈ s,
      φ v ∈ carrierFace L (f x) := by
    intro s hs x hxs v hv
    have hv' : {v} ∈ K'.faces :=
      K'.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    have hxK : x ∈ K.space := by
      rw [← hK'space]
      exact K'.convexHull_subset_space hs hxs
    have hxstar : x ∈ closedStar K' v :=
      mem_biUnion (s := {s ∈ K'.faces | v ∈ convexHull ℝ (s : Set E)})
        (t := fun s => convexHull ℝ (s : Set E)) ⟨hs, subset_convexHull ℝ _ hv⟩ hxs
    have hφv : φ v = ψ ⟨v, hv'⟩ := by
      rw [hφdef]
      simp only [hv', dif_pos]
    rw [hφv]
    exact mem_carrierFace_of_mem_openStar L (hψstar ⟨v, hv'⟩ x ⟨hxstar, hxK⟩)
  refine ⟨K', φ, hK', hK'fin, ?_, ?_⟩
  · intro s hs
    obtain ⟨p, hp⟩ := K'.nonempty_of_mem_faces hs
    have hpH : p ∈ convexHull ℝ (s : Set E) := subset_convexHull ℝ _ hp
    have hpK : p ∈ K.space := by
      rw [← hK'space]
      exact K'.convexHull_subset_space hs hpH
    refine L.down_closed (carrierFace_mem (hmap hpK)) ?_ ((K'.nonempty_of_mem_faces hs).image φ)
    exact Finset.image_subset_iff.mpr fun v hv => hkey s hs p hpH v hv
  · intro x hx
    have hxK' : x ∈ K'.space := by rw [hK'space]; exact hx
    refine convexHull_mono ?_
      (simplicialMap_mem_convexHull_image K' φ (carrierFace_mem hxK')
        (mem_convexHull_carrierFace hxK'))
    intro y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
    exact hkey _ (carrierFace_mem hxK') x (mem_convexHull_carrierFace hxK') v hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isSubdivision_simplicialApproximation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isSubdivision_simplicialApproximation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isSubdivision_simplicialApproximation ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isSubdivision_simplicialApproximation

theorem mapsTo_lineMap_of_mem_convexHull_carrierFace
    {E F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : Geometry.SimplicialComplex ℝ F) {f g : E → F} {s : Set E}
    (hmap : _root_.Set.MapsTo f s L.space)
    (hg : ∀ x ∈ s, g x ∈ convexHull ℝ ((carrierFace L (f x) : Finset F) : Set F))
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    MapsTo (fun x => (1 - t) • f x + t • g x) s L.space := by
  intro x hx
  refine L.convexHull_subset_space (carrierFace_mem (hmap hx)) ?_
  exact (convex_convexHull ℝ _) (mem_convexHull_carrierFace (hmap hx)) (hg x hx)
    (by linarith) ht₀ (by ring)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_lineMap_of_mem_convexHull_carrierFace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_lineMap_of_mem_convexHull_carrierFace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_lineMap_of_mem_convexHull_carrierFace ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_lineMap_of_mem_convexHull_carrierFace

open _root_.Classical in
theorem exists_isPiecewiseAffineOn_mapsTo_dist_lt
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (L : Geometry.SimplicialComplex ℝ F) [Finite L.faces]
    {f : E → F} (hf : ContinuousOn f K.space) (hmap : _root_.Set.MapsTo f K.space L.space)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → F, IsPiecewiseAffineOn g K.space ∧ _root_.Set.MapsTo g K.space L.space ∧
      (∀ x ∈ K.space, _root_.Dist.dist (g x) (f x) < ε) ∧
      ContinuousOn (fun p : ℝ × E => (1 - p.1) • f p.2 + p.1 • g p.2)
        (Set.Icc (0 : ℝ) 1 ×ˢ K.space) ∧
      _root_.Set.MapsTo (fun p : ℝ × E => (1 - p.1) • f p.2 + p.1 • g p.2)
        (Set.Icc (0 : ℝ) 1 ×ˢ K.space) L.space := by
  classical
  obtain ⟨L', hL', hL'fin, -, hL'diam⟩ :=
    exists_isSubdivision_diam_lt L (N := Module.finrank ℝ F)
      (fun s hs => card_le_finrank_succ_of_mem_faces L hs) hε
  let _ : Finite L'.faces := hL'fin.to_subtype
  have hL'space : L'.space = L.space := hL'.space_eq
  obtain ⟨K', φ, hK', hK'fin, hφ, hclose⟩ :=
    exists_isSubdivision_simplicialApproximation K L' hf (by rw [hL'space]; exact hmap)
  let _ : Finite K'.faces := hK'fin.to_subtype
  have hK'space : K'.space = K.space := hK'.space_eq
  have hgc : ContinuousOn (simplicialMap K' φ) K.space := by
    rw [← hK'space]
    exact (isPiecewiseAffineOn_simplicialMap K' φ).continuousOn
  have hmapL' : _root_.Set.MapsTo f K.space L'.space := by rw [hL'space]; exact hmap
  refine ⟨simplicialMap K' φ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hK'space]
    exact isPiecewiseAffineOn_simplicialMap K' φ
  · rw [← hL'space, ← hK'space]
    exact simplicialMap_mapsTo K' L' φ hφ
  · intro x hx
    have hxL : f x ∈ L'.space := by rw [hL'space]; exact hmap hx
    have hbdd : Bornology.IsBounded (convexHull ℝ ((carrierFace L' (f x) : Finset F) : Set F)) :=
      isBounded_convexHull.mpr (carrierFace L' (f x)).finite_toSet.isBounded
    exact lt_of_le_of_lt
      (_root_.Metric.dist_le_diam_of_mem hbdd (hclose x hx) (mem_convexHull_carrierFace hxL))
      (hL'diam _ (carrierFace_mem hxL))
  · exact ((continuousOn_const.sub (continuous_fst.continuousOn)).smul
      (hf.comp continuous_snd.continuousOn fun p hp => hp.2)).add
      ((continuous_fst.continuousOn).smul (hgc.comp continuous_snd.continuousOn fun p hp => hp.2))
  · intro p hp
    rw [← hL'space]
    exact mapsTo_lineMap_of_mem_convexHull_carrierFace L' hmapL' hclose hp.1.1 hp.1.2 hp.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPiecewiseAffineOn_mapsTo_dist_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPiecewiseAffineOn_mapsTo_dist_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPiecewiseAffineOn_mapsTo_dist_lt ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPiecewiseAffineOn_mapsTo_dist_lt

theorem eqOn_simplicialApproximation_of_mem_carrierFace_singleton
    {E F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : Geometry.SimplicialComplex ℝ F) {f g : E → F} {s : Set E}
    (hmap : _root_.Set.MapsTo f s L.space)
    (hg : ∀ x ∈ s, g x ∈ convexHull ℝ ((carrierFace L (f x) : Finset F) : Set F))
    {x : E} (hx : x ∈ s) (hcard : (carrierFace L (f x)).card = 1) : g x = f x := by
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard
  have hsub : convexHull ℝ ((carrierFace L (f x) : Finset F) : Set F) = {v} := by
    rw [hv]
    simp
  have h1 := hg x hx
  have h2 := mem_convexHull_carrierFace (hmap hx)
  rw [hsub] at h1 h2
  rw [h1, h2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eqOn_simplicialApproximation_of_mem_carrierFace_singleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eqOn_simplicialApproximation_of_mem_carrierFace_singleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eqOn_simplicialApproximation_of_mem_carrierFace_singleton ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eqOn_simplicialApproximation_of_mem_carrierFace_singleton

theorem homotopic_restrict_of_continuousOn
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {S : Set X} {T : Set Y}
    {f g : X → Y} (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (hfT : _root_.Set.MapsTo f S T) (hgT : _root_.Set.MapsTo g S T)
    {H : ℝ × X → Y} (hH : ContinuousOn H (Set.Icc (0 : ℝ) 1 ×ˢ S))
    (hHT : _root_.Set.MapsTo H (Set.Icc (0 : ℝ) 1 ×ˢ S) T)
    (h0 : ∀ x ∈ S, H (0, x) = f x) (h1 : ∀ x ∈ S, H (1, x) = g x) :
    ContinuousMap.Homotopic
      (⟨fun x : S => (⟨f x, hfT x.2⟩ : T), hf.domRestrict.subtype_mk _⟩ : C(S, T))
      (⟨fun x : S => (⟨g x, hgT x.2⟩ : T), hg.domRestrict.subtype_mk _⟩ : C(S, T)) := by
  refine ⟨{ toFun := fun q => ⟨H ((q.1 : ℝ), (q.2 : X)), hHT ⟨q.1.2, q.2.2⟩⟩
            continuous_toFun := ?_
            map_zero_left := ?_
            map_one_left := ?_ }⟩
  · refine Continuous.subtype_mk ?_ _
    refine hH.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)) ?_
    exact fun q => ⟨q.1.2, q.2.2⟩
  · intro x
    exact Subtype.ext (h0 x x.2)
  · intro x
    exact Subtype.ext (h1 x x.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.homotopic_restrict_of_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.homotopic_restrict_of_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.homotopic_restrict_of_continuousOn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.homotopic_restrict_of_continuousOn

open _root_.Classical in
theorem exists_isPiecewiseAffineOn_mapsTo_dist_lt_homotopic
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (L : Geometry.SimplicialComplex ℝ F) [Finite L.faces]
    {f : E → F} (hf : ContinuousOn f K.space) (hmap : _root_.Set.MapsTo f K.space L.space)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : E → F) (hg : IsPiecewiseAffineOn g K.space) (hgmap : _root_.Set.MapsTo g K.space L.space),
      (∀ x ∈ K.space, _root_.Dist.dist (g x) (f x) < ε) ∧
      ContinuousMap.Homotopic
        (⟨fun x : K.space => (⟨f x, hmap x.2⟩ : L.space), hf.domRestrict.subtype_mk _⟩ :
          C(K.space, L.space))
        (⟨fun x : K.space => (⟨g x, hgmap x.2⟩ : L.space),
          hg.continuousOn.domRestrict.subtype_mk _⟩ : C(K.space, L.space)) := by
  obtain ⟨g, hg, hgmap, hdist, hHcont, hHmap⟩ :=
    exists_isPiecewiseAffineOn_mapsTo_dist_lt K L hf hmap hε
  refine ⟨g, hg, hgmap, hdist, ?_⟩
  exact homotopic_restrict_of_continuousOn hf hg.continuousOn hmap hgmap hHcont hHmap
    (fun x _ => by simp) (fun x _ => by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPiecewiseAffineOn_mapsTo_dist_lt_homotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPiecewiseAffineOn_mapsTo_dist_lt_homotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPiecewiseAffineOn_mapsTo_dist_lt_homotopic ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPiecewiseAffineOn_mapsTo_dist_lt_homotopic

open _root_.Classical in
theorem exists_isPiecewiseAffineOn_freeLoop_homotopic
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (J : Geometry.SimplicialComplex ℝ E) [Finite J.faces]
    (L : Geometry.SimplicialComplex ℝ F) [Finite L.faces]
    (e : loopCircle ≃ₜ J.space) (γ : freeLoop L.space) {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : E → F) (hg : IsPiecewiseAffineOn g J.space) (hgmap : _root_.Set.MapsTo g J.space L.space),
      γ.Homotopic
        ((⟨fun x : J.space => (⟨g x, hgmap x.2⟩ : L.space),
          hg.continuousOn.domRestrict.subtype_mk _⟩ : C(J.space, L.space)).comp
            (e : C(loopCircle, J.space))) := by
  classical
  set Φ : C(J.space, L.space) := γ.comp (e.symm : C(J.space, loopCircle)) with hΦdef
  set f : E → F := fun x => if h : x ∈ J.space then ((Φ ⟨x, h⟩ : L.space) : F) else 0 with hfdef
  have hfval : ∀ x : J.space, f x = ((Φ x : L.space) : F) := by
    intro x
    rw [hfdef]
    simp only [dif_pos x.2]
  have hf : ContinuousOn f J.space := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hres : J.space.domRestrict f = fun x => ((Φ x : L.space) : F) := funext hfval
    rw [hres]
    exact continuous_subtype_val.comp Φ.continuous
  have hmap : _root_.Set.MapsTo f J.space L.space := by
    intro x hx
    rw [hfval ⟨x, hx⟩]
    exact (Φ ⟨x, hx⟩).2
  obtain ⟨g, hg, hgmap, -, hhom⟩ :=
    exists_isPiecewiseAffineOn_mapsTo_dist_lt_homotopic J L hf hmap hε
  refine ⟨g, hg, hgmap, ?_⟩
  have hFΦ : (⟨fun x : J.space => (⟨f x, hmap x.2⟩ : L.space),
      hf.domRestrict.subtype_mk _⟩ : C(J.space, L.space)) = Φ :=
    ContinuousMap.ext fun x => Subtype.ext (hfval x)
  rw [hFΦ] at hhom
  have hγ : γ = Φ.comp (e : C(loopCircle, J.space)) :=
    ContinuousMap.ext fun t => by rw [hΦdef]; simp
  rw [hγ]
  exact hhom.comp (ContinuousMap.Homotopic.refl (e : C(loopCircle, J.space)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPiecewiseAffineOn_freeLoop_homotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPiecewiseAffineOn_freeLoop_homotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPiecewiseAffineOn_freeLoop_homotopic ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPiecewiseAffineOn_freeLoop_homotopic

end DifferentialGeometry.Topology.PiecewiseLinear
