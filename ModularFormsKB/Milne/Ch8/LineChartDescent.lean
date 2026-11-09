import ModularFormsKB.Milne.Ch8.LineCharts

/-!
# Milne, Chapter 8: charts on the affine line by descent from a family (for Theorem 8.4)

Used in the proof of the universal property in Milne's Theorem 8.4 (`milne2017mf`, Section 8, pdf p. 98). Let
$T = \operatorname{Spec} B$ be an affine variety with a map $\pi : k[X] \to B$ that is injective, and $h : T \to Z$ a
regular map with value $b(\tau(\pi X))$ at every $k$-point $\tau$ of $T$. Given one chart for $b$, there is a chart
for $b$ around every point $v$ of $\mathbb A^1$ over which $T$ has a $k$-point (`exists_chart_at`). The proof chooses
an affine open $U = \operatorname{Spec} C$ of $Z$ around $b(v)$, basic opens of $T$ and of the given chart mapping into
$U$, and applies the algebraic descent lemma `LineDescent.exists_descent` to the two ring maps out of $C$.
-/

universe u

open AlgebraicGeometry CategoryTheory Opposite Polynomial

noncomputable section

namespace ModularFormsKB.Milne

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **A nonzero element of a finitely generated $k$-domain is nonzero at some $k$-point** (Nullstellensatz). -/
theorem exists_algHom_ne_zero {R : Type u} [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R]
    {x : R} (hx : x ≠ 0) : ∃ τ : R →ₐ[k] k, τ x ≠ 0 := by
  have : IsDomain (Localization.Away x) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hx)
  have : Algebra.FiniteType k (Localization.Away x) := Algebra.FiniteType.trans (S := R) inferInstance inferInstance
  let V : Variety k := domVariety (Localization.Away x)
  have hV : IsVariety k V.obj.hom := V.property
  haveI : LocallyOfFiniteType V.obj.hom := hV.locallyOfFiniteType
  obtain ⟨y0⟩ : Nonempty (Spec (CommRingCat.of (Localization.Away x))) := inferInstance
  obtain ⟨y, -, hy⟩ := (isClosed_univ (X := Spec (CommRingCat.of (Localization.Away x)))).exists_closed_singleton
    ⟨y0, trivial⟩
  let p : Variety.point k ⟶ V := ⟨Over.homMk (pointOfClosedPoint V.obj.hom y hy)
    (pointOfClosedPoint_comp V.obj.hom y hy)⟩
  obtain ⟨φ, -⟩ := algPoint_surjective p
  refine ⟨φ.comp (IsScalarTower.toAlgHom k R _), ?_⟩
  exact ((IsLocalization.Away.algebraMap_isUnit x).map φ).ne_zero

/-- `LineDescent.toAway` as a $k$-algebra map. -/
def toAwayAlg {B : Type u} [CommRing B] [IsDomain B] [Algebra k B] (π : k[X] →ₐ[k] B) (g : B) (s : k[X]) :
    Localization.Away s →ₐ[k] Localization.Away (g * π s) where
  __ := LineDescent.toAway π g s
  commutes' c := by
    change LineDescent.toAway π g s (algebraMap k[X] _ (Polynomial.C c)) = _
    rw [LineDescent.toAway, IsLocalization.Away.lift_eq]
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [IsScalarTower.algebraMap_apply k B (Localization.Away (g * π s))]
    exact congrArg _ (π.commutes c)

/-- `LineDescent.fromAway` as a $k$-algebra map. -/
def fromAwayAlg {B : Type u} [CommRing B] [IsDomain B] [Algebra k B] (π : k[X] →ₐ[k] B) (g : B) (s : k[X]) :
    Localization.Away g →ₐ[k] Localization.Away (g * π s) where
  __ := LineDescent.fromAway π g s
  commutes' c := by
    change LineDescent.fromAway π g s (algebraMap B _ (algebraMap k B c)) = _
    rw [LineDescent.fromAway, IsLocalization.Away.awayToAwayRight_eq]
    exact (IsScalarTower.algebraMap_apply k B _ c).symm

variable {Z : Variety k} {b : k → (Variety.point k ⟶ Z)}

/-- A morphism $\operatorname{Spec} R \to Z$ with image in an affine open $U$ is $\operatorname{Spec}$ of a ring map
$\Gamma(U) \to R$ followed by $U \to Z$. -/
theorem exists_specMap_fromSpec {R : CommRingCat.{u}} {U : Z.obj.left.Opens} (hU : IsAffineOpen U)
    (m : Spec R ⟶ Z.obj.left) (hm : Set.range m ⊆ U) :
    ∃ φ : Γ(Z.obj.left, U) ⟶ R, Spec.map φ ≫ hU.fromSpec = m := by
  have hm' : Set.range m ⊆ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hm
  refine ⟨Spec.preimage (IsOpenImmersion.lift hU.fromSpec m hm'), ?_⟩
  rw [Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem linePointMor_eq (w : k) :
    linePointMor w = Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom w)) := by
  have h1 : (1 : k[X]).eval w ≠ 0 := by simp
  rw [← linePt_lineι 1 w h1, linePtMor, lineι, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext fun p ↦ evalAwayAlg_algebraMap 1 w h1 p)

theorem mem_basicOpen_linePointMor (w : k) (p : k[X]) :
    p ∉ (linePointMor w (pt0 k) : PrimeSpectrum k[X]).asIdeal ↔ p.eval w ≠ 0 := by
  rw [linePointMor_eq]
  change p ∉ Ideal.comap _ (IsLocalRing.maximalIdeal k) ↔ _
  rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not]
  rfl

/-- A chart whose value at $w_1$ lies in an open $U$ maps a smaller basic open $D(s p) \ni w_1$ into $U$. -/
theorem LineChart.exists_restrict_subset (c : LineChart Z b) (U : Z.obj.left.Opens) (w₁ : k)
    (hw₁ : c.s.eval w₁ ≠ 0) (hU : c.mor (linePtMor c.s w₁ hw₁ (pt0 k)) ∈ U) :
    ∃ p : k[X], p.eval w₁ ≠ 0 ∧
      Set.range (Spec.map (CommRingCat.ofHom (awayLeft c.s p).toRingHom) ≫ c.mor) ⊆ U := by
  let O := c.mor ⁻¹' (U : Set Z.obj.left)
  have hO : IsOpen O := U.2.preimage c.mor.continuous
  have hI : IsOpen (lineι c.s '' O) := (lineι (k := k) c.s).isOpenEmbedding.isOpenMap _ hO
  have hx₁ : linePointMor w₁ (pt0 k) ∈ lineι c.s '' O :=
    ⟨_, hU, by rw [← Scheme.Hom.comp_apply, linePt_lineι]⟩
  obtain ⟨_, ⟨p, rfl⟩, hxp, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx₁ hI
  refine ⟨p, (mem_basicOpen_linePointMor w₁ p).mp hxp, ?_⟩
  rintro _ ⟨y, rfl⟩
  have hy : lineι (k := k) (c.s * p) y ∈ (PrimeSpectrum.basicOpen p : Set (PrimeSpectrum k[X])) := by
    change p ∉ Ideal.comap _ y.asIdeal
    rw [Ideal.mem_comap]
    have hu : IsUnit (algebraMap k[X] (Localization.Away (c.s * p)) p) := by
      simpa using isUnit_algebraMap_of_dvd (dvd_mul_left p c.s) 1
    exact fun h ↦ y.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
  obtain ⟨o, ho, he⟩ := hsub hy
  rw [lineι_mul_left, Scheme.Hom.comp_apply] at he
  rw [(lineι (k := k) c.s).isOpenEmbedding.injective he] at ho
  exact ho

theorem isDomain_away_of_ne {B : Type u} [CommRing B] [IsDomain B] {g : B} (hg : g ≠ 0) :
    IsDomain (Localization.Away g) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hg)

/-- The family map $h$ and a chart agree on $\operatorname{Spec} B_{g \pi(s p)}$, since they agree on $k$-points. -/
theorem compat_of_points {B : Type u} [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    (π : k[X] →ₐ[k] B) (h : domVariety (k := k) B ⟶ Z) (hh : ∀ τ : B →ₐ[k] k, algPoint τ ≫ h = b (τ (π X)))
    (c : LineChart Z b) (p : k[X]) (hp : c.s * p ≠ 0) (g : B) (hg : g * π (c.s * p) ≠ 0) :
    Spec.map (CommRingCat.ofHom (toAwayAlg π g (c.s * p)).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (awayLeft c.s p).toRingHom) ≫ c.mor =
      Spec.map (CommRingCat.ofHom (fromAwayAlg π g (c.s * p)).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away g))) ≫ h.hom.left := by
  haveI := isDomain_away k c.hs
  haveI := isDomain_away k hp
  haveI := isDomain_away_of_ne (left_ne_zero_of_mul hg)
  haveI := isDomain_away_of_ne hg
  haveI : Algebra.FiniteType k (Localization.Away g) := Algebra.FiniteType.trans (S := B) inferInstance
    inferInstance
  haveI : Algebra.FiniteType k (Localization.Away (g * π (c.s * p))) :=
    Algebra.FiniteType.trans (S := B) inferInstance inferInstance
  have key : (domHom (toAwayAlg π g (c.s * p)) ≫ domHom (awayLeft c.s p) ≫ c.m :
      domVariety (Localization.Away (g * π (c.s * p))) ⟶ Z) =
      domHom (fromAwayAlg π g (c.s * p)) ≫ domHom (IsScalarTower.toAlgHom k B (Localization.Away g)) ≫ h := by
    apply Variety.hom_ext_of_points
    intro t
    obtain ⟨τ, rfl⟩ := algPoint_surjective t
    rw [← Category.assoc, algPoint_domHom, ← Category.assoc, algPoint_domHom, ← Category.assoc,
      algPoint_domHom, ← Category.assoc, algPoint_domHom, hh]
    obtain ⟨hw, e⟩ := evalAwayAlg_unique ((τ.comp (toAwayAlg π g (c.s * p))).comp (awayLeft c.s p))
    rw [e, c.val]
    congr 1
    change τ (LineDescent.toAway π g (c.s * p) (awayLeft c.s p (algebraMap k[X] _ X))) =
      τ (LineDescent.fromAway π g (c.s * p) (algebraMap B _ (π X)))
    rw [awayLeft_algebraMap, LineDescent.toAway, IsLocalization.Away.lift_eq, LineDescent.fromAway,
      IsLocalization.Away.awayToAwayRight_eq]
    rfl
  exact congrArg (fun φ ↦ φ.hom.left) key

theorem mem_basicOpen_algPoint {B : Type u} [CommRing B] [Algebra k B] (τ : B →ₐ[k] k) (g : B) :
    g ∉ (Spec.map (CommRingCat.ofHom τ.toRingHom) (pt0 k) : PrimeSpectrum B).asIdeal ↔ τ g ≠ 0 := by
  change g ∉ Ideal.comap _ (IsLocalRing.maximalIdeal k) ↔ _
  rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not]
  rfl

theorem range_specMap_away_subset {B : Type u} [CommRing B] (g : B) (y : Spec (CommRingCat.of (Localization.Away g))) :
    g ∉ (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away g))) y : PrimeSpectrum B).asIdeal := by
  change g ∉ Ideal.comap _ y.asIdeal
  rw [Ideal.mem_comap]
  exact fun h ↦ y.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit g))

theorem evalAway_comp_awayOfDvd {s' u : k[X]} (hd : s' ∣ u) (w : k) (hw : u.eval w ≠ 0) (hw' : s'.eval w ≠ 0) :
    (LineDescent.evalAway u w hw).comp (LineDescent.awayOfDvd hd) = LineDescent.evalAway s' w hw' := by
  apply IsLocalization.ringHom_ext (Submonoid.powers s')
  ext q
  · simp [LineDescent.awayOfDvd, LineDescent.evalAway, IsLocalization.Away.lift_eq]
  · simp [LineDescent.awayOfDvd, LineDescent.evalAway, IsLocalization.Away.lift_eq]

theorem awayOfDvd_algebraMap {s' u : k[X]} (hd : s' ∣ u) (c : k) :
    LineDescent.awayOfDvd hd (algebraMap k _ c) = algebraMap k _ c := by
  rw [IsScalarTower.algebraMap_apply k k[X] (Localization.Away s'), LineDescent.awayOfDvd,
    IsLocalization.Away.lift_eq, ← IsScalarTower.algebraMap_apply]

/-- A $k$-point of a variety as a morphism of schemes. -/
def pointMor {V : Variety k} (q : Variety.point k ⟶ V) : Spec (CommRingCat.of k) ⟶ V.obj.left := q.hom.left

/-- **A chart around every point over which the family has a $k$-point.** -/
theorem exists_chart_at {B : Type u} [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    (π : k[X] →ₐ[k] B) (hπ : Function.Injective π) (h : domVariety (k := k) B ⟶ Z)
    (hh : ∀ τ : B →ₐ[k] k, algPoint τ ≫ h = b (τ (π X))) (c : LineChart Z b) (v : k)
    (τ₀ : B →ₐ[k] k) (hτ₀ : τ₀ (π X) = v) : ∃ c' : LineChart Z b, c'.s.eval v ≠ 0 := by
  let H : Spec (CommRingCat.of B) ⟶ Z.obj.left := h.hom.left
  let t₀ : Spec (CommRingCat.of B) := Spec.map (CommRingCat.ofHom τ₀.toRingHom) (pt0 k)
  -- an affine open `U` around `b v`
  obtain ⟨U, hU', hzU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.obj.left.isBasis_affineOpens)
    (show H t₀ ∈ (⊤ : Z.obj.left.Opens) from trivial)
  have hU : IsAffineOpen U := hU'
  -- a basic open `D(g) ∋ t₀` of `T` mapping into `U`
  obtain ⟨_, ⟨g, rfl⟩, htg, hgsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (show t₀ ∈ H ⁻¹' U from hzU) (U.2.preimage H.continuous)
  have hτg : τ₀ g ≠ 0 := (mem_basicOpen_algPoint τ₀ g).mp htg
  have hg0 : g ≠ 0 := fun h0 ↦ hτg (by simp [h0])
  have hrg : Set.range (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away g))) ≫ H) ⊆ U := by
    rintro _ ⟨y, rfl⟩
    exact hgsub (range_specMap_away_subset g y)
  obtain ⟨ψ, hψ⟩ := exists_specMap_fromSpec hU _ hrg
  -- a point `w₁` of `D(s)` whose image lies in `U`
  have hπne : ∀ q : k[X], q ≠ 0 → π q ≠ 0 := fun q hq h0 ↦ hq (hπ (by simpa using h0))
  obtain ⟨τ₁, hτ₁⟩ := exists_algHom_ne_zero (k := k) (mul_ne_zero hg0 (hπne _ c.hs))
  have hev₁ := LineDescent.eval_of_algHom π τ₁ (v := τ₁ (π X)) rfl
  rw [map_mul] at hτ₁
  have hw₁ : c.s.eval (τ₁ (π X)) ≠ 0 := by rw [← hev₁]; exact right_ne_zero_of_mul hτ₁
  have hU₁ : c.mor (linePtMor c.s _ hw₁ (pt0 k)) ∈ U := by
    have e1 : linePtMor c.s _ hw₁ ≫ c.mor = Spec.map (CommRingCat.ofHom τ₁.toRingHom) ≫ H :=
      congrArg (fun φ ↦ φ.hom.left) ((c.val _ hw₁).trans (hh τ₁).symm)
    rw [← Scheme.Hom.comp_apply, e1, Scheme.Hom.comp_apply]
    exact hgsub ((mem_basicOpen_algPoint τ₁ g).mpr (left_ne_zero_of_mul hτ₁))
  -- a smaller basic open `D(s p)` of the chart mapping into `U`
  obtain ⟨p, hp, hpsub⟩ := c.exists_restrict_subset U _ hw₁ hU₁
  obtain ⟨φ, hφ⟩ := exists_specMap_fromSpec hU _ hpsub
  have hsp : c.s * p ≠ 0 := mul_ne_zero c.hs (fun h0 ↦ hp (by simp [h0]))
  have hgsp : g * π (c.s * p) ≠ 0 := mul_ne_zero hg0 (hπne _ hsp)
  -- the two ring maps out of `Γ(U)` agree on `B_{g π(s p)}`
  have hcomp : (LineDescent.toAway π g (c.s * p)).comp φ.hom =
      (LineDescent.fromAway π g (c.s * p)).comp ψ.hom := by
    have key := compat_of_points π h hh c p hsp g hgsp
    rw [← hφ] at key
    change _ = _ ≫ Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away g))) ≫ H at key
    rw [← hψ] at key
    have key2 : Spec.map (CommRingCat.ofHom (toAwayAlg π g (c.s * p)).toRingHom) ≫ Spec.map φ =
        Spec.map (CommRingCat.ofHom (fromAwayAlg π g (c.s * p)).toRingHom) ≫ Spec.map ψ := by
      rw [← cancel_mono hU.fromSpec]
      simpa only [Category.assoc] using key
    rw [← Spec.map_comp, ← Spec.map_comp] at key2
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective key2)
  -- descent
  obtain ⟨s', e, hs', hv, φ₀, h1, h2⟩ :=
    LineDescent.exists_descent π hπ τ₀ v hτ₀ (c.s * p) hsp g hτg φ.hom ψ.hom hcomp
  have hs'0 : s' ≠ 0 := fun h0 ↦ hsp (by rw [hs', h0, mul_zero])
  have hd : s' ∣ c.s * p := Dvd.intro_left _ hs'.symm
  have hinj := LineDescent.awayOfDvd_injective hsp hd
  let m' : Spec (CommRingCat.of (Localization.Away s')) ⟶ Z.obj.left :=
    Spec.map (CommRingCat.ofHom φ₀) ≫ hU.fromSpec
  -- `m'` is a morphism over `k`
  have hover : m' ≫ Z.obj.hom = specStructure k (Localization.Away s') := by
    let κ : CommRingCat.of k ⟶ Γ(Z.obj.left, U) := Spec.preimage (hU.fromSpec ≫ Z.obj.hom)
    have hκ : Spec.map κ = hU.fromSpec ≫ Z.obj.hom := Spec.map_preimage _
    have hκφ : κ ≫ φ = CommRingCat.ofHom (algebraMap k (Localization.Away (c.s * p))) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hκ, ← Category.assoc, hφ, Category.assoc]
      change _ ≫ c.m.hom.left ≫ Z.obj.hom = _
      rw [Over.w c.m.hom]
      change _ ≫ specStructure k (Localization.Away c.s) = specStructure k _
      rw [specStructure, specStructure, ← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext (RingHom.ext fun x ↦ (awayLeft c.s p).commutes x)
    have : κ ≫ CommRingCat.ofHom φ₀ = CommRingCat.ofHom (algebraMap k (Localization.Away s')) := by
      ext x
      apply hinj
      have e1 := congrArg (fun f ↦ f.hom x) hκφ
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at e1 ⊢
      rw [awayOfDvd_algebraMap, ← e1, ← h1]
      rfl
    change (Spec.map _ ≫ hU.fromSpec) ≫ Z.obj.hom = _
    rw [Category.assoc, ← hκ, ← Spec.map_comp, this]
  refine ⟨⟨s', hs'0, ⟨Over.homMk m' hover⟩, fun w hw ↦ ?_⟩, hv⟩
  refine InducedCategory.hom_ext (Over.OverMorphism.ext ?_)
  change linePtMor s' w hw ≫ m' = pointMor (b w)
  by_cases hwv : w = v
  · subst hwv
    have e2 : linePtMor s' w hw ≫ Spec.map (CommRingCat.ofHom φ₀) =
        Spec.map (CommRingCat.ofHom (LineDescent.evalAwayB τ₀ g hτg)) ≫ Spec.map ψ := by
      rw [linePtMor, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext h2
    change (linePtMor s' w hw ≫ Spec.map (CommRingCat.ofHom φ₀)) ≫ hU.fromSpec = _
    rw [e2, Category.assoc, hψ, ← Category.assoc, ← Spec.map_comp]
    have e3 : CommRingCat.ofHom (algebraMap B (Localization.Away g)) ≫
        CommRingCat.ofHom (LineDescent.evalAwayB τ₀ g hτg) = CommRingCat.ofHom τ₀.toRingHom :=
      CommRingCat.hom_ext (RingHom.ext fun x ↦ IsLocalization.Away.lift_eq _ (isUnit_iff_ne_zero.mpr hτg) x)
    rw [e3, ← hτ₀]
    exact congrArg (fun φ ↦ φ.hom.left) (hh τ₀)
  · have hw' : (c.s * p).eval w ≠ 0 := by
      rw [hs', eval_mul, eval_pow, eval_sub, eval_X, eval_C]
      exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hwv)) hw
    have e4 : linePtMor s' w hw = linePtMor (c.s * p) w hw' ≫
        Spec.map (CommRingCat.ofHom (LineDescent.awayOfDvd hd)) := by
      rw [linePtMor, linePtMor, ← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext (evalAway_comp_awayOfDvd hd w hw' hw).symm
    have e5 : Spec.map (CommRingCat.ofHom (LineDescent.awayOfDvd hd)) ≫ Spec.map (CommRingCat.ofHom φ₀) =
        Spec.map φ := by
      rw [← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext h1
    have e6 := congrArg (fun φ ↦ φ.hom.left) (linePt_awayLeft c.hs (right_ne_zero_of_mul hsp) w hw')
    change linePtMor (c.s * p) w hw' ≫ Spec.map (CommRingCat.ofHom (awayLeft c.s p).toRingHom) =
      linePtMor c.s w _ at e6
    change (linePtMor s' w hw ≫ Spec.map (CommRingCat.ofHom φ₀)) ≫ hU.fromSpec = _
    rw [e4]
    simp only [Category.assoc]
    erw [reassoc_of% e5]
    rw [hφ, ← Category.assoc, e6]
    exact congrArg (fun φ ↦ φ.hom.left) (c.val w _)

end ModularFormsKB.Milne
