import ModularFormsKB.Milne.Ch6.JCoefficients
import ModularFormsKB.Milne.Ch6.ModularEquation

/-!
# Milne, Example 6.2: $F_2(j(z), j(2z)) \to 0$ at $i\infty$

Let $F_2$ be the level-two modular polynomial of Example 6.2 (`ModularFormsKB.Milne.modularPolynomialTwo`), here as the
function `F2` of two complex variables. Write $q = e^{2\pi i z}$ and $qj(z) = p(q) + q^7 r(z)$, where
$p(q) = 1 + 744q + \cdots + 333202640600q^6$ (`ModularFormsKB.Milne.JCoefficients`) and $r$ converges at $i\infty$.
Then $q^2 j(2z) = p(q^2) + q^{14} r(2z)$, and a polynomial identity (`F2_hom_eq`) gives
$$F_2(j(z), j(2z)) = q \cdot H(q, r(z), r(2z))$$
for an explicit polynomial $H$ with integer coefficients. Hence $F_2(j(z), j(2z)) \to 0$ as $\operatorname{Im} z \to \infty$
(`tendsto_F2_j_j2`). This is the $q$-expansion check of Milne, Example 6.2, pdf p. 90.
-/

open UpperHalfPlane ModularForm Filter Topology
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Milne.LevelTwo

open TauCeti.ModularForm JCoefficients

local notation "𝕢" => Function.Periodic.qParam

/-- Milne's level-two modular polynomial $F_2(X, Y)$ (Example 6.2) as a function of two complex variables. -/
def F2 (X Y : ℂ) : ℂ :=
  X ^ 3 + Y ^ 3 - X ^ 2 * Y ^ 2 + 1488 * X * Y * (X + Y) - 162000 * (X ^ 2 + Y ^ 2) + 40773375 * X * Y +
    8748000000 * (X + Y) - 157464000000000

/-- `F2` is the evaluation of `modularPolynomialTwo`. -/
theorem eval_modularPolynomialTwo {R : Type*} [CommRing R] (x : Fin 2 → R) :
    MvPolynomial.eval₂ (Int.castRingHom R) x modularPolynomialTwo =
      x 0 ^ 3 + x 1 ^ 3 - x 0 ^ 2 * x 1 ^ 2 + 1488 * x 0 * x 1 * (x 0 + x 1) - 162000 * (x 0 ^ 2 + x 1 ^ 2) +
        40773375 * x 0 * x 1 + 8748000000 * (x 0 + x 1) - 157464000000000 := by
  simp [modularPolynomialTwo]

/-- $F_2$ is symmetric. -/
theorem F2_comm (X Y : ℂ) : F2 X Y = F2 Y X := by
  unfold F2; ring

/-- The truncation $1 + 744q + \cdots + 333202640600q^6$ of the $q$-expansion of $qj$. -/
def jPoly (w : ℂ) : ℂ :=
  1 + 744 * w + 196884 * w ^ 2 + 21493760 * w ^ 3 + 864299970 * w ^ 4 + 20245856256 * w ^ 5 +
    333202640600 * w ^ 6

/-- The remainder $r(z) = (qj(z) - p(q))/q^7$. -/
def jRem (τ : ℍ) : ℂ :=
  (𝕢 1 τ * j τ - jPoly (𝕢 1 τ)) / 𝕢 1 τ ^ 7

theorem qParam_ne_zero (τ : ℍ) : 𝕢 1 (τ : ℂ) ≠ 0 := Function.Periodic.qParam_ne_zero _

/-- $qj(z) = p(q) + q^7 r(z)$. -/
theorem qParam_mul_j_eq (τ : ℍ) : 𝕢 1 τ * j τ = jPoly (𝕢 1 τ) + 𝕢 1 τ ^ 7 * jRem τ := by
  have := qParam_ne_zero τ
  unfold jRem
  field_simp
  ring

/-- The $q$-expansion of the remainder: $r(z) = \sum_m c_{m+7} q^m$. -/
theorem hasSum_jRem (τ : ℍ) :
    HasSum (fun m ↦ (qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ)).coeff (m + 7) • 𝕢 1 τ ^ m) (jRem τ) := by
  have hq := qParam_ne_zero τ
  have h := ((hasSum_nat_add_iff' 7).mpr (hasSum_qExpansion_qParam_mul_j τ)).div_const (𝕢 1 τ ^ 7)
  convert h using 1
  · funext m
    simp only [smul_eq_mul, pow_add]
    field_simp
  · simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, smul_eq_mul,
      qExpansion_qParam_mul_j_coeff_zero, qExpansion_qParam_mul_j_coeff_one,
      qExpansion_qParam_mul_j_coeff_two, j_coeff_three, j_coeff_four, j_coeff_five, j_coeff_six, jRem, jPoly]
    ring

/-- The remainder converges at $i\infty$. -/
theorem tendsto_jRem :
    Tendsto jRem atImInfty (𝓝 ((qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ)).coeff 7)) := by
  simpa using tendsto_atImInfty_of_hasSum_qExpansion one_pos hasSum_jRem

/-- Coefficient of $u^0v^0$ in `Hpoly`. -/
def hc00 (w : ℂ) : ℂ :=
  8504046600192 + 89313988143870 * w + 1675113692605513728 * w ^ 2 + 17590839618130669728 * w ^ 3 +
    7508186530353938445570 * w ^ 4 + 78441800789148509501592 * w ^ 5 + 3536258012229689454097800 * w ^ 6 +
    16881751242575703514533888 * w ^ 7 + 267114312221075495861623916 * w ^ 8 - 2360907213943224980018439720 *
    w ^ 9 - 209427884590737839671679477616 * w ^ 10 - 9749780328428313123227235963776 * w ^ 11 -
    304447754243996388263131935502896 * w ^ 12 - 7576180470453218595217920469101600 * w ^ 13 -
    119392620760050386696803169856983104 * w ^ 14 - 1816099000464896756200754172821422080 * w ^ 15 -
    13138763804059978236386802514619105280 * w ^ 16 - 136735871786384433998893286570506081672 * w ^ 17 -
    697314230128528007988185306617234194432 * w ^ 18 - 6820960524778252409125887264418577827200 * w ^ 19 -
    26068300265126006898486097503300551180288 * w ^ 20 - 244487944490356456167819854769969440008800 * w ^ 21
    - 714663420102398348405827126194914344304640 * w ^ 22 - 6471381282374294367164535782473373232686080 * w ^
    23 - 13971727766523259787792868664971681477427200 * w ^ 24 -
    122950510234916357270725596623668054667414400 * w ^ 25 - 187508357961553152189741727325855897354240000 *
    w ^ 26 - 1607384849590361507345447988981846858612480000 * w ^ 27 -
    1497929756670124974880961020688267476992000000 * w ^ 28 - 12326328509973176187250579820182068958184000000
    * w ^ 29

/-- Coefficient of $u^0v^1$ in `Hpoly`. -/
def hc01 (w : ℂ) : ℂ :=
  1 * w ^ 7 - 42987521 * w ^ 10 - 40491712512 * w ^ 11 - 8544538509588 * w ^ 12 - 682000087255040 * w ^ 13 -
    53115380872874946 * w ^ 14 - 2642701420451260656 * w ^ 15 - 87667996677328555736 * w ^ 16 -
    2289666676845656956608 * w ^ 17 - 45118819280402537693184 * w ^ 18 - 945154548169654491833120 * w ^ 19 -
    21375419632132805428838400 * w ^ 20 - 464758561328713966308370176 * w ^ 21 - 7511213815773151797680308224
    * w ^ 22 - 89152815343502564521727605380 * w ^ 23 - 667073670335219811815691780096 * w ^ 24 -
    6548155501525082874057277541760 * w ^ 25 - 25349321799712921486298757857280 * w ^ 26 -
    233000828671625230118779719697824 * w ^ 27 - 579179448737092964266447693414400 * w ^ 28 -
    5152540026150675229102415934681600 * w ^ 29 - 8991103755797336108391939440640000 * w ^ 30 -
    73986979741568587330787824526920000 * w ^ 31

/-- Coefficient of $u^0v^2$ in `Hpoly`. -/
def hc02 (w : ℂ) : ℂ :=
  2 * w ^ 21 - 42987520 * w ^ 24 - 40491318744 * w ^ 25 - 8504046600192 * w ^ 26 - 802981730324480 * w ^ 27 -
    45126282572587008 * w ^ 28 - 1748538123654806910 * w ^ 29 - 49320541086215536640 * w ^ 30 -
    985868760026878332768 * w ^ 31 - 13491945531414459187200 * w ^ 32 - 111023999701813160438200 * w ^ 33

/-- Coefficient of $u^0v^3$ in `Hpoly`. -/
def hc03 (w : ℂ) : ℂ :=
  1 * w ^ 35

/-- Coefficient of $u^1v^0$ in `Hpoly`. -/
def hc10 (w : ℂ) : ℂ :=
  - 2 - 393768 * w ^ 2 + 2 * w ^ 3 - 1728599940 * w ^ 4 + 787536 * w ^ 5 - 666362293680 * w ^ 6 +
    8585030418984 * w ^ 7 + 8504046206424 * w ^ 8 + 1484981925048320 * w ^ 9 + 45109196952767712 * w ^ 10 +
    1801483423682606730 * w ^ 11 + 45969973367290934704 * w ^ 12 + 953321971761854606880 * w ^ 13 -
    1524558903914239459776 * w ^ 14 - 45775283424192024366104 * w ^ 15 - 7072948631373477718024584 * w ^ 16 -
    34453974962259344259809280 * w ^ 17 - 613805215115388619303462560 * w ^ 18 - 1902405778337304721921130496
    * w ^ 19 - 33114338749974960006559702992 * w ^ 20 - 72921470870647817960324464640 * w ^ 21 -
    1250878756627237118867463987648 * w ^ 22 - 2039453223640965306014279270400 * w ^ 23 -
    34576954649486958794917040765440 * w ^ 24 - 40499499686400232709074354962432 * w ^ 25 -
    680354042226884290944987541171200 * w ^ 26 - 551084626093302004064190457446400 * w ^ 27 -
    9183019835022178277610269339040000 * w ^ 28 - 4495551877898668054195969720320000 * w ^ 29 -
    73986979741901659329896262832000000 * w ^ 30

/-- Coefficient of $u^1v^1$ in `Hpoly`. -/
def hc11 (w : ℂ) : ℂ :=
  - 4 * w ^ 14 - 787536 * w ^ 16 - 42987521 * w ^ 17 - 3457987416 * w ^ 18 - 80983425024 * w ^ 19 -
    1487949775264 * w ^ 20 - 16927109775360 * w ^ 21 - 697597908149160 * w ^ 22 - 17792267528175616 * w ^ 23
    - 337398047584909344 * w ^ 24 - 1814946525936599040 * w ^ 25 - 31651113779721615216 * w ^ 26 -
    71734610120184299520 * w ^ 27 - 1222204509991511138880 * w ^ 28 - 1668225892508147974144 * w ^ 29 -
    28135839191926921502400 * w ^ 30 - 26983891062828918374400 * w ^ 31 - 444095998811251073440000 * w ^ 32

/-- Coefficient of $u^1v^2$ in `Hpoly`. -/
def hc12 (w : ℂ) : ℂ :=
  - 2 * w ^ 28 - 393768 * w ^ 30 - 42987520 * w ^ 31 - 1728599940 * w ^ 32 - 40491712512 * w ^ 33 -
    666405281200 * w ^ 34

/-- Coefficient of $u^2v^0$ in `Hpoly`. -/
def hc20 (w : ℂ) : ℂ :=
  - 1 * w ^ 7 + 3 * w ^ 10 + 590652 * w ^ 12 + 21493760 * w ^ 13 + 2592899910 * w ^ 14 + 20245659372 * w ^ 15
    + 999607921800 * w ^ 16 - 8504046600192 * w ^ 17 - 802981794805760 * w ^ 19 - 45126282572587008 * w ^ 21
    - 1748538126247706820 * w ^ 23 - 49320541086215536640 * w ^ 25 - 985868760087615901536 * w ^ 27 -
    13491945531414459187200 * w ^ 29 - 111023999702812768360000 * w ^ 31

/-- Coefficient of $u^2v^1$ in `Hpoly`. -/
def hc21 (w : ℂ) : ℂ :=
  - 2 * w ^ 21 - 393768 * w ^ 25 - 42987520 * w ^ 27 - 1728599940 * w ^ 29 - 40491712512 * w ^ 31 -
    666405281200 * w ^ 33

/-- Coefficient of $u^2v^2$ in `Hpoly`. -/
def hc22 (w : ℂ) : ℂ :=
  - 1 * w ^ 35

/-- Coefficient of $u^3v^0$ in `Hpoly`. -/
def hc30 (w : ℂ) : ℂ :=
  1 * w ^ 17

/-- The explicit polynomial $H$ with $F_2(j(z), j(2z)) = q\,H(q, r(z), r(2z))$. -/
def Hpoly (w u v : ℂ) : ℂ :=
  hc00 w +
    hc01 w * v +
    hc02 w * v ^ 2 +
    hc03 w * v ^ 3 +
    hc10 w * u +
    hc11 w * u * v +
    hc12 w * u * v ^ 2 +
    hc20 w * u ^ 2 +
    hc21 w * u ^ 2 * v +
    hc22 w * u ^ 2 * v ^ 2 +
    hc30 w * u ^ 3

/-- **The polynomial identity.** With $x = p(w) + w^7u$ and $y = p(w^2) + w^{14}v$,
$w^6 F_2(x/w, y/w^2) = w^7 H(w, u, v)$; in homogenized form. -/
theorem F2_hom_eq (w u v : ℂ) :
    let x := jPoly w + w ^ 7 * u
    let y := jPoly (w ^ 2) + w ^ 14 * v
    w ^ 3 * x ^ 3 + y ^ 3 - x ^ 2 * y ^ 2 + 1488 * w ^ 2 * x ^ 2 * y + 1488 * w * x * y ^ 2 -
        162000 * w ^ 4 * x ^ 2 - 162000 * w ^ 2 * y ^ 2 + 40773375 * w ^ 3 * x * y +
        8748000000 * w ^ 5 * x + 8748000000 * w ^ 4 * y - 157464000000000 * w ^ 6 =
      w ^ 7 * Hpoly w u v := by
  intro x y
  simp only [x, y, jPoly, Hpoly, hc00, hc01, hc02, hc03, hc10, hc11, hc12, hc20, hc21, hc22, hc30]
  ring

/-- The point $2z$. -/
abbrev two (τ : ℍ) : ℍ := scaleH 2 (by norm_num) τ

theorem qParam_two (τ : ℍ) : 𝕢 1 ((two τ : ℍ) : ℂ) = 𝕢 1 τ ^ 2 := by
  simp only [Function.Periodic.qParam, scaleH, UpperHalfPlane.coe_mk]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- $F_2(j(z), j(2z)) = q\,H(q, r(z), r(2z))$. -/
theorem F2_j_j2_eq (τ : ℍ) :
    F2 (j τ) (j (two τ)) = 𝕢 1 τ * Hpoly (𝕢 1 τ) (jRem τ) (jRem (two τ)) := by
  have hq := qParam_ne_zero τ
  set w := 𝕢 1 τ with hw
  have hx : j τ = (jPoly w + w ^ 7 * jRem τ) / w := by
    rw [eq_div_iff hq, mul_comm, qParam_mul_j_eq]
  have hy : j (two τ) = (jPoly (w ^ 2) + w ^ 14 * jRem (two τ)) / w ^ 2 := by
    have h2 := qParam_mul_j_eq (two τ)
    rw [qParam_two, ← hw] at h2
    rw [eq_div_iff (pow_ne_zero 2 hq), mul_comm, h2]
    ring
  have key := F2_hom_eq w (jRem τ) (jRem (two τ))
  simp only at key
  rw [hx, hy]
  unfold F2
  have hw6 : w ^ 6 ≠ 0 := pow_ne_zero 6 hq
  apply mul_left_cancel₀ hw6
  rw [show w ^ 6 * (w * Hpoly w (jRem τ) (jRem (two τ))) = w ^ 7 * Hpoly w (jRem τ) (jRem (two τ)) by ring,
    ← key]
  field_simp
  ring

theorem continuous_Hpoly : Continuous fun p : ℂ × ℂ × ℂ ↦ Hpoly p.1 p.2.1 p.2.2 := by
  unfold Hpoly hc00 hc01 hc02 hc03 hc10 hc11 hc12 hc20 hc21 hc22 hc30
  fun_prop

theorem tendsto_two_atImInfty : Tendsto two atImInfty atImInfty := by
  rw [atImInfty, tendsto_comap_iff]
  have : (UpperHalfPlane.im ∘ two) = fun τ ↦ 2 * τ.im := by
    funext τ
    change ((2 : ℕ) * (τ : ℂ)).im = 2 * τ.im
    simp
  rw [this]
  exact tendsto_comap.const_mul_atTop two_pos

/-- **$F_2(j(z), j(2z)) \to 0$ at $i\infty$** (Milne, Example 6.2, pdf p. 90: the $q$-expansion check). -/
theorem tendsto_F2_j_j2 : Tendsto (fun τ : ℍ ↦ F2 (j τ) (j (two τ))) atImInfty (𝓝 0) := by
  simp_rw [F2_j_j2_eq]
  set c := (qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ)).coeff 7
  have hq := qParam_tendsto_atImInfty (h := 1) one_pos
  have hp : Tendsto (fun τ : ℍ ↦ ((𝕢 1 τ, jRem τ, jRem (two τ)) : ℂ × ℂ × ℂ)) atImInfty (𝓝 (0, c, c)) :=
    hq.prodMk_nhds (tendsto_jRem.prodMk_nhds (tendsto_jRem.comp tendsto_two_atImInfty))
  have hH := (continuous_Hpoly.tendsto ((0 : ℂ), c, c)).comp hp
  have := hq.mul hH
  rw [zero_mul] at this
  exact this

end ModularFormsKB.Milne.LevelTwo
