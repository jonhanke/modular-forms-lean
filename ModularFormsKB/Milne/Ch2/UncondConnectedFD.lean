import ModularFormsKB.Milne.Ch2.DiscreteGroups

/-!
# Milne, Proposition 2.17: what is proved

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Proposition 2.17, pdf p. 35
(proof omitted in the book).

Proposition 2.17 says that the representatives in Proposition 2.16 can be chosen so that the closure of
$D' = \bigcup_i \gamma_iD$ is connected, and that the interior of that closure is then a connected fundamental
domain for $\Gamma'$. We prove the second half for **every** choice of representatives
(`isFundamentalDomain_interior_closure`): the interior of the closure of $D'$ is open, no two of its points are
$\Gamma'$-equivalent, and its closure contains the closure of $D'$; so it is a fundamental domain as soon as it is
connected. The named statement `ConnectedFundamentalDomainStatement` is therefore equivalent to the existence of
representatives for which both the closure of $D'$ and the interior of that closure are connected
(`connectedFundamentalDomainStatement_iff`).

Whether such representatives exist for an arbitrary fundamental domain $D$ is not settled here: the definition of a
fundamental domain (p. 32) allows wild domains (for a translation group, a "lakes of Wada" domain whose translates
share one common boundary makes the interior of the closure of every $D'$ with $m \ge 2$ disconnected), so the
statement is doubtful in the generality in which it is quantified.
-/

open UpperHalfPlane Pointwise Topology

open scoped MatrixGroups

namespace ModularFormsKB.Milne

/-- **The interior of the closure of `D'` is a fundamental set** for `Γ'`, for every choice of representatives in
Proposition 2.16. -/
theorem isFundamentalSet_interior_closure {Γ Γ' : Subgroup SL(2, ℝ)} [DiscreteTopology Γ] (hΓ' : Γ' ≤ Γ)
    {D : Set ℍ} (hD : IsFundamentalDomain Γ D) {m : ℕ} (γs : Fin m → SL(2, ℝ)) (hγs : ∀ i, γs i ∈ Γ)
    (hcos : ∀ γ ∈ Γ, ∃! i : Fin m, ∃ γ' ∈ Γ', γ = γ' * γs i ∨ γ = -(γ' * γs i)) :
    IsFundamentalSet Γ' (interior (closure (⋃ i, γs i • D))) := by
  obtain ⟨hopen, hinj, hcov⟩ := isFundamentalSet_iUnion hΓ' hD γs hγs hcos
  set D' := ⋃ i, γs i • D
  have hsub : D' ⊆ interior (closure D') := interior_maximal subset_closure hopen
  refine ⟨isOpen_interior, ?_, fun z ↦ ?_⟩
  · intro z hz w hw γ hγ hzw
    -- `γ` fixes points arbitrarily close to `z`, hence fixes `z`
    have hcl : IsClosed {u : ℍ | γ • u = u} :=
      isClosed_eq (continuous_const_smul γ) continuous_id
    have hfix : z ∈ closure {u : ℍ | γ • u = u} := by
      rw [mem_closure_iff]
      intro O hO hzO
      set O' := O ∩ interior (closure D') ∩ (fun x ↦ γ • x) ⁻¹' interior (closure D')
      have hO' : IsOpen O' := (hO.inter isOpen_interior).inter
        (isOpen_interior.preimage (continuous_const_smul γ))
      have hzO' : z ∈ O' := ⟨⟨hzO, hz⟩, by simpa [hzw] using hw⟩
      obtain ⟨u, ⟨huO', huD'⟩⟩ := (mem_closure_iff.mp (interior_subset hzO'.1.2)) O' hO' hzO'
      have hP : IsOpen (γ • (O' ∩ D')) := (hO'.inter hopen).smul γ
      have hγu : γ • u ∈ γ • (O' ∩ D') := Set.smul_mem_smul_set ⟨huO', huD'⟩
      have hγuU : γ • u ∈ interior (closure D') := huO'.2
      obtain ⟨v, hvP, hvD'⟩ := (mem_closure_iff.mp (interior_subset hγuU)) _ hP hγu
      obtain ⟨x, ⟨hxO', hxD'⟩, rfl⟩ := Set.mem_smul_set.mp hvP
      exact ⟨x, hxO'.1.1, (hinj x hxD' (γ • x) hvD' γ hγ rfl).symm⟩
    have hz' : γ • z = z := hcl.closure_subset hfix
    rw [← hzw, hz']
  · obtain ⟨γ, hγ, h⟩ := hcov z
    exact ⟨γ, hγ, closure_mono hsub h⟩

/-- **Milne, Proposition 2.17, second half**, for every choice of representatives: if the interior of the closure
of `D' = ⋃ γᵢ D` is connected, it is a fundamental domain for `Γ'`. -/
@[kb "milne2017mf" "Proposition 2.17, pdf p. 35"]
theorem isFundamentalDomain_interior_closure {Γ Γ' : Subgroup SL(2, ℝ)} [DiscreteTopology Γ] (hΓ' : Γ' ≤ Γ)
    {D : Set ℍ} (hD : IsFundamentalDomain Γ D) {m : ℕ} (γs : Fin m → SL(2, ℝ)) (hγs : ∀ i, γs i ∈ Γ)
    (hcos : ∀ γ ∈ Γ, ∃! i : Fin m, ∃ γ' ∈ Γ', γ = γ' * γs i ∨ γ = -(γ' * γs i))
    (hconn : IsConnected (interior (closure (⋃ i, γs i • D)))) :
    IsFundamentalDomain Γ' (interior (closure (⋃ i, γs i • D))) :=
  ⟨hconn, isFundamentalSet_interior_closure hΓ' hD γs hγs hcos⟩

/-- `ConnectedFundamentalDomainStatement` is equivalent to the existence, for every datum of Proposition 2.16, of
representatives for which both the closure of `D'` and its interior are connected. -/
theorem connectedFundamentalDomainStatement_iff :
    ConnectedFundamentalDomainStatement ↔
      ∀ {Γ Γ' : Subgroup SL(2, ℝ)} [DiscreteTopology Γ], Γ' ≤ Γ → ∀ {D : Set ℍ}, IsFundamentalDomain Γ D →
        ∀ {m : ℕ}, (∃ γs : Fin m → SL(2, ℝ), (∀ i, γs i ∈ Γ) ∧
          ∀ γ ∈ Γ, ∃! i : Fin m, ∃ γ' ∈ Γ', γ = γ' * γs i ∨ γ = -(γ' * γs i)) →
        ∃ γs : Fin m → SL(2, ℝ), (∀ i, γs i ∈ Γ) ∧
          (∀ γ ∈ Γ, ∃! i : Fin m, ∃ γ' ∈ Γ', γ = γ' * γs i ∨ γ = -(γ' * γs i)) ∧
          IsConnected (closure (⋃ i, γs i • D)) ∧ IsConnected (interior (closure (⋃ i, γs i • D))) := by
  constructor
  · intro h Γ Γ' _ hΓ' D hD m hex
    obtain ⟨γs, hγs, hcos, hc, hfd⟩ := h.out hΓ' hD hex
    exact ⟨γs, hγs, hcos, hc, hfd.1⟩
  · intro h
    refine ⟨?_⟩
    intro Γ Γ' _ hΓ' D hD m hex
    obtain ⟨γs, hγs, hcos, hc, hi⟩ := h hΓ' hD hex
    exact ⟨γs, hγs, hcos, hc, isFundamentalDomain_interior_closure hΓ' hD γs hγs hcos hi⟩

end ModularFormsKB.Milne
