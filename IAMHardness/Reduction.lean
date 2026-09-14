import IAMHardness.CNF
import IAMHardness.IAM

/-!
# Reduction from CNF satisfiability to the policy model

We map a CNF α to a configuration with the following policies.

- A distinguished attached policy allows the target action and the attachment
  of arbitrary policies.
- For every clause `C` of the α there is an attached policy `p(C)` that
  denies the target action.
- For every literal `l` occurring in the α there is an unattached policy
  `p(l)` that allows detaching `p(C)` for every clause `C` containing `l`, and
  that denies attaching `p(l')` whenever `l'` is the complement of `l`.
-/

namespace IAM

/-- Permissions that neither allow nor deny anything. -/
def Permissions.none : Permissions where
  target := false
  attach := fun _ => False
  detach := fun _ => False

/-- Permissions that deny the target action and nothing else. -/
def Permissions.denyTarget : Permissions where
  target := true
  attach := fun _ => False
  detach := fun _ => False

/-! ## Structural identifiers and their string encoding -/

/-- Structural identifiers used by the reduction. -/
inductive ReductionId where
  | root : ReductionId
  | clause : Clause → ReductionId
  | literal : Literal → ReductionId

/-- Unary code of a natural number, terminated by `.`. -/
def encNat (n : Nat) : List Char := List.replicate n '|' ++ ['.']

theorem encNat_ne_nil (n : Nat) : encNat n ≠ [] := by
  cases n <;> simp [encNat, List.replicate]

theorem encNat_append_ne_nil (n : Nat) (x : List Char) : encNat n ++ x ≠ [] := by
  cases n <;> simp [encNat, List.replicate]

theorem encNat_append_inj {n m : Nat} {a b : List Char}
    (h : encNat n ++ a = encNat m ++ b) : n = m ∧ a = b := by
  induction n generalizing m a b with
  | zero =>
      cases m with
      | zero => simp [encNat] at h; exact ⟨rfl, h⟩
      | succ m =>
          simp only [encNat, List.replicate_zero, List.replicate_succ, List.nil_append,
            List.cons_append] at h
          cases h
  | succ n ih =>
      cases m with
      | zero =>
          simp only [encNat, List.replicate_zero, List.replicate_succ, List.nil_append,
            List.cons_append] at h
          cases h
      | succ m =>
          simp only [encNat, List.replicate_succ, List.cons_append, List.cons.injEq] at h
          obtain ⟨_, h⟩ := h
          obtain ⟨hn, hab⟩ := ih h
          exact ⟨by rw [hn], hab⟩

theorem encNat_inj {n m : Nat} (h : encNat n = encNat m) : n = m :=
  (encNat_append_inj (a := []) (b := []) (by simpa using h)).1

/-- Splitting a concatenation whose two heads have equal length. -/
theorem list_append_inj_of_length {α : Type} {as cs x y : List α}
    (hlen : as.length = cs.length) (h : as ++ x = cs ++ y) : as = cs ∧ x = y := by
  induction as generalizing cs with
  | nil =>
      cases cs with
      | nil => simp at h; exact ⟨rfl, h⟩
      | cons c cs => cases hlen
  | cons a as ih =>
      cases cs with
      | nil => cases hlen
      | cons c cs =>
          simp only [List.cons_append, List.cons.injEq] at h
          obtain ⟨rfl, h⟩ := h
          have hlen' : as.length = cs.length := Nat.succ.inj hlen
          obtain ⟨has, hxy⟩ := ih hlen' h
          exact ⟨by rw [has], hxy⟩

/-- The body of a literal code: a sign tag followed by the name. -/
def literalBody : Literal → List Char
  | .pos name => 'p' :: name.toList
  | .neg name => 'n' :: name.toList

theorem literalBody_inj {l l' : Literal} (h : literalBody l = literalBody l') : l = l' := by
  cases l with
  | pos name =>
      cases l' with
      | pos name' =>
          simp only [literalBody, List.cons.injEq] at h
          obtain ⟨_, hmem⟩ := h
          rw [String.toList_inj] at hmem
          rw [hmem]
      | neg name' => simp [literalBody] at h
  | neg name =>
      cases l' with
      | pos name' => simp [literalBody] at h
      | neg name' =>
          simp only [literalBody, List.cons.injEq] at h
          obtain ⟨_, hmem⟩ := h
          rw [String.toList_inj] at hmem
          rw [hmem]

/-- Length-prefixed code of a literal. -/
def encLiteral (literal : Literal) : List Char :=
  encNat (literalBody literal).length ++ literalBody literal

theorem encLiteral_append_ne_nil (l : Literal) (x : List Char) : encLiteral l ++ x ≠ [] := by
  simp only [encLiteral]
  rw [List.append_assoc]
  exact encNat_append_ne_nil _ _

theorem encLiteral_ne_nil (l : Literal) : encLiteral l ≠ [] := by
  simpa using encLiteral_append_ne_nil l []

theorem encLiteral_append_inj {l l' : Literal} {a b : List Char}
    (h : encLiteral l ++ a = encLiteral l' ++ b) : l = l' ∧ a = b := by
  simp only [encLiteral] at h
  rw [List.append_assoc, List.append_assoc] at h
  obtain ⟨hlen, hbody⟩ := encNat_append_inj h
  obtain ⟨hbodyEq, hab⟩ := list_append_inj_of_length hlen hbody
  exact ⟨literalBody_inj hbodyEq, hab⟩

theorem encLiteral_inj (h : encLiteral l = encLiteral l') : l = l' :=
  (encLiteral_append_inj (a := []) (b := []) (by simpa using h)).1

/-- Code of a clause: the concatenation of the literal codes. -/
def encClauseBody (clause : Clause) : List Char := (clause.map encLiteral).flatten

theorem encClauseBody_inj {c c' : Clause} (h : encClauseBody c = encClauseBody c') : c = c' := by
  induction c generalizing c' with
  | nil =>
      cases c' with
      | nil => rfl
      | cons d ds =>
          simp only [encClauseBody, List.map_nil, List.flatten_nil, List.map_cons,
            List.flatten_cons] at h
          exact absurd h.symm (encLiteral_append_ne_nil d (encClauseBody ds))
  | cons d ds ih =>
      cases c' with
      | nil =>
          simp only [encClauseBody, List.map_nil, List.flatten_nil, List.map_cons,
            List.flatten_cons] at h
          exact absurd h (encLiteral_append_ne_nil d (encClauseBody ds))
      | cons e es =>
          simp only [encClauseBody, List.map_cons, List.flatten_cons] at h
          obtain ⟨hde, hds⟩ := encLiteral_append_inj h
          rw [hde, ih hds]

/-- Length-prefixed code of a clause. -/
def encClause (clause : Clause) : List Char :=
  encNat (encClauseBody clause).length ++ encClauseBody clause

theorem encClause_append_inj {c c' : Clause} {a b : List Char}
    (h : encClause c ++ a = encClause c' ++ b) : c = c' ∧ a = b := by
  simp only [encClause] at h
  rw [List.append_assoc, List.append_assoc] at h
  obtain ⟨hlen, hbody⟩ := encNat_append_inj h
  obtain ⟨hbodyEq, hab⟩ := list_append_inj_of_length hlen hbody
  exact ⟨encClauseBody_inj hbodyEq, hab⟩

theorem encClause_inj (h : encClause c = encClause c') : c = c' :=
  (encClause_append_inj (a := []) (b := []) (by simpa using h)).1

/-- Encoding of a structural identifier as a list of characters. -/
def encodeList : ReductionId → List Char
  | .root => encNat 0 ++ []
  | .clause clause => encNat 1 ++ encClause clause
  | .literal literal => encNat 2 ++ encLiteral literal

theorem encodeList_inj {r r' : ReductionId} (h : encodeList r = encodeList r') : r = r' := by
  cases r with
  | root =>
      cases r' with
      | root => rfl
      | clause c =>
          simp only [encodeList] at h
          obtain ⟨hne, _⟩ := encNat_append_inj h
          cases hne
      | literal l =>
          simp only [encodeList] at h
          obtain ⟨hne, _⟩ := encNat_append_inj h
          cases hne
  | clause c =>
      cases r' with
      | root =>
          simp only [encodeList] at h
          obtain ⟨hne, _⟩ := encNat_append_inj h
          cases hne
      | clause c' =>
          simp only [encodeList] at h
          obtain ⟨_, hce⟩ := encNat_append_inj h
          exact congrArg ReductionId.clause (encClause_inj hce)
      | literal l =>
          simp only [encodeList] at h
          obtain ⟨hne, _⟩ := encNat_append_inj h
          cases hne
  | literal l =>
      cases r' with
      | root =>
          simp only [encodeList] at h
          obtain ⟨hne, _⟩ := encNat_append_inj h
          cases hne
      | clause c =>
          simp only [encodeList] at h
          obtain ⟨hne, _⟩ := encNat_append_inj h
          cases hne
      | literal l' =>
          simp only [encodeList] at h
          obtain ⟨_, hle⟩ := encNat_append_inj h
          exact congrArg ReductionId.literal (encLiteral_inj hle)

/-- The encoding of structural identifiers as policy identifiers. -/
def encode (r : ReductionId) : PolicyId := String.ofList (encodeList r)

theorem encode_inj : Function.Injective encode := by
  intro r r' h
  apply encodeList_inj
  have := congrArg String.toList h
  simpa [encode, String.toList_ofList] using this

/-- Identifier of the distinguished policy. -/
def rootId : PolicyId := encode .root

/-- Identifier of the policy associated with a literal. -/
def literalId (literal : Literal) : PolicyId := encode (.literal literal)

/-- Identifier of the policy associated with a clause. -/
def clauseId (clause : Clause) : PolicyId := encode (.clause clause)

@[simp] theorem clauseId_inj {c c' : Clause} : clauseId c = clauseId c' ↔ c = c' := by
  constructor
  · intro h
    have := encode_inj h
    cases this
    rfl
  · intro h; rw [h]

@[simp] theorem literalId_inj {l l' : Literal} : literalId l = literalId l' ↔ l = l' := by
  constructor
  · intro h
    have := encode_inj h
    cases this
    rfl
  · intro h; rw [h]

theorem clauseId_ne_rootId (c : Clause) : clauseId c ≠ rootId := by
  intro h
  have := encode_inj h
  cases this

theorem literalId_ne_rootId (l : Literal) : literalId l ≠ rootId := by
  intro h
  have := encode_inj h
  cases this

theorem clauseId_ne_literalId (c : Clause) (l : Literal) : clauseId c ≠ literalId l := by
  intro h
  have := encode_inj h
  cases this

/-- The distinguished policy: it allows the target action and the attachment of
arbitrary policies. -/
def rootPolicy : Policy where
  id := rootId
  allow :=
    { target := true
      attach := fun _ => True
      detach := fun _ => False }
  deny := Permissions.none

/-- The policy denying the target action that is attached for a clause. -/
def clausePolicy (clause : Clause) : Policy where
  id := clauseId clause
  allow := Permissions.none
  deny := Permissions.denyTarget

/-- The unattached policy for a literal. It allows detaching the clause policy
of every clause of the α that contains the literal, and denies attaching
the policy of the complementary literal. -/
def literalPolicy (α : Formula) (literal : Literal) : Policy where
  id := literalId literal
  allow :=
    { target := false
      attach := fun _ => False
      detach := fun i =>
        ∃ clause ∈ α, literal ∈ clause ∧ i = clauseId clause }
  deny :=
    { target := false
      attach := fun i => i = literalId literal.complement
      detach := fun _ => False }

/-- The configuration associated with a α: the distinguished policy and
the clause policies are attached, while the literal policies only exist. -/
def reduce (α : Formula) : Configuration where
  policy_exists := fun policy =>
    policy = rootPolicy ∨
      (∃ clause ∈ α, policy = clausePolicy clause) ∨
      (∃ literal ∈ α.flatten, policy = literalPolicy α literal)
  attached_to_principal := fun policy =>
    policy = rootPolicy ∨ ∃ clause ∈ α, policy = clausePolicy clause

/-- A policy is one of the three policies built by the reduction. -/
def IsReductionPolicy (α : Formula) (policy : Policy) : Prop :=
  policy = rootPolicy ∨
    (∃ clause ∈ α, policy = clausePolicy clause) ∨
    (∃ literal, policy = literalPolicy α literal)

/-! ## Shape lemmas -/

theorem clausePolicy_inj {clause clause' : Clause} :
    clausePolicy clause = clausePolicy clause' → clause = clause' := by
  intro h
  exact clauseId_inj.mp (by simpa [clausePolicy] using congrArg Policy.id h)

theorem literalPolicy_inj (α : Formula) {literal literal' : Literal} :
    literalPolicy α literal = literalPolicy α literal' → literal = literal' := by
  intro h
  have hid : literalId literal = literalId literal' := by
    simpa [literalPolicy] using congrArg Policy.id h
  exact literalId_inj.mp hid

theorem rootPolicy_ne_clausePolicy (clause : Clause) :
    rootPolicy ≠ clausePolicy clause := by
  intro h
  have hid : clauseId clause = rootId := by
    simpa [rootPolicy, clausePolicy] using (congrArg Policy.id h).symm
  exact clauseId_ne_rootId clause hid

theorem rootPolicy_ne_literalPolicy (α : Formula) (literal : Literal) :
    rootPolicy ≠ literalPolicy α literal := by
  intro h
  have hid : literalId literal = rootId := by
    simpa [rootPolicy, literalPolicy] using (congrArg Policy.id h).symm
  exact literalId_ne_rootId literal hid

theorem clausePolicy_ne_literalPolicy (α : Formula) (clause : Clause) (literal : Literal) :
    clausePolicy clause ≠ literalPolicy α literal := by
  intro h
  have hid : clauseId clause = literalId literal := by
    simpa [clausePolicy, literalPolicy] using congrArg Policy.id h
  exact clauseId_ne_literalId clause literal hid

theorem reduce_policy_exists_shape (α : Formula) {policy : Policy}
    (h : (reduce α).policy_exists policy) : IsReductionPolicy α policy := by
  rcases h with h | h | h
  · exact Or.inl h
  · obtain ⟨clause, hclause, hp⟩ := h
    exact Or.inr (Or.inl ⟨clause, hclause, hp⟩)
  · obtain ⟨literal, _, hp⟩ := h
    exact Or.inr (Or.inr ⟨literal, hp⟩)

theorem shaped_allow_target (α : Formula) {policy : Policy}
    (h : IsReductionPolicy α policy) :
    policy.allow.target = true → policy = rootPolicy := by
  rcases h with rfl | ⟨_, _, rfl⟩ | ⟨_, rfl⟩
  · intro _; rfl
  · simp [clausePolicy, Permissions.none]
  · simp [literalPolicy]

theorem shaped_deny_target (α : Formula) {policy : Policy}
    (h : IsReductionPolicy α policy) :
    policy.deny.target = true → ∃ clause ∈ α, policy = clausePolicy clause := by
  rcases h with rfl | ⟨clause, hclause, rfl⟩ | ⟨_, rfl⟩
  · simp [rootPolicy, Permissions.none]
  · intro _; exact ⟨clause, hclause, rfl⟩
  · simp [literalPolicy]

theorem shaped_deny_attach (α : Formula) {policy : Policy}
    (h : IsReductionPolicy α policy) (hi : policy.deny.attach i) :
    ∃ literal, policy = literalPolicy α literal ∧ i = literalId literal.complement := by
  rcases h with rfl | ⟨_, _, rfl⟩ | ⟨literal, rfl⟩
  · simp [rootPolicy, Permissions.none] at hi
  · simp [clausePolicy, Permissions.denyTarget] at hi
  · exact ⟨literal, rfl, hi⟩

theorem shaped_allow_detach (α : Formula) {policy : Policy}
    (h : IsReductionPolicy α policy) (hi : policy.allow.detach i) :
    ∃ clause ∈ α, ∃ literal,
      policy = literalPolicy α literal ∧ literal ∈ clause ∧ i = clauseId clause := by
  rcases h with rfl | ⟨_, _, rfl⟩ | ⟨literal, rfl⟩
  · simp [rootPolicy] at hi
  · simp [clausePolicy, Permissions.none] at hi
  · rcases hi with ⟨clause, hclause, hmem, hi⟩
    exact ⟨clause, hclause, literal, rfl, hmem, hi⟩

theorem shaped_deny_detach (α : Formula) {policy : Policy}
    (h : IsReductionPolicy α policy) : ¬ policy.deny.detach i := by
  rcases h with rfl | ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;>
    simp [rootPolicy, clausePolicy, literalPolicy, Permissions.none, Permissions.denyTarget]

theorem shaped_not_allow_detach_root (α : Formula) {policy : Policy}
    (h : IsReductionPolicy α policy) : ¬ policy.allow.detach rootId := by
  intro hd
  obtain ⟨clause, _, _, _, _, hid⟩ := shaped_allow_detach α h hd
  exact clauseId_ne_rootId clause hid.symm

theorem shaped_not_allow_detach_literal (α : Formula) {policy : Policy}
    (h : IsReductionPolicy α policy) (literal : Literal) :
    ¬ policy.allow.detach (literalId literal) := by
  intro hd
  obtain ⟨clause, _, _, _, _, hid⟩ := shaped_allow_detach α h hd
  exact clauseId_ne_literalId clause literal hid.symm

theorem Literal.complement_ne (literal : Literal) : literal.complement ≠ literal := by
  cases literal <;> intro h <;> cases h

/-! ## Invariants of configurations reachable from the reduction -/

/-- Invariant maintained by every configuration reachable from `reduce α`. -/
structure Inv (α : Formula) (config : Configuration) : Prop where
  /-- The set of existing policies never changes. -/
  policy_exists_eq : config.policy_exists = (reduce α).policy_exists
  /-- The distinguished policy stays attached. -/
  root_attached : config.attached_to_principal rootPolicy
  /-- Every attached policy is one of the built policies. -/
  shape : ∀ policy, config.attached_to_principal policy → IsReductionPolicy α policy
  /-- Attached literal policies are consistent. -/
  consistent : ∀ literal, config.attached_to_principal (literalPolicy α literal) →
    ¬ config.attached_to_principal (literalPolicy α literal.complement)
  /-- Every detached clause policy is witnessed by an attached literal policy. -/
  covers : ∀ clause ∈ α, ¬ config.attached_to_principal (clausePolicy clause) →
    ∃ literal, config.attached_to_principal (literalPolicy α literal) ∧ literal ∈ clause

theorem Inv.base (α : Formula) : Inv α (reduce α) where
  policy_exists_eq := rfl
  root_attached := Or.inl rfl
  shape := by
    intro policy h
    rcases h with h | ⟨clause, hclause, hp⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨clause, hclause, hp⟩)
  consistent := by
    intro literal h
    rcases h with h | ⟨clause, _, h⟩
    · exact absurd h.symm (rootPolicy_ne_literalPolicy α literal)
    · exact absurd h.symm (clausePolicy_ne_literalPolicy α clause literal)
  covers := by
    intro clause hclause hnot
    exact absurd (Or.inr ⟨clause, hclause, rfl⟩) hnot

theorem not_allowsDetach_root (α : Formula) {config : Configuration}
    (hc : Inv α config) : ¬ config.AllowsDetachPolicy rootId := by
  rintro ⟨⟨policy, hpolicy, hd⟩, _⟩
  exact shaped_not_allow_detach_root α (hc.shape policy hpolicy) hd

theorem not_allowsDetach_literal (α : Formula) {config : Configuration}
    (hc : Inv α config) (literal : Literal) :
    ¬ config.AllowsDetachPolicy (literalId literal) := by
  rintro ⟨⟨policy, hpolicy, hd⟩, _⟩
  exact shaped_not_allow_detach_literal α (hc.shape policy hpolicy) literal hd

theorem Inv.of_transition (α : Formula) {config config' : Configuration}
    (hc : Inv α config) (h : Transition config config') :
    Inv α config' := by
  cases h with
  | attach policy hExists hAllowed =>
      have hp : IsReductionPolicy α policy :=
        reduce_policy_exists_shape α (hc.policy_exists_eq ▸ hExists)
      refine
        { policy_exists_eq := hc.policy_exists_eq
          root_attached := Or.inr hc.root_attached
          shape := ?_
          consistent := ?_
          covers := ?_ }
      · intro q hq
        rcases hq with rfl | hq
        · exact hp
        · exact hc.shape q hq
      · intro literal hl hcomp
        rcases hl with hl | hl <;> rcases hcomp with hcomp | hcomp
        · exact Literal.complement_ne literal
            (literalPolicy_inj α (hl.trans hcomp.symm)).symm
        · have hdeny : (literalPolicy α literal.complement).deny.attach policy.id := by
            rw [← hl]
            simp [literalPolicy, Literal.complement_complement]
          exact hAllowed.2 ⟨literalPolicy α literal.complement, hcomp, hdeny⟩
        · have hdeny : (literalPolicy α literal).deny.attach policy.id := by
            rw [← hcomp]
            simp [literalPolicy]
          exact hAllowed.2 ⟨literalPolicy α literal, hl, hdeny⟩
        · exact hc.consistent literal hl hcomp
      · intro clause hclause hnot
        have hnot' : ¬ config.attached_to_principal (clausePolicy clause) :=
          fun hc' => hnot (Or.inr hc')
        obtain ⟨literal, hl, hmem⟩ := hc.covers clause hclause hnot'
        exact ⟨literal, Or.inr hl, hmem⟩
  | detach policy hExists hAllowed =>
      have hp : IsReductionPolicy α policy :=
        reduce_policy_exists_shape α (hc.policy_exists_eq ▸ hExists)
      have hclause : ∃ clause ∈ α, policy = clausePolicy clause := by
        rcases hp with hp | hp | hp
        · subst policy
          exact absurd hAllowed (not_allowsDetach_root α hc)
        · exact hp
        · obtain ⟨literal, hlit⟩ := hp
          subst policy
          exact absurd hAllowed (not_allowsDetach_literal α hc literal)
      obtain ⟨clause₀, hclause₀, rfl⟩ := hclause
      refine
        { policy_exists_eq := hc.policy_exists_eq
          root_attached := ⟨hc.root_attached, rootPolicy_ne_clausePolicy clause₀⟩
          shape := ?_
          consistent := ?_
          covers := ?_ }
      · intro q hq
        exact hc.shape q hq.1
      · intro literal hl hcomp
        exact hc.consistent literal hl.1 hcomp.1
      · intro clause hclause hnot
        by_cases hEq : clause = clause₀
        · obtain ⟨policy, hpolicy, hd⟩ := hAllowed.1
          obtain ⟨clause', hclause', literal, hlit, hmem, hid⟩ :=
            shaped_allow_detach α (hc.shape policy hpolicy) hd
          have hclause'eq : clause₀ = clause' := clauseId_inj.mp hid
          have hmem₀ : literal ∈ clause := by rw [hEq, hclause'eq]; exact hmem
          refine ⟨literal, ⟨?_, ?_⟩, hmem₀⟩
          · rw [hlit] at hpolicy; exact hpolicy
          · exact (clausePolicy_ne_literalPolicy α clause₀ literal).symm
        · have hne : clausePolicy clause ≠ clausePolicy clause₀ :=
            fun h => hEq (clausePolicy_inj h)
          have hnot' : ¬ config.attached_to_principal (clausePolicy clause) :=
            fun hc' => hnot ⟨hc', hne⟩
          obtain ⟨literal, hl, hmem⟩ := hc.covers clause hclause hnot'
          exact ⟨literal, ⟨hl, (clausePolicy_ne_literalPolicy α clause₀ literal).symm⟩, hmem⟩

theorem Inv.of_reachable (α : Formula) :
    ∀ {config config' : Configuration}, Reachable config config' →
      Inv α config → Inv α config' := by
  intro config config' h
  induction h with
  | refl => exact id
  | step hreach htrans ih => exact fun hc => Inv.of_transition α (ih hc) htrans

theorem Inv.allowsTarget_iff (α : Formula) {config : Configuration}
    (hc : Inv α config) :
    config.AllowsTarget ↔ ∀ clause ∈ α, ¬ config.attached_to_principal (clausePolicy clause) := by
  constructor
  · intro htarget clause hclause hattached
    exact htarget.2 ⟨clausePolicy clause, hattached, rfl⟩
  · intro hno
    refine ⟨⟨rootPolicy, hc.root_attached, rfl⟩, ?_⟩
    rintro ⟨policy, hpolicy, hdeny⟩
    obtain ⟨clause, hclause, hp⟩ := shaped_deny_target α (hc.shape policy hpolicy) hdeny
    exact hno clause hclause (hp ▸ hpolicy)

/-! ## Reachability lemmas -/

theorem Reachable.trans {a b c : Configuration} (hab : Reachable a b) (hbc : Reachable b c) :
    Reachable a c := by
  induction hbc with
  | refl => exact hab
  | step _ htrans ih => exact Reachable.step ih htrans

/-- Attach the literal policies of a list of literals, in order. -/
def attachLiterals (α : Formula) (config : Configuration) : List Literal → Configuration
  | [] => config
  | literal :: literals => attachLiterals α (config.attach (literalPolicy α literal)) literals

/-- Detach the clause policies of a list of clauses, in order. -/
def detachClauses (α : Formula) (config : Configuration) : List Clause → Configuration
  | [] => config
  | clause :: clauses => detachClauses α (config.detach (clausePolicy clause)) clauses

theorem attachLiterals_mono (α : Formula) :
    ∀ (literals : List Literal) (config : Configuration) (policy : Policy),
      config.attached_to_principal policy →
        (attachLiterals α config literals).attached_to_principal policy := by
  intro literals
  induction literals with
  | nil => intro config policy h; exact h
  | cons literal literals ih =>
      intro config policy h
      exact ih (config.attach (literalPolicy α literal)) policy (Or.inr h)

theorem attachLiterals_attached_of_mem (α : Formula) :
    ∀ (literals : List Literal) (config : Configuration) (literal : Literal),
      literal ∈ literals →
        (attachLiterals α config literals).attached_to_principal
          (literalPolicy α literal) := by
  intro literals
  induction literals with
  | nil => intro config literal h; exact absurd h (by simp)
  | cons head literals ih =>
      intro config literal h
      rcases List.mem_cons.mp h with heq | h
      · rw [heq]
        exact attachLiterals_mono α literals (config.attach (literalPolicy α head))
          (literalPolicy α head) (Or.inl rfl)
      · exact ih (config.attach (literalPolicy α head)) literal h

theorem detachClauses_sub (α : Formula) :
    ∀ (clauses : List Clause) (config : Configuration) (policy : Policy),
      (detachClauses α config clauses).attached_to_principal policy →
        config.attached_to_principal policy := by
  intro clauses
  induction clauses with
  | nil => intro config policy h; exact h
  | cons clause clauses ih =>
      intro config policy h
      exact (ih (config.detach (clausePolicy clause)) policy h).1

theorem detachClauses_not_attached_of_mem (α : Formula) :
    ∀ (clauses : List Clause) (config : Configuration) (clause : Clause),
      clause ∈ clauses →
        ¬(detachClauses α config clauses).attached_to_principal (clausePolicy clause) := by
  intro clauses
  induction clauses with
  | nil => intro config clause h; exact absurd h (by simp)
  | cons head clauses ih =>
      intro config clause h
      rcases List.mem_cons.mp h with heq | h
      · rw [heq]
        intro hattached
        exact (detachClauses_sub α clauses (config.detach (clausePolicy head))
          (clausePolicy head) hattached).2 rfl
      · exact ih (config.detach (clausePolicy head)) clause h

theorem attachLiterals_spec (α : Formula) (selector : LiteralSet) :
    ∀ (literals : List Literal) (config : Configuration),
      Inv α config →
      (∀ literal, config.attached_to_principal (literalPolicy α literal) → selector literal) →
      LiteralSet.Consistent selector →
      (∀ literal ∈ literals, selector literal) →
      (∀ literal ∈ literals, (reduce α).policy_exists (literalPolicy α literal)) →
      Inv α (attachLiterals α config literals) ∧
        (∀ literal, (attachLiterals α config literals).attached_to_principal
          (literalPolicy α literal) → selector literal) ∧
        Reachable config (attachLiterals α config literals) := by
  intro literals
  induction literals with
  | nil => intro config hc hS hcons hL hex; exact ⟨hc, hS, Reachable.refl⟩
  | cons literal literals ih =>
      intro config hc hS hcons hL hex
      have hliteral : selector literal := hL literal (List.mem_cons_self ..)
      have hL' : ∀ l' ∈ literals, selector l' :=
        fun l' hl' => hL l' (List.mem_cons_of_mem literal hl')
      have hex' : ∀ l' ∈ literals, (reduce α).policy_exists (literalPolicy α l') :=
        fun l' hl' => hex l' (List.mem_cons_of_mem literal hl')
      have hexc : config.policy_exists (literalPolicy α literal) := by
        rw [hc.policy_exists_eq]
        exact hex literal (List.mem_cons_self ..)
      have hallowed : config.AllowsAttachPolicy (literalId literal) := by
        refine ⟨⟨rootPolicy, hc.root_attached, trivial⟩, ?_⟩
        rintro ⟨policy, hpolicy, hdeny⟩
        obtain ⟨other, hother, hid⟩ := shaped_deny_attach α (hc.shape policy hpolicy) hdeny
        rw [hother] at hpolicy
        have hSother : selector other := hS other hpolicy
        have hcomp : literal = other.complement := literalId_inj.mp hid
        exact hcons other hSother (hcomp ▸ hliteral)
      have htrans : Transition config (config.attach (literalPolicy α literal)) :=
        Transition.attach config (literalPolicy α literal) hexc hallowed
      have hc' : Inv α (config.attach (literalPolicy α literal)) :=
        Inv.of_transition α hc htrans
      have hS' : ∀ l', (config.attach (literalPolicy α literal)).attached_to_principal
          (literalPolicy α l') → selector l' := by
        intro l' h'
        rcases h' with h' | h'
        · rw [literalPolicy_inj α h']; exact hliteral
        · exact hS l' h'
      obtain ⟨hinv, hSfin, hreach⟩ :=
        ih (config.attach (literalPolicy α literal)) hc' hS' hcons hL' hex'
      exact ⟨hinv, hSfin,
        Reachable.trans (Reachable.step Reachable.refl htrans) hreach⟩

theorem detachClauses_spec (α : Formula) :
    ∀ (clauses : List Clause) (config : Configuration),
      Inv α config →
      (∀ clause ∈ clauses, clause ∈ α) →
      (∀ clause ∈ clauses,
        ∃ literal, config.attached_to_principal (literalPolicy α literal) ∧ literal ∈ clause) →
      Inv α (detachClauses α config clauses) ∧
        Reachable config (detachClauses α config clauses) := by
  intro clauses
  induction clauses with
  | nil => intro config hc hsub hwit; exact ⟨hc, Reachable.refl⟩
  | cons clause clauses ih =>
      intro config hc hsub hwit
      have hclause : clause ∈ α := hsub clause (List.mem_cons_self ..)
      obtain ⟨literal, hliteral, hmem⟩ := hwit clause (List.mem_cons_self ..)
      have hexc : config.policy_exists (clausePolicy clause) := by
        rw [hc.policy_exists_eq]
        exact Or.inr (Or.inl ⟨clause, hclause, rfl⟩)
      have hallowed : config.AllowsDetachPolicy (clauseId clause) := by
        refine ⟨⟨literalPolicy α literal, hliteral, ⟨clause, hclause, hmem, rfl⟩⟩, ?_⟩
        rintro ⟨policy, hpolicy, hd⟩
        exact shaped_deny_detach α (hc.shape policy hpolicy) hd
      have htrans : Transition config (config.detach (clausePolicy clause)) :=
        Transition.detach config (clausePolicy clause) hexc hallowed
      have hc' : Inv α (config.detach (clausePolicy clause)) :=
        Inv.of_transition α hc htrans
      have hsub' : ∀ clause' ∈ clauses, clause' ∈ α :=
        fun clause' hclause' => hsub clause' (List.mem_cons_of_mem clause hclause')
      have hwit' : ∀ clause' ∈ clauses,
          ∃ literal, (config.detach (clausePolicy clause)).attached_to_principal
            (literalPolicy α literal) ∧ literal ∈ clause' := by
        intro clause' hclause'
        obtain ⟨literal, hliteral, hmem⟩ := hwit clause' (List.mem_cons_of_mem clause hclause')
        exact ⟨literal, ⟨hliteral, (clausePolicy_ne_literalPolicy α clause literal).symm⟩, hmem⟩
      obtain ⟨hinv, hreach⟩ := ih (config.detach (clausePolicy clause)) hc' hsub' hwit'
      exact ⟨hinv, Reachable.trans (Reachable.step Reachable.refl htrans) hreach⟩

/-! ## Main theorem -/

/-- A formula has a consistent literal selector if and only if its reduction is
in `PE`. -/
theorem reduce_PE_iff_selector (α : Formula) :
    AdmitsPrivilegeEscalation (reduce α) ↔
      ∃ selector : LiteralSet,
        LiteralSet.IsSelector selector α ∧ LiteralSet.Consistent selector := by
  constructor
  · rintro ⟨config, hreach, htarget⟩
    have hinv : Inv α config := Inv.of_reachable α hreach (Inv.base α)
    refine ⟨fun literal => config.attached_to_principal (literalPolicy α literal), ?_, ?_⟩
    · intro clause hclause
      have hno := (Inv.allowsTarget_iff α hinv).mp htarget clause hclause
      obtain ⟨literal, hliteral, hmem⟩ := hinv.covers clause hclause hno
      exact ⟨literal, hmem, hliteral⟩
    · intro literal
      exact hinv.consistent literal
  · rintro ⟨selector, hselector, hconsistent⟩
    classical
    let literals : List Literal := α.flatten.filter (fun literal => decide (selector literal))
    have hL : ∀ literal ∈ literals, selector literal := by
      intro literal hliteral
      rw [List.mem_filter] at hliteral
      exact decide_eq_true_eq.mp hliteral.2
    have hexL : ∀ literal ∈ literals, (reduce α).policy_exists (literalPolicy α literal) := by
      intro literal hliteral
      rw [List.mem_filter] at hliteral
      obtain ⟨clause, hclause, hmem⟩ := List.mem_flatten.mp hliteral.1
      exact Or.inr (Or.inr ⟨literal, List.mem_flatten.mpr ⟨clause, hclause, hmem⟩, rfl⟩)
    have hS₀ : ∀ literal,
        (reduce α).attached_to_principal (literalPolicy α literal) → selector literal := by
      intro literal hliteral
      rcases hliteral with h | ⟨clause, _, h⟩
      · exact absurd h.symm (rootPolicy_ne_literalPolicy α literal)
      · exact absurd h.symm (clausePolicy_ne_literalPolicy α clause literal)
    obtain ⟨hc₁, _, hreach₁⟩ :=
      attachLiterals_spec α selector literals (reduce α) (Inv.base α)
        hS₀ hconsistent hL hexL
    have hwit : ∀ clause ∈ α,
        ∃ literal, (attachLiterals α (reduce α) literals).attached_to_principal
          (literalPolicy α literal) ∧ literal ∈ clause := by
      intro clause hclause
      obtain ⟨literal, hmem, hsel⟩ := hselector clause hclause
      have hflat : literal ∈ α.flatten := List.mem_flatten.mpr ⟨clause, hclause, hmem⟩
      have hin : literal ∈ literals := by
        rw [List.mem_filter]
        exact ⟨hflat, by rw [decide_eq_true_eq]; exact hsel⟩
      exact ⟨literal, attachLiterals_attached_of_mem α literals (reduce α) literal hin, hmem⟩
    obtain ⟨hc₂, hreach₂⟩ :=
      detachClauses_spec α α (attachLiterals α (reduce α) literals) hc₁
        (fun _ h => h) hwit
    refine ⟨detachClauses α (attachLiterals α (reduce α) literals) α,
      Reachable.trans hreach₁ hreach₂, ?_⟩
    exact (Inv.allowsTarget_iff α hc₂).mpr
      (detachClauses_not_attached_of_mem α α
        (attachLiterals α (reduce α) literals))

/-- A α is satisfiable if and only if its reduction is in `PE`. -/
theorem admits_PE_iff_satisfiable (α : Formula) :
    AdmitsPrivilegeEscalation (reduce α) ↔ Formula.Satisfiable α :=
  (reduce_PE_iff_selector α).trans
    (Formula.satisfiable_iff_exists_consistent_selector α).symm

end IAM
