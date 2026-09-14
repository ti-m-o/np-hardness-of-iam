import IAMHardness.CNF
import IAMHardness.IAM

/-!
# Reduction from CNF satisfiability to the policy model

We map a CNF formula to a configuration with the following policies.

- A distinguished attached policy allows the target action and the attachment
  of arbitrary policies.
- For every clause `C` of the formula there is an attached policy `p(C)` that
  denies the target action.
- For every literal `l` occurring in the formula there is an unattached policy
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

/-- Identifier of the distinguished policy. -/
def rootId : PolicyId := .root

/-- Identifier of the policy associated with a literal. -/
def literalId (literal : Literal) : PolicyId := .literal literal

/-- Identifier of the policy associated with a clause. -/
def clauseId (clause : Clause) : PolicyId := .clause clause

@[simp] theorem clauseId_inj {c c' : Clause} : clauseId c = clauseId c' ↔ c = c' := by
  simp [clauseId]

@[simp] theorem literalId_inj {l l' : Literal} : literalId l = literalId l' ↔ l = l' := by
  simp [literalId]

theorem clauseId_ne_rootId (c : Clause) : clauseId c ≠ rootId := by
  intro h; cases h

theorem literalId_ne_rootId (l : Literal) : literalId l ≠ rootId := by
  intro h; cases h

theorem clauseId_ne_literalId (c : Clause) (l : Literal) : clauseId c ≠ literalId l := by
  intro h; cases h

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
of every clause of the formula that contains the literal, and denies attaching
the policy of the complementary literal. -/
def literalPolicy (formula : Formula) (literal : Literal) : Policy where
  id := literalId literal
  allow :=
    { target := false
      attach := fun _ => False
      detach := fun i =>
        ∃ clause ∈ formula, literal ∈ clause ∧ i = clauseId clause }
  deny :=
    { target := false
      attach := fun i => i = literalId literal.complement
      detach := fun _ => False }

/-- The configuration associated with a formula: the distinguished policy and
the clause policies are attached, while the literal policies only exist. -/
def reduce (formula : Formula) : Configuration where
  policy_exists := fun policy =>
    policy = rootPolicy ∨
      (∃ clause ∈ formula, policy = clausePolicy clause) ∨
      (∃ literal ∈ formula.flatten, policy = literalPolicy formula literal)
  attached_to_principal := fun policy =>
    policy = rootPolicy ∨ ∃ clause ∈ formula, policy = clausePolicy clause

/-- A policy is one of the three policies built by the reduction. -/
def IsReductionPolicy (formula : Formula) (policy : Policy) : Prop :=
  policy = rootPolicy ∨
    (∃ clause ∈ formula, policy = clausePolicy clause) ∨
    (∃ literal, policy = literalPolicy formula literal)

/-! ## Shape lemmas -/

theorem clausePolicy_inj {clause clause' : Clause} :
    clausePolicy clause = clausePolicy clause' → clause = clause' := by
  intro h
  exact clauseId_inj.mp (by simpa [clausePolicy] using congrArg Policy.id h)

theorem literalPolicy_inj (formula : Formula) {literal literal' : Literal} :
    literalPolicy formula literal = literalPolicy formula literal' → literal = literal' := by
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

theorem rootPolicy_ne_literalPolicy (formula : Formula) (literal : Literal) :
    rootPolicy ≠ literalPolicy formula literal := by
  intro h
  have hid : literalId literal = rootId := by
    simpa [rootPolicy, literalPolicy] using (congrArg Policy.id h).symm
  exact literalId_ne_rootId literal hid

theorem clausePolicy_ne_literalPolicy (formula : Formula) (clause : Clause) (literal : Literal) :
    clausePolicy clause ≠ literalPolicy formula literal := by
  intro h
  have hid : clauseId clause = literalId literal := by
    simpa [clausePolicy, literalPolicy] using congrArg Policy.id h
  exact clauseId_ne_literalId clause literal hid

theorem reduce_policy_exists_shape (formula : Formula) {policy : Policy}
    (h : (reduce formula).policy_exists policy) : IsReductionPolicy formula policy := by
  rcases h with h | h | h
  · exact Or.inl h
  · obtain ⟨clause, hclause, hp⟩ := h
    exact Or.inr (Or.inl ⟨clause, hclause, hp⟩)
  · obtain ⟨literal, _, hp⟩ := h
    exact Or.inr (Or.inr ⟨literal, hp⟩)

theorem shaped_allow_target (formula : Formula) {policy : Policy}
    (h : IsReductionPolicy formula policy) :
    policy.allow.target = true → policy = rootPolicy := by
  rcases h with rfl | ⟨_, _, rfl⟩ | ⟨_, rfl⟩
  · intro _; rfl
  · simp [clausePolicy, Permissions.none]
  · simp [literalPolicy]

theorem shaped_deny_target (formula : Formula) {policy : Policy}
    (h : IsReductionPolicy formula policy) :
    policy.deny.target = true → ∃ clause ∈ formula, policy = clausePolicy clause := by
  rcases h with rfl | ⟨clause, hclause, rfl⟩ | ⟨_, rfl⟩
  · simp [rootPolicy, Permissions.none]
  · intro _; exact ⟨clause, hclause, rfl⟩
  · simp [literalPolicy]

theorem shaped_deny_attach (formula : Formula) {policy : Policy}
    (h : IsReductionPolicy formula policy) (hi : policy.deny.attach i) :
    ∃ literal, policy = literalPolicy formula literal ∧ i = literalId literal.complement := by
  rcases h with rfl | ⟨_, _, rfl⟩ | ⟨literal, rfl⟩
  · simp [rootPolicy, Permissions.none] at hi
  · simp [clausePolicy, Permissions.denyTarget] at hi
  · exact ⟨literal, rfl, hi⟩

theorem shaped_allow_detach (formula : Formula) {policy : Policy}
    (h : IsReductionPolicy formula policy) (hi : policy.allow.detach i) :
    ∃ clause ∈ formula, ∃ literal,
      policy = literalPolicy formula literal ∧ literal ∈ clause ∧ i = clauseId clause := by
  rcases h with rfl | ⟨_, _, rfl⟩ | ⟨literal, rfl⟩
  · simp [rootPolicy] at hi
  · simp [clausePolicy, Permissions.none] at hi
  · rcases hi with ⟨clause, hclause, hmem, hi⟩
    exact ⟨clause, hclause, literal, rfl, hmem, hi⟩

theorem shaped_deny_detach (formula : Formula) {policy : Policy}
    (h : IsReductionPolicy formula policy) : ¬ policy.deny.detach i := by
  rcases h with rfl | ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;>
    simp [rootPolicy, clausePolicy, literalPolicy, Permissions.none, Permissions.denyTarget]

theorem shaped_not_allow_detach_root (formula : Formula) {policy : Policy}
    (h : IsReductionPolicy formula policy) : ¬ policy.allow.detach rootId := by
  intro hd
  obtain ⟨clause, _, _, _, _, hid⟩ := shaped_allow_detach formula h hd
  exact clauseId_ne_rootId clause hid.symm

theorem shaped_not_allow_detach_literal (formula : Formula) {policy : Policy}
    (h : IsReductionPolicy formula policy) (literal : Literal) :
    ¬ policy.allow.detach (literalId literal) := by
  intro hd
  obtain ⟨clause, _, _, _, _, hid⟩ := shaped_allow_detach formula h hd
  exact clauseId_ne_literalId clause literal hid.symm

theorem Literal.complement_ne (literal : Literal) : literal.complement ≠ literal := by
  cases literal <;> intro h <;> cases h

/-! ## Invariants of configurations reachable from the reduction -/

/-- Invariant maintained by every configuration reachable from `reduce formula`. -/
structure Inv (formula : Formula) (config : Configuration) : Prop where
  /-- The set of existing policies never changes. -/
  policy_exists_eq : config.policy_exists = (reduce formula).policy_exists
  /-- The distinguished policy stays attached. -/
  root_attached : config.attached_to_principal rootPolicy
  /-- Every attached policy is one of the built policies. -/
  shape : ∀ policy, config.attached_to_principal policy → IsReductionPolicy formula policy
  /-- Attached literal policies are consistent. -/
  consistent : ∀ literal, config.attached_to_principal (literalPolicy formula literal) →
    ¬ config.attached_to_principal (literalPolicy formula literal.complement)
  /-- Every detached clause policy is witnessed by an attached literal policy. -/
  covers : ∀ clause ∈ formula, ¬ config.attached_to_principal (clausePolicy clause) →
    ∃ literal, config.attached_to_principal (literalPolicy formula literal) ∧ literal ∈ clause

theorem Inv.base (formula : Formula) : Inv formula (reduce formula) where
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
    · exact absurd h.symm (rootPolicy_ne_literalPolicy formula literal)
    · exact absurd h.symm (clausePolicy_ne_literalPolicy formula clause literal)
  covers := by
    intro clause hclause hnot
    exact absurd (Or.inr ⟨clause, hclause, rfl⟩) hnot

theorem not_allowsDetach_root (formula : Formula) {config : Configuration}
    (hc : Inv formula config) : ¬ config.AllowsDetachPolicy rootId := by
  rintro ⟨⟨policy, hpolicy, hd⟩, _⟩
  exact shaped_not_allow_detach_root formula (hc.shape policy hpolicy) hd

theorem not_allowsDetach_literal (formula : Formula) {config : Configuration}
    (hc : Inv formula config) (literal : Literal) :
    ¬ config.AllowsDetachPolicy (literalId literal) := by
  rintro ⟨⟨policy, hpolicy, hd⟩, _⟩
  exact shaped_not_allow_detach_literal formula (hc.shape policy hpolicy) literal hd

theorem Inv.of_transition (formula : Formula) {config config' : Configuration}
    (hc : Inv formula config) (h : Transition config config') :
    Inv formula config' := by
  cases h with
  | attach policy hExists hAllowed =>
      have hp : IsReductionPolicy formula policy :=
        reduce_policy_exists_shape formula (hc.policy_exists_eq ▸ hExists)
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
            (literalPolicy_inj formula (hl.trans hcomp.symm)).symm
        · have hdeny : (literalPolicy formula literal.complement).deny.attach policy.id := by
            rw [← hl]
            simp [literalPolicy, Literal.complement_complement]
          exact hAllowed.2 ⟨literalPolicy formula literal.complement, hcomp, hdeny⟩
        · have hdeny : (literalPolicy formula literal).deny.attach policy.id := by
            rw [← hcomp]
            simp [literalPolicy]
          exact hAllowed.2 ⟨literalPolicy formula literal, hl, hdeny⟩
        · exact hc.consistent literal hl hcomp
      · intro clause hclause hnot
        have hnot' : ¬ config.attached_to_principal (clausePolicy clause) :=
          fun hc' => hnot (Or.inr hc')
        obtain ⟨literal, hl, hmem⟩ := hc.covers clause hclause hnot'
        exact ⟨literal, Or.inr hl, hmem⟩
  | detach policy hExists hAllowed =>
      have hp : IsReductionPolicy formula policy :=
        reduce_policy_exists_shape formula (hc.policy_exists_eq ▸ hExists)
      have hclause : ∃ clause ∈ formula, policy = clausePolicy clause := by
        rcases hp with hp | hp | hp
        · subst policy
          exact absurd hAllowed (not_allowsDetach_root formula hc)
        · exact hp
        · obtain ⟨literal, hlit⟩ := hp
          subst policy
          exact absurd hAllowed (not_allowsDetach_literal formula hc literal)
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
            shaped_allow_detach formula (hc.shape policy hpolicy) hd
          have hclause'eq : clause₀ = clause' := clauseId_inj.mp hid
          have hmem₀ : literal ∈ clause := by rw [hEq, hclause'eq]; exact hmem
          refine ⟨literal, ⟨?_, ?_⟩, hmem₀⟩
          · rw [hlit] at hpolicy; exact hpolicy
          · exact (clausePolicy_ne_literalPolicy formula clause₀ literal).symm
        · have hne : clausePolicy clause ≠ clausePolicy clause₀ :=
            fun h => hEq (clausePolicy_inj h)
          have hnot' : ¬ config.attached_to_principal (clausePolicy clause) :=
            fun hc' => hnot ⟨hc', hne⟩
          obtain ⟨literal, hl, hmem⟩ := hc.covers clause hclause hnot'
          exact ⟨literal, ⟨hl, (clausePolicy_ne_literalPolicy formula clause₀ literal).symm⟩, hmem⟩

theorem Inv.of_reachable (formula : Formula) :
    ∀ {config config' : Configuration}, Reachable config config' →
      Inv formula config → Inv formula config' := by
  intro config config' h
  induction h with
  | refl => exact id
  | step hreach htrans ih => exact fun hc => Inv.of_transition formula (ih hc) htrans

theorem Inv.allowsTarget_iff (formula : Formula) {config : Configuration}
    (hc : Inv formula config) :
    config.AllowsTarget ↔ ∀ clause ∈ formula, ¬ config.attached_to_principal (clausePolicy clause) := by
  constructor
  · intro htarget clause hclause hattached
    exact htarget.2 ⟨clausePolicy clause, hattached, rfl⟩
  · intro hno
    refine ⟨⟨rootPolicy, hc.root_attached, rfl⟩, ?_⟩
    rintro ⟨policy, hpolicy, hdeny⟩
    obtain ⟨clause, hclause, hp⟩ := shaped_deny_target formula (hc.shape policy hpolicy) hdeny
    exact hno clause hclause (hp ▸ hpolicy)

/-! ## Reachability lemmas -/

theorem Reachable.trans {a b c : Configuration} (hab : Reachable a b) (hbc : Reachable b c) :
    Reachable a c := by
  induction hbc with
  | refl => exact hab
  | step _ htrans ih => exact Reachable.step ih htrans

/-- Attach the literal policies of a list of literals, in order. -/
def attachLiterals (formula : Formula) (config : Configuration) : List Literal → Configuration
  | [] => config
  | literal :: literals => attachLiterals formula (config.attach (literalPolicy formula literal)) literals

/-- Detach the clause policies of a list of clauses, in order. -/
def detachClauses (formula : Formula) (config : Configuration) : List Clause → Configuration
  | [] => config
  | clause :: clauses => detachClauses formula (config.detach (clausePolicy clause)) clauses

theorem attachLiterals_mono (formula : Formula) :
    ∀ (literals : List Literal) (config : Configuration) (policy : Policy),
      config.attached_to_principal policy →
        (attachLiterals formula config literals).attached_to_principal policy := by
  intro literals
  induction literals with
  | nil => intro config policy h; exact h
  | cons literal literals ih =>
      intro config policy h
      exact ih (config.attach (literalPolicy formula literal)) policy (Or.inr h)

theorem attachLiterals_attached_of_mem (formula : Formula) :
    ∀ (literals : List Literal) (config : Configuration) (literal : Literal),
      literal ∈ literals →
        (attachLiterals formula config literals).attached_to_principal
          (literalPolicy formula literal) := by
  intro literals
  induction literals with
  | nil => intro config literal h; exact absurd h (by simp)
  | cons head literals ih =>
      intro config literal h
      rcases List.mem_cons.mp h with heq | h
      · rw [heq]
        exact attachLiterals_mono formula literals (config.attach (literalPolicy formula head))
          (literalPolicy formula head) (Or.inl rfl)
      · exact ih (config.attach (literalPolicy formula head)) literal h

theorem detachClauses_sub (formula : Formula) :
    ∀ (clauses : List Clause) (config : Configuration) (policy : Policy),
      (detachClauses formula config clauses).attached_to_principal policy →
        config.attached_to_principal policy := by
  intro clauses
  induction clauses with
  | nil => intro config policy h; exact h
  | cons clause clauses ih =>
      intro config policy h
      exact (ih (config.detach (clausePolicy clause)) policy h).1

theorem detachClauses_not_attached_of_mem (formula : Formula) :
    ∀ (clauses : List Clause) (config : Configuration) (clause : Clause),
      clause ∈ clauses →
        ¬(detachClauses formula config clauses).attached_to_principal (clausePolicy clause) := by
  intro clauses
  induction clauses with
  | nil => intro config clause h; exact absurd h (by simp)
  | cons head clauses ih =>
      intro config clause h
      rcases List.mem_cons.mp h with heq | h
      · rw [heq]
        intro hattached
        exact (detachClauses_sub formula clauses (config.detach (clausePolicy head))
          (clausePolicy head) hattached).2 rfl
      · exact ih (config.detach (clausePolicy head)) clause h

theorem attachLiterals_spec (formula : Formula) (selector : LiteralSet) :
    ∀ (literals : List Literal) (config : Configuration),
      Inv formula config →
      (∀ literal, config.attached_to_principal (literalPolicy formula literal) → selector literal) →
      LiteralSet.Consistent selector →
      (∀ literal ∈ literals, selector literal) →
      (∀ literal ∈ literals, (reduce formula).policy_exists (literalPolicy formula literal)) →
      Inv formula (attachLiterals formula config literals) ∧
        (∀ literal, (attachLiterals formula config literals).attached_to_principal
          (literalPolicy formula literal) → selector literal) ∧
        Reachable config (attachLiterals formula config literals) := by
  intro literals
  induction literals with
  | nil => intro config hc hS hcons hL hex; exact ⟨hc, hS, Reachable.refl⟩
  | cons literal literals ih =>
      intro config hc hS hcons hL hex
      have hliteral : selector literal := hL literal (List.mem_cons_self ..)
      have hL' : ∀ l' ∈ literals, selector l' :=
        fun l' hl' => hL l' (List.mem_cons_of_mem literal hl')
      have hex' : ∀ l' ∈ literals, (reduce formula).policy_exists (literalPolicy formula l') :=
        fun l' hl' => hex l' (List.mem_cons_of_mem literal hl')
      have hexc : config.policy_exists (literalPolicy formula literal) := by
        rw [hc.policy_exists_eq]
        exact hex literal (List.mem_cons_self ..)
      have hallowed : config.AllowsAttachPolicy (literalId literal) := by
        refine ⟨⟨rootPolicy, hc.root_attached, trivial⟩, ?_⟩
        rintro ⟨policy, hpolicy, hdeny⟩
        obtain ⟨other, hother, hid⟩ := shaped_deny_attach formula (hc.shape policy hpolicy) hdeny
        rw [hother] at hpolicy
        have hSother : selector other := hS other hpolicy
        have hcomp : literal = other.complement := literalId_inj.mp hid
        exact hcons other hSother (hcomp ▸ hliteral)
      have htrans : Transition config (config.attach (literalPolicy formula literal)) :=
        Transition.attach config (literalPolicy formula literal) hexc hallowed
      have hc' : Inv formula (config.attach (literalPolicy formula literal)) :=
        Inv.of_transition formula hc htrans
      have hS' : ∀ l', (config.attach (literalPolicy formula literal)).attached_to_principal
          (literalPolicy formula l') → selector l' := by
        intro l' h'
        rcases h' with h' | h'
        · rw [literalPolicy_inj formula h']; exact hliteral
        · exact hS l' h'
      obtain ⟨hinv, hSfin, hreach⟩ :=
        ih (config.attach (literalPolicy formula literal)) hc' hS' hcons hL' hex'
      exact ⟨hinv, hSfin,
        Reachable.trans (Reachable.step Reachable.refl htrans) hreach⟩

theorem detachClauses_spec (formula : Formula) :
    ∀ (clauses : List Clause) (config : Configuration),
      Inv formula config →
      (∀ clause ∈ clauses, clause ∈ formula) →
      (∀ clause ∈ clauses,
        ∃ literal, config.attached_to_principal (literalPolicy formula literal) ∧ literal ∈ clause) →
      Inv formula (detachClauses formula config clauses) ∧
        Reachable config (detachClauses formula config clauses) := by
  intro clauses
  induction clauses with
  | nil => intro config hc hsub hwit; exact ⟨hc, Reachable.refl⟩
  | cons clause clauses ih =>
      intro config hc hsub hwit
      have hclause : clause ∈ formula := hsub clause (List.mem_cons_self ..)
      obtain ⟨literal, hliteral, hmem⟩ := hwit clause (List.mem_cons_self ..)
      have hexc : config.policy_exists (clausePolicy clause) := by
        rw [hc.policy_exists_eq]
        exact Or.inr (Or.inl ⟨clause, hclause, rfl⟩)
      have hallowed : config.AllowsDetachPolicy (clauseId clause) := by
        refine ⟨⟨literalPolicy formula literal, hliteral, ⟨clause, hclause, hmem, rfl⟩⟩, ?_⟩
        rintro ⟨policy, hpolicy, hd⟩
        exact shaped_deny_detach formula (hc.shape policy hpolicy) hd
      have htrans : Transition config (config.detach (clausePolicy clause)) :=
        Transition.detach config (clausePolicy clause) hexc hallowed
      have hc' : Inv formula (config.detach (clausePolicy clause)) :=
        Inv.of_transition formula hc htrans
      have hsub' : ∀ clause' ∈ clauses, clause' ∈ formula :=
        fun clause' hclause' => hsub clause' (List.mem_cons_of_mem clause hclause')
      have hwit' : ∀ clause' ∈ clauses,
          ∃ literal, (config.detach (clausePolicy clause)).attached_to_principal
            (literalPolicy formula literal) ∧ literal ∈ clause' := by
        intro clause' hclause'
        obtain ⟨literal, hliteral, hmem⟩ := hwit clause' (List.mem_cons_of_mem clause hclause')
        exact ⟨literal, ⟨hliteral, (clausePolicy_ne_literalPolicy formula clause literal).symm⟩, hmem⟩
      obtain ⟨hinv, hreach⟩ := ih (config.detach (clausePolicy clause)) hc' hsub' hwit'
      exact ⟨hinv, Reachable.trans (Reachable.step Reachable.refl htrans) hreach⟩

/-! ## Main theorem -/

/-- A formula has a consistent literal selector if and only if its reduction is
in `PE`. -/
theorem reduce_PE_iff_selector (formula : Formula) :
    PE (reduce formula) ↔
      ∃ selector : LiteralSet,
        LiteralSet.IsSelector selector formula ∧ LiteralSet.Consistent selector := by
  constructor
  · rintro ⟨config, hreach, htarget⟩
    have hinv : Inv formula config := Inv.of_reachable formula hreach (Inv.base formula)
    refine ⟨fun literal => config.attached_to_principal (literalPolicy formula literal), ?_, ?_⟩
    · intro clause hclause
      have hno := (Inv.allowsTarget_iff formula hinv).mp htarget clause hclause
      obtain ⟨literal, hliteral, hmem⟩ := hinv.covers clause hclause hno
      exact ⟨literal, hmem, hliteral⟩
    · intro literal
      exact hinv.consistent literal
  · rintro ⟨selector, hselector, hconsistent⟩
    classical
    let literals : List Literal := formula.flatten.filter (fun literal => decide (selector literal))
    have hL : ∀ literal ∈ literals, selector literal := by
      intro literal hliteral
      rw [List.mem_filter] at hliteral
      exact decide_eq_true_eq.mp hliteral.2
    have hexL : ∀ literal ∈ literals, (reduce formula).policy_exists (literalPolicy formula literal) := by
      intro literal hliteral
      rw [List.mem_filter] at hliteral
      obtain ⟨clause, hclause, hmem⟩ := List.mem_flatten.mp hliteral.1
      exact Or.inr (Or.inr ⟨literal, List.mem_flatten.mpr ⟨clause, hclause, hmem⟩, rfl⟩)
    have hS₀ : ∀ literal,
        (reduce formula).attached_to_principal (literalPolicy formula literal) → selector literal := by
      intro literal hliteral
      rcases hliteral with h | ⟨clause, _, h⟩
      · exact absurd h.symm (rootPolicy_ne_literalPolicy formula literal)
      · exact absurd h.symm (clausePolicy_ne_literalPolicy formula clause literal)
    obtain ⟨hc₁, _, hreach₁⟩ :=
      attachLiterals_spec formula selector literals (reduce formula) (Inv.base formula)
        hS₀ hconsistent hL hexL
    have hwit : ∀ clause ∈ formula,
        ∃ literal, (attachLiterals formula (reduce formula) literals).attached_to_principal
          (literalPolicy formula literal) ∧ literal ∈ clause := by
      intro clause hclause
      obtain ⟨literal, hmem, hsel⟩ := hselector clause hclause
      have hflat : literal ∈ formula.flatten := List.mem_flatten.mpr ⟨clause, hclause, hmem⟩
      have hin : literal ∈ literals := by
        rw [List.mem_filter]
        exact ⟨hflat, by rw [decide_eq_true_eq]; exact hsel⟩
      exact ⟨literal, attachLiterals_attached_of_mem formula literals (reduce formula) literal hin, hmem⟩
    obtain ⟨hc₂, hreach₂⟩ :=
      detachClauses_spec formula formula (attachLiterals formula (reduce formula) literals) hc₁
        (fun _ h => h) hwit
    refine ⟨detachClauses formula (attachLiterals formula (reduce formula) literals) formula,
      Reachable.trans hreach₁ hreach₂, ?_⟩
    exact (Inv.allowsTarget_iff formula hc₂).mpr
      (detachClauses_not_attached_of_mem formula formula
        (attachLiterals formula (reduce formula) literals))

/-- A formula is satisfiable if and only if its reduction is in `PE`. -/
theorem reduce_PE_iff_satisfiable (formula : Formula) :
    PE (reduce formula) ↔ Formula.Satisfiable formula :=
  (reduce_PE_iff_selector formula).trans
    (Formula.satisfiable_iff_exists_consistent_selector formula).symm

end IAM
