/-!
# CNF formulas and satisfiability

Variables are named by strings. A clause is a disjunction of literals, and a
CNF formula is a conjunction of clauses. The empty clause is false, while the
empty formula is true.
-/

namespace IAM

/-- A named variable or its negation. -/
inductive Literal where
  | pos : String → Literal
  | neg : String → Literal
  deriving DecidableEq, Repr

/-- A disjunction of literals. -/
abbrev Clause := List Literal

/-- A formula in conjunctive normal form. -/
abbrev Formula := List Clause

/-- A truth assignment gives a Boolean value to each variable name. -/
abbrev Assignment := String → Bool

/-- An assignment satisfies a literal when it gives the indicated truth value. -/
def Literal.Satisfies (assignment : Assignment) : Literal → Prop
  | .pos name => assignment name = true
  | .neg name => assignment name = false

/-- A clause is satisfied when at least one of its literals is satisfied. -/
def Clause.Satisfies (assignment : Assignment) (clause : Clause) : Prop :=
  ∃ literal ∈ clause, Literal.Satisfies assignment literal

/-- A CNF formula is satisfied when all of its clauses are satisfied. -/
def Formula.Satisfies (assignment : Assignment) (formula : Formula) : Prop :=
  ∀ clause ∈ formula, Clause.Satisfies assignment clause

/-- A CNF formula is satisfiable when some truth assignment satisfies it. -/
def Formula.Satisfiable (formula : Formula) : Prop :=
  ∃ assignment : Assignment, Formula.Satisfies assignment formula

/-- A set of literals, represented by its membership predicate. -/
abbrev LiteralSet := Literal → Prop

namespace Literal

/-- The literal with the opposite sign. -/
def complement : Literal → Literal
  | .pos name => .neg name
  | .neg name => .pos name

@[simp] theorem complement_complement (literal : Literal) :
    literal.complement.complement = literal := by
  cases literal <;> rfl

/-- A literal and its complement are never both satisfied. -/
theorem not_satisfies_complement (assignment : Assignment) (literal : Literal) :
    Literal.Satisfies assignment literal →
      ¬Literal.Satisfies assignment literal.complement := by
  cases literal <;> simp [Literal.Satisfies, Literal.complement]

end Literal

namespace LiteralSet

/-- A literal selector for a formula contains at least one literal of every
clause of the formula. -/
def IsSelector (selector : LiteralSet) (formula : Formula) : Prop :=
  ∀ clause ∈ formula, ∃ literal ∈ clause, selector literal

/-- A literal selector is consistent when it contains no literal together with
its complement. -/
def Consistent (selector : LiteralSet) : Prop :=
  ∀ literal, selector literal → ¬selector literal.complement

end LiteralSet

/-- A formula is satisfiable exactly when it has a consistent literal
selector. -/
theorem Formula.satisfiable_iff_exists_consistent_selector (formula : Formula) :
    Formula.Satisfiable formula ↔
      ∃ selector : LiteralSet,
        LiteralSet.IsSelector selector formula ∧ LiteralSet.Consistent selector := by
  constructor
  · rintro ⟨assignment, hsat⟩
    refine ⟨fun literal => Literal.Satisfies assignment literal, ?_, ?_⟩
    · intro clause hclause
      exact hsat clause hclause
    · intro literal
      exact Literal.not_satisfies_complement assignment literal
  · rintro ⟨selector, hselector, hconsistent⟩
    classical
    let assignment : Assignment :=
      fun name => if selector (.pos name) then true else false
    refine ⟨assignment, ?_⟩
    intro clause hclause
    rcases hselector clause hclause with ⟨literal, hmem, hselected⟩
    refine ⟨literal, hmem, ?_⟩
    cases literal with
    | pos name => simp [Literal.Satisfies, assignment, hselected]
    | neg name =>
        have hnot : ¬selector (.pos name) := by
          have := hconsistent (.neg name) hselected
          simpa [Literal.complement] using this
        simp [Literal.Satisfies, assignment, hnot]

end IAM
