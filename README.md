# NP-hardness of detecting privilege escalations

A well-known problem in Identity-and-Access-Management (IAM) is the detection of *privilege escalation paths*: Sequences of IAM requests leading to an unintended state where some critical action can be executed.

The bounded version of this problem - where the number of steps in a privilege escalation path is restricted to some constant - is obviously decidable, and one can use SMT-based model checking to find a solution.

This repository contains a proof that the unbounded version of the problem is NP-hard, which rules out that it has certain trivial solutions. This in itself is not surprising, given the expressivity of modern IAM languages. However, it is shown that NP-hardness appears already in a tiny fragment of IAM: We need just a single user, a set of policies, and the two IAM actions of attaching and detaching policies.

The proof is formalised in the Lean theorem prover. More precisely, what is formally proved is the correctness of the reduction. NP-hardness also needs the fact that the reduction is computable in polynomial time, which is not hard to see.

## Main result

We define a function `reduce` that maps a CNF $\alpha$ to an IAM configuration and show:

```lean
theorem IAM.reduce_PE_iff_satisfiable (α : Formula) :
    PE (reduce α) ↔ Formula.Satisfiable α
```

Here `PE` contains all configurations from which there is a path (of any length) to a configuration where a dedicated critical action is possible.


## Modules

- `IAMHardness/CNF.lean`: Basic definitions of CNF formulas and satisfiability.
- `IAMHardness/IAM.lean`: The IAM model. This is an extremely simplified model which is just expressive enough to encode the CNF query. There is only one principal (implicit), the notion of a policy, and the actions of attaching and detaching policies together with one critical action. As usual in IAM, an action is allowed if it is allowed by at least one of the policies attached to the principal, and denied by no policy attached to the principal.

- `IAMHardness/Reduction.lean`: Defines the reduction and proofs its correctness, which is the main theorem.
- `IAMHardness.lean`: the library entry point; imports all modules.

## The reduction

`reduce` turns a CNF formula `α` into a configuration as follows.

- `rootPolicy` (ID `rootId`) is attached to the principal. It allows the target action and the attachment of arbitrary policies.
- For every clause `C ∈ formula` there is an attached `clausePolicy C` that
  denies the target action.
- For every literal `l` occurring in `α` there is
  a policy `literalPolicy α l`, which exists but is not attached. It
  allows detaching the clause policy of each clause containing `l`, and denies attaching the literal policy of the complementary
  literal.

Intuition: allowing the target action requires detaching every `clausePolicy`,
which requires attaching the `literalPolicy` of a literal in that clause; we think of this as assigning the literal the truth value $1$.
Because complementary literal policies deny each other's attachment, no literal and its complement can get assigned to $1$. Therefore detaching every `clausePolicy` corresponds to finding a satisfying assignment of `α`.


## Building

Build the `IAMHardness` library target with `lake build`.
