# NP-hardness of detecting privilege escalations

A well-known problem in Identity-and-Access-Management (IAM) is the detection of *privilege escalation paths*: sequences of IAM requests leading to an unintended state where some critical action can be executed. [1](#1)

The bounded version of this problem — where the number of steps in a privilege escalation path is restricted to some constant — is obviously decidable, and one can use SMT-based model checking to find a solution. [2](#2)

This repository contains a proof that the unbounded version of the problem is NP-hard, so it has no polynomial-time algorithm unless P = NP. This in itself is not surprising, given the expressivity of modern IAM languages. However, it is shown that NP-hardness appears already in a tiny fragment of IAM: We need just a single user, a set of policies, and the two IAM actions of attaching and detaching policies.

The proof is formalised in the Lean theorem prover. More precisely, what is formally proved is the correctness of the reduction. NP-hardness also needs the fact that the reduction is computable in polynomial time, which is not hard to see.

## Main result

We define a function `reduce` that maps a CNF `α` to an IAM configuration and show:

```lean
theorem IAM.admits_PE_iff_satisfiable (α : Formula) :
    AdmitsPrivilegeEscalation (reduce α) ↔ Formula.Satisfiable α
```

Here `AdmitsPrivilegeEscalation` is the set of configurations from which there is a path (of any length) to a configuration where the dedicated target action is possible.


## Modules

- `IAMHardness/CNF.lean`: basic definitions of CNF formulas and satisfiability.
- `IAMHardness/IAM.lean`: the IAM model. This is an extremely simplified model which is just expressive enough to encode the CNF query. There is only one principal (implicit), the notion of a policy, and the actions of attaching and detaching policies together with one target action. As usual in IAM, an action is allowed if it is allowed by at least one of the policies attached to the principal, and denied by no policy attached to the principal. The hardness result extends to every real-world IAM system in which the simple model can be embedded (presumably this is the case for all such systems).
- `IAMHardness/Reduction.lean`: defines the reduction and proves its correctness, which is the main theorem.
- `IAMHardness.lean`: the library entry point; imports all modules.

## The reduction

`reduce` turns a CNF formula `α` into a configuration as follows.

- `rootPolicy` (ID `rootId`) is attached to the principal. It allows the target action and the attachment of arbitrary policies.
- For every clause `C ∈ α` there is an attached `clausePolicy C` that denies the target action.
- For every literal `l` occurring in `α` there is a policy `literalPolicy α l`, which exists but is not attached. It allows detaching the clause policy of each clause containing `l`, and denies attaching the literal policy of the complementary literal.

Intuition: allowing the target action requires detaching every `clausePolicy`, which requires attaching the `literalPolicy` of a literal in that clause; we think of this as assigning the literal the truth value $1$. Because complementary literal policies deny each other's attachment, no literal and its complement can get assigned to $1$. Therefore detaching every `clausePolicy` corresponds to finding a satisfying assignment of `α`.


## Building

Build the `IAMHardness` library target with `lake build`. Verified with Lean 4.31.0.

## References

<a id="1">[1]</a>
Rhino Security Labs. *AWS Privilege Escalation Methods and Mitigation*. https://rhinosecuritylabs.com/aws/aws-privilege-escalation-methods-mitigation/

<a id="2">[2]</a>
Ilia Shevrin and Oded Margalit. 2023. Detecting multi-step IAM attacks in AWS environments via model checking. In *Proceedings of the 32nd USENIX Conference on Security Symposium* (SEC '23). USENIX Association, USA, Article 337, 6025–6042. https://dl.acm.org/doi/10.5555/3620237.3620574