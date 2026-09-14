/-!
# Basic IAM policies

There is one implicit user. Policies can mention the target action and the
attachment or detachment of policies identified by strings.
This module defines policy data, configurations of attached policies, and
the authorization and transition semantics over them.
-/

namespace IAM

/-- Every policy is identified by a string. -/
abbrev PolicyId := String

/-- A set of policy identifiers, represented by its membership predicate. -/
abbrev PolicyIdSet := PolicyId → Prop

/-- The actions mentioned in either the allow or the deny part of a policy. -/
structure Permissions where
  /-- Whether the dedicated target action is included. -/
  target : Bool
  /-- Identifiers of policies whose attachment is included. -/
  attach : PolicyIdSet
  /-- Identifiers of policies whose detachment is included. -/
  detach : PolicyIdSet

/-- A policy with an identifier and separate allow and deny permissions.
No restriction is imposed on overlap between its allow and deny parts. -/
structure Policy where
  id : PolicyId
  allow : Permissions
  deny : Permissions

/-- A configuration is a set of attached policies together with the set of
policies that exist, represented by membership predicates. -/
structure Configuration where
  policy_exists : Policy → Prop
  attached_to_principal : Policy → Prop

/-- A configuration allows an action when some attached policy allows it and no
attached policy denies it. -/
def Configuration.Allows (config : Configuration) (allowed denied : Policy → Prop) : Prop :=
  (∃ policy, config.attached_to_principal policy ∧ allowed policy) ∧
    ¬∃ policy, config.attached_to_principal policy ∧ denied policy

/-- A configuration allows the target action when some attached policy allows
it and no attached policy denies it. -/
def Configuration.AllowsTarget (config : Configuration) : Prop :=
  config.Allows (fun policy => policy.allow.target = true)
    (fun policy => policy.deny.target = true)

/-- A configuration allows attaching the policy with the given identifier when
some attached policy allows that attachment and none denies it. -/
def Configuration.AllowsAttachPolicy (config : Configuration) (i : PolicyId) : Prop :=
  config.Allows (fun policy => policy.allow.attach i)
    (fun policy => policy.deny.attach i)

/-- A configuration allows detaching the policy with the given identifier when
some attached policy allows that detachment and none denies it. -/
def Configuration.AllowsDetachPolicy (config : Configuration) (i : PolicyId) : Prop :=
  config.Allows (fun policy => policy.allow.detach i)
    (fun policy => policy.deny.detach i)

/-- Attach a policy to the principal, keeping the set of existing policies. -/
def Configuration.attach (config : Configuration) (policy : Policy) : Configuration where
  policy_exists := config.policy_exists
  attached_to_principal := fun p => p = policy ∨ config.attached_to_principal p

/-- Detach a policy from the principal, keeping the set of existing policies. -/
def Configuration.detach (config : Configuration) (policy : Policy) : Configuration where
  policy_exists := config.policy_exists
  attached_to_principal := fun p => config.attached_to_principal p ∧ p ≠ policy

/-- Transitions attach or detach an existing policy from the principal. They are
permitted only when the corresponding attach or detach action is allowed. -/
inductive Transition : Configuration → Configuration → Prop where
  | attach (config : Configuration) (policy : Policy)
      (hExists : config.policy_exists policy)
      (hAllowed : config.AllowsAttachPolicy policy.id) :
      Transition config (config.attach policy)
  | detach (config : Configuration) (policy : Policy)
      (hExists : config.policy_exists policy)
      (hAllowed : config.AllowsDetachPolicy policy.id) :
      Transition config (config.detach policy)

/-- A configuration is reachable from another when some finite sequence of
transitions leads from the latter to the former. -/
inductive Reachable (config : Configuration) : Configuration → Prop where
  | refl : Reachable config config
  | step {mid last : Configuration} :
      Reachable config mid → Transition mid last → Reachable config last

/-- `PE` is the set of configurations from which the target action can be
allowed after some finite sequence of transitions. -/
def AdmitsPrivilegeEscalation (config : Configuration) : Prop :=
  ∃ config', Reachable config config' ∧ config'.AllowsTarget

end IAM
