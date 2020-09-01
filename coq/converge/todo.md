# Facts remaining (Urgent):
* Prove that the space `Rfct` is complete wrt to the Max norm. 
* Prove that `Finite A -> Finite B -> Finite ( A -> B)` and it's dependent analogue. This helps us cut down on hypotheses where we assume that the set of decision rules is also finite/nonempty. 
* Prove the law of total expectation and the "take out what is known" property of conditional expectations. 
* Use contraction coinduction to prove Proposition 1 of the LTV paper. This should prove that there is a policy (called the greedy policy) whose long term value is equal to the fixed point.
* Prove that the fixed point is actually the max value function over all policies. 
* Prove the policy improvement theorem. 
* Set up the turtle example.

# Refactoring todos.
 
* Delete the `ltv_gen` section in `mdp.v`. Break out `Rfct` stuff into a new file. Break out quotients into a new file. Delete everything related to Streams. 
* See if the hypothesis `gamma <> 0` can be deleted.

