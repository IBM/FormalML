# Optional:

## Dvoretzky's convergence result.
* To complete Dvoretzky, we need to prove the law of total expectation and the "take out what is known" property of conditional expectations. 
* Either do it using the `group_by_image` or `quotient` stuff defined in `cond_expt.v` or using `ProbSpace.v`.
* Move `infprod.v` from `master` to this branch. 
* Even without this piece, the existing proof may still be valuable (but it needs a story to tie it in with the rest). For example, consider : http://www.gatsby.ucl.ac.uk/~dayan/papers/cjch.pdf

## MDPs/RL
* Prove the policy improvement theorem. 
* State and prove policy+value iteration. 
* If Dvoretzky is done, Q-learning is within reach. 

# Refactoring:
* Cut down on hypotheses where we assume that the set of decision rules is also finite/nonempty. 
* Delete the `ltv_gen` section in `mdp.v`. Break out `Rfct` stuff into a new file. Break out quotients into a new file. Delete everything related to Streams. 

# Paper:
* Make a `paper.v` file. 
* Extract code (?)
* Set up the turtle example.
