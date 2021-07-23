# The CertRL library

In this subdirectory we give a formal proof of convergence of the classical policy and value iteration algorithms in Reinforcement Learning. 

Our formalization is novel in that it utilizes the Finitary Giry Monad and a proof technique called Metric Coinduction. 

For more information, see our [CPP paper](https://dl.acm.org/doi/10.1145/3437992.3439927). 

## Contents
Here is a brief summary of the main files in this directory:

* [`mdp.v`](https://github.com/IBM/FormalML/blob/master/coq/CertRL/mdp.v)
  * defines Markov Decision Processes (MDP) and proves various properties about them
  * definitions of long-term values (LTVs)
  * optimal value function
  * contraction and metric coinduction
  * proofs that LTVs are convergent
  * proofs that they satisfy the Bellman equation.
* [`finite_time.v`](https://github.com/IBM/FormalML/blob/master/coq/CertRL/finite_time.v)
  * Proves the bellman equation for the optimal value function over a finite list of policies.  
* [`pmf_monad.v`](https://github.com/IBM/FormalML/blob/master/coq/CertRL/pmf_monad.v)
  * Contains the infrastructure for the monad structure on the the type of discrete probability measures on a type. 
* [`mdp_turtle.v`](https://github.com/IBM/FormalML/blob/master/coq/CertRL/mdp_turtle.v)
  * Defines a term of the `MDP` type.

