### BabyGiry -- A Probability Monad for Elementary Probability in Lean

This project aims to demonstrate how to "do probability with monads" using a simple toy version of the Giry monad. It allows you to define conditional probability distributions using "randomly do" blocks of the form:

```lean
def Posterior : Random ℚ := randomly do
  let p <-~ Unif (Linspace 0 1) -- "Let p be uniformly distributed on {0/10, 1/10, ..., 10/10}.
  let k <-~ Binomial 5 p -- Let k be the number of successes in 5 Bernoulli trials with success probability p.
  observe <| k = 3 -- Observe that k = 3.
  return p

-- #eval ℙ[p ≥ 4/10 ∧ p ≤ 6/10 | p ~ Posterior]
-- >> (1777 : Rat)/3333
-- #eval (1777 : Float)/3333
-- >> 0.533153

example : ℙ[p ≥ 4/10 ∧ p ≤ 6/10 | p ~ Posterior] = 1777/3333 := by rfl
```

In such a do block, "random variables" simply become dummy variables in a local context -- no need to fix a "background probability space" as usually done in classical probability theory to work with random variables. 

The capability of computing conditional probabilities "automatically", by merely _specifying_ a model, also illustrates the basic idea of a probabilistic programming language.
See Examples.lean for more examples, including the famous Monty Hall Problem and a version of the Birthday Paradox.
