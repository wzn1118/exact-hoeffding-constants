# Independent Bernoulli product law

`ExactHoeffding/BernoulliProductLaw.lean` constructs
`independentBernoulliMeasure p` as the actual finite product of Bernoulli
probability measures on real coordinates.  The parameters range over the
closed unit interval; the empty product and deterministic endpoints are included.

The kernel-checked statements establish:

- every coordinate has the prescribed Bernoulli pushforward law;
- the coordinate family is independent on the product probability space;
- the MGF of the sum is the finite product of Bernoulli MGFs;
- adding any real constant multiplies that MGF by its exponential;
- positive-real equality of finite-lattice PGFs implies equality of measures;
- equality of actual finite-lattice MGFs implies equality of the corresponding
  pushforward laws, including real-valued pushforwards on arbitrary finite
  measure spaces.

The product-space construction does not assume the existence of a target
hypergeometric representation.  Its application to that target uses the
separate Jacobi-derived MGF factorization.

Compilation evidence:
`/data/hoeffding_full_20261015/evidence/bernoulli_product_law4.log`
(`lean_exit_code=0`; one subsequently removed unused simp argument).
