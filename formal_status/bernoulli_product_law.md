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

The measurable finite-valued `bernoulliSuccessCount` equals the real sum of
coordinates almost everywhere, and its MGF is the same finite product.

`ExactHoeffding/HypergeomBernoulliLaw.lean` applies the all-parameter
Jacobi-derived factorization from `HypergeomBernoulliMGF`.  It constructs the
actual tilted hypergeometric probability measure and proves equality of its
real pushforward law with the lower-support shift plus an independent
Bernoulli sum.  This includes all legal parameters, zero support width,
population zero, and deterministic boundary laws.  The Bernoulli parameters
are strictly between zero and one whenever their index set is nonempty.

Compilation evidence (each reports `lean_exit_code=0`):

- `/data/hoeffding_full_20261015/evidence/bernoulli_product_law8.log`
- `/data/hoeffding_full_20261015/evidence/hypergeom_bernoulli_law3.log`
