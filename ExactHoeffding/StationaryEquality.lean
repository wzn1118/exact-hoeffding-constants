import ExactHoeffding.StationaryCertificates

namespace ExactHoeffding

theorem stationary_small_A_q_bound_strict (j L A q : ℝ)
    (hj : 3≤j) (hL : j-1≤L) (hq : 0≤q)
    (hrel : A=j^2*(j-1)-(L+j)*q^2) (hAL : A*L≤j^2) : j<L*q := by
  have hj0 : 0<j := by linarith
  have hL0 : 0<L := by linarith
  have hT : 0<L+j := by linarith
  have haux := stationary_small_A_auxiliary_positive j L hj hL
  by_contra hh
  have hqj : L*q≤j := le_of_not_gt hh
  have hs : (L*q)^2≤j^2 := sq_le_sq₀ (by positivity) (le_of_lt hj0) |>.2 hqj
  have hmul := mul_le_mul_of_nonneg_left hAL hL0.le
  have hmul2 := mul_le_mul_of_nonneg_left hs hT.le
  have hmul3 := mul_pos (sq_pos_of_pos hj0) haux
  nlinarith [hrel]

theorem stationary_G_positive (j L A q d : ℝ)
    (hj : 3≤j) (hL : j-1≤L) (hq : 0<q) (hd : 0≤d)
    (hdS : d≤L-j+1) (hA : 0<A)
    (hrel : A=j^2*(j-1)-(L+j)*q^2) :
    0<stationaryG A L (L*(L+1)-2*j) j q d := by
  have hj0 : 0<j := by linarith
  have hL0 : 0<L := by linarith
  have hL1 : 0<L-1 := by linarith
  have hLp : 0<L+1 := by linarith
  have hS : 0≤L-j+1 := by linarith
  by_cases hbig : j^2≤A*L
  · have hid := stationary_large_A_square A L j q d
    rcases hbig.eq_or_lt with hEq | hstrict
    · have hAL : A*L=j^2 := hEq.symm
      have hqj := stationary_small_A_q_bound_strict j L A q hj hL hq.le hrel hAL.le
      have hterm : A*(d+q)-j*(L+1)*q ≠ 0 := by
        intro hz
        have hprod : j*(j*d-(L*(L+1)-j)*q)=0 := by
          linear_combination L*hz-(d+q)*hAL
        have hlinear : j*d=(L*(L+1)-j)*q := by
          have := (mul_eq_zero.mp hprod).resolve_left hj0.ne'
          linarith
        have hqS := mul_nonneg (sub_nonneg.mpr hqj.le) hS
        have hextra : 0<j*(L-1)*q := by positivity
        have hgap : (L*(L+1)-j)*q-j*(L-j+1) =
            (L*q-j)*(L-j+1)+j*(L-1)*q := by ring
        have hbound := mul_le_mul_of_nonneg_left hdS hj0.le
        linarith
      have hsq : 0<(A*(d+q)-j*(L+1)*q)^2 := sq_pos_of_ne_zero hterm
      rw [hAL, sub_self, mul_zero, add_zero] at hid
      have hp : 0<A*stationaryG A L (L*(L+1)-2*j) j q d := by rw [hid]; exact hsq
      exact pos_of_mul_pos_right hp hA.le
    · have hpositive : 0<(L+1)^2*q^2*(A*L-j^2) := by positivity
      have hsq := sq_nonneg (A*(d+q)-j*(L+1)*q)
      have hp : 0<A*stationaryG A L (L*(L+1)-2*j) j q d := by linarith
      exact pos_of_mul_pos_right hp hA.le
  · have hsmall : A*L<j^2 := lt_of_not_ge hbig
    have hqj := stationary_small_A_q_bound j L A q hj hL hq.le hrel hsmall
    have hEq := stationary_small_A_Eq_bound j L A q hj hL hq.le hrel hsmall
    have h1 := mul_nonneg (sub_nonneg.mpr hqj) (mul_nonneg hj0.le hS)
    have h2 : 0≤j^2*q*(L-1) := by positivity
    have h3 := mul_le_mul_of_nonneg_right hsmall.le (add_nonneg hS hq.le)
    have hderiv : A*(L-j+1+q)≤j*(L+1)*q := by nlinarith
    have hbracket : 0≤2*j*(L+1)*q-A*(d+(L-j+1)+2*q) := by nlinarith
    have hdiff := mul_nonneg (sub_nonneg.mpr hdS) hbracket
    have hgs : 0<stationaryG A L (L*(L+1)-2*j) j q (L-j+1) := by
      unfold stationaryG
      have hlast : 0≤(L*(L+1)-2*j)*q-2*j*(L-j+1) := sub_nonneg.mpr hEq
      have hp : 0≤(L+1)*q*((L*(L+1)-2*j)*q-2*j*(L-j+1)) := by positivity
      have hfirst : 0<A*(L-j+1+q)^2 := by positivity
      nlinarith
    have hid : stationaryG A L (L*(L+1)-2*j) j q d-
        stationaryG A L (L*(L+1)-2*j) j q (L-j+1) =
        (L-j+1-d)*(2*j*(L+1)*q-A*(d+(L-j+1)+2*q)) := by
      unfold stationaryG
      ring
    linarith

theorem universal_stationary_comparison_positive (j L D x : ℝ)
    (hj : 3≤j) (hL : j-1≤L) (hD : |D|≤L-j+1)
    (hA : 0<j^2*(j-1)-(L+j)*x^2) (hnonzero : D≠0 ∨ x≠0) :
    0<(j^2*(j-1)-(L+j)*x^2)*(D-x)^2+
      (L+1)*(2*j*D*x+(L*(L+1)-2*j)*x^2) := by
  have hj0 : 0<j := by linarith
  have hLp : 0<L+1 := by linarith
  have hE : 0≤L*(L+1)-2*j := by nlinarith
  by_cases hsign : 0≤D*x
  · have hfirst := mul_nonneg hA.le (sq_nonneg (D-x))
    have hcross : 0≤2*j*(D*x) := by positivity
    have hlast := mul_nonneg hE (sq_nonneg x)
    have hsecond := mul_nonneg hLp.le (add_nonneg hcross hlast)
    by_cases heq : D=x
    · have hx : x≠0 := by rcases hnonzero with hD | hx; exact heq ▸ hD; exact hx
      have hstrict : 0<2*j*x^2 := by positivity
      have hp := mul_pos hLp hstrict
      rw [heq] at *
      nlinarith
    · have hstrict := mul_pos hA (sq_pos_of_ne_zero (sub_ne_zero.mpr heq))
      nlinarith
  · have hx : x≠0 := by intro hx; simp [hx] at hsign
    have habs : |D| * |x| = -(D*x) := by
      rw [← abs_mul,abs_of_neg (lt_of_not_ge hsign)]
    have hx2 : |x|^2=x^2 := sq_abs x
    have hd2 : |D|^2=D^2 := sq_abs D
    have hg := stationary_G_positive j L (j^2*(j-1)-(L+j)*x^2)
      |x| |D| hj hL (abs_pos.mpr hx) (abs_nonneg _) hD hA (by rw [hx2])
    unfold stationaryG at hg
    have hsquare : (|D| + |x|)^2=(D-x)^2 := by nlinarith
    rw [hsquare,hx2] at hg
    have hcross : 2*j * |x| * |D| = -(2*j*D*x) := by nlinarith [habs]
    rw [hcross] at hg
    nlinarith

theorem universal_stationary_comparison_eq_zero_iff (j L D x : ℝ)
    (hj : 3≤j) (hL : j-1≤L) (hD : |D|≤L-j+1)
    (hA : 0<j^2*(j-1)-(L+j)*x^2) :
    (j^2*(j-1)-(L+j)*x^2)*(D-x)^2+
      (L+1)*(2*j*D*x+(L*(L+1)-2*j)*x^2)=0 ↔ D=0 ∧ x=0 := by
  constructor
  · intro heq
    by_contra hh
    have hne : D≠0 ∨ x≠0 := by simpa only [not_and_or] using hh
    have := universal_stationary_comparison_positive j L D x hj hL hD hA hne
    linarith
  · rintro ⟨rfl, rfl⟩
    ring


end ExactHoeffding
