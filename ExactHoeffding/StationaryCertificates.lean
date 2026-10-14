import ExactHoeffding.Basic
import Mathlib.Tactic.LinearCombination

namespace ExactHoeffding

def stationaryDen (j m u v : ℝ) : ℝ :=
  (j-u)*(m-u)-v*(j+m-2*u-1)

def stationaryPolynomial (j m r u v : ℝ) : ℝ :=
  (stationaryDen j m u v-v*(r+2*u))*(v+u^2)+r*stationaryDen j m u v*u+
    (j+m)*v*(r+2*u)*u-j*m*v*(r+2*u)

theorem stationary_elimination (j m r u v z : ℝ)
    (hr : (1-z)*(v+u^2)+(r+(j+m)*z)*u-j*m*z=0)
    (hs : z*stationaryDen j m u v=v*(r+2*u)) :
    stationaryPolynomial j m r u v=0 := by
  unfold stationaryPolynomial
  linear_combination (stationaryDen j m u v)*hr +
    (v+u^2-(j+m)*u+j*m)*hs

theorem stationary_polynomial_constant (j m r u : ℝ) :
    stationaryPolynomial j m r u 0=u*(j-u)*(r+u)*(m-u) := by
  unfold stationaryPolynomial stationaryDen
  ring

theorem stationary_polynomial_quadratic (j m r u v : ℝ) :
    stationaryPolynomial j m r u v = -(j+m+r-1)*v^2+
      (-j*m*r-2*j*m*u+j*m+j*u^2-j*u+m*u^2-m*u+r*u^2+r*u+2*u^2)*v+
      u*(j-u)*(r+u)*(m-u) := by
  unfold stationaryPolynomial stationaryDen
  ring

/-- Sign comparison for a positive root of a concave quadratic with positive constant. -/
theorem concave_quadratic_positive_root_bound (T b c v B : ℝ)
    (hT : 0<T) (hc : 0<c) (hv : 0<v) (hB : 0<B)
    (hroot : -T*v^2+b*v+c=0) (hbound : -T*B^2+b*B+c≤0) : v≤B := by
  by_contra h
  have hBV : B<v := lt_of_not_ge h
  have hpos : 0<(v-B)*(T*v*B+c) := by positivity
  have hid : v*(-T*B^2+b*B+c)-B*(-T*v^2+b*v+c)=
      (v-B)*(T*v*B+c) := by ring
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hv) hbound
  nlinarith

theorem stationary_main_identity (j h r x : ℝ) (hT : 2*j+h+r-1 ≠ 0) :
    -16*(2*j+h+r-1)*stationaryPolynomial j (j+h) r ((j+x)/2)
       (j*(j+h+r)/(4*(2*j+h+r-1))) =
    (j^2*(j-1)-(2*j+h+r-1)*x^2)*(h-r-x)^2+
      (j+h+r)*(2*j*(h-r)*x+((j+h+r-1)*(j+h+r)-2*j)*x^2) := by
  unfold stationaryPolynomial stationaryDen
  field_simp
  ring

def stationaryK (j L S : ℝ) : ℝ :=
  (L*(L+1)-2*j)^2*((j-1)*L-1)-4*S^2*L*(L+j)

theorem stationary_K_expansion (a S : ℝ) :
    stationaryK (a+3) (a+2+S) S =
      a^2*(a+1)*(a+3)^3+
      a*(a+3)^2*(5*a^2+16*a+10)*S+
      (10*a^4+80*a^3+213*a^2+202*a+35)*S^2+
      (10*a^3+64*a^2+117*a+52)*S^3+
      (5*a^2+22*a+19)*S^4+(a+2)*S^5 := by
  unfold stationaryK
  ring

theorem stationary_K_nonnegative (j S : ℝ) (hj : 3≤j) (hS : 0≤S) :
    0≤stationaryK j (j-1+S) S := by
  have ha : 0≤j-3 := by linarith
  have h := stationary_K_expansion (j-3) S
  have hj1 : j-3+3=j := by ring
  have hj2 : j-3+2+S=j-1+S := by ring
  rw [hj1,hj2] at h
  rw [h]
  positivity

theorem stationary_square_identity (A L E j q d : ℝ) (hA : A≠0) :
    A*(d+q)^2+(L+1)*(E*q^2-2*j*q*d) =
    A*(d+q-j*(L+1)*q/A)^2+
      (L+1)*q^2*(E+2*j-j^2*(L+1)/A) := by
  field_simp
  ring

theorem stationary_small_A_auxiliary (a S : ℝ) :
    ((a+3-1)*(a+2+S)^2-2*(a+2+S)-(a+3)) =
      (a+2)*S^2+(2*a^2+8*a+6)*S+a^3+6*a^2+9*a+1 := by ring

theorem stationary_small_A_auxiliary_positive (j L : ℝ)
    (hj : 3≤j) (hL : j-1≤L) : 0<(j-1)*L^2-2*L-j := by
  have ha : 0≤j-3 := by linarith
  have hS : 0≤L-j+1 := by linarith
  have hid := stationary_small_A_auxiliary (j-3) (L-j+1)
  have hj3 : j-3+3=j := by ring
  have hLL : j-3+2+(L-j+1)=L := by ring
  simp only [hj3,hLL] at hid
  rw [hid]
  positivity

def stationaryG (A L E j q d : ℝ) : ℝ :=
  A*(d+q)^2+(L+1)*(E*q^2-2*j*q*d)

theorem stationary_large_A_square (A L j q d : ℝ) :
    A*stationaryG A L (L*(L+1)-2*j) j q d =
      (A*(d+q)-j*(L+1)*q)^2+(L+1)^2*q^2*(A*L-j^2) := by
  unfold stationaryG
  ring

theorem stationary_large_A_nonnegative (A L j q d : ℝ)
    (hA : 0<A) (hAL : j^2≤A*L) :
    0≤stationaryG A L (L*(L+1)-2*j) j q d := by
  have hid := stationary_large_A_square A L j q d
  have hp : 0≤(L+1)^2*q^2*(A*L-j^2) := by positivity
  have hs := sq_nonneg (A*(d+q)-j*(L+1)*q)
  nlinarith

theorem stationary_small_A_q_bound (j L A q : ℝ)
    (hj : 3≤j) (hL : j-1≤L) (hq : 0≤q)
    (hrel : A=j^2*(j-1)-(L+j)*q^2) (hAL : A*L<j^2) : j≤L*q := by
  have hj0 : 0<j := by linarith
  have hL0 : 0<L := by linarith
  have hT : 0<L+j := by linarith
  have haux := stationary_small_A_auxiliary_positive j L hj hL
  by_contra hh
  have hqj : L*q<j := lt_of_not_ge hh
  have hs : (L*q)^2<j^2 := sq_lt_sq₀ (by positivity) (le_of_lt hj0) |>.2 hqj
  have hmul := mul_lt_mul_of_pos_left hAL hL0
  have hmul2 := mul_lt_mul_of_pos_left hs hT
  have hmul3 := mul_pos (sq_pos_of_pos hj0) haux
  nlinarith [hrel]

theorem stationary_small_A_Eq_bound (j L A q : ℝ)
    (hj : 3≤j) (hL : j-1≤L) (hq : 0≤q)
    (hrel : A=j^2*(j-1)-(L+j)*q^2) (hAL : A*L<j^2) :
    2*j*(L-j+1)≤(L*(L+1)-2*j)*q := by
  have hj0 : 0<j := by linarith
  have hL0 : 0<L := by linarith
  have hS : 0≤L-j+1 := by linarith
  have hE : 0≤L*(L+1)-2*j := by nlinarith
  have hK := stationary_K_nonnegative j (L-j+1) hj hS
  have hidL : j-1+(L-j+1)=L := by ring
  rw [hidL] at hK
  unfold stationaryK at hK
  have hbase : j^2*((j-1)*L-1)<L*(L+j)*q^2 := by nlinarith [hrel]
  have hmul := mul_le_mul_of_nonneg_left (le_of_lt hbase) (sq_nonneg (L*(L+1)-2*j))
  have hmulK := mul_nonneg (sq_nonneg j) hK
  have hLT : 0<L*(L+j) := by positivity
  have hsq : (2*j*(L-j+1))^2≤((L*(L+1)-2*j)*q)^2 := by
    nlinarith
  have hleft : 0≤2*j*(L-j+1) := by positivity
  have hright : 0≤(L*(L+1)-2*j)*q := mul_nonneg hE hq
  nlinarith

theorem stationary_G_nonnegative (j L A q d : ℝ)
    (hj : 3≤j) (hL : j-1≤L) (hq : 0≤q) (hd : 0≤d)
    (hdS : d≤L-j+1) (hA : 0<A)
    (hrel : A=j^2*(j-1)-(L+j)*q^2) :
    0≤stationaryG A L (L*(L+1)-2*j) j q d := by
  by_cases hbig : j^2≤A*L
  · exact stationary_large_A_nonnegative A L j q d hA hbig
  have hsmall : A*L<j^2 := lt_of_not_ge hbig
  have hj0 : 0<j := by linarith
  have hL0 : 0<L := by linarith
  have hL1 : 0≤L-1 := by linarith
  have hS : 0≤L-j+1 := by linarith
  have hqj := stationary_small_A_q_bound j L A q hj hL hq hrel hsmall
  have hEq := stationary_small_A_Eq_bound j L A q hj hL hq hrel hsmall
  have h1 := mul_nonneg (sub_nonneg.mpr hqj) (mul_nonneg (le_of_lt hj0) hS)
  have h2 : 0≤j^2*q*(L-1) := by positivity
  have h3 := mul_le_mul_of_nonneg_right (le_of_lt hsmall) (add_nonneg hS hq)
  have hderiv : A*(L-j+1+q)≤j*(L+1)*q := by nlinarith
  have hbracket : 0≤2*j*(L+1)*q-A*(d+(L-j+1)+2*q) := by nlinarith
  have hdiff := mul_nonneg (sub_nonneg.mpr hdS) hbracket
  have hgs : 0≤stationaryG A L (L*(L+1)-2*j) j q (L-j+1) := by
    unfold stationaryG
    have hlast : 0≤(L*(L+1)-2*j)*q-2*j*(L-j+1) := sub_nonneg.mpr hEq
    have hp : 0≤(L+1)*q*((L*(L+1)-2*j)*q-2*j*(L-j+1)) := by positivity
    nlinarith [sq_nonneg (L-j+1+q)]
  have hid : stationaryG A L (L*(L+1)-2*j) j q d-
      stationaryG A L (L*(L+1)-2*j) j q (L-j+1) =
      (L-j+1-d)*(2*j*(L+1)*q-A*(d+(L-j+1)+2*q)) := by
    unfold stationaryG
    ring
  linarith

theorem universal_stationary_comparison (j L D x : ℝ)
    (hj : 3≤j) (hL : j-1≤L) (hD : |D|≤L-j+1)
    (hA : 0<j^2*(j-1)-(L+j)*x^2) :
    0≤(j^2*(j-1)-(L+j)*x^2)*(D-x)^2+
      (L+1)*(2*j*D*x+(L*(L+1)-2*j)*x^2) := by
  have hj0 : 0≤j := by linarith
  have hLp : 0≤L+1 := by linarith
  have hE : 0≤L*(L+1)-2*j := by nlinarith
  by_cases hsign : 0≤D*x
  · have hfirst := mul_nonneg (le_of_lt hA) (sq_nonneg (D-x))
    have hcross : 0≤2*j*(D*x) := by positivity
    have hlast := mul_nonneg hE (sq_nonneg x)
    have hsecond := mul_nonneg hLp (add_nonneg hcross hlast)
    nlinarith
  have habs : |D| * |x| = -(D*x) := by
    rw [← abs_mul,abs_of_neg (lt_of_not_ge hsign)]
  have hx2 : |x|^2=x^2 := sq_abs x
  have hd2 : |D|^2=D^2 := sq_abs D
  have hg := stationary_G_nonnegative j L (j^2*(j-1)-(L+j)*x^2)
    |x| |D| hj hL (abs_nonneg _) (abs_nonneg _) hD hA (by rw [hx2])
  unfold stationaryG at hg
  have hsquare : (|D| + |x|)^2=(D-x)^2 := by nlinarith
  rw [hsquare,hx2] at hg
  have hcross : 2*j * |x| * |D| = -(2*j*D*x) := by nlinarith [habs]
  rw [hcross] at hg
  nlinarith

theorem admissible_stationary_sharp_bound (j h r u v : ℝ)
    (hj : 3≤j) (hh : 0≤h) (hr : 0≤r)
    (hu : 0<u) (huj : u<j) (hv : 0<v)
    (hPB : v≤u*(j-u)/j)
    (hstat : stationaryPolynomial j (j+h) r u v=0) :
    v≤j*(j+h+r)/(4*(2*j+h+r-1)) := by
  let T := 2*j+h+r-1
  let L := j+h+r-1
  let B := j*(j+h+r)/(4*T)
  have hjp : 0<j := by linarith
  have hT : 0<T := by dsimp [T]; linarith
  have hL : j-1≤L := by dsimp [L]; linarith
  have hB : 0<B := by dsimp [B]; positivity
  have hBT : B*(4*T)=j*(j+h+r) := by
    dsimp [B]
    field_simp
  change v≤B
  by_contra hnot
  have hvB : B<v := lt_of_not_ge hnot
  have hpb := (le_div_iff₀ hjp).mp hPB
  have hstrict : B*j<u*(j-u) := by nlinarith
  have hp := mul_pos (sub_pos.mpr hstrict) (mul_pos (by norm_num : (0:ℝ)<4) hT)
  have hBTj := congrArg (fun z : ℝ => z*j) hBT
  have hA : 0<j^2*(j-1)-T*(2*u-j)^2 := by
    dsimp [T] at hp hBTj ⊢
    nlinarith only [hp,hBTj]
  have hD : |h-r|≤L-j+1 := by
    apply abs_le.mpr
    dsimp [L]
    constructor <;> linarith
  have hcmp := universal_stationary_comparison j L (h-r) (2*u-j) hj hL hD
    (by dsimp [L]; dsimp [T] at hA; nlinarith only [hA])
  have hid := stationary_main_identity j h r (2*u-j) (ne_of_gt hT)
  have huform : (j+(2*u-j))/2=u := by ring
  rw [huform] at hid
  change -16*T*stationaryPolynomial j (j+h) r u B = _ at hid
  dsimp [L] at hcmp
  have hFB : stationaryPolynomial j (j+h) r u B≤0 := by
    have hprod : 0≤-16*T*stationaryPolynomial j (j+h) r u B := by
      rw [hid]
      convert hcmp using 1 <;> ring
    nlinarith only [hprod,hT]
  have hju : 0<j-u := sub_pos.mpr huj
  have hru : 0<r+u := by linarith
  have hjhu : 0<j+h-u := by linarith
  have hc : 0<u*(j-u)*(r+u)*(j+h-u) := by positivity
  have hquadratic_v := stationary_polynomial_quadratic j (j+h) r u v
  have hquadratic_B := stationary_polynomial_quadratic j (j+h) r u B
  have hTv : j+(j+h)+r-1=T := by dsimp [T]; ring
  rw [hTv] at hquadratic_v hquadratic_B
  rw [hquadratic_v] at hstat
  rw [hquadratic_B] at hFB
  have hfinal := concave_quadratic_positive_root_bound T _ _ v B hT hc hv hB hstat hFB
  exact (not_le_of_gt hvB) hfinal

theorem two_mark_variance_envelope (rho q : ℝ)
    (hr : 0<rho) (hr2 : rho≤2) (hq : 1≤q) :
    (rho*q+1)/(rho+q)^2≤1/(1+rho) := by
  have hd : 0<(rho+q)^2 := sq_pos_of_pos (by linarith)
  have h1 : 0<1+rho := by linarith
  apply (div_le_div_iff₀ hd h1).mpr
  have h : 0≤(q-1)*(q+1+rho-rho^2) := by
    have hh : 0≤(2-rho)*(rho+1) := by positivity
    have hbr : 0≤q+1+rho-rho^2 := by nlinarith
    exact mul_nonneg (sub_nonneg.mpr hq) hbr
  nlinarith

end ExactHoeffding
