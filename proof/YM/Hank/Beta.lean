import YM.Hank.Plots
/-!
# Quantitative pricing of bare suffix translation in stride two.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive
open Function Filter Set Lattice Wilson RG MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical ComplexConjugate Kronecker Matrix ComplexOrder
namespace Romance.HankV
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead QCD.Revolve Tide
open TorusPCAC.Geometry Chess Patria Patria.Exposure Cells QCD.RP
variable {i j k d N n r t m:ℕ}{c f:Side}
section difference
variable (U:ℕ→ℝ){B:ℝ} (hN:∀ i,i≤n→U i≥0)(hF:∀ i,i≤n→ U i ≤ B)(hU:∀ i:ℕ,i+2≤n→ U (i+1)-U i≤ U (i+2)-U (i+1))
local notation "dT" i:arg=>U (i+1)-U i
include hU
lemma tideV (hi:i≤j)(hj:j<n): U (i+1)-U i ≤ dT j:=by
   induction hi with
   | refl=>rfl
   | @step j h ih=> exact (ih (by omega)).trans (hU j hj)
lemma steepP (h:i+k≤n): (k:ℝ)*(dT i) ≤ U (i+k)-U i:=by
   induction k with
   | zero=>simp
   | succ k ih=> rw [Nat.cast_succ,add_mul,one_mul]; have hv:=ih (show _≤_ from Nat.le_trans (by omega : i+k ≤ i+k.succ) h); rw [←Nat.add_assoc] at h ⊢; linarith only [tideV U hU (show i ≤ i+k by omega) (show i+k<n by omega),hv]
lemma sunkP (h:i+k≤j) (hv:j<n): U (i+k)-U i ≤ (k:ℝ)*(dT j):=by
   induction k with
   | zero=>simp
   | succ k ih=> rw [Nat.cast_succ,add_mul,one_mul]; have he:=ih (show i+k≤ j from (Nat.le_trans (by omega) h)); rw [← Nat.add_assoc] at h ⊢; linarith only [he,tideV U hU (show i+k ≤ j from (Nat.le_of_lt h)) hv]
include hN hF
lemma stepping_more (h:0<k)(hv:k ≤ i)(hz:i+k≤ n): |U (i+1)-U i|≤ B/(k:ℝ):=by
   let x:=dT i; have he: i<n:=by omega
   have hp:0<(k:ℝ):=by exact_mod_cast h
   have hb:= steepP U hU hz; apply (le_div_iff₀ hp).2; rw [← abs_of_nonneg hp.le,← abs_mul]; apply abs_le.mpr; constructor
   · let j:= i-k; have hx:j+k=i:=Nat.sub_add_cancel hv; have hz':=sunkP U hU (le_of_eq hx) he; rw [hx] at hz'; linarith only [hz', hN i he.le,hF j (show j≤n from (by omega))]
   linarith only [hb,hN i he.le,hF (i+k) hz]
-- local monot.Re. Nat
lemma steeper (h:0<k)(hv:k ≤ i)(hx:i+d+k ≤ n): |U (i+d) - U i| ≤ d*(B/(k:ℝ)):=by
    induction d with
    | zero=> simp
    | succ d ih=>
        rw [←Nat.add_assoc i] at hx ⊢; rw [Nat.cast_succ]; have h₀:i+d+k ≤ n:=by omega
        apply le_trans (b:= |U (i+d+1)-U (i+d)| + |U (i+d)-U i|)
        · exact (congr_arg abs (show U (i+d+1)-U i=(U (i+d+1)-U (i+d))+(U (i+d)-U i) from (by ring))).le.trans (abs_add_le ..)
        linarith only [ih h₀,stepping_more U hN hF hU h (show k ≤ i+d by omega) h₀] -- implicit binder order h.
end difference
variable (C: Regulator c 6) (T: Cells.Cut c) (a:Cover)
local notation "X"=> Insertion c 6
local notation "Q"=> T.sector
local notation "S"=> banner
local notation "Θ"=> picture T C.zeroCut
local notation "Pv"=>C.average
local notation "L" => plot C T
variable (hq:C.t=0)(hk:T.kind=.link)(ht:0 ≤ C.β)(hp:2≤ T.half.val)(hz:0 < C.Z) (ha:T.flip.act a= -a)
local notation "uK"=> Complex.I
variable {B D:ℝ}
local notation "xK"=> tidal a
include ha hq hk hz ht hp
lemma diagonalP (x:X)(hV: Budget C T a x n B)(h:0<k)(hv:k ≤ i)(hx:i+d+k ≤ n) : ‖L x (xK x (2*(i+d)))-L x (xK x (2*i))‖ ≤ (d:ℝ)*(B/(k:ℝ)):=by
    let f:= fondV C T a x
    have hi (i:ℕ) (ht':i≤n):0 ≤ f i ∧ L x (xK x (2*i))= (↑(f i):ℂ) ∧ f i ≤ B:=by
         obtain ⟨H,h1,h2⟩:= precise C T hk ht hp hz _ (hV.safe i ht'); exact ⟨h1,by rw [two_mul,← plot_add C T a hq hk ha]; exact H,h2.symm.le.trans (hV.price i ht') ⟩
    rw [(hi _ (by omega :i+d≤n)).2.1,(hi _ (by omega: i≤n)).2.1,← Complex.ofReal_sub, Complex.norm_real,Real.norm_eq_abs]
    exact steeper _ (fun i hi'=> (hi i hi').1) (fun i hi'=> (hi i hi').2.2) (fun i hi'=> connected C T a hq hk ht hp hz ha _ hV hi') h hv hx
omit ha hq hk hz ht hp
lemma lapD (x y:X)(i:ℕ) : L x (xK y i)=(4:ℂ)⁻¹*((L (x+(1:ℂ) • y) (xK (x+(1:ℂ) • y) i)-L (x+(-1:ℂ) • y) (xK (x+(-1:ℂ) • y) i)) - uK * (L (x+uK • y) (xK (x+uK • y) i)-L (x+ -uK • y) (xK (x+ -uK • y) i))):=by
   let f:=L x (xK x i); let p:=L x (xK y i); let q:=L y (xK x i); let r:=L y (xK y i)
   have h(c:ℂ): L (x+c • y) (xK (x+c • y) i)= f+c*p+star c*q+ star c*c*r:=by
       rw [tidal,banner_plus,banner_smul]; unfold plot; rw [pic_add,pic_smul]; simp only [add_mul,mul_add,mul_smul_comm,smul_mul_assoc,map_add,map_smul,smul_eq_mul]; change _=f+c*p+star _*q+_*r; unfold f p q r plot tidal; ring
   rw [h,h,h,h]; simp only [star_one,star_neg, show star uK= -uK from Complex.conj_I]; linear_combination ((f-f)*p+(p-q)/2+0)*Complex.I_sq -- coefficient sign? identity diff: inside=2p+2q + -2I²p+2I²q ; RHS=.5(p+q)+.5 I²*(q-p); lhs-rhs = -.5(q-p)*(1+I²)
include ha hq hk hz ht hp
lemma hankel (x y:X)(hX:Budget C T a x n B)(hY:Budget C T a y n B)(hK:0<k)(h:k ≤ i)(hx:i+d+k ≤ n) : ‖L x (xK y (2*(i+d))) - L x (xK y (2*i))‖ ≤ (d:ℝ)*(4*B/(k:ℝ)):=by
   let αV:=uK; let Zt(j) (c:ℂ):= L (x+c • y) (xK (x+c • y) j)
   let a':=2*(i+d); let b':=2*i; let Y(c:ℂ):= Zt a' c-Zt b' c; let D':=(d:ℝ)*(4*B/(k:ℝ)); have he(c:ℂ)(h:‖c‖=1): ‖Y c‖ ≤ D':= diagonalP C T a hq hk ht hp hz ha _ (combine C T a hk ht hp hz _ _ hX hY c h) hK (by assumption) hx
   have hA:L x (xK y a') - L x (xK y b')=(4:ℂ)⁻¹*((Y 1-Y (-1))-uK*(Y uK-Y (-uK))):=by
        rw [lapD C T a x y a',lapD C T a x y b']; unfold Y Zt; ring
   rw [show L x (xK y (2*(i+d)))-L x (xK y (2*i))=_ from hA, norm_mul,norm_inv]; have hp:‖(4:ℂ)‖=4:=by norm_num
   let p:= Y 1; let q:=Y (-1); let r:=Y uK; let v:=Y (-uK); have hm : ‖p-q-uK*(r-v)‖ ≤ 4*D':=by linarith only [norm_sub_le p q,norm_sub_le r v,norm_sub_le (p-q) (uK*(r-v)), show ‖uK*(r-v)‖=‖r-v‖ from (by simp),show ‖p‖≤D' from he _ (by simp), he (-1) (by simp), he uK (by simp), he (-uK) (by simp)]
   rw [hp]; exact (mul_le_mul_of_nonneg_left hm (by norm_num)).trans_eq (by ring)
end HankV
end Romance
end YM.Massive
#print axioms YM.Massive.Romance.HankV.hankel
