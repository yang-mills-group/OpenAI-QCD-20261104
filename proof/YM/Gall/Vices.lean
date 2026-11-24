import YM.Gall.Chix
import YM.Tawny.Rays
import YM.Oriole.Grin
/-! J T moment readings native. Bias through symmetric shifts. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
open Tawny.Cast.Rays
variable {u t a D C v e s:ℝ}{c:Side}{n j d m r w:ℕ}
local notation "Y★"=> Cray c
local notation "G★"=> Lat.Fields c 6
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas
open QCD.Entr.Goals
noncomputable def bias (T:Taper)(p:Multi d)(x:Cover)(u:Site c):ℂ:= Np T u * SourceRead.profile p (Lattice.lift u+x) 1
noncomputable def beamT (T:Taper)(p q:Multi d)(x:Cover)(u v:Site c):ℂ:= bias T p x u * bias T q x v
variable (p q:Multi d)(T:Taper)(x:Cover)(k:Axis)
lemma colon (u:Site c)(he:Nearby x)(hu:8*(pdist u+2)< c.val): heat x u * Nw T p (u+wrap c x)=bias T p x u:= by
    obtain ⟨k,hk⟩:=he; obtain ⟨hU,hW,hP⟩:=Oriole.charts u x T (flipT x k hk (c:=c)).2 hu; unfold Nw bias; rw[←mul_assoc,hP,hW,hU]
lemma short (u:Site c) : ‖Nw T p u‖ ≤ (peg u (order (power p))):=by
    unfold Nw; rw [norm_mul]; apply (mul_le_of_le_one_left (norm_nonneg _) (tintE u T)).trans;  have h:= profile_pay (b:=0) p u; simpa only [offset,map_zero,sub_zero,peg,separation] using! h
lemma tinct (u:Site c)(he:Nearby x): ‖heat x u*Nw T p (u+wrap c x)‖ ≤ 2^order (power p)*peg u (order (power p)):=by
    obtain ⟨k,h⟩:=he; rw [norm_mul, show ‖heat x u‖=1 from (by rcases (glares x|>.sign u) with h|h<;>simp[h]),one_mul]; exact (short ..).trans (fancy u _ (flipT x k h (c:=c)).1)
lemma sta (u:Site c)(he:Nearby x) : ‖bias T p x u‖≤ peg u (order (power p)):=by
    obtain ⟨k,he⟩:=he; let f:=Lattice.lift u+x; let K:=power p
    unfold bias; rw [norm_mul]; apply (mul_le_of_le_one_left (norm_nonneg _) (tintE u T)).trans; rw [profile,Complex.norm_real,norm_mul,norm_prod]; simp only [one_pow,norm_one,one_mul]; unfold peg order; rw[← prod_pow_eq_pow_sum]; refine prod_le_prod (fun i _=> norm_nonneg _) (fun i _=>?_)
    have hp : Int.natAbs (f i) ≤ 1+pdist u:= (Int.natAbs_add_le ..).trans ((Nat.add_le_add (component_le u i) ((flipT (c:=c) _ _ he).2 i)).trans_eq (Nat.add_comm ..))
    rw [norm_div,norm_pow]; refine (div_le_self (pow_nonneg (norm_nonneg _) _) (by simp; exact Nat.factorial_pos _)).trans (pow_le_pow_left₀ (norm_nonneg _) ?_ _); change ‖(f i:ℝ)‖≤_; rw [←norm_natAbs, Real.norm_natCast]; exact_mod_cast hp
lemma sep0(u v:Site c): sepW 0 u v=1+max (pdist u:ℝ) (pdist v:ℝ):=by simp[sepW,separation]
lemma nova(hp:Nearby x)(h: order (power p)+order (power q) ≤ 2)(u v:Site c): ‖syrup T p q x u v-beamT T p q x u v‖≤ (80/(c.val:ℝ))*sepW 0 u v^3:=by
     let f:= heat x u*Nw T p (u+wrap c x); let g:= heat x v*Nw T q (v+wrap c x); let z:= order (power p); let k:=order (power q); let y:= bias T p x u; let H:= bias T q x v; let M:=sepW 0 u v; have hM:1 ≤ M:=arm ..; have hV: syrup T p q x u v=f*g:=by unfold syrup f g; ring
     rw [hV]; by_cases hx: 8*(pdist u+2)< c.val ∧ 8*(pdist v+2)< c.val; · rw[show f=y from colon p T x u hp hx.1,show g=H from colon q T x v hp hx.2, show y*H=beamT T p q x u v from rfl, sub_self,norm_zero]; change _ ≤ _ * M^3; positivity
     have hu:= tinct p T x u hp; have hv:= tinct q T x v hp; have h1:= sta p T x u hp; have h2:= sta q T x v hp; have hb:peg u z*peg v k ≤ M^2:=by
         refine le_trans (b:= M^(z+k)) ?_ (pow_le_pow_right₀ hM h); rw [pow_add]; have hf:1+(pdist u:ℝ) ≤ M:=by unfold M; rw [sep0]; exact add_le_add_right (le_max_left ..) _ -- conj
         have hh:1+(pdist v:ℝ) ≤ M:=by unfold M; rw[sep0]; exact add_le_add_right (le_max_right ..) _
         exact mul_le_mul (pow_le_pow_left₀ (by positivity) hf _) (pow_le_pow_left₀ (by positivity) hh _) (by positivity) (by positivity)
     have hy:(c.val:ℝ) ≤16*M:=by
         unfold M; rw[sep0]; by_cases hp:¬ 8*(pdist u+2)< c.val
         · have ht : (c.val:ℝ) ≤8*(pdist u+2:ℝ):=by exact_mod_cast Nat.le_of_not_gt hp
           linarith[le_max_left (pdist u:ℝ) (pdist v:ℝ),Nat.cast_nonneg (α:=ℝ) (pdist u)]
         have ht: (c.val:ℝ)≤8*(pdist v+2:ℝ):=by exact_mod_cast Nat.le_of_not_gt (not_and.mp hx (not_not.mp hp))
         linarith [le_max_right (pdist u:ℝ) (pdist v:ℝ), Nat.cast_nonneg (α:=ℝ) (pdist v)]
     have hQ:‖f*g‖≤4*M^2:=by
         rw [norm_mul]; apply (mul_le_mul hu hv (norm_nonneg _) ((norm_nonneg _).trans hu)).trans; rw [show (2:ℝ)^z* peg u z*(2^k*peg v k)= 2^(z+k)*(peg u z*peg v k) from (by rw [pow_add];ring)]; exact mul_le_mul ((pow_le_pow_right₀ (by norm_num) h).trans_eq (by norm_num : (2:ℝ)^ (2:ℕ)=4)) hb (mul_nonneg (pin_peg ..).le (pin_peg ..).le) (by norm_num)
     have hE:‖y*H‖ ≤ M^2:=by rw [norm_mul]; exact (mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)).trans hb
     change _ ≤ _*M^3; rw [div_mul_eq_mul_div,le_div_iff₀ (by positivity)]; apply le_trans (mul_le_mul_of_nonneg_right ((norm_sub_le ..).trans (add_le_add hQ hE)) (show 0≤(c.val:ℝ) from by positivity)); nlinarith only [mul_le_mul_of_nonneg_right hy (sq_nonneg M)]
variable (f g:Flavor 6)(i j:Fiber)
local notation "Rd"=> reed f g i j
lemma grains {U:BudgetPoint} (H:Grid c→G★)(he:Tutor 0 U H v n r C)(hv:0<v)(hp:Nearby x)(h: order (power p)+order (power q)≤ 2)(hn:3 ≤ n)(hr: 2< r) : ‖Rd (syrup T p q x) (H 1)- Rd (beamT T p q x) (H 1)‖ ≤ (80/(c.val:ℝ))*(C/v^2):=by
      change ‖(∑ k:Site c,∑ j:Site c,_)-(∑ k:Site c,∑ j:Site c,_)‖≤_; rw[←sum_sub_distrib]; simp_rw [←sum_sub_distrib,←sub_mul]; apply le_trans (norm_sum_le ..); apply (sum_le_sum (fun i _ => norm_sum_le ..)).trans
      apply le_trans _ (mul_le_mul_of_nonneg_left (fruitful he hv f g i j [] (Nat.zero_le _) (by simp) hn hr) (show (0:ℝ) ≤ 80/(c.val:ℝ) from by positivity)); simp_rw[Finset.mul_sum]; refine sum_le_sum fun i0 _=>sum_le_sum fun j0 _=>?_ ; rw[norm_mul]; exact (mul_le_mul_of_nonneg_right (nova p q T x hp h i0 j0) (norm_nonneg _)).trans_eq (mul_assoc ..)
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.grains
