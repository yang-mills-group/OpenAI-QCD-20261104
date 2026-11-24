import YM.QCD.Jets.Vault
/-! # earned short radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Jets.Touch
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.AbsoluteSums Footprint Trees
open Sun ConnectedActivityE6 Pressure Animals Garden
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F j k:ℕ}{L:Side} {x u v a b c ν C D T θ w κ q Y ε e z: ℝ} {i m:ℕ}{f g: ℝ→ℝ}
-- pick saturation exponent 1/32 so Slot germ lost s~ b^{1/16}. δ=b^-1/16. works with Taylor grade three. pick mass supply way larger than intended.
def haloK (L:Side)(x:ℝ) := betaF su x L ^ (-(1/32):ℝ)
def coneK (L:Side)(a x:ℝ) := a*haloK L x^2

lemma kentucky (L:Side){A:ℝ}(hp:0<A):∀ᶠ x in atTop,0<haloK L x ∧ haloK L x≤A∧ haloK L x≤1:=by
  let H:Rate su L (-(1/32)) (haloK L):=Rate.power
  filter_upwards [Delay.shift_pos su L,H.below (by norm_num) _ hp, H.below (by norm_num) _ one_pos] with x hx h ht using ⟨Real.rpow_pos_of_pos hx _,(le_abs_self _).trans h,(le_abs_self _).trans ht⟩
lemma shade_e (L: Side){A:ℝ}(he:A≠0): Rate su L (1/16) (fun x=>(coneK L A x/2)⁻¹):=by
   have hm : Rate su L (1/32) (fun x=> (haloK L x)⁻¹) := Rate.power.congr ((Delay.shift_pos su L).mono fun x hx=> by simp only [haloK,Real.rpow_neg hx.le,inv_inv])
   have hv:= ((hm.pow 2).mul_left (2*A⁻¹)); rw [show (1/32:ℝ)*↑(2:ℕ)=1/16 from by norm_num] at hv
   refine hv.congr (Eventually.of_forall fun x=>?_); dsimp only [coneK]; simp; ring
lemma filming (L: Side){A:ℝ}(he:0<A)(B:ℝ) : ∀ᶠ x in atTop,B*(radiusB x+1:ℝ)^5*fiery su x L < coneK L A x/2 :=by
   have h : Rate su L (-(1/2)) (fun x=>B*(radiusB x+1:ℝ)^5*fiery su x L):=by simpa only [zero_mul,zero_add] using! (((Rate.radius_price.add (Rate.const 1)).pow 5|>.mul_left B).mul Rate.flame)
   filter_upwards [(h.mul (shade_e L he.ne')).below (by norm_num) (1/2) (by norm_num),kentucky L he] with x hx hz; have hv:= (le_abs_self _).trans hx; rw [← div_eq_mul_inv] at hv; exact (div_lt_one (half_pos (mul_pos he (pow_pos hz.1 _)))).mp (hv.trans_lt (by norm_num))

-- tab charge inequality
lemma sol (L:Side)(P : Plan j) (D R H a r A:ℝ)(he:0<A)(hr:0<r)(B m:ℕ):
    Rate su L (-(1/32)) (fun x=> tabP P L D R H a r 0 (haloK L x) (fiery su x L) (coneK L A x) m (radiusB x) B - D*slope L/(L.val:ℝ)):=by
    unfold tabP
    simp_rw [add_assoc,add_sub_cancel_left]
    have hp₁: Rate su L 0 (fun x=>(1+(↑(radiusB x)+1:ℝ))^m):=by simpa only [zero_mul] using ((Rate.const _).add ((Rate.radius_price).add (Rate.const (1:ℝ)))|>.pow m)
    have hp₂: Rate su L 0 (fun x=> (2*↑(radiusB x)+1:ℝ)^4):=by simpa only [zero_mul] using ((Rate.radius_price.mul_left (2:ℝ)).add (Rate.const (1:ℝ))|>.pow 4)
    apply Rate.add
    · exact ((hp₁.mul hp₂).mul ((((Rate.power.mul_left (stamp P L)).mul_right a⁻¹).mul_right (massL L)))|>.weaken (by norm_num)) -- defeq?
    have hP : Rate su L (1/16) (fun x=> (coneK L A x/2)⁻¹*H*(radiusB x+1:ℝ)^5):=by simpa only [zero_mul,add_zero] using! (((shade_e L he.ne').mul_right H).mul ((Rate.radius_price.add (Rate.const (1:ℝ))).pow 5))
    have hm: Rate su L (-(1/32)) (fun x => Real.exp (-r*fossil (radiusB x) B)):=by simpa only [sub_zero] using pale r 0 hr B
    exact ((hp₁.mul (hm.add ((hP.mul (Rate.flame)).weaken (by norm_num)))).mul_right _).weaken (by norm_num)
lemma presses (P:Plan j) (F:ℕ) (D K:ℝ)(hK:0<K)(he:0≤D): ∃ m:ℕ,∀ L:Side,m≤L.val → K*fingers F*(D*slope L/(L.val:ℝ)) ≤ 1/2:=by
 obtain ⟨n,hn⟩:=exists_nat_gt (2*K*fingers F*D); have hf:0≤fingers F:=by unfold fingers; positivity
 refine ⟨n,fun L h=>?_⟩
 have hp:1 ≤ (L.val:ℝ):=by exact_mod_cast L.property
 have hv : Kit.slope L ≤ 1:=by unfold Kit.slope; apply (inv_le_one₀ (by positivity)).mpr (Real.sqrt_one ▸ Real.sqrt_le_sqrt hp)
 have hz:= hn.le.trans (show (n:ℝ)≤ L.val by exact_mod_cast h); rw [← mul_div_assoc]; apply (div_le_iff₀ (zero_lt_one.trans_le hp)).2; apply le_trans _ (show K*fingers F*D ≤ _ from by linarith)
 exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right he hv) (by positivity)
end YM.QCD.Jets.Touch
