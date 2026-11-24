import YM.Alum.Rally
import YM.Alum.Ibis
import YM.Alum.Cords
import YM.Alum.Lit
import YM.Alum.Hoist
/-! Reading scales & geometry at vintage. Universal euclidean coordinates native stencil lifts presented at physical `resolution` r, independent of regulator beyond i. -/
set_option autoImplicit false
noncomputable section
namespace YM.Intag
open Function Filter MeasureTheory RG Lattice Wilson Cells YM.Next.Rank.Station Finset
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Tide Push.GridApprox
open scoped BigOperators Classical Matrix.Norms.L2Operator ContDiff Topology TensorProduct
namespace Ibis
open QCD.Lat QCD.Acre QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb QCD.Acre.Stratum.MarchQ.Suburb.Talis QCD.Acre.Stratum.MarchQ.Suburb.Sapphire
open YM.Bank.Jule YM.Bank.Kith YM.Bloom.Jar
open MintV Suburb.Melt Suburb.Melt.Lobby
variable (S:Scheme) (L:Side) {D:ℕ}(Hp:Dial D)(z:ℝ)
-- earnings at Lamp, numeric proof.Book.Hq. powers chosen arbitrarily.Meet eventual budgets.
variable (w Uq m K a q:ℕ)(e v H:ℝ)
local notation "ω"=>measureV L
noncomputable abbrev pib := Dial.worthA L Hp z
local notation "K!" x:arg=> Dial.worthA L Hp x
local notation "dP"=>Hp.R
local notation "A" z:arg=> Dial.rateB L w z + Dial.worthA L Hp z
noncomputable def reserved (w:ℕ)(x:ℝ):= Dial.rateB L w x + Dial.worthA L Hp x
noncomputable def pennies := H*((K:ℝ)*(pib L Hp z * ((reserved L Hp w z)^K)))
noncomputable abbrev lapT (z:ℝ):= 200*(measureV L Hp.e z)⁻¹
noncomputable abbrev minorV (a:ℕ)(z:ℝ):= (measureV L a z)⁻¹
set_option quotPrecheck false
structure Promises (z:ℝ):Prop where
     hue : Room L Hp w Uq m K e v z
     fonts : w<Hp.e
     permit : 2 ≤Uq
     dust : 2*lapT L Hp z ≤ min (v/4) e
     arity : ∀ (n:ℕ), n≤ K→ ∀ (r:ℕ), r≤ 2^n→(r:ℝ)*(pennies L Hp z w n H)+pib L Hp z ≤ minorV L a z
     tide : ∀ (n:ℕ), n≤ K→ (n:ℝ)*(pib L Hp z*(reserved L Hp w z)^n)+((2:ℝ)^n*(H*pib L Hp z)+ H*lapT L Hp z) ≤ minorV L a z /4
     prep : 1 ≤unveil L Hp z
     watch : 4*(4*(reserved L Hp w z)^2 / (unveil L Hp z:ℝ)) + H*lapT L Hp z≤ minorV L a z/2
#print Promises
variable (hL:1< L.val)
include hL
lemma starCostP {a b c:ℕ}(x:ℝ→ ℝ)(hx:PageP L x b)(hf:max a b<c)(u:ℝ)(hu:0 < u): ∀ᶠ z:ℝ in atTop,x z * minorV L c z ≤ minorV L a z/u:=by
     let f(z):=u * x z * measureV L a z; have ht:PageP L f (max a b):=((hx.out L (le_max_right ..)).timesL L u).times L (PageP.budget_lo L (le_max_left ..)); filter_upwards [ht.cheaper L hL hf] with z h; have hp:0 < ω a z:=χone ..; have hv:0<ω c z:=χone ..; unfold minorV; unfold f at h; field_simp; nlinarith only [h]
omit hL
lemma riseT : PageP L (reserved L Hp w) (w+9):= (PageP.loan L _).harm L (PageP.seed L _)
lemma gold0 : 1 ≤ reserved L Hp w z:= le_trans (uniformV ..) (le_add_of_nonneg_right (inv_nonneg.mpr ((χone ..).le)))
lemma grow : 0 < minorV L a z:=inv_pos.mpr (χone ..)
lemma avona (x:ℝ):(unveil L Hp x : ℝ)=measureV L Hp.R x:=(pitchN ..).symm
lemma jovial (x:ℝ):1 ≤ unveil L Hp x:= by exact_mod_cast (show (1:ℝ) ≤ (unveil L Hp x:ℝ) from (uniformV ..|>.trans (avona L Hp x|>.symm.le)))
include hL
lemma fig (hk:100*(K+1) ≤ Uq)(he:dP<Hp.e) (hy:w+9<dP) (hu:a< dP)(hw:0<w)(hP:0< e)(hV:0 < v)(hG:1≤ H) :∀ᶠ z in atTop, Promises L Hp w Uq m K a e v H z:=by
     let Z:= reserved L Hp w; have ht:= riseT L Hp w
     have h₁:=starCostP L (x:=fun z=> ((2:ℝ)^K*H*K)*Z z^K) hL ((ht.liftNat L K).timesL L _) (show max a (w+9)<Hp.R from max_lt hu hy) 2 (by norm_num)
     have h₂:=starCostP L (x:=fun z=> (K:ℝ)*Z z^K) hL ((ht.liftNat L K).timesL L _) (max_lt hu hy) 12 (by norm_num)
     have h₃:=starCostP L (x:=fun _=> (2:ℝ)^K*H) hL (PageP.just L _ a) (show max a a <dP from max_lt hu hu) 12 (by norm_num)
     have h₄:=starCostP L (x:=fun z=> 16*Z z^2) hL ((ht.liftNat L 2).timesL L _) (max_lt hu hy) 4 (by norm_num)
     have h₅:=starCostP L (x:=fun z=>1) hL (PageP.just L _ a) (show max a a<Hp.R from max_lt hu hu) 2 (by norm_num)
     have h₆:=starCostP L (x:=fun z=> H*200) hL (PageP.just L _ a) (show max a a< Hp.e from lt_trans (max_lt hu hu) he) 12 (by norm_num)
     have hm:= PageP.absorb L (PageP.just L 400 0) hL (B:=Hp.e) (by omega) (min (v/4) e) (lt_min (by positivity) hP) -- argument name B
     filter_upwards [hm,h₁,h₂,h₃,h₄,h₅,h₆,light L Hp w Uq m K e v hL hk he hw (lt_trans (Nat.lt_of_le_of_lt (Nat.le_add_right ..) hy) he) hP hV] with z hz ha hb hc hd he hf hT
     have hE:0 ≤ H:= zero_le_one.trans hG; have hU:0≤ pib L Hp z:= (grow L z dP).le -- order
     have hZ:1 ≤ Z z:= gold0 L Hp z w
     let m':= minorV L a z
     change _ * minorV L Hp.R z ≤ m'/2 at he; rw [one_mul] at he
     have ht:H * lapT L Hp z ≤ m'/12:= (show H * _= (H*200)*minorV L Hp.e z from (mul_assoc ..).symm).trans_le hf
     refine ⟨hT,by omega, by omega,(?_),fun n hn r hr=>?_ ,fun n hn=>?_,jovial ..,(?_)⟩
     · unfold lapT; rw [←mul_assoc,show (2:ℝ)*200=400 by norm_num,← div_eq_mul_inv]; exact hz
     · have hp: r*pennies L Hp z w n H ≤ m'/2:=by
                 unfold pennies; refine le_trans ?_ ha
                 calc (r:ℝ)*(H*((n:ℝ)*(_ * _))) ≤ ((2:ℝ)^K)*(H*((K:ℝ)*( (pib L Hp z) * Z z^K))) := by
                       have hK:0 ≤ Z z:=zero_le_one.trans hZ
                       refine mul_le_mul (show (r:ℝ) ≤ (2:ℝ)^K from ?_) (mul_le_mul_of_nonneg_left (mul_le_mul (by exact_mod_cast hn) (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hZ hn) hU) (mul_nonneg hU (pow_nonneg hK _)) (Nat.cast_nonneg _)) hE) ?_ (by positivity); exact_mod_cast hr.trans (pow_le_pow_right₀ (show 1 ≤ (2:ℕ) from (by omega)) hn); exact mul_nonneg hE (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hU (pow_nonneg hK _)))
                      _= _ :=by change _=_*pib L Hp z; ring
       have hx:= add_le_add hp he; apply le_trans hx; change m'/2+m'/2≤ m'; linarith
     · have he :0 ≤ Z z:= zero_le_one.trans hZ; have hi: (n:ℝ)*(pib L Hp z*Z z ^ n) ≤ m'/12 :=calc
                _ ≤ (↑K:ℝ)*(pib L Hp z*Z z^K):=mul_le_mul (by exact_mod_cast hn) (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hZ hn) hU) (mul_nonneg hU (pow_nonneg he _)) (Nat.cast_nonneg _)
                _ ≤ _:=by rw [mul_comm (pib ..),←mul_assoc]; exact hb
       have hj:(2:ℝ)^n*(H*pib L Hp z) ≤ m'/12:= (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num:(1:ℝ)≤2) hn) (mul_nonneg hE hU)).trans ((mul_assoc ..).symm.trans_le hc)
       apply (add_le_add hi (add_le_add hj ht)).trans; change m'/12+(m'/12+m'/12) ≤ m'/4; linarith
     · rw [avona]; let q:=4*(4*Z z^2 / measureV L Hp.R z); have h:q ≤ m'/4:= (show q= (16*Z z ^ 2)* minorV L Hp.R z from (by unfold q minorV; ring)).trans_le hd; have he := add_le_add h ht; apply he.trans; have h0:0 < m':= grow ..; change m'/4 + m'/12 ≤ m'/2; linarith
end Ibis
end YM.Intag
#print axioms YM.Intag.Ibis.fig
