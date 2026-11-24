import YM.Alum.Clean
set_option autoImplicit false
noncomputable section
namespace YM.Intag.Ibis
open Function Filter MeasureTheory RG Lattice Wilson Cells YM.Next.Rank.Station Finset
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Tide Push.GridApprox
open scoped BigOperators Classical Matrix.Norms.L2Operator ContDiff Topology TensorProduct
open QCD.Lat QCD.Acre QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb QCD.Acre.Stratum.MarchQ.Suburb.Talis QCD.Acre.Stratum.MarchQ.Suburb.Sapphire
open YM.Bank.Jule YM.Bank.Kith YM.Bloom.Jar
open MintV Suburb.Melt Suburb.Melt.Lobby
open Grammar Metric
variable {S:Scheme}{n D i ℓ j k m j₀ p w Uq q:ℕ}{L:Side}{Hp:Dial D}{H X z e v:ℝ}{R:Side}
local notation "η"=>measureV L Hp.e z
local notation "ξ"=>sharpM S L Hp z i
local notation "Pe" j:arg=> screen S j (sharpM S L Hp z i)
variable (Hp':Tier S L Hp z i ℓ j₀ p w)(A : Promises L Hp w Uq m k q e v H z)
variable (x y:Cover)(d: Axis→ℕ)(hk:ℓ≤ j)(hV:∀ a,d a ≤ ratioTo S j ℓ)(hd:∀ a,y a=(ratioTo S j ℓ • x) a+2*d a)
include Hp' hk hd hV
lemma shiftW : ‖(Pe j) y-(Pe ℓ) x‖ ≤ 4*(measureV L Hp.e z)⁻¹ :=by
     let V:=Pe j; let t:=ratioTo S j ℓ; let x':Cover:=t • x; let g:=rescaling S j (sharpM S L Hp z i); have hv : g*t= η⁻¹:= (Hp'.rise_step hk).trans Hp'.shadows
     have hG:0<g:=Hp'.rising
     let w: ℝ:= 2*η⁻¹; let p':= V y-V x'
     have h(i:Axis): ‖p' i‖ ≤ w:=by
           change ‖g*(y i:ℝ)-g*(↑(x' i):ℝ)‖≤ w; unfold w;  -- adjust type Pi smul
           have he:(d i:ℝ) ≤ t:=Nat.cast_le.mpr (hV i)
           have hh:g*((y i:ℤ):ℝ)-g*((x' i:ℤ):ℝ)=g*(2*d i):=by rw [hd i]; push_cast; change g*((↑(x' i):ℝ)+2*d i)-_= _; ring
           -- no rw hd first.Edit
           rw [hh,Real.norm_of_nonneg (by positivity), ←hv]; nlinarith only [mul_le_mul_of_nonneg_left he hG.le]
     have HpZ:‖p'‖^2 ≤4*w^2:=by
           rw [PiLp.norm_sq_eq_of_L2]; exact (Finset.sum_le_sum (fun i _=>pow_le_pow_left₀ (norm_nonneg _) (h i) 2)).trans_eq (by simp[Axis])
     rw [Hp'.joins x hk]; change ‖p'‖ ≤ _; unfold w at HpZ; have ht: 0< η⁻¹ := inv_pos.mpr (χone ..); nlinarith only [ht, HpZ, norm_nonneg p']
local notation "xy!" x:arg=> ![(0:E4), x]
variable (ht: ![(0:E4), screen S j (sharpM S L Hp z i) y] ∈ flats (Fin 2) (3*e) (v/4))
variable (hn: 2*(v*measureV L Hp.e z)<((S.side R ℓ).val:ℝ))
include A
lemma plump : ‖ ![(0:E4),(Pe ℓ) x]- ![0,(Pe j) y]‖≤ lapT L Hp z:=by
       apply profits _ _ _ (mul_nonneg (by norm_num:(0:ℝ) ≤200) (inv_nonneg.mpr ((χone ..).le))); intro i; fin_cases i
       · change ‖(0:E4)-0‖ ≤ _; rw [sub_self,norm_zero]; exact mul_nonneg (by norm_num) (inv_nonneg.mpr (χone ..).le) -- prove maybe positivity unknown
       change ‖(Pe ℓ) x-(Pe j) y‖ ≤ _; rw[norm_sub_rev]; apply (shiftW Hp' x y d hk hV hd).trans; exact mul_le_mul_of_nonneg_right (by norm_num) (inv_nonneg.mpr ((χone ..).le))
-- strict cone choosing.
include ht hn
set_option maxHeartbeats 610000
lemma spirit (he:0<e)(hφ:0<v)(hN:∀ a:Axis,2*e≤ ((Pe j) y) a) : ![0,(Pe ℓ) x] ∈ flats (Fin 2) (2*e) (v/2):=by
       let X:=(xy! ((Pe j) y)); let Y:=xy! ((Pe ℓ) x); have hh: 2*lapT L Hp z ≤ e := A.dust.trans (min_le_right ..); have hv: 2*lapT L Hp z ≤ v/4 := A.dust.trans (min_le_left ..); have hp : Y∈ flats (Fin 2) (2*e) (v/2) := puff (3*e) (v/4) X ht Y _ _ (lapT L Hp z) (plump Hp' A x y d hk hV hd) (by linarith only [hh]) (by linarith only [hv]);
       exact hp
lemma blunt (he:0<e)(hφ:0<v)(hN:∀ a:Axis,2*e≤ ((Pe j) y) a) (a:Axis) : (ratioTo S ℓ p:ℤ) ≤ x a:=by
       have hh: 2*lapT L Hp z ≤ e := A.dust.trans (min_le_right ..)
       let g:=measureV L Hp.e z; have hG:0<g:=χone ..
       have hx : (Pe ℓ) x=g⁻¹ • Massive.vector x:=by unfold screen; rw[Hp'.shadows]
       have h:((Pe j) y) a-((Pe ℓ) x) a ≤ lapT L Hp z:=calc
              _ ≤ ‖((Pe j) y-(Pe ℓ) x) a‖:= le_abs_self _
              _ ≤ ‖(Pe j) y-(Pe ℓ) x‖:=PiLp.norm_apply_le ..
              _ ≤ lapT L Hp z:= (shiftW Hp' x y d hk hV hd).trans (mul_le_mul_of_nonneg_right (by norm_num: (4:ℝ) ≤ 200) (inv_nonneg.mpr hG.le))
       have hz:e≤ ((Pe ℓ) x) a:=by linarith only [hh,h,hN a,he]
       rw [hx] at hz; change e ≤g⁻¹*(↑(x a):ℝ) at hz; rw [inv_mul_eq_div] at hz; have h':=(le_div_iff₀ hG).1 hz; have hk':= A.hue.marks _ Hp'.repB; exact_mod_cast (show (ratioTo S ℓ p:ℝ) ≤ ↑(x a) from by linarith only [h',hk',show (0:ℝ) ≤ratioTo S ℓ p from Nat.cast_nonneg _]) -- mod_cast Int corners.
lemma scone (he:0<e)(hφ:0<v)(hN:∀ a:Axis,2*e≤ ((Pe j) y) a) (a:Axis): 2*x a≤(S.side R ℓ).val:=by
       let Y:=xy! ((Pe ℓ) x); have hp := spirit Hp' A x y d hk hV hd ht hn he hφ hN
       let g:=measureV L Hp.e z; have hG:0<g:=χone ..
       have hx : (Pe ℓ) x=g⁻¹ • Massive.vector x:=by unfold screen; rw[Hp'.shadows]
       have h:‖(Pe ℓ) x‖ ≤ v/2/2:= perim (2*e) (v/2) Y hp (by linarith only[hφ]) 1
       have Hx:= ((le_abs_self (((Pe ℓ) x) a)).trans ((show ‖((Pe ℓ) x) a‖≤ ‖(Pe ℓ) x‖ from PiLp.norm_apply_le ..).trans h))
       rw [hx] at Hx; change g⁻¹*(↑(x a):ℝ) ≤ _ at Hx; rw [inv_mul_eq_div] at Hx; replace Hx:=(div_le_iff₀ hG).1 Hx; exact_mod_cast (show 2*(x a:ℝ)≤ (↑(S.side R ℓ).val:ℝ) from by nlinarith only [Hx,hG,hφ, hn])
lemma spoofs (he:0<e)(hφ:0<v)(hN:∀ a:Axis,2*e≤ ((Pe j) y) a) : ![0,(Pe ℓ) x] ∈ flats (Fin 2) (2*e) (v/2) ∧(∀ a:Axis,(ratioTo S ℓ p:ℤ) ≤ x a) ∧(∀ a:Axis,2*x a≤(S.side R ℓ).val):=by
   exact ⟨spirit Hp' A x y d hk hV hd ht hn he hφ hN,blunt Hp' A x y d hk hV hd ht hn he hφ hN,scone Hp' A x y d hk hV hd ht hn he hφ hN⟩
end YM.Intag.Ibis
#print axioms YM.Intag.Ibis.spoofs
